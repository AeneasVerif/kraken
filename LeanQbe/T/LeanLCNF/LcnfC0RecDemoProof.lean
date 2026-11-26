module

public import LeanQbe.T.LeanLCNF.LcnfC0RecDemo
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.MainCertScc
public import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.Rules

/-!
# Budget-Indexed WP Soundness & Concrete `List Nat` Fixture (`LcnfC0RecDemoProof`)

Target-generic (`0` arch imports, `0` `import all`) soundness proof for the structurally recursive
Lean `LCNF` function `RecDemo.listSum : List Nat → Nat` compiled through
`compile_linked_budget_scc!` and linked onto `rtC0CoreMod`:

1. **`List Nat` heap representation (`consNodeAt`, `listNatAt`)**: exact `24`-byte Lean 4
   `List.cons` constructor layout (`m_rc = 1`, `m_cs_sz = 24`, `m_other = 2`, `m_tag = 1`,
   tagged scalar `boxNat x` @ `+8`, tail pointer @ `+16`; `List.nil = 1#64`).
2. **Budget-indexed specification (`listSumSpec`) & fixed-point proof (`listSum_budgetSemScc`)**:
   well-founded induction (`BudgetEnv.lfp_wf_mkSccOp` on list length `d`) proving
   `BudgetEnv.semScc` at stack budget `256 + 32 * d`.
3. **Target-generic `LinkedCertScc` bridge (`recDemoCert_listSum_fnSpec`,
   `recDemoCert_listSum_eventually`)**: connects `semChunks` across `rtScc.chunks ++ [recChunk]`
   to `LinkedCertScc.fnSpec_host_src_of_le` and `LinkedCertScc.eventually_ret1_i64_of_le`.
4. **Concrete `[10, 20, 30]` fixture (`recList3Bytes`, `recList3_listNatAt`)**: `72`-byte
   `List.cons` chain at `0x1000#64` summing to `RecDemo.listSum [10, 20, 30] = 60`
   (`boxNat 60 = 121#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step

/-! ## 1. Tagged-Scalar `Nat` Helpers & `List Nat` Heap Predicates -/

private theorem boxNat_and_one {n : Nat} (hn : n < 2 ^ 63) :
    (boxNat n &&& 1#64) = 1#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := by decide
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, boxNat, BitVec.toNat_ofNat, hmod]
  omega

private theorem boxNat_add_fast {aVal bVal : Nat} (hlt : aVal + bVal < 2 ^ 63) :
    ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true ∧
    ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false ∧
    (boxNat aVal - 1#64) + boxNat bVal = boxNat (aVal + bVal) := by
  have ha : (boxNat aVal).toNat = 2 * aVal + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb : (boxNat bVal).toNat = 2 * bVal + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (boxNat aVal - 1#64).toNat = 2 * aVal := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, ha])]
    simp [ha]
  have hadd : ((boxNat aVal - 1#64) + boxNat bVal).toNat = 2 * (aVal + bVal) + 1 := by
    rw [BitVec.toNat_add, hsub, hb, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsumEq : (boxNat aVal - 1#64) + boxNat bVal = boxNat (aVal + bVal) := by
    apply BitVec.eq_of_toNat_eq
    rw [hadd, boxNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha1 : (boxNat aVal &&& 1#64) = 1#64 := boxNat_and_one (by omega)
  have hb1 : (boxNat bVal &&& 1#64) = 1#64 := boxNat_and_one (by omega)
  have hlsb : (boxNat aVal &&& boxNat bVal &&& 1#64) = 1#64 := by
    rw [BitVec.and_assoc, hb1, ha1]
  have hbit : ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true := by
    rw [hlsb]; decide
  have hult : ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, hadd, hb]
    omega
  exact ⟨hbit, hult, hsumEq⟩

/-- Little-endian header bytes of a `List.cons` heap object (`m_rc = 1`, `m_cs_sz = 24`,
`m_other = 2`, `m_tag = 1`). -/
@[expose] def consHdrBytes : List (Val i8) :=
  [1#8, 0#8, 0#8, 0#8, 24#8, 0#8, 2#8, 1#8]

/-- Raw byte image of `consHdrBytes`, matching `LcnfObj.header` for a `List.cons` cell. -/
theorem consHdrBytes_matches_lcnfObj (p head tail : BitVec 64) :
    bytesOf (t := i8) consHdrBytes =
      Int.toBytes 8 (LcnfObj.header
        { addr := p, rc := 1#32, csSz := 24, other := 2, tag := 1,
          fields := [head, tail] }).toInt := by
  dsimp only [LcnfObj.header]
  decide

/-- Separation-logic footprint of one `24`-byte `List.cons` heap node at `p` (`tag = 1` @ `+7`,
`head` @ `+8`, `tail` @ `+16`). -/
@[expose] def consNodeAt (p head tail : BitVec 64) : Mem 64 → Prop :=
  array (t := i8) p consHdrBytes ⋆ cell64 (p + 8#64) head ⋆ cell64 (p + 16#64) tail

/-- Inductive heap layout of a `List Nat` of tagged-scalar elements rooted at `p`
(`List.nil = 1#64`, `List.cons` = aligned heap pointer to `consNodeAt`). -/
@[expose] def listNatAt : BitVec 64 → List Nat → Mem 64 → Prop
  | p, [], m => p = 1#64 ∧ emp m
  | p, x :: rest, m =>
    (p &&& 1#64) = 0#64 ∧
    ∃ nxt : BitVec 64, (consNodeAt p (boxNat x) nxt ⋆ listNatAt nxt rest) m

private theorem consNodeAt_load_tag {p head tail : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (consNodeAt p head tail ⋆ R) m) :
    loadVal m i8 (p + 7#64) = some 1#8 := by
  unfold consNodeAt at hm
  have hm' : (array (t := i8) p consHdrBytes ⋆
      (cell64 (p + 8#64) head ⋆ cell64 (p + 16#64) tail ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  have hld := loadVal_array (t := i8) (i := 7) (by decide) (by decide) hm'
  exact hld

private theorem consNodeAt_load_head {p head tail : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (consNodeAt p head tail ⋆ R) m) :
    loadVal m i64 (p + 8#64) = some head := by
  unfold consNodeAt at hm
  have hm' : (cell64 (p + 8#64) head ⋆
      (array (t := i8) p consHdrBytes ⋆ cell64 (p + 16#64) tail ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

private theorem consNodeAt_load_tail {p head tail : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (consNodeAt p head tail ⋆ R) m) :
    loadVal m i64 (p + 16#64) = some tail := by
  unfold consNodeAt at hm
  have hm' : (cell64 (p + 16#64) tail ⋆
      (array (t := i8) p consHdrBytes ⋆ cell64 (p + 8#64) head ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

/-! ## 2. Budget-Indexed Specification & `BudgetEnv.lfp_wf_mkSccOp` Proof -/

/-- Exact stack budget required by `RecDemo.listSum` for lists of length `≤ d`:
`256 + 32 * d`. -/
@[expose] def listSumReqBudget (d : Nat) : Nat :=
  recDemoMinEntry + d * recDemoMaxFrame

/-- Source-level specification of `RecDemo.listSum` at maximum list depth `D`:
for any `xs : List Nat` laid out at `p` with `xs.length ≤ D` and `RecDemo.listSum xs < 2 ^ 63`,
`listSum(rt, p)` returns `boxNat (RecDemo.listSum xs)` leaving memory unchanged (`XPost`-free). -/
@[expose] def listSumSpec (D : Nat) : Spec [i64, i64] [i64] :=
  fun (_rt, p, ()) m Q _ =>
    ∃ (xs : List Nat) (R : Mem 64 → Prop),
      xs.length ≤ D ∧ RecDemo.listSum xs < 2 ^ 63 ∧
      (listNatAt p xs ⋆ R) m ∧
      Q (boxNat (RecDemo.listSum xs), ()) m

private def listSumIdxEnv (d : Nat) : Env :=
  fun nm as bs xs m Q X =>
    nm = recDemoListSumName ∧
    ∃ (ha : as = [i64, i64]) (hb : bs = [i64]),
      listSumSpec d (ha ▸ xs) m (hb ▸ Q) X

private theorem budget_wp_mono_local :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m' _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m' hwp

private theorem listSum_step_wp {Γcall : Env} {d : Nat}
    (hrec : ∀ j, j < d →
      ∀ xs m Q X, listSumSpec j xs m Q X →
        Γcall recDemoListSumName [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, listSumSpec d xs m Q X →
      Func.wp Γcall recDemoListSumFn.body xs m Q X := by
  rintro ⟨rt, p, ⟨⟩⟩ m Q X ⟨xs, R, hlen, hsum, hm, hq⟩
  let sumBlk (v7 : Val i64) (sumTup : Tup Val [i64]) : Expr Val Cont [i64] :=
    .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v7) (.imm 1#64)) fun v11 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v11.1) (.imm 0#64)) fun v12 =>
        .group (sig := [[]])
          (fun _ => .cons (fun _ => .ret (.var sumTup.1, ())) .nil)
          fun Jret =>
          .jnz (.var v12.1)
            (.jump Jret.1 ())
            (.load i32 (.var v7) fun rc =>
              .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var rc) (.imm 1#32)) fun is1 =>
                .jnz (.var is1.1)
                  (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := [])
                    (.var rt, .var v7, ()) fun _ => .jump Jret.1 ())
                  (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var rc) (.imm 1#32)) fun gt1 =>
                    .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var gt1.1)) fun b1 =>
                      .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var rc) (.var b1.1))
                        fun rc' => .store (.var rc'.1) (.var v7) (.jump Jret.1 ())))
  let tagBlk (tagTup : Tup Val [i64]) : Expr Val Cont [i64] :=
    .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i64) (.var tagTup.1) (.imm 0#64)) fun v2 =>
      .jnz (.var v2.1)
        (.ret (.imm 1#64, ()))
        (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 8#64)) fun v3 =>
          .load i64 (.var v3.1) fun v4 =>
            .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 16#64)) fun v5 =>
              .load i64 (.var v5.1) fun v6 =>
                .call recDemoListSumName (as := [i64, i64]) (bs := [i64])
                  (.var rt, .var v6, ()) fun v7 =>
                  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v4) (.var v7.1)) fun v8 =>
                    .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v8.1) (.imm 1#64)) fun v9 =>
                      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v9.1) (.imm 0#64))
                        fun v10 =>
                        .group (sig := [[i64]])
                          (fun _ => .cons (sumBlk v7.1) .nil)
                          fun Jsum =>
                          .jnz (.var v10.1)
                            (.let_ (_root_.LeanQbe.T.op2 (OpCode.sub i64) (.var v4) (.imm 1#64))
                              fun v13 =>
                              .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var v13.1)
                                  (.var v7.1)) fun v14 =>
                                .let_ (_root_.LeanQbe.T.op2 (OpCode.ult i64) (.var v14.1)
                                    (.var v7.1)) fun v15 =>
                                  .jnz (.var v15.1)
                                    (.call "lcnf_nat_slow"
                                      (as := [i64, i64, i64, i64]) (bs := [i64])
                                      (.var rt, .imm 1#64, .var v4, .var v7.1, ())
                                      fun v16 => .jump Jsum.1 (.var v16.1, ()))
                                    (.jump Jsum.1 (.var v14.1, ())))
                            (.call "lcnf_nat_slow"
                              (as := [i64, i64, i64, i64]) (bs := [i64])
                              (.var rt, .imm 1#64, .var v4, .var v7.1, ()) fun v17 =>
                              .jump Jsum.1 (.var v17.1, ())))
  change wp Γcall Q X
    (.let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var p) (.imm 1#64)) fun v0 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v0.1) (.imm 0#64)) fun v1 =>
        .group (sig := [[i64]]) (fun _ => .cons tagBlk .nil) fun Jtag =>
          .jnz (.var v1.1)
            (.let_ (_root_.LeanQbe.T.op2 (OpCode.lshr i64) (.var p) (.imm 1#64)) fun scTag =>
              .jump Jtag.1 (.var scTag.1, ()))
            (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 7#64)) fun tagAddr =>
              .load i8 (.var tagAddr.1) fun tag8 =>
                .let_ (_root_.LeanQbe.T.op1 (OpCode.zext 8 64) (.var tag8)) fun tag64 =>
                  .jump Jtag.1 (.var tag64.1, ()))) m
  cases xs with
  | nil =>
    obtain ⟨rfl, _⟩ := sep_pure_l.mp hm
    c0_let_simp
    refine wp_join_group (fun tagTup m' => tagTup.1 = 0#64 ∧ m' = m) ?_ ?_
    · rintro J ⟨tag, ⟨⟩⟩ m' ⟨rfl, rfl⟩
      rw [Blocks.get.eq_1]
      dsimp only [tagBlk]
      c0_let_simp
      rw [wp_jnz]
      refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var])⟩
      rw [wp_ret]
      exact hq
    · intro J hJ
      rw [wp_jnz]
      refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var])⟩
      c0_let_simp
      exact hJ _ m ⟨by decide, rfl⟩
  | cons x rest =>
    obtain ⟨hp0, hm1⟩ := sep_pure_l.mp hm
    obtain ⟨nxt, hmNode⟩ := sep_ex_l.mp hm1
    have hNodeR : (consNodeAt p (boxNat x) nxt ⋆ (listNatAt nxt rest ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hRestR : (listNatAt nxt rest ⋆ (consNodeAt p (boxNat x) nxt ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hldTag : loadVal m i8 (p + 7#64) = some 1#8 := consNodeAt_load_tag hNodeR
    have hldHd : loadVal m i64 (p + 8#64) = some (boxNat x) := consNodeAt_load_head hNodeR
    have hldTl : loadVal m i64 (p + 16#64) = some nxt := consNodeAt_load_tail hNodeR
    have hsumDef : RecDemo.listSum (x :: rest) = x + RecDemo.listSum rest := rfl
    have hsumRest : RecDemo.listSum rest < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hrestLt : rest.length < d := by simp at hlen; omega
    obtain ⟨hfastBit, hfastUlt, hfastEq⟩ := boxNat_add_fast (by rw [hsumDef] at hsum; exact hsum)
    have hrestBit : ((boxNat (RecDemo.listSum rest) &&& 1#64) != 0#64) = true := by
      rw [boxNat_and_one hsumRest]; decide
    c0_let_simp
    refine wp_join_group (fun tagTup m' => tagTup.1 = 1#64 ∧ m' = m) ?_ ?_
    · rintro J ⟨tag, ⟨⟩⟩ m' ⟨rfl, hm'⟩
      subst m'
      rw [Blocks.get.eq_1]
      dsimp only [tagBlk]
      c0_let_simp
      rw [wp_jnz]
      refine ⟨fun h => absurd h (by simp [Arg.val_var]), fun _ => ?_⟩
      c0_let_simp
      refine wp_load_of (v := boxNat x) (by simpa [Arg.val_var] using hldHd) ?_
      c0_let_simp
      refine wp_load_of (v := nxt) (by simpa [Arg.val_var] using hldTl) ?_
      let Pcall : Post [i64] := fun r m'' => r = (boxNat (RecDemo.listSum rest), ()) ∧ m'' = m
      have hCall : Γcall recDemoListSumName [i64, i64] [i64] (rt, nxt, ()) m Pcall X :=
        hrec rest.length hrestLt (rt, nxt, ()) m Pcall X
          ⟨rest, consNodeAt p (boxNat x) nxt ⋆ R, Nat.le_refl _, hsumRest, hRestR, ⟨rfl, rfl⟩⟩
      refine ⟨Pcall, X, hCall, ?_, fun _ _ _ _ hx => hx⟩
      rintro ⟨rVal, ⟨⟩⟩ m'' ⟨hrEq, hm''⟩
      subst m''
      obtain rfl : rVal = boxNat (RecDemo.listSum rest) := (Prod.ext_iff.mp hrEq).1
      c0_let_simp
      refine wp_join_group
        (fun sumTup m''' => sumTup.1 = boxNat (x + RecDemo.listSum rest) ∧ m''' = m) ?_ ?_
      · rintro Jsum ⟨sVal, ⟨⟩⟩ m''' ⟨rfl, hm'''⟩
        subst m'''
        rw [Blocks.get.eq_1]
        dsimp only [sumBlk]
        c0_let_simp
        refine wp_join_group (fun _ m4 => m4 = m) ?_ ?_
        · rintro Jret ⟨⟩ m4 hm4
          subst m4
          rw [Blocks.get.eq_1, wp_ret]
          exact hq
        · intro Jret hJret
          rw [wp_jnz]
          refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hrestBit])⟩
          rw [wp_jump]
          exact hJret () m rfl
      · intro Jsum hJsum
        rw [wp_jnz]
        refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hfastBit])⟩
        c0_let_simp
        rw [wp_jnz]
        refine ⟨fun h => absurd h (by simp [Arg.val_var, hfastUlt]), fun _ => ?_⟩
        rw [wp_jump]
        exact hJsum _ m ⟨hfastEq, rfl⟩
    · intro J hJ
      rw [wp_jnz]
      refine ⟨fun h => absurd h (by simp [Arg.val_var, hp0]), fun _ => ?_⟩
      c0_let_simp
      refine wp_load_of (v := 1#8) (by simpa [Arg.val_var] using hldTag) ?_
      c0_let_simp
      exact hJ (1#64, ()) m ⟨rfl, rfl⟩

/-- Budget-indexed `BudgetEnv.semScc` soundness for `RecDemo.listSum` at any depth `d` and
stack budget `sb ≥ 256 + 32 * d`, proved via `BudgetEnv.lfp_wf_mkSccOp`. -/
theorem listSum_budgetSemScc (extSigs : List SigEntry) (Γext : Env)
    (d sb : Nat) (hsb : listSumReqBudget d ≤ sb) :
    ∀ xs m Q X, listSumSpec d xs m Q X →
      BudgetEnv.semScc ⟨[recDemoListSumBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
        Γext sb recDemoListSumName [i64, i64] [i64] xs m Q X := by
  let BM : BudgetModule := ⟨[recDemoListSumBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
  have hmem : recDemoListSumBudgetFn ∈ BM.fns := List.mem_cons_self
  have hsig : (recDemoListSumName, [i64, i64], [i64]) ∈ BM.fnSigs := by
    simp [BM, BudgetModule.fnSigs, recDemoListSumBudgetFn, recDemoListSumFn,
      recDemoListSumName, recDemoTfs.tf_0, Fn.sig, Frontend.C0.TFlatFn.toFn]
  intro xs m Q X hspec
  refine BudgetEnv.lfp_wf_mkSccOp (lt := Nat.lt) Nat.lt_wfRel.wf listSumReqBudget BM
    (BudgetEnv.const Γext) budget_wp_mono_local listSumIdxEnv
    (fun idx sb' hsb' bfn hbfn Γcall _ hcall _ _ _ xs' m' Q' X' hS => by
      dsimp only [BM] at hbfn
      rw [List.mem_singleton] at hbfn
      subst hbfn
      rcases hS with ⟨_, ha, hb, hsp⟩
      have hmax : recDemoListSumBudgetFn.maxFrame ≤ sb' := by
        dsimp only [recDemoListSumBudgetFn, listSumReqBudget, recDemoMaxFrame,
          recDemoMinEntry] at hsb' ⊢
        omega
      have hmin : recDemoListSumBudgetFn.minEntry ≤ sb' := by
        dsimp only [recDemoListSumBudgetFn, listSumReqBudget, recDemoMaxFrame,
          recDemoMinEntry] at hsb' ⊢
        omega
      refine ⟨hmax, hmin, ?_⟩
      have hrec : ∀ j, j < idx → ∀ ys m₁ Q₁ X₁, listSumSpec j ys m₁ Q₁ X₁ →
          Γcall recDemoListSumName [i64, i64] [i64] ys m₁ Q₁ X₁ := by
        intro j hlt ys m₁ Q₁ X₁ hspj
        have hreqj : listSumReqBudget j ≤ sb' - recDemoListSumBudgetFn.maxFrame := by
          dsimp only [recDemoListSumBudgetFn, listSumReqBudget, recDemoMaxFrame,
            recDemoMinEntry] at hsb' ⊢
          omega
        exact hcall j hlt hreqj recDemoListSumName [i64, i64] [i64] ys m₁ Q₁ X₁
          ⟨hsig, rfl, rfl, rfl, hspj⟩
      exact listSum_step_wp hrec xs' m' Q' X' (by simpa using hsp))
    d sb hsb recDemoListSumName [i64, i64] [i64] xs m Q X ⟨hsig, rfl, rfl, rfl, hspec⟩

/-! ## 3. Target-Generic `LinkedCertScc` Semantic & Machine Bridges -/

theorem semChunks_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (cs₁ cs₂ : List (Chunk T lt exits nX)) (extSigs : List SigEntry) (Γ₀ : Env) :
    semChunks extSigs Γ₀ (cs₁ ++ cs₂) =
      semChunks (sccChunksSigAcc extSigs cs₁) (semChunks extSigs Γ₀ cs₁) cs₂ := by
  induction cs₁ generalizing extSigs Γ₀ with
  | nil => rfl
  | cons c rest ih =>
    simpa only [List.cons_append, semChunks, sccChunksSigAcc] using
      ih (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)

/-- Target-generic semantic bridge: any `LinkedCertScc` whose chunk list is
`preChunks ++ [Chunk.recBudgetSCC ext [recDemoListSumBudgetFn] hints recDemoExportBound
[(recDemoListSumName, recDemoExportBound)] cbr]` entails `listSumSpec recDemoDepthBudget`
in `cert.sem`. -/
theorem recDemoCert_listSum_sem
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl recDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (hchunks : ∃ (pre : List (Chunk T lt rtExitSyms 64)) (ext : List (SigEntry × Nat))
      (hints : List T.toIsa.Hints)
      (cbr : CompiledBudgetRec T lt ext rtExitSyms 64 [recDemoListSumBudgetFn] hints
        recDemoExportBound [(recDemoListSumName, recDemoExportBound)]),
      cert.chunks = pre ++
        [Chunk.recBudgetSCC ext [recDemoListSumBudgetFn] hints
          recDemoExportBound [(recDemoListSumName, recDemoExportBound)] cbr]) :
    ∀ xs m Q X, listSumSpec recDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) recDemoListSumName [i64, i64] [i64] xs m Q X := by
  rcases hchunks with ⟨pre, ext, hints, cbr, hceq⟩
  intro xs m Q X hspec
  dsimp only [LinkedCertScc.sem]
  rw [hceq, semChunks_append]
  dsimp only [semChunks]
  have hsb : listSumReqBudget recDemoDepthBudget ≤
      budgetBound [(recDemoListSumName, recDemoExportBound)] recDemoExportBound
        recDemoListSumBudgetFn.toFn.name := by
    decide
  exact LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr List.mem_cons_self hsb
    (listSum_budgetSemScc _ _ recDemoDepthBudget _ (Nat.le_refl _) xs m Q X hspec)

private theorem recDemoLinkedMod_fns_wf : ∀ f ∈ recDemoLinkedMod.fns, f.Wf := by
  intro f hf
  simp only [recDemoLinkedMod, linkLcnfWithRtC0, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact rtC0CoreMod_fns_wf f hrt
  · obtain ⟨tf, _, rfl⟩ := List.mem_map.mp hprog
    exact tf.toFn_wf

private theorem recDemoListSumFn_mem_linked : recDemoListSumFn ∈ recDemoLinkedMod.fns := by
  simp only [recDemoLinkedMod, linkLcnfWithRtC0]
  exact List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self)

/-- Target-generic `T.Defined` + `T.FnSpec` bridge for `RecDemo.listSum` via
`LinkedCertScc.fnSpec_host_src_of_le`. -/
theorem recDemoCert_listSum_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl recDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (has : lt.legalSig [i64, i64] = [i64, i64])
    (hrs : lt.legalSig [i64] = [i64])
    (hsem : ∀ xs m Q X, listSumSpec recDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) recDemoListSumName [i64, i64] [i64] xs m Q X) :
    T.Defined cert.host recDemoListSumName ∧
      T.FnSpec cert.host recDemoListSumName (listSumSpec recDemoDepthBudget)
        (cert.bound recDemoListSumName) 64 :=
  cert.fnSpec_host_src_of_le recDemoLinkedMod_fns_wf (f := recDemoListSumFn)
    recDemoListSumFn_mem_linked (listSumSpec recDemoDepthBudget) has hrs
    (fun _ _ _ _ _ h => h) hsem

/-- Target-generic closed `Eventually` machine-execution bridge for `RecDemo.listSum` via
`LinkedCertScc.eventually_ret1_i64_of_le`. -/
theorem recDemoCert_listSum_eventually
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxStack maxMem : Nat}
    (cert : LinkedCertScc T L lt hcl recDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (I : TargetInit T maxStack maxMem)
    (has : lt.legalSig [i64, i64] = [i64, i64])
    (hrs : lt.legalSig [i64] = [i64])
    (hargs : (T.toIsa.assignArgs [i64, i64]).isSome = true)
    (hsem : ∀ xs m Q X, listSumSpec recDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) recDemoListSumName [i64, i64] [i64] xs m Q X)
    (bsMem : List UInt8) (rt p : BitVec 64) (xs : List Nat)
    (hbs : bsMem.length ≤ maxMem)
    (hlen : xs.length ≤ recDemoDepthBudget) (hsum : RecDemo.listSum xs < 2 ^ 63)
    (hmem : listNatAt p xs (bsMem.At 0x1000#64))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        T.mach.getGpr (T.mach.data st) I.ret0 = boxNat (RecDemo.listSum xs))
      (T.mach.mkState
        (I.initState (as := [i64, i64]) (cert.bound recDemoListSumName) bsMem (rt, p, ()))
        (T.mach.labelAddr cert.host recDemoListSumName)) := by
  have hsp : listSumSpec recDemoDepthBudget (rt, p, ()) (bsMem.At 0x1000#64)
      (fun r _ => r = (boxNat (RecDemo.listSum xs), ())) (fun _ _ _ _ => False) :=
    ⟨xs, emp, hlen, hsum, by rw [sep_emp]; exact hmem, rfl⟩
  exact cert.eventually_ret1_i64_of_le I recDemoLinkedMod_fns_wf
    (f := recDemoListSumFn) recDemoListSumFn_mem_linked rfl has hrs
    (listSumSpec recDemoDepthBudget) (fun _ _ _ _ _ h => h) hsem bsMem (rt, p, ())
    (boxNat (RecDemo.listSum xs)) hbs hargs hsp (fun _ _ h => h) hbound

/-! ## 4. Concrete `[10, 20, 30]` → `60` `List Nat` Heap Fixture (`72` Bytes @ `0x1000#64`) -/

/-- Byte image of one `24`-byte `List.cons` heap node (`header` + `[head, tail]`). -/
@[expose] def consNodeBytes (head tail : BitVec 64) : List UInt8 :=
  bytesOf (t := i8) consHdrBytes ++ bytes64 [head, tail]

/-- Concrete `72`-byte heap image of `[10, 20, 30] : List Nat` packed at
`0x1000#64 → 0x1018#64 → 0x1030#64 → 1#64`. -/
@[expose] def recList3Bytes : List UInt8 :=
  consNodeBytes (boxNat 10) 0x1018#64 ++
  (consNodeBytes (boxNat 20) 0x1030#64 ++
   consNodeBytes (boxNat 30) 1#64)

theorem recList3Bytes_length : recList3Bytes.length = 72 := by
  decide

private theorem sep_append_bytes {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs : (Eq (bs1.At a) ⋆ Eq (bs2.At (a + BitVec.ofNat 64 bs1.length))) ((bs1 ++ bs2).At a) :=
    (congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)).mp rfl
  exact sep_mono2 (fun _ h => h ▸ hp) (fun _ h => h ▸ (h1 ▸ hq)) _ hs

private theorem consNodeBytes_ok (p head tail : BitVec 64) :
    consNodeAt p head tail ((consNodeBytes head tail).At p) := by
  have hHdr : array (t := i8) p consHdrBytes ((bytesOf (t := i8) consHdrBytes).At p) :=
    array_bytes (t := i8) p consHdrBytes (by decide)
  have hFlds : array64 (p + 8#64) [head, tail] ((bytes64 [head, tail]).At (p + 8#64)) :=
    array64_bytes (p + 8#64) [head, tail] (by simp)
  have hFlds' : (cell64 (p + 8#64) head ⋆ cell64 (p + 16#64) tail)
      ((bytes64 [head, tail]).At (p + 8#64)) := by
    have ha : array64 (p + 8#64) [head, tail] =
        (cell64 (p + 8#64) head ⋆ cell64 (p + 16#64) tail) := by
      simp only [array64_cons, array64_nil, sep_emp]
      have h16 : (p + 8#64) + 8 = p + 16#64 := by bv_omega
      rw [h16]
    rwa [← ha]
  have hAll := sep_append_bytes (by decide : (bytesOf (t := i8) consHdrBytes).length = 8)
    (by rw [bytes64_length]; simp : (bytes64 [head, tail]).length = 16) (by decide) hHdr hFlds'
  exact sep_cast hAll (by unfold consNodeAt; ac_rfl)

/-- Concrete proof that `recList3Bytes.At 0x1000#64` realizes `[10, 20, 30] : List Nat`. -/
theorem recList3_listNatAt :
    listNatAt 0x1000#64 [10, 20, 30] (recList3Bytes.At 0x1000#64) := by
  have hLen1 : (consNodeBytes (boxNat 10) 0x1018#64).length = 24 := by decide
  have hLen2 : (consNodeBytes (boxNat 20) 0x1030#64).length = 24 := by decide
  have hLen3 : (consNodeBytes (boxNat 30) 1#64).length = 24 := by decide
  have hLen23 : (consNodeBytes (boxNat 20) 0x1030#64 ++ consNodeBytes (boxNat 30) 1#64).length =
      48 := by rw [List.length_append, hLen2, hLen3]
  have hNode3 : listNatAt 0x1030#64 [30] ((consNodeBytes (boxNat 30) 1#64).At 0x1030#64) := by
    refine ⟨by decide, 1#64, ?_⟩
    have heq : (consNodeAt 0x1030#64 (boxNat 30) 1#64 ⋆ listNatAt 1#64 []) =
        consNodeAt 0x1030#64 (boxNat 30) 1#64 := by
      funext m
      exact propext ⟨fun h => by
        obtain ⟨_, hm⟩ := sep_pure_r.mp h; rwa [sep_emp] at hm,
        fun h => sep_pure_r.mpr ⟨rfl, by rwa [sep_emp]⟩⟩
    rw [heq]
    exact consNodeBytes_ok 0x1030#64 (boxNat 30) 1#64
  have hNode23 : listNatAt 0x1018#64 [20, 30]
      ((consNodeBytes (boxNat 20) 0x1030#64 ++ consNodeBytes (boxNat 30) 1#64).At 0x1018#64) := by
    refine ⟨by decide, 0x1030#64, ?_⟩
    exact sep_append_bytes hLen2 hLen3 (by decide)
      (consNodeBytes_ok 0x1018#64 (boxNat 20) 0x1030#64) hNode3
  refine ⟨by decide, 0x1018#64, ?_⟩
  exact sep_append_bytes hLen1 hLen23 (by decide)
    (consNodeBytes_ok 0x1000#64 (boxNat 10) 0x1018#64) hNode23

/-- Concrete proof that `([] : List UInt8).At 0x1000#64` realizes `[] : List Nat` at `1#64`. -/
theorem recListNil_listNatAt :
    listNatAt 1#64 [] (([] : List UInt8).At 0x1000#64) :=
  ⟨rfl, array_bytes (t := i8) 0x1000#64 [] (by decide)⟩

end LeanQbe.T.LeanLCNF

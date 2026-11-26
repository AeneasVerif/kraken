module

public import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.MainCertScc
public import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.Rules

/-!
# Mutual 2-Function SCC WP Soundness & Rose-Tree Fixtures (`LcnfC0MutRecDemoProof`)

Target-generic (`0` arch imports, `0` `import all`) soundness proof for the 2-function
mutually-recursive Lean `LCNF` SCC `{MutRecDemo.roseSum, MutRecDemo.forestSum}` compiled as a
**single 2-function `.recBudgetSCC` chunk** via `compile_linked_budget_scc!` and linked onto
`rtC0CoreMod`:

1. **`Rose` / `Forest` heap predicates (`roseNodeAt`, `forestConsAt`, `roseNatAt`, `forestNatAt`)**:
   exact `24`-byte Lean 4 constructor layouts (`Rose.node`: `m_tag = 0`, `v @ +8`, `cs @ +16`;
   `Forest.nil = 1#64`; `Forest.cons`: `m_tag = 1`, `hd @ +8`, `tl @ +16`).
2. **Joint depth-indexed mutual fixed point (`mutRec_budgetSemScc`)**: single
   `BudgetEnv.lfp_wf_mkSccOp` proof simultaneously certifying BOTH `roseSumSpec` and
   `forestSumSpec` inside `[mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn]` at stack budget
   `272 + 48 * d`.
3. **Target-generic `LinkedCertScc` bridges**: projects both `roseSum` and `forestSum` out of the
   single 2-fn `.recBudgetSCC` chunk to `T.FnSpec` and closed machine `Eventually`.
4. **Concrete nested multi-child rose-tree fixture (`sampleRose`, `sampleForest`,
   `sampleRoseBytes`)**: `312`-byte (`13 × 24`B) 3-level rose tree at `0x1000#64` with
   `roseSum = 90` (`boxNat 90 = 181#64`), `forestSum = 80` (`boxNat 80 = 161#64`), `depth = 7`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step

/-! ## 1. Tagged-Scalar Helpers & Mutual `Rose` / `Forest` Heap Predicates -/

private theorem mr_boxNat_and_one {n : Nat} (hn : n < 2 ^ 63) :
    (boxNat n &&& 1#64) = 1#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := by decide
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, boxNat, BitVec.toNat_ofNat, hmod]
  omega

private theorem mr_boxNat_add_fast {aVal bVal : Nat} (hlt : aVal + bVal < 2 ^ 63) :
    ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true ∧
    ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false ∧
    (boxNat aVal - 1#64) + boxNat bVal = boxNat (aVal + bVal) := by
  have ha : (boxNat aVal).toNat = 2 * aVal + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb : (boxNat bVal).toNat = 2 * bVal + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (boxNat aVal - 1#64).toNat = 2 * aVal := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, ha])]; simp [ha]
  have hadd : ((boxNat aVal - 1#64) + boxNat bVal).toNat = 2 * (aVal + bVal) + 1 := by
    rw [BitVec.toNat_add, hsub, hb, Nat.mod_eq_of_lt (by omega)]; omega
  have hsumEq : (boxNat aVal - 1#64) + boxNat bVal = boxNat (aVal + bVal) := by
    apply BitVec.eq_of_toNat_eq
    rw [hadd, boxNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha1 : (boxNat aVal &&& 1#64) = 1#64 := mr_boxNat_and_one (by omega)
  have hb1 : (boxNat bVal &&& 1#64) = 1#64 := mr_boxNat_and_one (by omega)
  have hlsb : (boxNat aVal &&& boxNat bVal &&& 1#64) = 1#64 := by
    rw [BitVec.and_assoc, hb1, ha1]
  have hbit : ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true := by rw [hlsb]; decide
  have hult : ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, hadd, hb]; omega
  exact ⟨hbit, hult, hsumEq⟩

/-- Little-endian header bytes of `Rose.node` (`m_rc = 1`, `m_cs_sz = 24`, `m_other = 2`,
`m_tag = 0`). -/
@[expose] def roseNodeHdrBytes : List (Val i8) :=
  [1#8, 0#8, 0#8, 0#8, 24#8, 0#8, 2#8, 0#8]

/-- Little-endian header bytes of `Forest.cons` (`m_rc = 1`, `m_cs_sz = 24`, `m_other = 2`,
`m_tag = 1`). -/
@[expose] def forestConsHdrBytes : List (Val i8) :=
  [1#8, 0#8, 0#8, 0#8, 24#8, 0#8, 2#8, 1#8]

theorem roseNodeHdrBytes_matches_lcnfObj (p v cs : BitVec 64) :
    bytesOf (t := i8) roseNodeHdrBytes =
      Int.toBytes 8 (LcnfObj.header
        { addr := p, rc := 1#32, csSz := 24, other := 2, tag := 0, fields := [v, cs] }).toInt := by
  dsimp only [LcnfObj.header]; decide

theorem forestConsHdrBytes_matches_lcnfObj (p hd tl : BitVec 64) :
    bytesOf (t := i8) forestConsHdrBytes =
      Int.toBytes 8 (LcnfObj.header
        { addr := p, rc := 1#32, csSz := 24, other := 2, tag := 1, fields := [hd, tl] }).toInt := by
  dsimp only [LcnfObj.header]; decide

/-- `24`-byte heap cell for `Rose.node` at `p` (`v` @ `+8`, `cs` @ `+16`). -/
@[expose] def roseNodeAt (p v cs : BitVec 64) : Mem 64 → Prop :=
  array (t := i8) p roseNodeHdrBytes ⋆ cell64 (p + 8#64) v ⋆ cell64 (p + 16#64) cs

/-- `24`-byte heap cell for `Forest.cons` at `p` (`tag = 1` @ `+7`, `hd` @ `+8`, `tl` @ `+16`). -/
@[expose] def forestConsAt (p hd tl : BitVec 64) : Mem 64 → Prop :=
  array (t := i8) p forestConsHdrBytes ⋆ cell64 (p + 8#64) hd ⋆ cell64 (p + 16#64) tl

mutual
  /-- Inductive heap layout of a `MutRecDemo.Rose` tree rooted at `p`. -/
  @[expose] def roseNatAt : BitVec 64 → MutRecDemo.Rose → Mem 64 → Prop
    | p, .node v cs, m =>
      (p &&& 1#64) = 0#64 ∧
      ∃ pcs : BitVec 64, (roseNodeAt p (boxNat v) pcs ⋆ forestNatAt pcs cs) m

  /-- Inductive heap layout of a `MutRecDemo.Forest` rooted at `p` (`nil = 1#64`). -/
  @[expose] def forestNatAt : BitVec 64 → MutRecDemo.Forest → Mem 64 → Prop
    | p, .nil, m => p = 1#64 ∧ emp m
    | p, .cons hd tl, m =>
      (p &&& 1#64) = 0#64 ∧
      ∃ phd ptl : BitVec 64,
        (forestConsAt p phd ptl ⋆ roseNatAt phd hd ⋆ forestNatAt ptl tl) m
end

private theorem roseNodeAt_load_val {p v cs : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (roseNodeAt p v cs ⋆ R) m) : loadVal m i64 (p + 8#64) = some v := by
  unfold roseNodeAt at hm
  exact loadVal_cell64 (R := array (t := i8) p roseNodeHdrBytes ⋆ cell64 (p + 16#64) cs ⋆ R)
    (sep_cast hm (by ac_rfl))

private theorem roseNodeAt_load_cs {p v cs : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (roseNodeAt p v cs ⋆ R) m) : loadVal m i64 (p + 16#64) = some cs := by
  unfold roseNodeAt at hm
  exact loadVal_cell64 (R := array (t := i8) p roseNodeHdrBytes ⋆ cell64 (p + 8#64) v ⋆ R)
    (sep_cast hm (by ac_rfl))

private theorem forestConsAt_load_tag {p hd tl : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (forestConsAt p hd tl ⋆ R) m) : loadVal m i8 (p + 7#64) = some 1#8 := by
  unfold forestConsAt at hm
  have hm' : (array (t := i8) p forestConsHdrBytes ⋆
      (cell64 (p + 8#64) hd ⋆ cell64 (p + 16#64) tl ⋆ R)) m := sep_cast hm (by ac_rfl)
  exact loadVal_array (t := i8) (i := 7) (by decide) (by decide) hm'

private theorem forestConsAt_load_hd {p hd tl : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (forestConsAt p hd tl ⋆ R) m) : loadVal m i64 (p + 8#64) = some hd := by
  unfold forestConsAt at hm
  exact loadVal_cell64 (R := array (t := i8) p forestConsHdrBytes ⋆ cell64 (p + 16#64) tl ⋆ R)
    (sep_cast hm (by ac_rfl))

private theorem forestConsAt_load_tl {p hd tl : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (forestConsAt p hd tl ⋆ R) m) : loadVal m i64 (p + 16#64) = some tl := by
  unfold forestConsAt at hm
  exact loadVal_cell64 (R := array (t := i8) p forestConsHdrBytes ⋆ cell64 (p + 8#64) hd ⋆ R)
    (sep_cast hm (by ac_rfl))

/-! ## 2. Reusable Lowered-IR Pattern WP Helpers -/

private def mrDecRefExpr (rt obj : Val i64) (cont : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var obj) (.imm 1#64)) fun b0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var b0.1) (.imm 0#64)) fun b1 =>
      .group (sig := [[]]) (fun _ => .cons (fun _ => cont) .nil) fun J =>
        .jnz (.var b1.1) (.jump J.1 ())
          (.load i32 (.var obj) fun rc =>
            .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var rc) (.imm 1#32)) fun is1 =>
              .jnz (.var is1.1)
                (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := [])
                  (.var rt, .var obj, ()) fun _ => .jump J.1 ())
                (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var rc) (.imm 1#32)) fun gt1 =>
                  .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var gt1.1)) fun b =>
                    .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var rc) (.var b.1)) fun rc' =>
                      .store (.var rc'.1) (.var obj) (.jump J.1 ())))

private theorem wp_mrDecRefExpr_scalar {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {rt obj : Val i64} {cont : Expr Val Cont [i64]}
    (hsc : (obj &&& 1#64) = 1#64) (hcont : wp Γ Q X cont m) :
    wp Γ Q X (mrDecRefExpr rt obj cont) m := by
  have hbit : ((obj &&& 1#64) != 0#64) = true := by rw [hsc]; decide
  dsimp only [mrDecRefExpr]; c0_let_simp
  refine wp_join_group (fun _ m' => m' = m) ?_ ?_
  · rintro J ⟨⟩ m' hm'; subst m'; rw [Blocks.get.eq_1]; exact hcont
  · intro J hJ
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hbit])⟩
    rw [wp_jump]; exact hJ () m rfl

private def mrNatAddExpr (rt : Val i64) (a b : Val i64)
    (cont : Tup Val [i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var a) (.var b)) fun v0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v0.1) (.imm 1#64)) fun v1 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v1.1) (.imm 0#64)) fun v2 =>
        .group (sig := [[i64]]) (fun _ => .cons cont .nil) fun Jsum =>
          .jnz (.var v2.1)
            (.let_ (_root_.LeanQbe.T.op2 (OpCode.sub i64) (.var a) (.imm 1#64)) fun v3 =>
              .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var v3.1) (.var b)) fun v4 =>
                .let_ (_root_.LeanQbe.T.op2 (OpCode.ult i64) (.var v4.1) (.var b)) fun v5 =>
                  .jnz (.var v5.1)
                    (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
                      (.var rt, .imm 1#64, .var a, .var b, ()) fun v6 =>
                      .jump Jsum.1 (.var v6.1, ()))
                    (.jump Jsum.1 (.var v4.1, ())))
            (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
              (.var rt, .imm 1#64, .var a, .var b, ()) fun v7 => .jump Jsum.1 (.var v7.1, ()))

private theorem wp_mrNatAddExpr_fast {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {rt : Val i64} {aVal bVal : Nat} {cont : Tup Val [i64] → Expr Val Cont [i64]}
    (hlt : aVal + bVal < 2 ^ 63) (hcont : wp Γ Q X (cont (boxNat (aVal + bVal), ())) m) :
    wp Γ Q X (mrNatAddExpr rt (boxNat aVal) (boxNat bVal) cont) m := by
  obtain ⟨hbit, hult, heq⟩ := mr_boxNat_add_fast hlt
  dsimp only [mrNatAddExpr]; c0_let_simp
  refine wp_join_group (fun s m' => s.1 = boxNat (aVal + bVal) ∧ m' = m) ?_ ?_
  · rintro Jsum ⟨sVal, ⟨⟩⟩ m' ⟨rfl, hm'⟩; subst m'; rw [Blocks.get.eq_1]; exact hcont
  · intro Jsum hJsum
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hbit])⟩
    c0_let_simp; rw [wp_jnz]
    refine ⟨fun h => absurd h (by simp [Arg.val_var, hult]), fun _ => ?_⟩
    rw [wp_jump]; exact hJsum _ m ⟨heq, rfl⟩

private def mrTagDispatchExpr (p : Val i64) (consBody : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  let tagBlk (tagTup : Tup Val [i64]) : Expr Val Cont [i64] :=
    .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i64) (.var tagTup.1) (.imm 0#64)) fun v2 =>
      .jnz (.var v2.1) (.ret (.imm 1#64, ())) consBody
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var p) (.imm 1#64)) fun v0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v0.1) (.imm 0#64)) fun v1 =>
      .group (sig := [[i64]]) (fun _ => .cons tagBlk .nil) fun Jtag =>
        .jnz (.var v1.1)
          (.let_ (_root_.LeanQbe.T.op2 (OpCode.lshr i64) (.var p) (.imm 1#64)) fun scTag =>
            .jump Jtag.1 (.var scTag.1, ()))
          (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 7#64)) fun tagAddr =>
            .load i8 (.var tagAddr.1) fun tag8 =>
              .let_ (_root_.LeanQbe.T.op1 (OpCode.zext 8 64) (.var tag8)) fun tag64 =>
                .jump Jtag.1 (.var tag64.1, ()))

private theorem wp_mrTagDispatch_nil {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {consBody : Expr Val Cont [i64]} (hq : Q (1#64, ()) m) :
    wp Γ Q X (mrTagDispatchExpr 1#64 consBody) m := by
  dsimp only [mrTagDispatchExpr]; c0_let_simp
  refine wp_join_group (fun tagTup m' => tagTup.1 = 0#64 ∧ m' = m) ?_ ?_
  · rintro J ⟨tag, ⟨⟩⟩ m' ⟨rfl, rfl⟩
    rw [Blocks.get.eq_1]; c0_let_simp; rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var])⟩
    rw [wp_ret]; exact hq
  · intro J hJ
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var])⟩
    c0_let_simp; exact hJ _ m ⟨by decide, rfl⟩

private theorem wp_mrTagDispatch_cons {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {p : Val i64} {consBody : Expr Val Cont [i64]}
    (hp0 : (p &&& 1#64) = 0#64) (hldTag : loadVal m i8 (p + 7#64) = some 1#8)
    (hbody : wp Γ Q X consBody m) :
    wp Γ Q X (mrTagDispatchExpr p consBody) m := by
  dsimp only [mrTagDispatchExpr]; c0_let_simp
  refine wp_join_group (fun tagTup m' => tagTup.1 = 1#64 ∧ m' = m) ?_ ?_
  · rintro J ⟨tag, ⟨⟩⟩ m' ⟨rfl, hm'⟩
    subst m'; rw [Blocks.get.eq_1]; c0_let_simp; rw [wp_jnz]
    exact ⟨fun h => absurd h (by simp [Arg.val_var]), fun _ => hbody⟩
  · intro J hJ
    rw [wp_jnz]
    refine ⟨fun h => absurd h (by simp [Arg.val_var, hp0]), fun _ => ?_⟩
    c0_let_simp
    refine wp_load_of (v := 1#8) (by simpa [Arg.val_var] using hldTag) ?_
    c0_let_simp; exact hJ (1#64, ()) m ⟨rfl, rfl⟩

/-! ## 3. Joint Depth-Indexed Mutual Specifications & `BudgetEnv.lfp_wf_mkSccOp` Proof -/

/-- Exact stack budget required by the `{roseSum, forestSum}` SCC at mutual depth `≤ d`:
`272 + 48 * d`. -/
@[expose] def mutRecReqBudget (d : Nat) : Nat :=
  mutRecDemoMinEntry + d * mutRecDemoMaxFrame

/-- Source-level specification of `MutRecDemo.roseSum` at maximum mutual call depth `D`. -/
@[expose] def roseSumSpec (D : Nat) : Spec [i64, i64] [i64] :=
  fun (_rt, p, ()) m Q _ =>
    ∃ (r : MutRecDemo.Rose) (R : Mem 64 → Prop),
      MutRecDemo.roseDepth r ≤ D ∧ MutRecDemo.roseSum r < 2 ^ 63 ∧
      (roseNatAt p r ⋆ R) m ∧
      Q (boxNat (MutRecDemo.roseSum r), ()) m

/-- Source-level specification of `MutRecDemo.forestSum` at maximum mutual call depth `D`. -/
@[expose] def forestSumSpec (D : Nat) : Spec [i64, i64] [i64] :=
  fun (_rt, p, ()) m Q _ =>
    ∃ (f : MutRecDemo.Forest) (R : Mem 64 → Prop),
      MutRecDemo.forestDepth f ≤ D ∧ MutRecDemo.forestSum f < 2 ^ 63 ∧
      (forestNatAt p f ⋆ R) m ∧
      Q (boxNat (MutRecDemo.forestSum f), ()) m

private def mutRecIdxEnv (d : Nat) : Env :=
  fun nm as bs xs m Q X =>
    (nm = mutRecDemoRoseName ∧
      ∃ (ha : as = [i64, i64]) (hb : bs = [i64]),
        roseSumSpec d (ha ▸ xs) m (hb ▸ Q) X) ∨
    (nm = mutRecDemoForestName ∧
      ∃ (ha : as = [i64, i64]) (hb : bs = [i64]),
        forestSumSpec d (ha ▸ xs) m (hb ▸ Q) X)

private theorem mr_budget_wp_mono_local :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m' _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m' hwp

private theorem roseSum_step_wp {Γcall : Env} {d : Nat}
    (hrecF : ∀ j, j < d →
      ∀ xs m Q X, forestSumSpec j xs m Q X →
        Γcall mutRecDemoForestName [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, roseSumSpec d xs m Q X →
      Func.wp Γcall mutRecDemoRoseFn.body xs m Q X := by
  rintro ⟨rt, p, ⟨⟩⟩ m Q X ⟨r, R, hdep, hsum, hm, hq⟩
  change wp Γcall Q X
    (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 8#64)) fun a0 =>
      .load i64 (.var a0.1) fun v =>
        .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 16#64)) fun a1 =>
          .load i64 (.var a1.1) fun cs =>
            .call mutRecDemoForestName (as := [i64, i64]) (bs := [i64])
              (.var rt, .var cs, ()) fun s =>
              mrNatAddExpr rt v s.1 fun res =>
                mrDecRefExpr rt s.1 (.ret (.var res.1, ()))) m
  cases r with
  | node v cs =>
    obtain ⟨_, hm1⟩ := sep_pure_l.mp hm
    obtain ⟨pcs, hmNode⟩ := sep_ex_l.mp hm1
    have hNodeR : (roseNodeAt p (boxNat v) pcs ⋆ (forestNatAt pcs cs ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hCsR : (forestNatAt pcs cs ⋆ (roseNodeAt p (boxNat v) pcs ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hldVal := roseNodeAt_load_val hNodeR
    have hldCs := roseNodeAt_load_cs hNodeR
    have hdepCs : MutRecDemo.forestDepth cs < d := by
      dsimp only [MutRecDemo.roseDepth] at hdep; omega
    have hsumDef : MutRecDemo.roseSum (.node v cs) = v + MutRecDemo.forestSum cs := rfl
    have hsumCs : MutRecDemo.forestSum cs < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hsumAll : v + MutRecDemo.forestSum cs < 2 ^ 63 := by rw [hsumDef] at hsum; exact hsum
    c0_let_simp
    refine wp_load_of (v := boxNat v) (by simpa [Arg.val_var] using hldVal) ?_
    c0_let_simp
    refine wp_load_of (v := pcs) (by simpa [Arg.val_var] using hldCs) ?_
    let PF : Post [i64] := fun s m' => s = (boxNat (MutRecDemo.forestSum cs), ()) ∧ m' = m
    have hCallF : Γcall mutRecDemoForestName [i64, i64] [i64] (rt, pcs, ()) m PF X :=
      hrecF (MutRecDemo.forestDepth cs) hdepCs (rt, pcs, ()) m PF X
        ⟨cs, roseNodeAt p (boxNat v) pcs ⋆ R, Nat.le_refl _, hsumCs, hCsR, ⟨rfl, rfl⟩⟩
    refine ⟨PF, X, hCallF, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨sVal, ⟨⟩⟩ m1 ⟨hsEq, hm1'⟩; subst m1
    obtain rfl : sVal = boxNat (MutRecDemo.forestSum cs) := (Prod.ext_iff.mp hsEq).1
    refine wp_mrNatAddExpr_fast (aVal := v) (bVal := MutRecDemo.forestSum cs) hsumAll ?_
    refine wp_mrDecRefExpr_scalar (mr_boxNat_and_one hsumCs) ?_
    rw [wp_ret]; exact hq

private theorem forestSum_step_wp {Γcall : Env} {d : Nat}
    (hrecR : ∀ j, j < d →
      ∀ xs m Q X, roseSumSpec j xs m Q X →
        Γcall mutRecDemoRoseName [i64, i64] [i64] xs m Q X)
    (hrecF : ∀ j, j < d →
      ∀ xs m Q X, forestSumSpec j xs m Q X →
        Γcall mutRecDemoForestName [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, forestSumSpec d xs m Q X →
      Func.wp Γcall mutRecDemoForestFn.body xs m Q X := by
  rintro ⟨rt, p, ⟨⟩⟩ m Q X ⟨f, R, hdep, hsum, hm, hq⟩
  change wp Γcall Q X
    (mrTagDispatchExpr p
      (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 8#64)) fun a0 =>
        .load i64 (.var a0.1) fun hd =>
          .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 16#64)) fun a1 =>
            .load i64 (.var a1.1) fun tl =>
              .call mutRecDemoRoseName (as := [i64, i64]) (bs := [i64])
                (.var rt, .var hd, ()) fun sh =>
                .call mutRecDemoForestName (as := [i64, i64]) (bs := [i64])
                  (.var rt, .var tl, ()) fun st =>
                  mrNatAddExpr rt sh.1 st.1 fun res =>
                    mrDecRefExpr rt st.1
                      (mrDecRefExpr rt sh.1 (.ret (.var res.1, ()))))) m
  cases f with
  | nil =>
    obtain ⟨rfl, _⟩ := sep_pure_l.mp hm
    exact wp_mrTagDispatch_nil hq
  | cons hd tl =>
    obtain ⟨hp0, hm1⟩ := sep_pure_l.mp hm
    obtain ⟨phd, hm2⟩ := sep_ex_l.mp hm1
    obtain ⟨ptl, hmNode⟩ := sep_ex_l.mp hm2
    have hNodeR : (forestConsAt p phd ptl ⋆ (roseNatAt phd hd ⋆ forestNatAt ptl tl ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hHdR : (roseNatAt phd hd ⋆ (forestConsAt p phd ptl ⋆ forestNatAt ptl tl ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hTlR : (forestNatAt ptl tl ⋆ (forestConsAt p phd ptl ⋆ roseNatAt phd hd ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hldTag := forestConsAt_load_tag hNodeR
    have hldHd := forestConsAt_load_hd hNodeR
    have hldTl := forestConsAt_load_tl hNodeR
    have hdepHd : MutRecDemo.roseDepth hd < d := by
      dsimp only [MutRecDemo.forestDepth] at hdep; omega
    have hdepTl : MutRecDemo.forestDepth tl < d := by
      dsimp only [MutRecDemo.forestDepth] at hdep; omega
    have hsumDef : MutRecDemo.forestSum (.cons hd tl) =
        MutRecDemo.roseSum hd + MutRecDemo.forestSum tl := rfl
    have hsumHd : MutRecDemo.roseSum hd < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hsumTl : MutRecDemo.forestSum tl < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hsumAll : MutRecDemo.roseSum hd + MutRecDemo.forestSum tl < 2 ^ 63 := by
      rw [hsumDef] at hsum; exact hsum
    refine wp_mrTagDispatch_cons hp0 hldTag ?_
    c0_let_simp
    refine wp_load_of (v := phd) (by simpa [Arg.val_var] using hldHd) ?_
    c0_let_simp
    refine wp_load_of (v := ptl) (by simpa [Arg.val_var] using hldTl) ?_
    let PH : Post [i64] := fun s m' => s = (boxNat (MutRecDemo.roseSum hd), ()) ∧ m' = m
    have hCallH : Γcall mutRecDemoRoseName [i64, i64] [i64] (rt, phd, ()) m PH X :=
      hrecR (MutRecDemo.roseDepth hd) hdepHd (rt, phd, ()) m PH X
        ⟨hd, forestConsAt p phd ptl ⋆ forestNatAt ptl tl ⋆ R,
          Nat.le_refl _, hsumHd, hHdR, ⟨rfl, rfl⟩⟩
    refine ⟨PH, X, hCallH, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨shVal, ⟨⟩⟩ m1 ⟨hshEq, hm1'⟩; subst m1
    obtain rfl : shVal = boxNat (MutRecDemo.roseSum hd) := (Prod.ext_iff.mp hshEq).1
    let PT : Post [i64] := fun s m' => s = (boxNat (MutRecDemo.forestSum tl), ()) ∧ m' = m
    have hCallT : Γcall mutRecDemoForestName [i64, i64] [i64] (rt, ptl, ()) m PT X :=
      hrecF (MutRecDemo.forestDepth tl) hdepTl (rt, ptl, ()) m PT X
        ⟨tl, forestConsAt p phd ptl ⋆ roseNatAt phd hd ⋆ R,
          Nat.le_refl _, hsumTl, hTlR, ⟨rfl, rfl⟩⟩
    refine ⟨PT, X, hCallT, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨stVal, ⟨⟩⟩ m2 ⟨hstEq, hm2'⟩; subst m2
    obtain rfl : stVal = boxNat (MutRecDemo.forestSum tl) := (Prod.ext_iff.mp hstEq).1
    refine wp_mrNatAddExpr_fast (aVal := MutRecDemo.roseSum hd) (bVal := MutRecDemo.forestSum tl)
      hsumAll ?_
    refine wp_mrDecRefExpr_scalar (mr_boxNat_and_one hsumTl) ?_
    refine wp_mrDecRefExpr_scalar (mr_boxNat_and_one hsumHd) ?_
    rw [wp_ret]; exact hq

/-- Joint budget-indexed `BudgetEnv.semScc` soundness for the **2-function mutually-recursive
SCC** `[mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn]` via a single `BudgetEnv.lfp_wf_mkSccOp`
induction over mutual call depth `d` at stack budget `sb ≥ 272 + 48 * d`. -/
theorem mutRec_budgetSemScc (extSigs : List SigEntry) (Γext : Env)
    (d sb : Nat) (hsb : mutRecReqBudget d ≤ sb) :
    (∀ xs m Q X, roseSumSpec d xs m Q X →
      BudgetEnv.semScc ⟨[mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn],
          externsOfSigs extSigs, rtExitSyms⟩
        Γext sb mutRecDemoRoseName [i64, i64] [i64] xs m Q X) ∧
    (∀ xs m Q X, forestSumSpec d xs m Q X →
      BudgetEnv.semScc ⟨[mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn],
          externsOfSigs extSigs, rtExitSyms⟩
        Γext sb mutRecDemoForestName [i64, i64] [i64] xs m Q X) := by
  let BM : BudgetModule :=
    ⟨[mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
  have hsigR : (mutRecDemoRoseName, [i64, i64], [i64]) ∈ BM.fnSigs := by
    simp [BM, BudgetModule.fnSigs, mutRecDemoRoseBudgetFn, mutRecDemoRoseFn,
      mutRecDemoRoseName, mutRecDemoTfs.tf_0, Fn.sig, Frontend.C0.TFlatFn.toFn]
  have hsigF : (mutRecDemoForestName, [i64, i64], [i64]) ∈ BM.fnSigs := by
    simp [BM, BudgetModule.fnSigs, mutRecDemoForestBudgetFn, mutRecDemoForestFn,
      mutRecDemoForestName, mutRecDemoTfs.tf_1, Fn.sig, Frontend.C0.TFlatFn.toFn]
  have hLfp := BudgetEnv.lfp_wf_mkSccOp (lt := Nat.lt) Nat.lt_wfRel.wf mutRecReqBudget BM
    (BudgetEnv.const Γext) mr_budget_wp_mono_local mutRecIdxEnv
    (fun idx sb' hsb' bfn hbfn Γcall _ hcall _ _ _ xs' m' Q' X' hS => by
      dsimp only [BM] at hbfn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbfn
      rcases hbfn with rfl | rfl
      · rcases hS with ⟨_, ha, hb, hsp⟩ | ⟨hne, _⟩
        · have hmax : mutRecDemoRoseBudgetFn.maxFrame ≤ sb' := by
            dsimp only [mutRecDemoRoseBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
              mutRecDemoMinEntry] at hsb' ⊢; omega
          have hmin : mutRecDemoRoseBudgetFn.minEntry ≤ sb' := by
            dsimp only [mutRecDemoRoseBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
              mutRecDemoMinEntry] at hsb' ⊢; omega
          refine ⟨hmax, hmin, ?_⟩
          have hrecF : ∀ j, j < idx → ∀ ys m₁ Q₁ X₁, forestSumSpec j ys m₁ Q₁ X₁ →
              Γcall mutRecDemoForestName [i64, i64] [i64] ys m₁ Q₁ X₁ := by
            intro j hlt ys m₁ Q₁ X₁ hspj
            have hreqj : mutRecReqBudget j ≤ sb' - mutRecDemoRoseBudgetFn.maxFrame := by
              dsimp only [mutRecDemoRoseBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
                mutRecDemoMinEntry] at hsb' ⊢; omega
            exact hcall j hlt hreqj mutRecDemoForestName [i64, i64] [i64] ys m₁ Q₁ X₁
              ⟨hsigF, Or.inr ⟨rfl, rfl, rfl, hspj⟩⟩
          exact roseSum_step_wp hrecF xs' m' Q' X' (by simpa using hsp)
        · exact absurd hne (by decide)
      · rcases hS with ⟨hne, _⟩ | ⟨_, ha, hb, hsp⟩
        · exact absurd hne (by decide)
        · have hmax : mutRecDemoForestBudgetFn.maxFrame ≤ sb' := by
            dsimp only [mutRecDemoForestBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
              mutRecDemoMinEntry] at hsb' ⊢; omega
          have hmin : mutRecDemoForestBudgetFn.minEntry ≤ sb' := by
            dsimp only [mutRecDemoForestBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
              mutRecDemoMinEntry] at hsb' ⊢; omega
          refine ⟨hmax, hmin, ?_⟩
          have hrecR : ∀ j, j < idx → ∀ ys m₁ Q₁ X₁, roseSumSpec j ys m₁ Q₁ X₁ →
              Γcall mutRecDemoRoseName [i64, i64] [i64] ys m₁ Q₁ X₁ := by
            intro j hlt ys m₁ Q₁ X₁ hspj
            have hreqj : mutRecReqBudget j ≤ sb' - mutRecDemoForestBudgetFn.maxFrame := by
              dsimp only [mutRecDemoForestBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
                mutRecDemoMinEntry] at hsb' ⊢; omega
            exact hcall j hlt hreqj mutRecDemoRoseName [i64, i64] [i64] ys m₁ Q₁ X₁
              ⟨hsigR, Or.inl ⟨rfl, rfl, rfl, hspj⟩⟩
          have hrecF : ∀ j, j < idx → ∀ ys m₁ Q₁ X₁, forestSumSpec j ys m₁ Q₁ X₁ →
              Γcall mutRecDemoForestName [i64, i64] [i64] ys m₁ Q₁ X₁ := by
            intro j hlt ys m₁ Q₁ X₁ hspj
            have hreqj : mutRecReqBudget j ≤ sb' - mutRecDemoForestBudgetFn.maxFrame := by
              dsimp only [mutRecDemoForestBudgetFn, mutRecReqBudget, mutRecDemoMaxFrame,
                mutRecDemoMinEntry] at hsb' ⊢; omega
            exact hcall j hlt hreqj mutRecDemoForestName [i64, i64] [i64] ys m₁ Q₁ X₁
              ⟨hsigF, Or.inr ⟨rfl, rfl, rfl, hspj⟩⟩
          exact forestSum_step_wp hrecR hrecF xs' m' Q' X' (by simpa using hsp))
    d sb hsb
  exact ⟨fun xs m Q X hsp => hLfp mutRecDemoRoseName [i64, i64] [i64] xs m Q X
           ⟨hsigR, Or.inl ⟨rfl, rfl, rfl, hsp⟩⟩,
         fun xs m Q X hsp => hLfp mutRecDemoForestName [i64, i64] [i64] xs m Q X
           ⟨hsigF, Or.inr ⟨rfl, rfl, rfl, hsp⟩⟩⟩

/-! ## 4. Target-Generic `LinkedCertScc` Semantic & Machine Bridges -/

private theorem mr_semChunks_append {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} (cs₁ cs₂ : List (Chunk T lt exits nX)) (extSigs : List SigEntry) (Γ₀ : Env) :
    semChunks extSigs Γ₀ (cs₁ ++ cs₂) =
      semChunks (sccChunksSigAcc extSigs cs₁) (semChunks extSigs Γ₀ cs₁) cs₂ := by
  induction cs₁ generalizing extSigs Γ₀ with
  | nil => rfl
  | cons c rest ih =>
    simpa only [List.cons_append, semChunks, sccChunksSigAcc] using
      ih (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)

/-- Structural shape witness for a `mutRecDemoLinkedMod` certificate whose tail is a **single
2-function `.recBudgetSCC` chunk** containing `[mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn]`.
-/
@[expose] def MutRecDemoChunksShape {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound []) : Prop :=
  ∃ (pre : List (Chunk T lt rtExitSyms 64))
    (ext1 : List (SigEntry × Nat))
    (hints1 : List T.toIsa.Hints)
    (cbr1 : CompiledBudgetRec T lt ext1 rtExitSyms 64
      [mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn] hints1
      mutRecDemoExportBound mutRecDemoExportBounds),
    cert.chunks = pre ++
      [Chunk.recBudgetSCC ext1 [mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn] hints1
        mutRecDemoExportBound mutRecDemoExportBounds cbr1]

/-- Target-generic semantic bridge for `MutRecDemo.roseSum` from the single 2-fn SCC chunk. -/
theorem mutRecDemoCert_roseSum_sem
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (hchunks : MutRecDemoChunksShape cert) :
    ∀ xs m Q X, roseSumSpec mutRecDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoRoseName [i64, i64] [i64] xs m Q X := by
  rcases hchunks with ⟨pre, ext1, hints1, cbr1, hceq⟩
  intro xs m Q X hspec
  dsimp only [LinkedCertScc.sem]
  rw [hceq, mr_semChunks_append]
  dsimp only [semChunks]
  have hsb : mutRecReqBudget mutRecDemoDepthBudget ≤
      budgetBound mutRecDemoExportBounds mutRecDemoExportBound
        mutRecDemoRoseBudgetFn.toFn.name := by decide
  exact LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr1 List.mem_cons_self hsb
    ((mutRec_budgetSemScc _ _ mutRecDemoDepthBudget _ (Nat.le_refl _)).1 xs m Q X hspec)

/-- Target-generic semantic bridge for `MutRecDemo.forestSum` from the single 2-fn SCC chunk. -/
theorem mutRecDemoCert_forestSum_sem
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (hchunks : MutRecDemoChunksShape cert) :
    ∀ xs m Q X, forestSumSpec mutRecDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoForestName [i64, i64] [i64] xs m Q X := by
  rcases hchunks with ⟨pre, ext1, hints1, cbr1, hceq⟩
  intro xs m Q X hspec
  dsimp only [LinkedCertScc.sem]
  rw [hceq, mr_semChunks_append]
  dsimp only [semChunks]
  have hsb : mutRecReqBudget mutRecDemoDepthBudget ≤
      budgetBound mutRecDemoExportBounds mutRecDemoExportBound
        mutRecDemoForestBudgetFn.toFn.name := by decide
  exact LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr1
    (List.mem_cons_of_mem _ List.mem_cons_self) hsb
    ((mutRec_budgetSemScc _ _ mutRecDemoDepthBudget _ (Nat.le_refl _)).2 xs m Q X hspec)

private theorem mutRecDemoLinkedMod_fns_wf : ∀ f ∈ mutRecDemoLinkedMod.fns, f.Wf := by
  intro f hf
  simp only [mutRecDemoLinkedMod, linkLcnfWithRtC0, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact rtC0CoreMod_fns_wf f hrt
  · obtain ⟨tf, _, rfl⟩ := List.mem_map.mp hprog; exact tf.toFn_wf

private theorem mutRecDemoRoseFn_mem_linked : mutRecDemoRoseFn ∈ mutRecDemoLinkedMod.fns := by
  simp only [mutRecDemoLinkedMod, linkLcnfWithRtC0]
  exact List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self)

private theorem mutRecDemoForestFn_mem_linked :
    mutRecDemoForestFn ∈ mutRecDemoLinkedMod.fns := by
  simp only [mutRecDemoLinkedMod, linkLcnfWithRtC0]
  exact List.mem_append_right _
    (List.mem_map_of_mem (List.mem_cons_of_mem _ List.mem_cons_self))

theorem mutRecDemoCert_roseSum_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (has : lt.legalSig [i64, i64] = [i64, i64]) (hrs : lt.legalSig [i64] = [i64])
    (hsem : ∀ xs m Q X, roseSumSpec mutRecDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoRoseName [i64, i64] [i64] xs m Q X) :
    T.Defined cert.host mutRecDemoRoseName ∧
      T.FnSpec cert.host mutRecDemoRoseName (roseSumSpec mutRecDemoDepthBudget)
        (cert.bound mutRecDemoRoseName) 64 :=
  cert.fnSpec_host_src_of_le mutRecDemoLinkedMod_fns_wf (f := mutRecDemoRoseFn)
    mutRecDemoRoseFn_mem_linked (roseSumSpec mutRecDemoDepthBudget) has hrs
    (fun _ _ _ _ _ h => h) hsem

theorem mutRecDemoCert_forestSum_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (has : lt.legalSig [i64, i64] = [i64, i64]) (hrs : lt.legalSig [i64] = [i64])
    (hsem : ∀ xs m Q X, forestSumSpec mutRecDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoForestName [i64, i64] [i64] xs m Q X) :
    T.Defined cert.host mutRecDemoForestName ∧
      T.FnSpec cert.host mutRecDemoForestName (forestSumSpec mutRecDemoDepthBudget)
        (cert.bound mutRecDemoForestName) 64 :=
  cert.fnSpec_host_src_of_le mutRecDemoLinkedMod_fns_wf (f := mutRecDemoForestFn)
    mutRecDemoForestFn_mem_linked (forestSumSpec mutRecDemoDepthBudget) has hrs
    (fun _ _ _ _ _ h => h) hsem

theorem mutRecDemoCert_roseSum_eventually
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxStack maxMem : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (I : TargetInit T maxStack maxMem)
    (has : lt.legalSig [i64, i64] = [i64, i64]) (hrs : lt.legalSig [i64] = [i64])
    (hargs : (T.toIsa.assignArgs [i64, i64]).isSome = true)
    (hsem : ∀ xs m Q X, roseSumSpec mutRecDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoRoseName [i64, i64] [i64] xs m Q X)
    (bsMem : List UInt8) (rt p : BitVec 64) (r : MutRecDemo.Rose)
    (hbs : bsMem.length ≤ maxMem)
    (hdep : MutRecDemo.roseDepth r ≤ mutRecDemoDepthBudget) (hsum : MutRecDemo.roseSum r < 2 ^ 63)
    (hmem : roseNatAt p r (bsMem.At 0x1000#64))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        T.mach.getGpr (T.mach.data st) I.ret0 = boxNat (MutRecDemo.roseSum r))
      (T.mach.mkState
        (I.initState (as := [i64, i64]) (cert.bound mutRecDemoRoseName) bsMem (rt, p, ()))
        (T.mach.labelAddr cert.host mutRecDemoRoseName)) := by
  have hsp : roseSumSpec mutRecDemoDepthBudget (rt, p, ()) (bsMem.At 0x1000#64)
      (fun v _ => v = (boxNat (MutRecDemo.roseSum r), ())) (fun _ _ _ _ => False) :=
    ⟨r, emp, hdep, hsum, by rw [sep_emp]; exact hmem, rfl⟩
  exact cert.eventually_ret1_i64_of_le I mutRecDemoLinkedMod_fns_wf
    (f := mutRecDemoRoseFn) mutRecDemoRoseFn_mem_linked rfl has hrs
    (roseSumSpec mutRecDemoDepthBudget) (fun _ _ _ _ _ h => h) hsem bsMem (rt, p, ())
    (boxNat (MutRecDemo.roseSum r)) hbs hargs hsp (fun _ _ h => h) hbound

theorem mutRecDemoCert_forestSum_eventually
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxStack maxMem : Nat}
    (cert : LinkedCertScc T L lt hcl mutRecDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (I : TargetInit T maxStack maxMem)
    (has : lt.legalSig [i64, i64] = [i64, i64]) (hrs : lt.legalSig [i64] = [i64])
    (hargs : (T.toIsa.assignArgs [i64, i64]).isSome = true)
    (hsem : ∀ xs m Q X, forestSumSpec mutRecDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoForestName [i64, i64] [i64] xs m Q X)
    (bsMem : List UInt8) (rt p : BitVec 64) (f : MutRecDemo.Forest) (R : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem)
    (hdep : MutRecDemo.forestDepth f ≤ mutRecDemoDepthBudget)
    (hsum : MutRecDemo.forestSum f < 2 ^ 63)
    (hmem : (forestNatAt p f ⋆ R) (bsMem.At 0x1000#64))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        T.mach.getGpr (T.mach.data st) I.ret0 = boxNat (MutRecDemo.forestSum f))
      (T.mach.mkState
        (I.initState (as := [i64, i64]) (cert.bound mutRecDemoForestName) bsMem (rt, p, ()))
        (T.mach.labelAddr cert.host mutRecDemoForestName)) := by
  have hsp : forestSumSpec mutRecDemoDepthBudget (rt, p, ()) (bsMem.At 0x1000#64)
      (fun v _ => v = (boxNat (MutRecDemo.forestSum f), ())) (fun _ _ _ _ => False) :=
    ⟨f, R, hdep, hsum, hmem, rfl⟩
  exact cert.eventually_ret1_i64_of_le I mutRecDemoLinkedMod_fns_wf
    (f := mutRecDemoForestFn) mutRecDemoForestFn_mem_linked rfl has hrs
    (forestSumSpec mutRecDemoDepthBudget) (fun _ _ _ _ _ h => h) hsem bsMem (rt, p, ())
    (boxNat (MutRecDemo.forestSum f)) hbs hargs hsp (fun _ _ h => h) hbound

/-! ## 5. Concrete Nested Multi-Child Rose-Tree Fixture (`312` Bytes @ `0x1000#64`) -/

/-- Nested 3-child `Forest` (`forestSum = 80`, `forestDepth = 6`):
`[node 20 [node 5 [], node 7 []], node 30 [], node 15 [node 3 []]]`. -/
@[expose] def sampleForest : MutRecDemo.Forest :=
  .cons (.node 20 (.cons (.node 5 .nil) (.cons (.node 7 .nil) .nil)))
    (.cons (.node 30 .nil)
      (.cons (.node 15 (.cons (.node 3 .nil) .nil)) .nil))

/-- Nested 3-level multi-child `Rose` tree (`roseSum = 90`, `roseDepth = 7`):
`node 10 sampleForest`. -/
@[expose] def sampleRose : MutRecDemo.Rose :=
  .node 10 sampleForest

/-- `24`-byte image of one `Rose.node` cell (`header` + `[v, cs]`). -/
@[expose] def roseNodeBytes (v cs : BitVec 64) : List UInt8 :=
  bytesOf (t := i8) roseNodeHdrBytes ++ bytes64 [v, cs]

/-- `24`-byte image of one `Forest.cons` cell (`header` + `[hd, tl]`). -/
@[expose] def forestConsBytes (hd tl : BitVec 64) : List UInt8 :=
  bytesOf (t := i8) forestConsHdrBytes ++ bytes64 [hd, tl]

@[expose] def sampleSub20Bytes : List UInt8 :=
  roseNodeBytes (boxNat 20) 0x1048#64 ++
  ((forestConsBytes 0x1060#64 0x1078#64 ++ roseNodeBytes (boxNat 5) 1#64) ++
   (forestConsBytes 0x1090#64 1#64 ++ roseNodeBytes (boxNat 7) 1#64))

@[expose] def sampleSub15Bytes : List UInt8 :=
  roseNodeBytes (boxNat 15) 0x1108#64 ++
  (forestConsBytes 0x1120#64 1#64 ++ roseNodeBytes (boxNat 3) 1#64)

@[expose] def sampleForestBytes : List UInt8 :=
  (forestConsBytes 0x1030#64 0x10a8#64 ++ sampleSub20Bytes) ++
  ((forestConsBytes 0x10c0#64 0x10d8#64 ++ roseNodeBytes (boxNat 30) 1#64) ++
   (forestConsBytes 0x10f0#64 1#64 ++ sampleSub15Bytes))

/-- Concrete `312`-byte (`13 × 24`B) heap image of `sampleRose` packed at `0x1000#64`
(`sampleForest` rooted at `0x1018#64`). -/
@[expose] def sampleRoseBytes : List UInt8 :=
  roseNodeBytes (boxNat 10) 0x1018#64 ++ sampleForestBytes

theorem roseNodeBytes_length (v cs : BitVec 64) : (roseNodeBytes v cs).length = 24 := by
  rw [roseNodeBytes, List.length_append, bytes64_length]
  have hHdr : (bytesOf (t := i8) roseNodeHdrBytes).length = 8 := by decide
  rw [hHdr]; simp

theorem forestConsBytes_length (hd tl : BitVec 64) : (forestConsBytes hd tl).length = 24 := by
  rw [forestConsBytes, List.length_append, bytes64_length]
  have hHdr : (bytesOf (t := i8) forestConsHdrBytes).length = 8 := by decide
  rw [hHdr]; simp

theorem sampleRoseBytes_length : sampleRoseBytes.length = 312 := by
  simp [sampleRoseBytes, sampleForestBytes, sampleSub20Bytes, sampleSub15Bytes,
    roseNodeBytes_length, forestConsBytes_length]

private theorem mr_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs : (Eq (bs1.At a) ⋆ Eq (bs2.At (a + BitVec.ofNat 64 bs1.length))) ((bs1 ++ bs2).At a) :=
    (congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)).mp rfl
  exact sep_mono2 (fun _ h => h ▸ hp) (fun _ h => h ▸ (h1 ▸ hq)) _ hs

private theorem array64_two_eq (p a b : BitVec 64) :
    array64 (p + 8#64) [a, b] = (cell64 (p + 8#64) a ⋆ cell64 (p + 16#64) b) := by
  simp only [array64_cons, array64_nil, sep_emp]
  have h16 : (p + 8#64) + 8 = p + 16#64 := by bv_omega
  rw [h16]

private theorem roseNodeBytes_ok (p v cs : BitVec 64) :
    roseNodeAt p v cs ((roseNodeBytes v cs).At p) := by
  have hHdr : array (t := i8) p roseNodeHdrBytes ((bytesOf (t := i8) roseNodeHdrBytes).At p) :=
    array_bytes (t := i8) p roseNodeHdrBytes (by decide)
  have hFlds : (cell64 (p + 8#64) v ⋆ cell64 (p + 16#64) cs) ((bytes64 [v, cs]).At (p + 8#64)) := by
    rw [← array64_two_eq]; exact array64_bytes (p + 8#64) [v, cs] (by simp)
  exact sep_cast (mr_sep_append
    (by decide : (bytesOf (t := i8) roseNodeHdrBytes).length = 8)
    (by rw [bytes64_length]; simp : (bytes64 [v, cs]).length = 16) (by decide) hHdr hFlds)
    (by unfold roseNodeAt; ac_rfl)

private theorem forestConsBytes_ok (p hd tl : BitVec 64) :
    forestConsAt p hd tl ((forestConsBytes hd tl).At p) := by
  have hHdr : array (t := i8) p forestConsHdrBytes ((bytesOf (t := i8) forestConsHdrBytes).At p) :=
    array_bytes (t := i8) p forestConsHdrBytes (by decide)
  have hFlds : (cell64 (p + 8#64) hd ⋆ cell64 (p + 16#64) tl)
      ((bytes64 [hd, tl]).At (p + 8#64)) := by
    rw [← array64_two_eq]; exact array64_bytes (p + 8#64) [hd, tl] (by simp)
  exact sep_cast (mr_sep_append
    (by decide : (bytesOf (t := i8) forestConsHdrBytes).length = 8)
    (by rw [bytes64_length]; simp : (bytes64 [hd, tl]).length = 16) (by decide) hHdr hFlds)
    (by unfold forestConsAt; ac_rfl)

private theorem roseNatAt_leaf (p : BitVec 64) (v : Nat) (hp0 : (p &&& 1#64) = 0#64) :
    roseNatAt p (.node v .nil) ((roseNodeBytes (boxNat v) 1#64).At p) := by
  refine ⟨hp0, 1#64, ?_⟩
  exact sep_pure_r.mpr ⟨rfl, by rw [sep_emp]; exact roseNodeBytes_ok p (boxNat v) 1#64⟩

private theorem forestNatAt_single {p : BitVec 64} {bs : List UInt8} {n : Nat}
    {hd : MutRecDemo.Rose}
    (hp0 : (p &&& 1#64) = 0#64) (hn : bs.length = n) (hfit : 24 + n ≤ 2 ^ 64)
    (hhd : roseNatAt (p + 24#64) hd (bs.At (p + 24#64))) :
    forestNatAt p (.cons hd .nil) ((forestConsBytes (p + 24#64) 1#64 ++ bs).At p) := by
  refine ⟨hp0, p + 24#64, 1#64, ?_⟩
  have hsep := mr_sep_append (forestConsBytes_length (p + 24#64) 1#64) hn hfit
    (forestConsBytes_ok p (p + 24#64) 1#64) hhd
  have hnil : ((forestConsAt p (p + 24#64) 1#64 ⋆ roseNatAt (p + 24#64) hd) ⋆
      forestNatAt 1#64 .nil) ((forestConsBytes (p + 24#64) 1#64 ++ bs).At p) :=
    sep_pure_r.mpr ⟨rfl, by rwa [sep_emp]⟩
  exact sep_cast hnil (by ac_rfl)

private theorem forestNatAt_cons_join {p : BitVec 64} {bsHd bsTl : List UInt8} {nHd nTl : Nat}
    {hd : MutRecDemo.Rose} {tl : MutRecDemo.Forest}
    (hp0 : (p &&& 1#64) = 0#64) (h1 : bsHd.length = nHd) (h2 : bsTl.length = nTl)
    (hfit1 : 24 + nHd ≤ 2 ^ 64) (hfit2 : (24 + nHd) + nTl ≤ 2 ^ 64)
    (hhd : roseNatAt (p + 24#64) hd (bsHd.At (p + 24#64)))
    (htl : forestNatAt (p + BitVec.ofNat 64 (24 + nHd)) tl
      (bsTl.At (p + BitVec.ofNat 64 (24 + nHd)))) :
    forestNatAt p (.cons hd tl)
      (((forestConsBytes (p + 24#64) (p + BitVec.ofNat 64 (24 + nHd)) ++ bsHd) ++ bsTl).At p) := by
  refine ⟨hp0, p + 24#64, p + BitVec.ofNat 64 (24 + nHd), ?_⟩
  have hL := mr_sep_append (forestConsBytes_length _ _) h1 hfit1
    (forestConsBytes_ok p (p + 24#64) (p + BitVec.ofNat 64 (24 + nHd))) hhd
  have hLenL : (forestConsBytes (p + 24#64) (p + BitVec.ofNat 64 (24 + nHd)) ++ bsHd).length =
      24 + nHd := by rw [List.length_append, forestConsBytes_length, h1]
  exact sep_cast (mr_sep_append hLenL h2 hfit2 hL htl) (by ac_rfl)

private theorem sampleForest_forestNatAt :
    forestNatAt 0x1018#64 sampleForest (sampleForestBytes.At 0x1018#64) := by
  have hR5 := roseNatAt_leaf 0x1060#64 5 (by decide)
  have hR7 := roseNatAt_leaf 0x1090#64 7 (by decide)
  have hR30 := roseNatAt_leaf 0x10c0#64 30 (by decide)
  have hR3 := roseNatAt_leaf 0x1120#64 3 (by decide)
  have hF7 : forestNatAt 0x1078#64 (.cons (.node 7 .nil) .nil)
      ((forestConsBytes 0x1090#64 1#64 ++ roseNodeBytes (boxNat 7) 1#64).At 0x1078#64) :=
    forestNatAt_single (p := 0x1078#64) (by decide) (roseNodeBytes_length _ _) (by decide) hR7
  have hF57 : forestNatAt 0x1048#64 (.cons (.node 5 .nil) (.cons (.node 7 .nil) .nil))
      (((forestConsBytes 0x1060#64 0x1078#64 ++ roseNodeBytes (boxNat 5) 1#64) ++
        (forestConsBytes 0x1090#64 1#64 ++ roseNodeBytes (boxNat 7) 1#64)).At 0x1048#64) :=
    forestNatAt_cons_join (p := 0x1048#64) (nHd := 24) (nTl := 48) (by decide)
      (roseNodeBytes_length _ _)
      (by rw [List.length_append, forestConsBytes_length, roseNodeBytes_length])
      (by decide) (by decide) hR5 hF7
  have hR20 : roseNatAt 0x1030#64
      (.node 20 (.cons (.node 5 .nil) (.cons (.node 7 .nil) .nil)))
      (sampleSub20Bytes.At 0x1030#64) := by
    refine ⟨by decide, 0x1048#64, ?_⟩
    exact mr_sep_append (roseNodeBytes_length _ _)
      (by simp [forestConsBytes_length, roseNodeBytes_length] :
        ((forestConsBytes 0x1060#64 0x1078#64 ++ roseNodeBytes (boxNat 5) 1#64) ++
         (forestConsBytes 0x1090#64 1#64 ++ roseNodeBytes (boxNat 7) 1#64)).length = 96)
      (by decide) (roseNodeBytes_ok 0x1030#64 (boxNat 20) 0x1048#64) hF57
  have hF3 : forestNatAt 0x1108#64 (.cons (.node 3 .nil) .nil)
      ((forestConsBytes 0x1120#64 1#64 ++ roseNodeBytes (boxNat 3) 1#64).At 0x1108#64) :=
    forestNatAt_single (p := 0x1108#64) (by decide) (roseNodeBytes_length _ _) (by decide) hR3
  have hR15 : roseNatAt 0x10f0#64 (.node 15 (.cons (.node 3 .nil) .nil))
      (sampleSub15Bytes.At 0x10f0#64) := by
    refine ⟨by decide, 0x1108#64, ?_⟩
    exact mr_sep_append (roseNodeBytes_length _ _)
      (by rw [List.length_append, forestConsBytes_length, roseNodeBytes_length] :
        (forestConsBytes 0x1120#64 1#64 ++ roseNodeBytes (boxNat 3) 1#64).length = 48)
      (by decide) (roseNodeBytes_ok 0x10f0#64 (boxNat 15) 0x1108#64) hF3
  have hF15 : forestNatAt 0x10d8#64 (.cons (.node 15 (.cons (.node 3 .nil) .nil)) .nil)
      ((forestConsBytes 0x10f0#64 1#64 ++ sampleSub15Bytes).At 0x10d8#64) :=
    forestNatAt_single (p := 0x10d8#64) (by decide)
      (by simp [sampleSub15Bytes, roseNodeBytes_length, forestConsBytes_length] :
        sampleSub15Bytes.length = 72)
      (by decide) hR15
  have hF30 : forestNatAt 0x10a8#64
      (.cons (.node 30 .nil) (.cons (.node 15 (.cons (.node 3 .nil) .nil)) .nil))
      (((forestConsBytes 0x10c0#64 0x10d8#64 ++ roseNodeBytes (boxNat 30) 1#64) ++
        (forestConsBytes 0x10f0#64 1#64 ++ sampleSub15Bytes)).At 0x10a8#64) :=
    forestNatAt_cons_join (p := 0x10a8#64) (nHd := 24) (nTl := 96) (by decide)
      (roseNodeBytes_length _ _)
      (by simp [sampleSub15Bytes, roseNodeBytes_length, forestConsBytes_length])
      (by decide) (by decide) hR30 hF15
  exact forestNatAt_cons_join (p := 0x1018#64) (nHd := 120) (nTl := 144) (by decide)
    (by simp [sampleSub20Bytes, roseNodeBytes_length, forestConsBytes_length])
    (by simp [sampleSub15Bytes, roseNodeBytes_length, forestConsBytes_length])
    (by decide) (by decide) hR20 hF30

/-- Concrete proof that `sampleRoseBytes.At 0x1000#64` realizes `sampleRose` at `0x1000#64`. -/
theorem sampleRose_roseNatAt :
    roseNatAt 0x1000#64 sampleRose (sampleRoseBytes.At 0x1000#64) := by
  refine ⟨by decide, 0x1018#64, ?_⟩
  exact mr_sep_append (roseNodeBytes_length _ _)
    (by simp [sampleForestBytes, sampleSub20Bytes, sampleSub15Bytes,
      roseNodeBytes_length, forestConsBytes_length] : sampleForestBytes.length = 288)
    (by decide) (roseNodeBytes_ok 0x1000#64 (boxNat 10) 0x1018#64) sampleForest_forestNatAt

/-- Concrete proof that `sampleRoseBytes.At 0x1000#64` exposes `sampleForest` at `0x1018#64`
framed against the root `Rose.node 10` cell. -/
theorem sampleRose_forestNatAt :
    (forestNatAt 0x1018#64 sampleForest ⋆ roseNodeAt 0x1000#64 (boxNat 10) 0x1018#64)
      (sampleRoseBytes.At 0x1000#64) := by
  have h1 := mr_sep_append (roseNodeBytes_length (boxNat 10) 0x1018#64)
    (by simp [sampleForestBytes, sampleSub20Bytes, sampleSub15Bytes,
      roseNodeBytes_length, forestConsBytes_length] : sampleForestBytes.length = 288)
    (by decide) (roseNodeBytes_ok 0x1000#64 (boxNat 10) 0x1018#64) sampleForest_forestNatAt
  exact sep_cast h1 (by ac_rfl)

/-- Concrete proof that `([] : List UInt8).At 0x1000#64` realizes `Forest.nil` at `1#64`. -/
theorem sampleForestNil_forestNatAt :
    (forestNatAt 1#64 .nil ⋆ emp) (([] : List UInt8).At 0x1000#64) := by
  rw [sep_emp]
  exact ⟨rfl, array_bytes (t := i8) 0x1000#64 [] (by decide)⟩

end LeanQbe.T.LeanLCNF

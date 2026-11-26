module

public import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.MainCertScc
public import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.Rules

/-!
# Budget-Indexed WP Soundness & Binary-Tree Heap Fixtures (`LcnfC0TreeDemoProof`)

Target-generic (`0` arch imports, `0` `import all`) soundness proof for the two-branch structurally
recursive Lean `LCNF` functions `TreeDemo.treeSum` and `TreeDemo.treeSize` compiled through
`compile_linked_budget_scc!` and linked onto `rtC0CoreMod`:

1. **`Tree` heap representation (`treeNodeAt`, `treeNatAt`)**: exact `32`-byte Lean 4
   `Tree.node` constructor layout (`m_rc = 1`, `m_cs_sz = 32`, `m_other = 3`, `m_tag = 1`,
   tagged scalar `boxNat v` @ `+8`, left pointer @ `+16`, right pointer @ `+24`;
   `Tree.leaf = 1#64`).
2. **Depth-indexed specifications (`treeSumSpec`, `treeSizeSpec`) & fixed-point proofs
   (`treeSum_budgetSemScc`, `treeSize_budgetSemScc`)**: well-founded induction via
   `BudgetEnv.lfp_wf_mkSccOp` on tree depth `d`, reusing stack budget `sb - 48` across both
   sequential sibling calls (`272 + 48 * d`).
3. **Target-generic `LinkedCertScc` bridges**: connects `semChunks` across
   `rtScc.chunks ++ [sumChunk, sizeChunk]` to `LinkedCertScc.fnSpec_host_src_of_le` and
   `LinkedCertScc.eventually_ret1_i64_of_le`.
4. **Concrete asymmetric binary-tree fixture (`sampleTree`, `sampleTreeBytes`)**: `128`-byte
   4-node tree `node 10 (node 20 leaf (node 5 leaf leaf)) (node 30 leaf leaf)` @ `0x1000#64`
   with `treeSum = 65` (`boxNat 65 = 131#64`), `treeSize = 4` (`boxNat 4 = 9#64`), `depth = 3`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step

/-! ## 1. Tagged-Scalar `Nat` Helpers & `Tree` Heap Predicates -/

private theorem tree_boxNat_and_one {n : Nat} (hn : n < 2 ^ 63) :
    (boxNat n &&& 1#64) = 1#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := by decide
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, boxNat, BitVec.toNat_ofNat, hmod]
  omega

private theorem tree_boxNat_add_fast {aVal bVal : Nat} (hlt : aVal + bVal < 2 ^ 63) :
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
  have ha1 : (boxNat aVal &&& 1#64) = 1#64 := tree_boxNat_and_one (by omega)
  have hb1 : (boxNat bVal &&& 1#64) = 1#64 := tree_boxNat_and_one (by omega)
  have hlsb : (boxNat aVal &&& boxNat bVal &&& 1#64) = 1#64 := by
    rw [BitVec.and_assoc, hb1, ha1]
  have hbit : ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true := by
    rw [hlsb]; decide
  have hult : ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, hadd, hb]
    omega
  exact ⟨hbit, hult, hsumEq⟩

/-- Little-endian header bytes of a `Tree.node` heap object (`m_rc = 1`, `m_cs_sz = 32`,
`m_other = 3`, `m_tag = 1`). -/
@[expose] def treeNodeHdrBytes : List (Val i8) :=
  [1#8, 0#8, 0#8, 0#8, 32#8, 0#8, 3#8, 1#8]

/-- Raw byte image of `treeNodeHdrBytes`, matching `LcnfObj.header` for a `Tree.node` cell. -/
theorem treeNodeHdrBytes_matches_lcnfObj (p v l r : BitVec 64) :
    bytesOf (t := i8) treeNodeHdrBytes =
      Int.toBytes 8 (LcnfObj.header
        { addr := p, rc := 1#32, csSz := 32, other := 3, tag := 1,
          fields := [v, l, r] }).toInt := by
  dsimp only [LcnfObj.header]
  decide

/-- Separation-logic footprint of one `32`-byte `Tree.node` heap object at `p` (`tag = 1` @ `+7`,
`v` @ `+8`, `l` @ `+16`, `r` @ `+24`). -/
@[expose] def treeNodeAt (p v l r : BitVec 64) : Mem 64 → Prop :=
  array (t := i8) p treeNodeHdrBytes ⋆
    cell64 (p + 8#64) v ⋆ cell64 (p + 16#64) l ⋆ cell64 (p + 24#64) r

/-- Inductive heap layout of a `TreeDemo.Tree` of tagged-scalar values rooted at `p`
(`Tree.leaf = 1#64`, `Tree.node` = aligned heap pointer to `treeNodeAt` and disjoint subtrees). -/
@[expose] def treeNatAt : BitVec 64 → TreeDemo.Tree → Mem 64 → Prop
  | p, .leaf, m => p = 1#64 ∧ emp m
  | p, .node v l r, m =>
    (p &&& 1#64) = 0#64 ∧
    ∃ pl pr : BitVec 64,
      (treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pl l ⋆ treeNatAt pr r) m

private theorem treeNodeAt_load_tag {p v l r : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (treeNodeAt p v l r ⋆ R) m) :
    loadVal m i8 (p + 7#64) = some 1#8 := by
  unfold treeNodeAt at hm
  have hm' : (array (t := i8) p treeNodeHdrBytes ⋆
      (cell64 (p + 8#64) v ⋆ cell64 (p + 16#64) l ⋆ cell64 (p + 24#64) r ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_array (t := i8) (i := 7) (by decide) (by decide) hm'

private theorem treeNodeAt_load_val {p v l r : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (treeNodeAt p v l r ⋆ R) m) :
    loadVal m i64 (p + 8#64) = some v := by
  unfold treeNodeAt at hm
  have hm' : (cell64 (p + 8#64) v ⋆
      (array (t := i8) p treeNodeHdrBytes ⋆ cell64 (p + 16#64) l ⋆
        cell64 (p + 24#64) r ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

private theorem treeNodeAt_load_left {p v l r : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (treeNodeAt p v l r ⋆ R) m) :
    loadVal m i64 (p + 16#64) = some l := by
  unfold treeNodeAt at hm
  have hm' : (cell64 (p + 16#64) l ⋆
      (array (t := i8) p treeNodeHdrBytes ⋆ cell64 (p + 8#64) v ⋆
        cell64 (p + 24#64) r ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

private theorem treeNodeAt_load_right {p v l r : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (treeNodeAt p v l r ⋆ R) m) :
    loadVal m i64 (p + 24#64) = some r := by
  unfold treeNodeAt at hm
  have hm' : (cell64 (p + 24#64) r ⋆
      (array (t := i8) p treeNodeHdrBytes ⋆ cell64 (p + 8#64) v ⋆
        cell64 (p + 16#64) l ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

/-! ## 2. Reusable Lowered-IR Pattern WP Lemmas -/

private def treeDecRefExpr (rt obj : Val i64) (cont : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var obj) (.imm 1#64)) fun b0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var b0.1) (.imm 0#64)) fun b1 =>
      .group (sig := [[]])
        (fun _ => .cons (fun _ => cont) .nil)
        fun J =>
        .jnz (.var b1.1)
          (.jump J.1 ())
          (.load i32 (.var obj) fun rc =>
            .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var rc) (.imm 1#32)) fun is1 =>
              .jnz (.var is1.1)
                (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := [])
                  (.var rt, .var obj, ()) fun _ => .jump J.1 ())
                (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var rc) (.imm 1#32)) fun gt1 =>
                  .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var gt1.1)) fun b =>
                    .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var rc) (.var b.1))
                      fun rc' => .store (.var rc'.1) (.var obj) (.jump J.1 ())))

private theorem wp_treeDecRefExpr_scalar {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {rt obj : Val i64} {cont : Expr Val Cont [i64]}
    (hsc : (obj &&& 1#64) = 1#64) (hcont : wp Γ Q X cont m) :
    wp Γ Q X (treeDecRefExpr rt obj cont) m := by
  have hbit : ((obj &&& 1#64) != 0#64) = true := by rw [hsc]; decide
  dsimp only [treeDecRefExpr]
  c0_let_simp
  refine wp_join_group (fun _ m' => m' = m) ?_ ?_
  · rintro J ⟨⟩ m' hm'
    subst m'
    rw [Blocks.get.eq_1]
    exact hcont
  · intro J hJ
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hbit])⟩
    rw [wp_jump]
    exact hJ () m rfl

private def treeNatAddExpr (rt : Val i64) (a : Arg Val i64) (b : Val i64)
    (cont : Tup Val [i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) a (.var b)) fun v0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v0.1) (.imm 1#64)) fun v1 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v1.1) (.imm 0#64)) fun v2 =>
        .group (sig := [[i64]])
          (fun _ => .cons cont .nil)
          fun Jsum =>
          .jnz (.var v2.1)
            (.let_ (_root_.LeanQbe.T.op2 (OpCode.sub i64) a (.imm 1#64)) fun v3 =>
              .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var v3.1) (.var b)) fun v4 =>
                .let_ (_root_.LeanQbe.T.op2 (OpCode.ult i64) (.var v4.1) (.var b)) fun v5 =>
                  .jnz (.var v5.1)
                    (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
                      (.var rt, .imm 1#64, a, .var b, ()) fun v6 => .jump Jsum.1 (.var v6.1, ()))
                    (.jump Jsum.1 (.var v4.1, ())))
            (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
              (.var rt, .imm 1#64, a, .var b, ()) fun v7 => .jump Jsum.1 (.var v7.1, ()))

private theorem wp_treeNatAddExpr_fast {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {rt : Val i64} {a : Arg Val i64} {aVal bVal : Nat}
    {cont : Tup Val [i64] → Expr Val Cont [i64]}
    (ha : a.val = boxNat aVal) (hlt : aVal + bVal < 2 ^ 63)
    (hcont : wp Γ Q X (cont (boxNat (aVal + bVal), ())) m) :
    wp Γ Q X (treeNatAddExpr rt a (boxNat bVal) cont) m := by
  obtain ⟨hbit, hult, heq⟩ := tree_boxNat_add_fast hlt
  dsimp only [treeNatAddExpr]
  c0_let_simp
  refine wp_join_group (fun s m' => s.1 = boxNat (aVal + bVal) ∧ m' = m) ?_ ?_
  · rintro Jsum ⟨sVal, ⟨⟩⟩ m' ⟨rfl, hm'⟩
    subst m'
    rw [Blocks.get.eq_1]
    exact hcont
  · intro Jsum hJsum
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, ha, hbit])⟩
    c0_let_simp
    rw [wp_jnz]
    refine ⟨fun h => absurd h (by simp [Arg.val_var, ha, hult]), fun _ => ?_⟩
    rw [wp_jump]
    exact hJsum _ m ⟨by simpa [Arg.val_var, ha] using heq, rfl⟩

private def treeTagDispatchExpr (p : Val i64) (nodeBody : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  let tagBlk (tagTup : Tup Val [i64]) : Expr Val Cont [i64] :=
    .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i64) (.var tagTup.1) (.imm 0#64)) fun v2 =>
      .jnz (.var v2.1) (.ret (.imm 1#64, ())) nodeBody
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

private theorem wp_treeTagDispatch_leaf {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {nodeBody : Expr Val Cont [i64]} (hq : Q (1#64, ()) m) :
    wp Γ Q X (treeTagDispatchExpr 1#64 nodeBody) m := by
  dsimp only [treeTagDispatchExpr]
  c0_let_simp
  refine wp_join_group (fun tagTup m' => tagTup.1 = 0#64 ∧ m' = m) ?_ ?_
  · rintro J ⟨tag, ⟨⟩⟩ m' ⟨rfl, rfl⟩
    rw [Blocks.get.eq_1]
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

private theorem wp_treeTagDispatch_node {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {p : Val i64} {nodeBody : Expr Val Cont [i64]}
    (hp0 : (p &&& 1#64) = 0#64) (hldTag : loadVal m i8 (p + 7#64) = some 1#8)
    (hbody : wp Γ Q X nodeBody m) :
    wp Γ Q X (treeTagDispatchExpr p nodeBody) m := by
  dsimp only [treeTagDispatchExpr]
  c0_let_simp
  refine wp_join_group (fun tagTup m' => tagTup.1 = 1#64 ∧ m' = m) ?_ ?_
  · rintro J ⟨tag, ⟨⟩⟩ m' ⟨rfl, hm'⟩
    subst m'
    rw [Blocks.get.eq_1]
    c0_let_simp
    rw [wp_jnz]
    refine ⟨fun h => absurd h (by simp [Arg.val_var]), fun _ => hbody⟩
  · intro J hJ
    rw [wp_jnz]
    refine ⟨fun h => absurd h (by simp [Arg.val_var, hp0]), fun _ => ?_⟩
    c0_let_simp
    refine wp_load_of (v := 1#8) (by simpa [Arg.val_var] using hldTag) ?_
    c0_let_simp
    exact hJ (1#64, ()) m ⟨rfl, rfl⟩

/-! ## 3. Depth-Indexed Specifications & `BudgetEnv.lfp_wf_mkSccOp` Proofs -/

/-- Exact stack budget required by `TreeDemo.treeSum` and `TreeDemo.treeSize` for trees of
depth `≤ d`: `272 + 48 * d`. -/
@[expose] def treeReqBudget (d : Nat) : Nat :=
  treeDemoMinEntry + d * treeDemoMaxFrame

/-- Source-level specification of `TreeDemo.treeSum` at maximum tree depth `D`:
for any `t : TreeDemo.Tree` laid out at `p` with `t.depth ≤ D` and `TreeDemo.treeSum t < 2 ^ 63`,
`treeSum(rt, p)` returns `boxNat (TreeDemo.treeSum t)` leaving memory unchanged (`XPost`-free). -/
@[expose] def treeSumSpec (D : Nat) : Spec [i64, i64] [i64] :=
  fun (_rt, p, ()) m Q _ =>
    ∃ (t : TreeDemo.Tree) (R : Mem 64 → Prop),
      t.depth ≤ D ∧ TreeDemo.treeSum t < 2 ^ 63 ∧
      (treeNatAt p t ⋆ R) m ∧
      Q (boxNat (TreeDemo.treeSum t), ()) m

/-- Source-level specification of `TreeDemo.treeSize` at maximum tree depth `D`:
for any `t : TreeDemo.Tree` laid out at `p` with `t.depth ≤ D` and `TreeDemo.treeSize t < 2 ^ 63`,
`treeSize(rt, p)` returns `boxNat (TreeDemo.treeSize t)` leaving memory unchanged. -/
@[expose] def treeSizeSpec (D : Nat) : Spec [i64, i64] [i64] :=
  fun (_rt, p, ()) m Q _ =>
    ∃ (t : TreeDemo.Tree) (R : Mem 64 → Prop),
      t.depth ≤ D ∧ TreeDemo.treeSize t < 2 ^ 63 ∧
      (treeNatAt p t ⋆ R) m ∧
      Q (boxNat (TreeDemo.treeSize t), ()) m

private def treeSumIdxEnv (d : Nat) : Env :=
  fun nm as bs xs m Q X =>
    nm = treeDemoSumName ∧
    ∃ (ha : as = [i64, i64]) (hb : bs = [i64]),
      treeSumSpec d (ha ▸ xs) m (hb ▸ Q) X

private def treeSizeIdxEnv (d : Nat) : Env :=
  fun nm as bs xs m Q X =>
    nm = treeDemoSizeName ∧
    ∃ (ha : as = [i64, i64]) (hb : bs = [i64]),
      treeSizeSpec d (ha ▸ xs) m (hb ▸ Q) X

private theorem tree_budget_wp_mono_local :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m' _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m' hwp

private theorem treeSum_step_wp {Γcall : Env} {d : Nat}
    (hrec : ∀ j, j < d →
      ∀ xs m Q X, treeSumSpec j xs m Q X →
        Γcall treeDemoSumName [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, treeSumSpec d xs m Q X →
      Func.wp Γcall treeDemoSumFn.body xs m Q X := by
  rintro ⟨rt, p, ⟨⟩⟩ m Q X ⟨t, R, hdep, hsum, hm, hq⟩
  change wp Γcall Q X
    (treeTagDispatchExpr p
      (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 8#64)) fun a0 =>
        .load i64 (.var a0.1) fun v =>
          .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 16#64)) fun a1 =>
            .load i64 (.var a1.1) fun l =>
              .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 24#64)) fun a2 =>
                .load i64 (.var a2.1) fun r =>
                  .call treeDemoSumName (as := [i64, i64]) (bs := [i64])
                    (.var rt, .var l, ()) fun sl =>
                    treeNatAddExpr rt (.var v) sl.1 fun vl =>
                      treeDecRefExpr rt sl.1
                        (.call treeDemoSumName (as := [i64, i64]) (bs := [i64])
                          (.var rt, .var r, ()) fun sr =>
                          treeNatAddExpr rt (.var vl.1) sr.1 fun res =>
                            treeDecRefExpr rt sr.1
                              (treeDecRefExpr rt vl.1 (.ret (.var res.1, ())))))) m
  cases t with
  | leaf =>
    obtain ⟨rfl, _⟩ := sep_pure_l.mp hm
    exact wp_treeTagDispatch_leaf hq
  | node v l r =>
    obtain ⟨hp0, hm1⟩ := sep_pure_l.mp hm
    obtain ⟨pl, hm2⟩ := sep_ex_l.mp hm1
    obtain ⟨pr, hmNode⟩ := sep_ex_l.mp hm2
    have hNodeR : (treeNodeAt p (boxNat v) pl pr ⋆ (treeNatAt pl l ⋆ treeNatAt pr r ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hLeftR : (treeNatAt pl l ⋆ (treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pr r ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hRightR : (treeNatAt pr r ⋆ (treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pl l ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hldTag := treeNodeAt_load_tag hNodeR
    have hldVal := treeNodeAt_load_val hNodeR
    have hldL := treeNodeAt_load_left hNodeR
    have hldR := treeNodeAt_load_right hNodeR
    have hdepL : l.depth < d := by dsimp only [TreeDemo.Tree.depth] at hdep; omega
    have hdepR : r.depth < d := by dsimp only [TreeDemo.Tree.depth] at hdep; omega
    have hsumDef : TreeDemo.treeSum (.node v l r) =
        v + TreeDemo.treeSum l + TreeDemo.treeSum r := rfl
    have hsumL : TreeDemo.treeSum l < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hsumVL : v + TreeDemo.treeSum l < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hsumR : TreeDemo.treeSum r < 2 ^ 63 := by rw [hsumDef] at hsum; omega
    have hsumAll : (v + TreeDemo.treeSum l) + TreeDemo.treeSum r < 2 ^ 63 := by
      rw [hsumDef] at hsum; exact hsum
    refine wp_treeTagDispatch_node hp0 hldTag ?_
    c0_let_simp
    refine wp_load_of (v := boxNat v) (by simpa [Arg.val_var] using hldVal) ?_
    c0_let_simp
    refine wp_load_of (v := pl) (by simpa [Arg.val_var] using hldL) ?_
    c0_let_simp
    refine wp_load_of (v := pr) (by simpa [Arg.val_var] using hldR) ?_
    let PL : Post [i64] := fun s m' => s = (boxNat (TreeDemo.treeSum l), ()) ∧ m' = m
    have hCallL : Γcall treeDemoSumName [i64, i64] [i64] (rt, pl, ()) m PL X :=
      hrec l.depth hdepL (rt, pl, ()) m PL X
        ⟨l, treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pr r ⋆ R,
          Nat.le_refl _, hsumL, hLeftR, ⟨rfl, rfl⟩⟩
    refine ⟨PL, X, hCallL, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨slVal, ⟨⟩⟩ m1 ⟨hslEq, hm1'⟩
    subst m1
    obtain rfl : slVal = boxNat (TreeDemo.treeSum l) := (Prod.ext_iff.mp hslEq).1
    refine wp_treeNatAddExpr_fast (aVal := v) (bVal := TreeDemo.treeSum l) rfl hsumVL ?_
    refine wp_treeDecRefExpr_scalar (tree_boxNat_and_one hsumL) ?_
    let PR : Post [i64] := fun s m' => s = (boxNat (TreeDemo.treeSum r), ()) ∧ m' = m
    have hCallR : Γcall treeDemoSumName [i64, i64] [i64] (rt, pr, ()) m PR X :=
      hrec r.depth hdepR (rt, pr, ()) m PR X
        ⟨r, treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pl l ⋆ R,
          Nat.le_refl _, hsumR, hRightR, ⟨rfl, rfl⟩⟩
    refine ⟨PR, X, hCallR, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨srVal, ⟨⟩⟩ m2 ⟨hsrEq, hm2'⟩
    subst m2
    obtain rfl : srVal = boxNat (TreeDemo.treeSum r) := (Prod.ext_iff.mp hsrEq).1
    refine wp_treeNatAddExpr_fast (aVal := v + TreeDemo.treeSum l) (bVal := TreeDemo.treeSum r)
      rfl hsumAll ?_
    refine wp_treeDecRefExpr_scalar (tree_boxNat_and_one hsumR) ?_
    refine wp_treeDecRefExpr_scalar (tree_boxNat_and_one hsumVL) ?_
    rw [wp_ret]
    exact hq

private theorem treeSize_step_wp {Γcall : Env} {d : Nat}
    (hrec : ∀ j, j < d →
      ∀ xs m Q X, treeSizeSpec j xs m Q X →
        Γcall treeDemoSizeName [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, treeSizeSpec d xs m Q X →
      Func.wp Γcall treeDemoSizeFn.body xs m Q X := by
  rintro ⟨rt, p, ⟨⟩⟩ m Q X ⟨t, R, hdep, hsz, hm, hq⟩
  change wp Γcall Q X
    (treeTagDispatchExpr p
      (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 16#64)) fun a1 =>
        .load i64 (.var a1.1) fun l =>
          .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var p) (.imm 24#64)) fun a2 =>
            .load i64 (.var a2.1) fun r =>
              .call treeDemoSizeName (as := [i64, i64]) (bs := [i64])
                (.var rt, .var l, ()) fun sl =>
                treeNatAddExpr rt (.imm 3#64) sl.1 fun vl =>
                  treeDecRefExpr rt sl.1
                    (.call treeDemoSizeName (as := [i64, i64]) (bs := [i64])
                      (.var rt, .var r, ()) fun sr =>
                      treeNatAddExpr rt (.var vl.1) sr.1 fun res =>
                        treeDecRefExpr rt sr.1
                          (treeDecRefExpr rt vl.1 (.ret (.var res.1, ())))))) m
  cases t with
  | leaf =>
    obtain ⟨rfl, _⟩ := sep_pure_l.mp hm
    exact wp_treeTagDispatch_leaf hq
  | node v l r =>
    obtain ⟨hp0, hm1⟩ := sep_pure_l.mp hm
    obtain ⟨pl, hm2⟩ := sep_ex_l.mp hm1
    obtain ⟨pr, hmNode⟩ := sep_ex_l.mp hm2
    have hNodeR : (treeNodeAt p (boxNat v) pl pr ⋆ (treeNatAt pl l ⋆ treeNatAt pr r ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hLeftR : (treeNatAt pl l ⋆ (treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pr r ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hRightR : (treeNatAt pr r ⋆ (treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pl l ⋆ R)) m :=
      sep_cast hmNode (by ac_rfl)
    have hldTag := treeNodeAt_load_tag hNodeR
    have hldL := treeNodeAt_load_left hNodeR
    have hldR := treeNodeAt_load_right hNodeR
    have hdepL : l.depth < d := by dsimp only [TreeDemo.Tree.depth] at hdep; omega
    have hdepR : r.depth < d := by dsimp only [TreeDemo.Tree.depth] at hdep; omega
    have hszDef : TreeDemo.treeSize (.node v l r) =
        1 + TreeDemo.treeSize l + TreeDemo.treeSize r := rfl
    have hszL : TreeDemo.treeSize l < 2 ^ 63 := by rw [hszDef] at hsz; omega
    have hsz1L : 1 + TreeDemo.treeSize l < 2 ^ 63 := by rw [hszDef] at hsz; omega
    have hszR : TreeDemo.treeSize r < 2 ^ 63 := by rw [hszDef] at hsz; omega
    have hszAll : (1 + TreeDemo.treeSize l) + TreeDemo.treeSize r < 2 ^ 63 := by
      rw [hszDef] at hsz; exact hsz
    refine wp_treeTagDispatch_node hp0 hldTag ?_
    c0_let_simp
    refine wp_load_of (v := pl) (by simpa [Arg.val_var] using hldL) ?_
    c0_let_simp
    refine wp_load_of (v := pr) (by simpa [Arg.val_var] using hldR) ?_
    let PL : Post [i64] := fun s m' => s = (boxNat (TreeDemo.treeSize l), ()) ∧ m' = m
    have hCallL : Γcall treeDemoSizeName [i64, i64] [i64] (rt, pl, ()) m PL X :=
      hrec l.depth hdepL (rt, pl, ()) m PL X
        ⟨l, treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pr r ⋆ R,
          Nat.le_refl _, hszL, hLeftR, ⟨rfl, rfl⟩⟩
    refine ⟨PL, X, hCallL, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨slVal, ⟨⟩⟩ m1 ⟨hslEq, hm1'⟩
    subst m1
    obtain rfl : slVal = boxNat (TreeDemo.treeSize l) := (Prod.ext_iff.mp hslEq).1
    refine wp_treeNatAddExpr_fast (aVal := 1) (bVal := TreeDemo.treeSize l) rfl hsz1L ?_
    refine wp_treeDecRefExpr_scalar (tree_boxNat_and_one hszL) ?_
    let PR : Post [i64] := fun s m' => s = (boxNat (TreeDemo.treeSize r), ()) ∧ m' = m
    have hCallR : Γcall treeDemoSizeName [i64, i64] [i64] (rt, pr, ()) m PR X :=
      hrec r.depth hdepR (rt, pr, ()) m PR X
        ⟨r, treeNodeAt p (boxNat v) pl pr ⋆ treeNatAt pl l ⋆ R,
          Nat.le_refl _, hszR, hRightR, ⟨rfl, rfl⟩⟩
    refine ⟨PR, X, hCallR, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨srVal, ⟨⟩⟩ m2 ⟨hsrEq, hm2'⟩
    subst m2
    obtain rfl : srVal = boxNat (TreeDemo.treeSize r) := (Prod.ext_iff.mp hsrEq).1
    refine wp_treeNatAddExpr_fast (aVal := 1 + TreeDemo.treeSize l) (bVal := TreeDemo.treeSize r)
      rfl hszAll ?_
    refine wp_treeDecRefExpr_scalar (tree_boxNat_and_one hszR) ?_
    refine wp_treeDecRefExpr_scalar (tree_boxNat_and_one hsz1L) ?_
    rw [wp_ret]
    exact hq

/-- Budget-indexed `BudgetEnv.semScc` soundness for `TreeDemo.treeSum` at any depth `d` and
stack budget `sb ≥ 272 + 48 * d`, proved via `BudgetEnv.lfp_wf_mkSccOp`. -/
theorem treeSum_budgetSemScc (extSigs : List SigEntry) (Γext : Env)
    (d sb : Nat) (hsb : treeReqBudget d ≤ sb) :
    ∀ xs m Q X, treeSumSpec d xs m Q X →
      BudgetEnv.semScc ⟨[treeDemoSumBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
        Γext sb treeDemoSumName [i64, i64] [i64] xs m Q X := by
  let BM : BudgetModule := ⟨[treeDemoSumBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
  have hsig : (treeDemoSumName, [i64, i64], [i64]) ∈ BM.fnSigs := by
    simp [BM, BudgetModule.fnSigs, treeDemoSumBudgetFn, treeDemoSumFn,
      treeDemoSumName, treeDemoTfs.tf_0, Fn.sig, Frontend.C0.TFlatFn.toFn]
  intro xs m Q X hspec
  refine BudgetEnv.lfp_wf_mkSccOp (lt := Nat.lt) Nat.lt_wfRel.wf treeReqBudget BM
    (BudgetEnv.const Γext) tree_budget_wp_mono_local treeSumIdxEnv
    (fun idx sb' hsb' bfn hbfn Γcall _ hcall _ _ _ xs' m' Q' X' hS => by
      dsimp only [BM] at hbfn
      rw [List.mem_singleton] at hbfn
      subst hbfn
      rcases hS with ⟨_, ha, hb, hsp⟩
      have hmax : treeDemoSumBudgetFn.maxFrame ≤ sb' := by
        dsimp only [treeDemoSumBudgetFn, treeReqBudget, treeDemoMaxFrame,
          treeDemoMinEntry] at hsb' ⊢
        omega
      have hmin : treeDemoSumBudgetFn.minEntry ≤ sb' := by
        dsimp only [treeDemoSumBudgetFn, treeReqBudget, treeDemoMaxFrame,
          treeDemoMinEntry] at hsb' ⊢
        omega
      refine ⟨hmax, hmin, ?_⟩
      have hrec : ∀ j, j < idx → ∀ ys m₁ Q₁ X₁, treeSumSpec j ys m₁ Q₁ X₁ →
          Γcall treeDemoSumName [i64, i64] [i64] ys m₁ Q₁ X₁ := by
        intro j hlt ys m₁ Q₁ X₁ hspj
        have hreqj : treeReqBudget j ≤ sb' - treeDemoSumBudgetFn.maxFrame := by
          dsimp only [treeDemoSumBudgetFn, treeReqBudget, treeDemoMaxFrame,
            treeDemoMinEntry] at hsb' ⊢
          omega
        exact hcall j hlt hreqj treeDemoSumName [i64, i64] [i64] ys m₁ Q₁ X₁
          ⟨hsig, rfl, rfl, rfl, hspj⟩
      exact treeSum_step_wp hrec xs' m' Q' X' (by simpa using hsp))
    d sb hsb treeDemoSumName [i64, i64] [i64] xs m Q X ⟨hsig, rfl, rfl, rfl, hspec⟩

/-- Budget-indexed `BudgetEnv.semScc` soundness for `TreeDemo.treeSize` at any depth `d` and
stack budget `sb ≥ 272 + 48 * d`, proved via `BudgetEnv.lfp_wf_mkSccOp`. -/
theorem treeSize_budgetSemScc (extSigs : List SigEntry) (Γext : Env)
    (d sb : Nat) (hsb : treeReqBudget d ≤ sb) :
    ∀ xs m Q X, treeSizeSpec d xs m Q X →
      BudgetEnv.semScc ⟨[treeDemoSizeBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
        Γext sb treeDemoSizeName [i64, i64] [i64] xs m Q X := by
  let BM : BudgetModule := ⟨[treeDemoSizeBudgetFn], externsOfSigs extSigs, rtExitSyms⟩
  have hsig : (treeDemoSizeName, [i64, i64], [i64]) ∈ BM.fnSigs := by
    simp [BM, BudgetModule.fnSigs, treeDemoSizeBudgetFn, treeDemoSizeFn,
      treeDemoSizeName, treeDemoTfs.tf_1, Fn.sig, Frontend.C0.TFlatFn.toFn]
  intro xs m Q X hspec
  refine BudgetEnv.lfp_wf_mkSccOp (lt := Nat.lt) Nat.lt_wfRel.wf treeReqBudget BM
    (BudgetEnv.const Γext) tree_budget_wp_mono_local treeSizeIdxEnv
    (fun idx sb' hsb' bfn hbfn Γcall _ hcall _ _ _ xs' m' Q' X' hS => by
      dsimp only [BM] at hbfn
      rw [List.mem_singleton] at hbfn
      subst hbfn
      rcases hS with ⟨_, ha, hb, hsp⟩
      have hmax : treeDemoSizeBudgetFn.maxFrame ≤ sb' := by
        dsimp only [treeDemoSizeBudgetFn, treeReqBudget, treeDemoMaxFrame,
          treeDemoMinEntry] at hsb' ⊢
        omega
      have hmin : treeDemoSizeBudgetFn.minEntry ≤ sb' := by
        dsimp only [treeDemoSizeBudgetFn, treeReqBudget, treeDemoMaxFrame,
          treeDemoMinEntry] at hsb' ⊢
        omega
      refine ⟨hmax, hmin, ?_⟩
      have hrec : ∀ j, j < idx → ∀ ys m₁ Q₁ X₁, treeSizeSpec j ys m₁ Q₁ X₁ →
          Γcall treeDemoSizeName [i64, i64] [i64] ys m₁ Q₁ X₁ := by
        intro j hlt ys m₁ Q₁ X₁ hspj
        have hreqj : treeReqBudget j ≤ sb' - treeDemoSizeBudgetFn.maxFrame := by
          dsimp only [treeDemoSizeBudgetFn, treeReqBudget, treeDemoMaxFrame,
            treeDemoMinEntry] at hsb' ⊢
          omega
        exact hcall j hlt hreqj treeDemoSizeName [i64, i64] [i64] ys m₁ Q₁ X₁
          ⟨hsig, rfl, rfl, rfl, hspj⟩
      exact treeSize_step_wp hrec xs' m' Q' X' (by simpa using hsp))
    d sb hsb treeDemoSizeName [i64, i64] [i64] xs m Q X ⟨hsig, rfl, rfl, rfl, hspec⟩

/-! ## 4. Target-Generic `LinkedCertScc` Semantic & Machine Bridges -/

private theorem tree_semChunks_append {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} (cs₁ cs₂ : List (Chunk T lt exits nX)) (extSigs : List SigEntry) (Γ₀ : Env) :
    semChunks extSigs Γ₀ (cs₁ ++ cs₂) =
      semChunks (sccChunksSigAcc extSigs cs₁) (semChunks extSigs Γ₀ cs₁) cs₂ := by
  induction cs₁ generalizing extSigs Γ₀ with
  | nil => rfl
  | cons c rest ih =>
    simpa only [List.cons_append, semChunks, sccChunksSigAcc] using
      ih (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)

/-- Structural shape witness for a `treeDemoLinkedMod` certificate whose tail consists of the two
`.recBudgetSCC` chunks for `treeSum` and `treeSize`. -/
@[expose] def TreeDemoChunksShape {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound []) : Prop :=
  ∃ (pre : List (Chunk T lt rtExitSyms 64))
    (ext1 ext2 : List (SigEntry × Nat))
    (hints1 hints2 : List T.toIsa.Hints)
    (cbr1 : CompiledBudgetRec T lt ext1 rtExitSyms 64 [treeDemoSumBudgetFn] hints1
      treeDemoExportBound treeDemoExportBounds)
    (cbr2 : CompiledBudgetRec T lt ext2 rtExitSyms 64 [treeDemoSizeBudgetFn] hints2
      treeDemoExportBound treeDemoExportBounds),
    cert.chunks = pre ++
      [Chunk.recBudgetSCC ext1 [treeDemoSumBudgetFn] hints1
        treeDemoExportBound treeDemoExportBounds cbr1,
       Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2
        treeDemoExportBound treeDemoExportBounds cbr2]

/-- Target-generic semantic bridge for `TreeDemo.treeSum` (first `.recBudgetSCC` chunk, projected
across the trailing `treeSize` chunk via `LinkedCertScc.semChunks_of_head`). -/
theorem treeDemoCert_treeSum_sem
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (hchunks : TreeDemoChunksShape cert) :
    ∀ xs m Q X, treeSumSpec treeDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSumName [i64, i64] [i64] xs m Q X := by
  rcases hchunks with ⟨pre, ext1, ext2, hints1, hints2, cbr1, cbr2, hceq⟩
  intro xs m Q X hspec
  dsimp only [LinkedCertScc.sem]
  rw [hceq, tree_semChunks_append]
  have hnot : treeDemoSumName ∉
      (sccChunksFns [Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2
        treeDemoExportBound treeDemoExportBounds cbr2]).map Fn.name := by
    simp only [sccChunksFns, Chunk.fns, List.append_nil, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    decide
  refine LinkedCertScc.semChunks_of_head (f := treeDemoSumFn) hnot xs m Q X ?_
  have hsb : treeReqBudget treeDemoDepthBudget ≤
      budgetBound treeDemoExportBounds treeDemoExportBound treeDemoSumBudgetFn.toFn.name := by
    decide
  exact LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr1 List.mem_cons_self hsb
    (treeSum_budgetSemScc _ _ treeDemoDepthBudget _ (Nat.le_refl _) xs m Q X hspec)

/-- Target-generic semantic bridge for `TreeDemo.treeSize` (second `.recBudgetSCC` chunk). -/
theorem treeDemoCert_treeSize_sem
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (hchunks : TreeDemoChunksShape cert) :
    ∀ xs m Q X, treeSizeSpec treeDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSizeName [i64, i64] [i64] xs m Q X := by
  rcases hchunks with ⟨pre, ext1, ext2, hints1, hints2, cbr1, cbr2, hceq⟩
  intro xs m Q X hspec
  dsimp only [LinkedCertScc.sem]
  have hceq' : cert.chunks =
      (pre ++ [Chunk.recBudgetSCC ext1 [treeDemoSumBudgetFn] hints1
        treeDemoExportBound treeDemoExportBounds cbr1]) ++
      [Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2
        treeDemoExportBound treeDemoExportBounds cbr2] := by
    rw [hceq, List.append_assoc]; rfl
  rw [hceq', tree_semChunks_append]
  dsimp only [semChunks]
  have hsb : treeReqBudget treeDemoDepthBudget ≤
      budgetBound treeDemoExportBounds treeDemoExportBound treeDemoSizeBudgetFn.toFn.name := by
    decide
  exact LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr2 List.mem_cons_self hsb
    (treeSize_budgetSemScc _ _ treeDemoDepthBudget _ (Nat.le_refl _) xs m Q X hspec)

private theorem treeDemoLinkedMod_fns_wf : ∀ f ∈ treeDemoLinkedMod.fns, f.Wf := by
  intro f hf
  simp only [treeDemoLinkedMod, linkLcnfWithRtC0, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact rtC0CoreMod_fns_wf f hrt
  · obtain ⟨tf, _, rfl⟩ := List.mem_map.mp hprog
    exact tf.toFn_wf

private theorem treeDemoSumFn_mem_linked : treeDemoSumFn ∈ treeDemoLinkedMod.fns := by
  simp only [treeDemoLinkedMod, linkLcnfWithRtC0]
  exact List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self)

private theorem treeDemoSizeFn_mem_linked : treeDemoSizeFn ∈ treeDemoLinkedMod.fns := by
  simp only [treeDemoLinkedMod, linkLcnfWithRtC0]
  exact List.mem_append_right _
    (List.mem_map_of_mem (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Target-generic `T.Defined` + `T.FnSpec` bridge for `TreeDemo.treeSum`. -/
theorem treeDemoCert_treeSum_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (has : lt.legalSig [i64, i64] = [i64, i64])
    (hrs : lt.legalSig [i64] = [i64])
    (hsem : ∀ xs m Q X, treeSumSpec treeDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSumName [i64, i64] [i64] xs m Q X) :
    T.Defined cert.host treeDemoSumName ∧
      T.FnSpec cert.host treeDemoSumName (treeSumSpec treeDemoDepthBudget)
        (cert.bound treeDemoSumName) 64 :=
  cert.fnSpec_host_src_of_le treeDemoLinkedMod_fns_wf (f := treeDemoSumFn)
    treeDemoSumFn_mem_linked (treeSumSpec treeDemoDepthBudget) has hrs
    (fun _ _ _ _ _ h => h) hsem

/-- Target-generic `T.Defined` + `T.FnSpec` bridge for `TreeDemo.treeSize`. -/
theorem treeDemoCert_treeSize_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (has : lt.legalSig [i64, i64] = [i64, i64])
    (hrs : lt.legalSig [i64] = [i64])
    (hsem : ∀ xs m Q X, treeSizeSpec treeDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSizeName [i64, i64] [i64] xs m Q X) :
    T.Defined cert.host treeDemoSizeName ∧
      T.FnSpec cert.host treeDemoSizeName (treeSizeSpec treeDemoDepthBudget)
        (cert.bound treeDemoSizeName) 64 :=
  cert.fnSpec_host_src_of_le treeDemoLinkedMod_fns_wf (f := treeDemoSizeFn)
    treeDemoSizeFn_mem_linked (treeSizeSpec treeDemoDepthBudget) has hrs
    (fun _ _ _ _ _ h => h) hsem

/-- Target-generic closed `Eventually` machine-execution bridge for `TreeDemo.treeSum`. -/
theorem treeDemoCert_treeSum_eventually
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxStack maxMem : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (I : TargetInit T maxStack maxMem)
    (has : lt.legalSig [i64, i64] = [i64, i64])
    (hrs : lt.legalSig [i64] = [i64])
    (hargs : (T.toIsa.assignArgs [i64, i64]).isSome = true)
    (hsem : ∀ xs m Q X, treeSumSpec treeDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSumName [i64, i64] [i64] xs m Q X)
    (bsMem : List UInt8) (rt p : BitVec 64) (t : TreeDemo.Tree)
    (hbs : bsMem.length ≤ maxMem)
    (hdep : t.depth ≤ treeDemoDepthBudget) (hsum : TreeDemo.treeSum t < 2 ^ 63)
    (hmem : treeNatAt p t (bsMem.At 0x1000#64))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        T.mach.getGpr (T.mach.data st) I.ret0 = boxNat (TreeDemo.treeSum t))
      (T.mach.mkState
        (I.initState (as := [i64, i64]) (cert.bound treeDemoSumName) bsMem (rt, p, ()))
        (T.mach.labelAddr cert.host treeDemoSumName)) := by
  have hsp : treeSumSpec treeDemoDepthBudget (rt, p, ()) (bsMem.At 0x1000#64)
      (fun r _ => r = (boxNat (TreeDemo.treeSum t), ())) (fun _ _ _ _ => False) :=
    ⟨t, emp, hdep, hsum, by rw [sep_emp]; exact hmem, rfl⟩
  exact cert.eventually_ret1_i64_of_le I treeDemoLinkedMod_fns_wf
    (f := treeDemoSumFn) treeDemoSumFn_mem_linked rfl has hrs
    (treeSumSpec treeDemoDepthBudget) (fun _ _ _ _ _ h => h) hsem bsMem (rt, p, ())
    (boxNat (TreeDemo.treeSum t)) hbs hargs hsp (fun _ _ h => h) hbound

/-- Target-generic closed `Eventually` machine-execution bridge for `TreeDemo.treeSize`. -/
theorem treeDemoCert_treeSize_eventually
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxStack maxMem : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (I : TargetInit T maxStack maxMem)
    (has : lt.legalSig [i64, i64] = [i64, i64])
    (hrs : lt.legalSig [i64] = [i64])
    (hargs : (T.toIsa.assignArgs [i64, i64]).isSome = true)
    (hsem : ∀ xs m Q X, treeSizeSpec treeDemoDepthBudget xs m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSizeName [i64, i64] [i64] xs m Q X)
    (bsMem : List UInt8) (rt p : BitVec 64) (t : TreeDemo.Tree)
    (hbs : bsMem.length ≤ maxMem)
    (hdep : t.depth ≤ treeDemoDepthBudget) (hsz : TreeDemo.treeSize t < 2 ^ 63)
    (hmem : treeNatAt p t (bsMem.At 0x1000#64))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        T.mach.getGpr (T.mach.data st) I.ret0 = boxNat (TreeDemo.treeSize t))
      (T.mach.mkState
        (I.initState (as := [i64, i64]) (cert.bound treeDemoSizeName) bsMem (rt, p, ()))
        (T.mach.labelAddr cert.host treeDemoSizeName)) := by
  have hsp : treeSizeSpec treeDemoDepthBudget (rt, p, ()) (bsMem.At 0x1000#64)
      (fun r _ => r = (boxNat (TreeDemo.treeSize t), ())) (fun _ _ _ _ => False) :=
    ⟨t, emp, hdep, hsz, by rw [sep_emp]; exact hmem, rfl⟩
  exact cert.eventually_ret1_i64_of_le I treeDemoLinkedMod_fns_wf
    (f := treeDemoSizeFn) treeDemoSizeFn_mem_linked rfl has hrs
    (treeSizeSpec treeDemoDepthBudget) (fun _ _ _ _ _ h => h) hsem bsMem (rt, p, ())
    (boxNat (TreeDemo.treeSize t)) hbs hargs hsp (fun _ _ h => h) hbound

/-! ## 5. Concrete Asymmetric Binary-Tree Fixture (`128` Bytes @ `0x1000#64`) -/

/-- Non-trivial asymmetric binary tree (`depth = 3`, `treeSum = 65`, `treeSize = 4`):
`node 10 (node 20 leaf (node 5 leaf leaf)) (node 30 leaf leaf)`. -/
@[expose] def sampleTree : TreeDemo.Tree :=
  .node 10 (.node 20 .leaf (.node 5 .leaf .leaf)) (.node 30 .leaf .leaf)

/-- Byte image of one `32`-byte `Tree.node` heap object (`header` + `[v, l, r]`). -/
@[expose] def treeNodeBytes (v l r : BitVec 64) : List UInt8 :=
  bytesOf (t := i8) treeNodeHdrBytes ++ bytes64 [v, l, r]

/-- Concrete `128`-byte heap image of `sampleTree` packed in preorder at:
* `0x1000#64`: `node 10 0x1020#64 0x1060#64`
* `0x1020#64`: `node 20 1#64 0x1040#64`
* `0x1040#64`: `node 5  1#64 1#64`
* `0x1060#64`: `node 30 1#64 1#64` -/
@[expose] def sampleTreeBytes : List UInt8 :=
  treeNodeBytes (boxNat 10) 0x1020#64 0x1060#64 ++
  ((treeNodeBytes (boxNat 20) 1#64 0x1040#64 ++
    treeNodeBytes (boxNat 5) 1#64 1#64) ++
   treeNodeBytes (boxNat 30) 1#64 1#64)

theorem treeNodeBytes_length (v l r : BitVec 64) : (treeNodeBytes v l r).length = 32 := by
  rw [treeNodeBytes, List.length_append, bytes64_length]
  have hHdr : (bytesOf (t := i8) treeNodeHdrBytes).length = 8 := by decide
  rw [hHdr]; simp

theorem sampleTreeBytes_length : sampleTreeBytes.length = 128 := by
  simp [sampleTreeBytes, treeNodeBytes_length]

private theorem tree_sep_append_bytes {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs : (Eq (bs1.At a) ⋆ Eq (bs2.At (a + BitVec.ofNat 64 bs1.length))) ((bs1 ++ bs2).At a) :=
    (congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)).mp rfl
  exact sep_mono2 (fun _ h => h ▸ hp) (fun _ h => h ▸ (h1 ▸ hq)) _ hs

private theorem treeNodeBytes_ok (p v l r : BitVec 64) :
    treeNodeAt p v l r ((treeNodeBytes v l r).At p) := by
  have hHdr : array (t := i8) p treeNodeHdrBytes ((bytesOf (t := i8) treeNodeHdrBytes).At p) :=
    array_bytes (t := i8) p treeNodeHdrBytes (by decide)
  have hFlds : array64 (p + 8#64) [v, l, r] ((bytes64 [v, l, r]).At (p + 8#64)) :=
    array64_bytes (p + 8#64) [v, l, r] (by simp)
  have hFlds' : (cell64 (p + 8#64) v ⋆ cell64 (p + 16#64) l ⋆ cell64 (p + 24#64) r)
      ((bytes64 [v, l, r]).At (p + 8#64)) := by
    have ha : array64 (p + 8#64) [v, l, r] =
        (cell64 (p + 8#64) v ⋆ cell64 (p + 16#64) l ⋆ cell64 (p + 24#64) r) := by
      simp only [array64_cons, array64_nil, sep_emp]
      have h16 : (p + 8#64) + 8 = p + 16#64 := by bv_omega
      have h24 : (p + 16#64) + 8 = p + 24#64 := by bv_omega
      rw [h16, h24]; ac_rfl
    rwa [← ha]
  have hAll := tree_sep_append_bytes
    (by decide : (bytesOf (t := i8) treeNodeHdrBytes).length = 8)
    (by rw [bytes64_length]; simp : (bytes64 [v, l, r]).length = 24) (by decide) hHdr hFlds'
  exact sep_cast hAll (by unfold treeNodeAt; ac_rfl)

private theorem treeNatAt_leaf_node (p : BitVec 64) (v : Nat) (hp0 : (p &&& 1#64) = 0#64) :
    treeNatAt p (.node v .leaf .leaf) ((treeNodeBytes (boxNat v) 1#64 1#64).At p) := by
  refine ⟨hp0, 1#64, 1#64, ?_⟩
  have heq : (treeNodeAt p (boxNat v) 1#64 1#64 ⋆ treeNatAt 1#64 .leaf ⋆ treeNatAt 1#64 .leaf) =
      treeNodeAt p (boxNat v) 1#64 1#64 := by
    funext m
    exact propext ⟨fun h => by
      obtain ⟨_, h1⟩ := sep_pure_r.mp h
      rw [sep_emp] at h1
      obtain ⟨_, h2⟩ := sep_pure_r.mp h1
      rwa [sep_emp] at h2,
      fun h => sep_pure_r.mpr ⟨rfl, by rw [sep_emp]; exact sep_pure_r.mpr ⟨rfl, by rwa [sep_emp]⟩⟩⟩
  rw [heq]
  exact treeNodeBytes_ok p (boxNat v) 1#64 1#64

/-- Concrete proof that `sampleTreeBytes.At 0x1000#64` realizes `sampleTree`. -/
theorem sampleTree_treeNatAt :
    treeNatAt 0x1000#64 sampleTree (sampleTreeBytes.At 0x1000#64) := by
  have hLen0 := treeNodeBytes_length (boxNat 10) 0x1020#64 0x1060#64
  have hLen1 := treeNodeBytes_length (boxNat 20) 1#64 0x1040#64
  have hLen2 := treeNodeBytes_length (boxNat 5) 1#64 1#64
  have hLen3 := treeNodeBytes_length (boxNat 30) 1#64 1#64
  have hLenL : (treeNodeBytes (boxNat 20) 1#64 0x1040#64 ++
      treeNodeBytes (boxNat 5) 1#64 1#64).length = 64 := by
    rw [List.length_append, hLen1, hLen2]
  have hLenLR : ((treeNodeBytes (boxNat 20) 1#64 0x1040#64 ++
      treeNodeBytes (boxNat 5) 1#64 1#64) ++
      treeNodeBytes (boxNat 30) 1#64 1#64).length = 96 := by
    rw [List.length_append, hLenL, hLen3]
  have hNode5 : treeNatAt 0x1040#64 (.node 5 .leaf .leaf)
      ((treeNodeBytes (boxNat 5) 1#64 1#64).At 0x1040#64) :=
    treeNatAt_leaf_node 0x1040#64 5 (by decide)
  have hNode30 : treeNatAt 0x1060#64 (.node 30 .leaf .leaf)
      ((treeNodeBytes (boxNat 30) 1#64 1#64).At 0x1060#64) :=
    treeNatAt_leaf_node 0x1060#64 30 (by decide)
  have hLeft : treeNatAt 0x1020#64 (.node 20 .leaf (.node 5 .leaf .leaf))
      ((treeNodeBytes (boxNat 20) 1#64 0x1040#64 ++
        treeNodeBytes (boxNat 5) 1#64 1#64).At 0x1020#64) := by
    refine ⟨by decide, 1#64, 0x1040#64, ?_⟩
    have hsep := tree_sep_append_bytes hLen1 hLen2 (by decide)
      (treeNodeBytes_ok 0x1020#64 (boxNat 20) 1#64 0x1040#64) hNode5
    have hswap : (treeNodeAt 0x1020#64 (boxNat 20) 1#64 0x1040#64 ⋆
        treeNatAt 1#64 .leaf ⋆ treeNatAt 0x1040#64 (.node 5 .leaf .leaf)) =
        (treeNodeAt 0x1020#64 (boxNat 20) 1#64 0x1040#64 ⋆
          treeNatAt 0x1040#64 (.node 5 .leaf .leaf)) := by
      funext m
      exact propext ⟨fun h => by
        have h' : ((treeNodeAt 0x1020#64 (boxNat 20) 1#64 0x1040#64 ⋆
            treeNatAt 0x1040#64 (.node 5 .leaf .leaf)) ⋆ treeNatAt 1#64 .leaf) m :=
          sep_cast h (by ac_rfl)
        obtain ⟨_, hm⟩ := sep_pure_r.mp h'; rwa [sep_emp] at hm,
        fun h => by
          have h' : ((treeNodeAt 0x1020#64 (boxNat 20) 1#64 0x1040#64 ⋆
              treeNatAt 0x1040#64 (.node 5 .leaf .leaf)) ⋆ treeNatAt 1#64 .leaf) m :=
            sep_pure_r.mpr ⟨rfl, by rwa [sep_emp]⟩
          exact sep_cast h' (by ac_rfl)⟩
    rw [hswap]
    exact hsep
  have hSubLR := tree_sep_append_bytes hLenL hLen3 (by decide) hLeft hNode30
  refine ⟨by decide, 0x1020#64, 0x1060#64, ?_⟩
  have hRoot := tree_sep_append_bytes hLen0 hLenLR (by decide)
    (treeNodeBytes_ok 0x1000#64 (boxNat 10) 0x1020#64 0x1060#64) hSubLR
  exact sep_cast hRoot (by ac_rfl)

/-- Concrete proof that `([] : List UInt8).At 0x1000#64` realizes `Tree.leaf` at `1#64`. -/
theorem sampleTreeLeaf_treeNatAt :
    treeNatAt 1#64 .leaf (([] : List UInt8).At 0x1000#64) :=
  ⟨rfl, array_bytes (t := i8) 0x1000#64 [] (by decide)⟩

end LeanQbe.T.LeanLCNF

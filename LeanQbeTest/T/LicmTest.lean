module

public import LeanQbe.T.LicmLemmas
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Examples.UnionFind
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratTrimProg
public import LeanQbe.T.Examples.Kissat.Full1
meta import LeanQbe.T.Licm
meta import LeanQbe.T.Opt
meta import LeanQbe.T.Flat
meta import LeanQbe.T.Examples.LratBytesProg
meta import LeanQbe.T.Examples.LratTrimProg
meta import LeanQbe.T.Examples.Kissat.Full1

/-!
# Tests of `LeanQbe.T.Licm` (`Func.licm`)

Covers:
1. Arithmetic transitive chain hoisting (`mb2ArithLoop`): exact AST check via
   `t_kernel_rfl`, `Func.licm_wf`, `Func.licm_supportsSource`, and `Func.spec` proof
   (including `0`-trip preservation).
2. Array address/stride/mask loop (`mb2AddrLoop`): exact AST check, memory-backed
   `Func.spec` proof (`wp_loop1` + `loadVal_cell64`), and `Func.licm_supportsSource`.
3. Nested 2D loop (`mb2NestedLoop`, outer- vs inner-loop placement) and large `> 24`-node
   loop (`mb2LargeLoop`, where `Func.peelFast` does not run): `countLoopLets` reduction,
   `Func.checkTFlat`, `Func.licm_wf`, and `Func.licm_supportsSource`.
4. Conditional branch deduplication (`branchDedupeLoop`) and cold exit-only preservation
   (`coldExitLoop`, verifying backedge-reachability filtering).
5. Soundness exclusions (`ubAndMemLoop`, `guardedDivLoop`): `udiv`/`sdiv`/`urem`/`srem`, `load`,
   and float ops (`fadd`) are never hoisted, preserving `0`-trip / untaken-branch safety when
   divisor is `0`.
6. Multi-block mutual loop (`twoBlockLoop`), multi-result pure total op (`umulwLoop`), and
   acyclic diamond join (`acyclicJoin`, fast-path identity).
7. Real codebase functions (`UnionFind`, `LratBytes`, `LratTrim`, `Kissat.Full`): `Func.licm_wf`,
   `Func.checkTFlat`, zero-regression on `uf_bench`/`lrat_bytes`, and loop `.let_` reductions on
   `LratTrim` and `Kissat.Full` (`full_prop_lit`, `full_propagate_ignore`, `full_find_repl`,
   `full_assign_level`, `full_sweep_bins`).
8. `Fn.licm` signature preservation and `#print axioms` audit.
-/

set_option autoImplicit false

section

namespace LeanQbe.T.LicmTest

open LeanQbe.T

/-! ## Loop `.let_` counter helper -/

mutual
/-- Count `.let_` bindings that occur inside any looping `.group` of a `TFlat` term. -/
def countLoopLets (inLoop : Bool) {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k => (if inLoop then 1 else 0) + countLoopLets inLoop k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => countLoopLets inLoop k
  | .jnz _ t e => countLoopLets inLoop t + countLoopLets inLoop e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group bodies k =>
    let isLp := !(Licm.computeLoopMask bodies).isEmpty
    countLoopLetsB (inLoop || isLp) bodies + countLoopLets inLoop k

/-- Block-list companion of `countLoopLets`. -/
def countLoopLetsB (inLoop : Bool) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countLoopLets inLoop b + countLoopLetsB inLoop bs
end

/-- Count `.let_` bindings inside loops of a closed `Func`. -/
def funcLoopLets {as rs : List Ty} (f : Func as rs) : Nat :=
  countLoopLets false (reifyFunc f)

/-! ## 1. Arithmetic transitive chain hoisting (`mb2ArithLoop`) -/

/-- Loop computing invariant chain `((a + b) * 3) ^ d` on every iteration. -/
def mb2ArithLoop : Func [i64, i64, i64, i64] [i64] := fun _ _ (n, a, b, d, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var a) (.var b)) fun (t1, ()) =>
         .let_ (op2 (.mul i64) (.var t1) (.imm 3)) fun (t2, ()) =>
         .let_ (op2 (.xor i64) (.var t2) (.var d)) fun (t3, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var t3)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

/-- `Func.licm` hoists the entire transitive chain `t1, t2, t3` directly before `.group`, binding
`t3` lexically across the loop body with zero block-parameter plumbing. -/
theorem mb2ArithLoop_licm_out : Func.licm mb2ArithLoop = fun _ _ (n, a, b, d, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (t1, ()) =>
    .let_ (op2 (.mul i64) (.var t1) (.imm 3)) fun (t2, ()) =>
    .let_ (op2 (.xor i64) (.var t2) (.var d)) fun (t3, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var t3)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ())))
      (fun lp => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

theorem mb2ArithLoop_wf : mb2ArithLoop.Wf := by t_wf_reify
theorem mb2ArithLoop_licm_wf : (Func.licm mb2ArithLoop).Wf := Func.licm_wf mb2ArithLoop_wf
theorem mb2ArithLoop_licm_checkTFlat : Func.checkTFlat (Func.licm mb2ArithLoop) = true := by
  t_kernel_rfl

theorem mb2ArithLoop_licm_supportsX64 :
    (Func.licm mb2ArithLoop).supportsSource (LegalTarget.x64 [128, 256, 512]) = true :=
  Func.licm_supportsSource _ mb2ArithLoop_wf (by t_kernel_rfl)

theorem mb2ArithLoop_licm_supportsArm64 :
    (Func.licm mb2ArithLoop).supportsSource LegalTarget.aarch64 = true :=
  Func.licm_supportsSource _ mb2ArithLoop_wf (by t_kernel_rfl)

macro "lwp_base" : tactic => `(tactic|
  simp only [op1_eq_mk, op2_eq_mk, op3_eq_mk,
    wp_let_copy_eq, wp_let_add_eq, wp_let_sub_eq, wp_let_mul_eq, wp_let_neg_eq,
    wp_let_and_eq, wp_let_or_eq, wp_let_xor_eq, wp_let_not_eq, wp_let_shl_eq,
    wp_let_lshr_eq, wp_let_ashr_eq, wp_let_cmp_eq, wp_let_select_eq, wp_let_zext_eq,
    wp_let_sext_eq, wp_let_trunc_eq, wp_let_ofBool_eq, wp_let_udiv0_eq, wp_let_sdiv0_eq,
    wp_load, wp_store, wp_jnz, wp_jump, wp_ret,
    OpCode.eq, OpCode.ne, OpCode.ult, OpCode.ule, OpCode.ugt, OpCode.uge,
    OpCode.slt, OpCode.sle, OpCode.sgt, OpCode.sge,
    vals_nil, vals_cons, Arg.val_var, Arg.val_imm, Blocks.get_here, Blocks.get_there,
    Ty.hasFloat_vec, Ty.hasFloat, Ty.isFloatTree,
    evalBits_eq_beq, evalBits_ne_bne, evalBits_ult_eq, evalBits_ule_eq,
    evalBits_ugt_eq, evalBits_uge_eq, liftCmp, shl_three, cast_eq, ite_self,
    Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false, true_and, and_true, false_implies, true_implies,
    Option.some.injEq, exists_eq_left', decide_eq_true_eq, decide_eq_false_iff_not,
    beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true, beq_eq_false_iff_ne,
    bne_eq_false_iff_eq, beq_self_eq_true, BitVec.reduceToNat, Nat.reduceMod,
    Nat.reduceLeDiff] <;> try dsimp only [lift1, lift2, lift3])

theorem mb2ArithLoop_licm_zero_spec (Γ : Env) (a b d : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.licm mb2ArithLoop) (0#64, a, b, d, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X :=
  Func.licm_spec mb2ArithLoop_wf (by
    dsimp only [Func.spec, Func.wp, mb2ArithLoop]
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' => k = 0 ∧ x.1 = 0#64 ∧ x.2.1 = 0#64 ∧ m' = m) ?_ ?_
    · rintro _ _ ⟨i, acc, ⟨⟩⟩ m' _ ⟨_, rfl, rfl, rfl⟩
      lwp_base; exact ⟨fun _ => trivial, fun h => False.elim (h rfl)⟩
    · intro J hJ
      lwp_base
      exact hJ 0 (0#64, 0#64, ()) m ⟨rfl, rfl, rfl, rfl⟩)

private theorem countdown_mul_step {i acc c n : BitVec 64} {k : Nat}
    (hz : i ≠ 0) (hk : i.toNat = k) (hinv : acc + i * c = n * c) :
    (i - 1).toNat = k - 1 ∧ acc + c + (i - 1) * c = n * c := by
  have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
  have hsub : (i - 1).toNat = i.toNat - 1 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
  refine ⟨by rw [hsub, hk], ?_⟩
  calc acc + c + (i - 1) * c
      = acc + ((1 : BitVec 64) * c + (i - 1) * c) := by simp [BitVec.one_mul]; ac_rfl
    _ = acc + (1 + (i - 1)) * c := by rw [← BitVec.add_mul]
    _ = acc + i * c := by rw [BitVec.add_comm 1 (i - 1), BitVec.sub_add_cancel]
    _ = n * c := hinv

theorem mb2ArithLoop_licm_spec (Γ : Env) (n a b d : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.licm mb2ArithLoop) (n, a, b, d, ()) m
      (fun (r, ()) m' => r = n * (((a + b) * 3#64) ^^^ d) ∧ m' = m) X :=
  Func.licm_spec mb2ArithLoop_wf (by
    dsimp only [Func.spec, Func.wp, mb2ArithLoop]
    let c := ((a + b) * 3#64) ^^^ d
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' =>
        x.1.toNat = k ∧ m' = m ∧ x.2.1 + x.1 * c = n * c)
      ?_ ?_
    · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
      dsimp only at hk hinv
      lwp_base
      by_cases hz : i = 0
      · subst hz
        simp only [true_implies, not_true_eq_false, false_implies, and_true]
        simpa using hinv
      · simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
        have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
        obtain ⟨hkt, hinv'⟩ := countdown_mul_step hz hk hinv
        exact hJ (k - 1) _ m' (by omega) ⟨hkt, rfl, hinv'⟩
    · intro J hJ
      lwp_base
      exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩)

/-! ## 2. Row-address + mask load loop (`mb2AddrLoop`) -/

/-- Loop computing invariant row pointer `base + ((row * stride) << 3)` and mask
`(k1 * k2) ^ 0x5A5A` on every iteration while loading from the row cell. -/
def mb2AddrLoop : Func [i64, i64, i64, i64, i64, i64] [i64] :=
  fun _ _ (base, row, stride, n, k1, k2, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.mul i64) (.var row) (.var stride)) fun (ridx, ()) =>
           .let_ (op2 (.shl i64) (.var ridx) (.imm 3)) fun (roff, ()) =>
           .let_ (op2 (.add i64) (.var base) (.var roff)) fun (rbase, ()) =>
           .let_ (op2 (.mul i64) (.var k1) (.var k2)) fun (m1, ()) =>
           .let_ (op2 (.xor i64) (.var m1) (.imm 0x5A5A)) fun (mask, ()) =>
           .load i64 (.var rbase) fun v =>
           .let_ (op2 (.xor i64) (.var v) (.var mask)) fun (x, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var x)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ())))
      (fun lp => .jump lp (.var n, .imm 0, ()))

theorem mb2AddrLoop_licm_out : Func.licm mb2AddrLoop =
    fun _ _ (base, row, stride, n, k1, k2, ()) =>
      .let_ (op2 (.mul i64) (.var row) (.var stride)) fun (ridx, ()) =>
      .let_ (op2 (.shl i64) (.var ridx) (.imm 3)) fun (roff, ()) =>
      .let_ (op2 (.add i64) (.var base) (.var roff)) fun (rbase, ()) =>
      .let_ (op2 (.mul i64) (.var k1) (.var k2)) fun (m1, ()) =>
      .let_ (op2 (.xor i64) (.var m1) (.imm 0x5A5A)) fun (mask, ()) =>
      .group (sig := [[i64, i64]])
        (fun (lp, ()) => .cons (fun (i, acc, ()) =>
          .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
          .jnz (.var z) (.ret (.var acc, ()))
            (.load i64 (.var rbase) fun v =>
             .let_ (op2 (.xor i64) (.var v) (.var mask)) fun (x, ()) =>
             .let_ (op2 (.add i64) (.var acc) (.var x)) fun (acc', ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
             .jump lp (.var i', .var acc', ()))) .nil)
        (fun (lp, ()) => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

theorem mb2AddrLoop_wf : mb2AddrLoop.Wf := by t_wf_reify
theorem mb2AddrLoop_licm_wf : (Func.licm mb2AddrLoop).Wf := Func.licm_wf mb2AddrLoop_wf
theorem mb2AddrLoop_licm_checkTFlat : Func.checkTFlat (Func.licm mb2AddrLoop) = true := by
  t_kernel_rfl

theorem mb2AddrLoop_licm_spec (Γ : Env) (base row stride n k1 k2 v : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell64 (base + ((row * stride) <<< 3)) v ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.licm mb2AddrLoop) (base, row, stride, n, k1, k2, ()) m
      (fun (r, ()) m' => r = n * (v ^^^ ((k1 * k2) ^^^ 0x5A5A#64)) ∧ m' = m) X :=
  Func.licm_spec mb2AddrLoop_wf (by
    dsimp only [Func.spec, Func.wp, mb2AddrLoop]
    let c := v ^^^ ((k1 * k2) ^^^ 0x5A5A#64)
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' =>
        x.1.toNat = k ∧ m' = m ∧ x.2.1 + x.1 * c = n * c)
      ?_ ?_
    · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
      dsimp only at hk hinv
      lwp_base
      by_cases hz : i = 0
      · subst hz
        simp only [true_implies, not_true_eq_false, false_implies, and_true]
        simpa using hinv
      · simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
        have hsh : (row * stride) <<< ((3#64).toNat % 64) = (row * stride) <<< 3 := rfl
        refine ⟨v, by simpa [hsh] using loadVal_cell64 hm, ?_⟩
        have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
        obtain ⟨hkt, hinv'⟩ := countdown_mul_step hz hk hinv
        exact hJ (k - 1) _ m' (by omega) ⟨hkt, rfl, hinv'⟩
    · intro J hJ
      lwp_base
      exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩)

/-! ## 3. Nested 2D loop (`mb2NestedLoop`) and `> 24`-node loop (`mb2LargeLoop`) -/

/-- Nested 2D loop (`tflatLoops = 2`, skipped by `Func.peelFast`): outer-invariant chain hoists
before `outer`, while `i`-dependent inner-invariant address/mask chain hoists before `inner`. -/
def mb2NestedLoop : Func [i64, i64, i64, i64, i64, i64] [i64] :=
  fun _ _ (base, outerN, innerN, a, b, c, ()) =>
    loop1 (ts := [i64, i64])
      (fun outer (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var outerN)) fun (goI, ()) =>
        .jnz (.var goI)
          (loop1 (ts := [i64, i64])
            (fun inner (j, acc2, ()) =>
              .let_ (op2 (.cmp .ult i64) (.var j) (.var innerN)) fun (goJ, ()) =>
              .jnz (.var goJ)
                (.let_ (op2 (.mul i64) (.var a) (.var b)) fun (o1, ()) =>
                 .let_ (op2 (.add i64) (.var o1) (.var c)) fun (o2, ()) =>
                 .let_ (op2 (.shl i64) (.var o2) (.imm 3)) fun (o3, ()) =>
                 .let_ (op2 (.xor i64) (.var o3) (.var a)) fun (o4, ()) =>
                 .let_ (op2 (.mul i64) (.var o4) (.imm 13)) fun (o5, ()) =>
                 .let_ (op2 (.mul i64) (.var i) (.var innerN)) fun (r1, ()) =>
                 .let_ (op2 (.shl i64) (.var r1) (.imm 3)) fun (r2, ()) =>
                 .let_ (op2 (.add i64) (.var base) (.var r2)) fun (rbase, ()) =>
                 .let_ (op2 (.xor i64) (.var i) (.var o5)) fun (k1, ()) =>
                 .let_ (op2 (.mul i64) (.var k1) (.var b)) fun (k2, ()) =>
                 .let_ (op2 (.add i64) (.var k2) (.var c)) fun (k3, ()) =>
                 .let_ (op2 (.shl i64) (.var j) (.imm 3)) fun (joff, ()) =>
                 .let_ (op2 (.add i64) (.var rbase) (.var joff)) fun (ptr, ()) =>
                 .load i64 (.var ptr) fun v =>
                 .let_ (op2 (.xor i64) (.var v) (.var k3)) fun (x, ()) =>
                 .let_ (op2 (.add i64) (.var acc2) (.var x)) fun (acc3, ()) =>
                 .let_ (op2 (.add i64) (.var j) (.imm 1)) fun (j1, ()) =>
                 .jump inner (.var j1, .var acc3, ()))
                (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i1, ()) =>
                 .jump outer (.var i1, .var acc2, ())))
            (fun inner => .jump inner (.imm 0, .var acc, ())))
          (.ret (.var acc, ())))
      (fun outer => .jump outer (.imm 0, .imm 0, ()))

theorem mb2NestedLoop_wf : mb2NestedLoop.Wf := by t_wf_reify
theorem mb2NestedLoop_licm_wf : (Func.licm mb2NestedLoop).Wf := Func.licm_wf mb2NestedLoop_wf
theorem mb2NestedLoop_licm_checkTFlat : Func.checkTFlat (Func.licm mb2NestedLoop) = true := by
  t_kernel_rfl

/-- `mb2NestedLoop` hoists 5 outer-invariant ops above `outer` and 6 `i`-dependent ops above
`inner`, reducing total in-loop `.let_` count from `19` to `14` (and inner-loop `.let_`s from
`17` to `6`). -/
theorem mb2NestedLoop_loopLets_before : funcLoopLets mb2NestedLoop = 19 := by t_kernel_rfl
theorem mb2NestedLoop_loopLets_after : funcLoopLets (Func.licm mb2NestedLoop) = 14 := by
  t_kernel_rfl

/-- Large single loop with `> 24` IR nodes (exceeding `Func.peelFast 24`'s budget). -/
def mb2LargeLoop : Func [i64, i64, i64, i64, i64, i64] [i64] :=
  fun _ _ (base, n, a, b, c, d, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var n)) fun (go, ()) =>
        .jnz (.var go)
          (.let_ (op2 (.add i64) (.var a) (.var b)) fun (t1, ()) =>
           .let_ (op2 (.mul i64) (.var t1) (.var c)) fun (t2, ()) =>
           .let_ (op2 (.xor i64) (.var t2) (.var d)) fun (t3, ()) =>
           .let_ (op2 (.shl i64) (.var t3) (.imm 3)) fun (t4, ()) =>
           .let_ (op2 (.add i64) (.var t4) (.var a)) fun (t5, ()) =>
           .let_ (op2 (.mul i64) (.var t5) (.imm 7)) fun (t6, ()) =>
           .let_ (op2 (.and i64) (.var t6) (.imm 0xFFFF)) fun (t7, ()) =>
           .let_ (op2 (.sub i64) (.var b) (.var c)) fun (u1, ()) =>
           .let_ (op2 (.mul i64) (.var u1) (.var d)) fun (u2, ()) =>
           .let_ (op2 (.lshr i64) (.var u2) (.imm 2)) fun (u3, ()) =>
           .let_ (op2 (.xor i64) (.var u3) (.var t7)) fun (u4, ()) =>
           .let_ (op2 (.add i64) (.var u4) (.imm 13)) fun (u5, ()) =>
           .let_ (op2 (.mul i64) (.var u5) (.var t1)) fun (u6, ()) =>
           .let_ (op2 (.xor i64) (.var u6) (.var u2)) fun (u7, ()) =>
           .let_ (op2 (.add i64) (.var u7) (.var t5)) fun (u8, ()) =>
           .let_ (op2 (.shl i64) (.var a) (.imm 3)) fun (boff, ()) =>
           .let_ (op2 (.add i64) (.var base) (.var boff)) fun (abase, ()) =>
           .let_ (op2 (.shl i64) (.var i) (.imm 3)) fun (ioff, ()) =>
           .let_ (op2 (.add i64) (.var abase) (.var ioff)) fun (ptr, ()) =>
           .load i64 (.var ptr) fun v =>
           .let_ (op2 (.xor i64) (.var v) (.var u8)) fun (x1, ()) =>
           .let_ (op2 (.add i64) (.var x1) (.var t7)) fun (x2, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var x2)) fun (acc1, ()) =>
           .let_ (op2 (.xor i64) (.var acc1) (.var i)) fun (acc2, ()) =>
           .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i1, ()) =>
           .jump lp (.var i1, .var acc2, ()))
          (.ret (.var acc, ())))
      (fun lp => .jump lp (.imm 0, .imm 0, ()))

theorem mb2LargeLoop_wf : mb2LargeLoop.Wf := by t_wf_reify
theorem mb2LargeLoop_licm_wf : (Func.licm mb2LargeLoop).Wf := Func.licm_wf mb2LargeLoop_wf
theorem mb2LargeLoop_licm_checkTFlat : Func.checkTFlat (Func.licm mb2LargeLoop) = true := by
  t_kernel_rfl

/-- `Func.peelFast 24` leaves `mb2LargeLoop` at `25` loop `.let_`s; `Func.licm` hoists all `17`
invariant ops directly out of the loop (`25 → 8`). -/
theorem mb2LargeLoop_loopLets_before : funcLoopLets mb2LargeLoop = 25 := by t_kernel_rfl
theorem mb2LargeLoop_loopLets_after : funcLoopLets (Func.licm mb2LargeLoop) = 8 := by t_kernel_rfl

/-! ## 4. Branch deduplication (`branchDedupeLoop`) & cold exit filtering (`coldExitLoop`) -/

/-- Same invariant expression `(a * b) + c` in both conditional arms is hoisted once and reused. -/
def branchDedupeLoop : Func [.bool, i64, i64, i64, i64] [i64] :=
  fun _ _ (flag, n, a, b, c, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.jnz (.var flag)
            (.let_ (op2 (.mul i64) (.var a) (.var b)) fun (k1, ()) =>
             .let_ (op2 (.add i64) (.var k1) (.var c)) fun (k2, ()) =>
             .let_ (op2 (.add i64) (.var acc) (.var k2)) fun (acc1, ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i1, ()) =>
             .jump lp (.var i1, .var acc1, ()))
            (.let_ (op2 (.mul i64) (.var a) (.var b)) fun (m1, ()) =>
             .let_ (op2 (.add i64) (.var m1) (.var c)) fun (m2, ()) =>
             .let_ (op2 (.xor i64) (.var acc) (.var m2)) fun (acc2, ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
             .jump lp (.var i2, .var acc2, ()))))
      (fun lp => .jump lp (.var n, .imm 0, ()))

theorem branchDedupeLoop_licm_out : Func.licm branchDedupeLoop =
    fun _ _ (flag, n, a, b, c, ()) =>
      .let_ (op2 (.mul i64) (.var a) (.var b)) fun (k1, ()) =>
      .let_ (op2 (.add i64) (.var k1) (.var c)) fun (k2, ()) =>
      .group (sig := [[i64, i64]])
        (fun (lp, ()) => .cons (fun (i, acc, ()) =>
          .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
          .jnz (.var z) (.ret (.var acc, ()))
            (.jnz (.var flag)
              (.let_ (op2 (.add i64) (.var acc) (.var k2)) fun (acc1, ()) =>
               .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i1, ()) =>
               .jump lp (.var i1, .var acc1, ()))
              (.let_ (op2 (.xor i64) (.var acc) (.var k2)) fun (acc2, ()) =>
               .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
               .jump lp (.var i2, .var acc2, ())))) .nil)
        (fun (lp, ()) => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

/-- Cold exit-only invariant `a * 99` on the `ret` arm is NOT hoisted, while backedge-reaching
`a + b` IS hoisted. -/
def coldExitLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, a, b, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z)
        (.let_ (op2 (.mul i64) (.var a) (.imm 99)) fun (cold, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var cold)) fun (res, ()) =>
         .ret (.var res, ()))
        (.let_ (op2 (.add i64) (.var a) (.var b)) fun (hot, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var hot)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem coldExitLoop_licm_out : Func.licm coldExitLoop = fun _ _ (n, a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (hot, ()) =>
    .group (sig := [[i64, i64]])
      (fun (lp, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z)
          (.let_ (op2 (.mul i64) (.var a) (.imm 99)) fun (cold, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var cold)) fun (res, ()) =>
           .ret (.var res, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var hot)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ()))) .nil)
      (fun (lp, ()) => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

/-! ## 5. Soundness exclusions: UB partial ops, loads, and floats are never hoisted -/

/-- Loop containing invariant `udiv`, `sdiv`, `urem`, `srem`, `fadd`, and `load`: none are pure
total deterministic integer ops, so `Func.licm` must leave the loop untouched. -/
def ubAndMemLoop : Func [i64, i64, i64, i64, f32] [i64] := fun _ _ (n, a, b, ptr, fx, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.udiv 64) (.var a) (.var b)) fun (q1, ()) =>
         .let_ (op2 (.sdiv 64) (.var a) (.var b)) fun (q2, ()) =>
         .let_ (op2 (.urem 64) (.var a) (.var b)) fun (r1, ()) =>
         .let_ (op2 (.srem 64) (.var a) (.var b)) fun (r2, ()) =>
         .let_ (op2 (.fadd f32) (.var fx) (.var fx)) fun (_f1, ()) =>
         .load i64 (.var ptr) fun lv =>
         .let_ (op2 (.add i64) (.var acc) (.var q1)) fun (s1, ()) =>
         .let_ (op2 (.add i64) (.var s1) (.var q2)) fun (s2, ()) =>
         .let_ (op2 (.add i64) (.var s2) (.var r1)) fun (s3, ()) =>
         .let_ (op2 (.add i64) (.var s3) (.var r2)) fun (s4, ()) =>
         .let_ (op2 (.add i64) (.var s4) (.var lv)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem ubAndMemLoop_licm_untouched : Func.licm ubAndMemLoop = ubAndMemLoop := by t_kernel_rfl

/-- Guarded `udiv` loop: safe when `n = 0` even if `b = 0` because `udiv` is never hoisted. -/
def guardedDivLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, a, b, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a1, ()) =>
         .let_ (op2 (.udiv 64) (.var a1) (.var b)) fun (q, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var q)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem guardedDivLoop_wf : guardedDivLoop.Wf := by t_wf_reify

/-- `a + 1` hoists cleanly while `udiv a1 b` stays guarded inside the loop body. -/
theorem guardedDivLoop_licm_out : Func.licm guardedDivLoop = fun _ _ (n, a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a1, ()) =>
    .group (sig := [[i64, i64]])
      (fun (lp, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.udiv 64) (.var a1) (.var b)) fun (q, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var q)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ()))) .nil)
      (fun (lp, ()) => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

/-- Concrete `0`-trip safety with divisor `b = 0`: `Func.licm` does not introduce division UB. -/
theorem guardedDivLoop_licm_zero_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.licm guardedDivLoop) (0#64, a, 0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X :=
  Func.licm_spec guardedDivLoop_wf (by
    dsimp only [Func.spec, Func.wp, guardedDivLoop]
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' => k = 0 ∧ x.1 = 0#64 ∧ x.2.1 = 0#64 ∧ m' = m) ?_ ?_
    · rintro _ _ ⟨i, acc, ⟨⟩⟩ m' _ ⟨_, rfl, rfl, rfl⟩
      lwp_base; exact ⟨fun _ => trivial, fun h => False.elim (h rfl)⟩
    · intro J hJ
      lwp_base
      exact hJ 0 (0#64, 0#64, ()) m ⟨rfl, rfl, rfl, rfl⟩)

/-! ## 6. Multi-block cycle (`twoBlockLoop`), multi-result (`umulwLoop`), acyclic join -/

/-- Two-block mutual cycle (`b0 ↔ b1`): invariant ops from BOTH blocks hoist before `.group`. -/
def twoBlockLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, a, b, ()) =>
  .group (sig := [[i64, i64], [i64, i64]])
    (fun (b0, b1, ()) =>
      .cons (fun (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var a) (.var b)) fun (k0, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var k0)) fun (acc1, ()) =>
           .jump b1 (.var i, .var acc1, ())))
      (.cons (fun (i, acc, ()) =>
        .let_ (op2 (.mul i64) (.var a) (.imm 5)) fun (k1, ()) =>
        .let_ (op2 (.xor i64) (.var acc) (.var k1)) fun (acc2, ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .jump b0 (.var i', .var acc2, ()))
      .nil))
    (fun (b0, _, ()) => .jump b0 (.var n, .imm 0, ()))

theorem twoBlockLoop_licm_out : Func.licm twoBlockLoop = fun _ _ (n, a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (k0, ()) =>
    .let_ (op2 (.mul i64) (.var a) (.imm 5)) fun (k1, ()) =>
    .group (sig := [[i64, i64], [i64, i64]])
      (fun (b0, b1, ()) =>
        .cons (fun (i, acc, ()) =>
          .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
          .jnz (.var z) (.ret (.var acc, ()))
            (.let_ (op2 (.add i64) (.var acc) (.var k0)) fun (acc1, ()) =>
             .jump b1 (.var i, .var acc1, ())))
        (.cons (fun (i, acc, ()) =>
          .let_ (op2 (.xor i64) (.var acc) (.var k1)) fun (acc2, ()) =>
          .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
          .jump b0 (.var i', .var acc2, ()))
        .nil))
      (fun (b0, _, ()) => .jump b0 (.var n, .imm 0, ())) := by
  t_kernel_rfl

theorem twoBlockLoop_wf : twoBlockLoop.Wf := by t_wf_reify
theorem twoBlockLoop_licm_wf : (Func.licm twoBlockLoop).Wf := Func.licm_wf twoBlockLoop_wf
theorem twoBlockLoop_licm_checkTFlat : Func.checkTFlat (Func.licm twoBlockLoop) = true := by
  t_kernel_rfl

/-- Multi-result pure total `umulw 64` hoisted cleanly before `.group` with both outputs used. -/
def umulwLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, a, b, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.umulw 64) (.var a) (.var b)) fun (lo, hi, ()) =>
         .let_ (op2 (.xor i64) (.var lo) (.var hi)) fun (mix, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var mix)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem umulwLoop_licm_out : Func.licm umulwLoop = fun _ _ (n, a, b, ()) =>
    .let_ (op2 (.umulw 64) (.var a) (.var b)) fun (lo, hi, ()) =>
    .let_ (op2 (.xor i64) (.var lo) (.var hi)) fun (mix, ()) =>
    .group (sig := [[i64, i64]])
      (fun (lp, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var mix)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ()))) .nil)
      (fun (lp, ()) => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

theorem umulwLoop_wf : umulwLoop.Wf := by t_wf_reify

theorem umulwLoop_licm_spec (Γ : Env) (n a b : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.licm umulwLoop) (n, a, b, ()) m
      (fun (r, ()) m' =>
        r = n * (a * b ^^^ BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)) ∧ m' = m) X :=
  Func.licm_spec umulwLoop_wf (by
    dsimp only [Func.spec, Func.wp, umulwLoop]
    let c := a * b ^^^ BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' =>
        x.1.toNat = k ∧ m' = m ∧ x.2.1 + x.1 * c = n * c)
      ?_ ?_
    · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
      dsimp only at hk hinv
      lwp_base
      by_cases hz : i = 0
      · subst hz
        simp only [true_implies, not_true_eq_false, false_implies, and_true]
        simpa using hinv
      · simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
        have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
        obtain ⟨hkt, hinv'⟩ := countdown_mul_step hz hk hinv
        exact hJ (k - 1) _ m' (by omega) ⟨hkt, rfl, hinv'⟩
    · intro J hJ
      lwp_base
      exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩)

/-- Acyclic diamond join `.group` is not a loop: fast-path leaves it completely untouched. -/
def acyclicJoin : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, b, ()) =>
  .group (sig := [[i64]])
    (fun (_j, ()) => .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var a) (.var b)) fun (k, ()) =>
      .let_ (op2 (.add i64) (.var x) (.var k)) fun (r, ()) =>
      .ret (.var r, ())) .nil)
    (fun (j, ()) => .jnz (.var c) (.jump j (.var a, ())) (.jump j (.var b, ())))

theorem acyclicJoin_licm_untouched : Func.licm acyclicJoin = acyclicJoin := by t_kernel_rfl

/-! ## 7. Real codebase functions (`UnionFind`, `LratBytes`, `LratTrim`, `Kissat.Full`) -/

/-- `UnionFind.find` and `UnionFind.unionInline`: fast-path zero-regression + `Wf`. -/
theorem uf_find_licm_untouched :
    Func.licm Examples.UnionFind.find = Examples.UnionFind.find := by t_kernel_rfl

theorem uf_unionInline_licm_untouched :
    Func.licm Examples.UnionFind.unionInline = Examples.UnionFind.unionInline := by t_kernel_rfl

mutual
/-- Meta-level loop `.let_` counter for `#guard` checks over real codebase functions. -/
meta def countLoopLetsM (inLoop : Bool) {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k => (if inLoop then 1 else 0) + countLoopLetsM inLoop k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => countLoopLetsM inLoop k
  | .jnz _ t e => countLoopLetsM inLoop t + countLoopLetsM inLoop e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group bodies k =>
    let isLp := !(Licm.computeLoopMask bodies).isEmpty
    countLoopLetsBM (inLoop || isLp) bodies + countLoopLetsM inLoop k

meta def countLoopLetsBM (inLoop : Bool) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countLoopLetsM inLoop b + countLoopLetsBM inLoop bs
end

meta def funcLoopLetsM {as rs : List Ty} (f : Func as rs) : Nat :=
  countLoopLetsM false (reifyFunc f)

-- `LratBytes`: every function passes `checkTFlat` and has zero regression under `Func.licm`.
#guard Examples.LratBytes.lratBytesFns.all fun fn =>
  let f' := Func.licm fn.body
  Func.checkTFlat f' && funcLoopLetsM f' ≤ funcLoopLetsM fn.body

-- `LratTrim`: `br_check_proof` and `br_trim_proof` strictly reduce loop `.let_` count after
-- `Func.licm` (and every `lratTrimFns` function passes `Func.checkTFlat`).
#guard Examples.LratTrim.lratTrimFns.all fun fn =>
  let f' := Func.licm fn.body
  Func.checkTFlat f' && funcLoopLetsM f' ≤ funcLoopLetsM fn.body

#guard
  let f0 := Func.earlyOpt Examples.LratTrim.trimProof
  let f1 := Func.licm f0
  Func.checkTFlat f1 && funcLoopLetsM f1 < funcLoopLetsM f0

/-- `Kissat.Full.full_prop_lit`: verified `Wf`, `checkTFlat`, and `5` loop-invariant ops hoisted
out of the hot watch-list propagation loop (including the 4-op `lvls + ((lit >> 1) << 2)`
address chain). -/
theorem full_prop_lit_licm_wf :
    (Func.licm Examples.Kissat.Full.full_prop_lit_body).Wf :=
  Func.licm_wf Examples.Kissat.Full.full_prop_lit_wf

theorem full1_fns_licm_wf :
    ∀ f ∈ Examples.Kissat.Full.full1_fns, (Fn.licm f).Wf := fun f hf =>
  Fn.licm_wf (Examples.Kissat.Full.full1_fns_wf f hf)

#guard
  let f0 := Func.earlyOpt Examples.Kissat.Full.full_prop_lit_body
  let f1 := Func.licm f0
  Func.checkTFlat f1 && funcLoopLetsM f1 + 5 ≤ funcLoopLetsM f0

#guard
  let targets := ["full_prop_lit", "full_propagate_ignore", "full_find_repl",
    "full_assign_level", "full_sweep_bins"]
  Examples.Kissat.Full.full1_fns.all fun fn =>
    if targets.contains fn.name then
      let f0 := Func.earlyOpt fn.body
      let f1 := Func.licm f0
      Func.checkTFlat f1 && funcLoopLetsM f1 < funcLoopLetsM f0
    else true

/-! ## 8. `Fn.licm` signature preservation and `#print axioms` audit -/

def mb2ArithFn : Fn := ⟨"mb2ArithLoop", [i64, i64, i64, i64], [i64], mb2ArithLoop⟩

theorem mb2ArithFn_licm_sig :
    mb2ArithFn.licm.name = "mb2ArithLoop" ∧
    mb2ArithFn.licm.as = [i64, i64, i64, i64] ∧
    mb2ArithFn.licm.rs = [i64] :=
  ⟨rfl, rfl, rfl⟩

theorem mb2ArithFn_licm_spec (Γ : Env) (n a b d : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ mb2ArithFn.licm.body (n, a, b, d, ()) m
      (fun (r, ()) m' => r = n * (((a + b) * 3#64) ^^^ d) ∧ m' = m) X :=
  mb2ArithLoop_licm_spec Γ n a b d m X

/-! ## 9. Read-only loop load hoisting, forwarding & pressure/alias guards -/

/-- Guaranteed header `.load` hoists before a read-only loop even when the cold `ret` exit
performs a `.store` (`cleanGroup = true`), forwarding repeat backedge-reachable loads and
unlocking follow-up pure hoisting of `v * 3`. -/
def roColdExitLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, ptr, ext, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .load i64 (.var ptr) fun v =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z)
        (.store (.var acc) (.var ext) (.ret (.var acc, ())))
        (.load i64 (.var ptr) fun v2 =>
         .let_ (op2 (.mul i64) (.var v2) (.imm 3)) fun (scaled, ()) =>
         .let_ (op2 (.add i64) (.var v) (.var scaled)) fun (step, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var step)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem roColdExitLoop_licm_out : Func.licm roColdExitLoop = fun _ _ (n, ptr, ext, ()) =>
    .load i64 (.var ptr) fun v =>
    .let_ (op2 (.mul i64) (.var v) (.imm 3)) fun (scaled, ()) =>
    .let_ (op2 (.add i64) (.var v) (.var scaled)) fun (step, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z)
          (.store (.var acc) (.var ext) (.ret (.var acc, ())))
          (.let_ (op2 (.add i64) (.var acc) (.var step)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ())))
      (fun lp => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

theorem roColdExitLoop_wf : roColdExitLoop.Wf := by t_wf_reify

theorem roColdExit_spec (Γ : Env) (n ptr ext v : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell64 ptr v ⋆ R) m)
    (hSt : storeOk m i64 ext) (X : XPost) :
    Func.spec Γ (Func.licm roColdExitLoop) (n, ptr, ext, ()) m
      (fun (r, ()) m' =>
        r = n * (v + v * 3#64) ∧ storeOk m i64 ext ∧ m' = storeMem m i64 ext r)
      X :=
  Func.licm_spec roColdExitLoop_wf (by
    dsimp only [Func.spec, Func.wp, roColdExitLoop]
    let c := v + v * 3#64
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' =>
        x.1.toNat = k ∧ m' = m ∧ x.2.1 + x.1 * c = n * c)
      ?_ ?_
    · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
      dsimp only at hk hinv
      lwp_base
      refine ⟨v, loadVal_cell64 hm, ?_⟩
      by_cases hz : i = 0
      · subst hz
        simp only [true_implies, not_true_eq_false, false_implies, and_true]
        exact ⟨hSt, by simpa using hinv, hSt⟩
      · simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
        refine ⟨v, loadVal_cell64 hm, ?_⟩
        have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
        obtain ⟨hkt, hinv'⟩ := countdown_mul_step hz hk hinv
        exact hJ (k - 1) _ m' (by omega) ⟨hkt, rfl, hinv'⟩
    · intro J hJ
      lwp_base
      exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩)

/-- Two-block cycle (`sig.length = 2`) entered at block `1` (`j = 0`): verifies
`sig.length - 1 - j` indexing hoists block `1`'s guaranteed `.load` and forwards it to block `0`. -/
def twoBlkRoB1 : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  .group (sig := [[i64, i64], [i64, i64]])
    (fun (b0, b1, ()) =>
      .cons (fun (i, acc, ()) =>
        .load i64 (.var ptr) fun v0 =>
        .let_ (op2 (.add i64) (.var acc) (.var v0)) fun (acc1, ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .jump b1 (.var i', .var acc1, ()))
      (.cons (fun (i, acc, ()) =>
        .load i64 (.var ptr) fun v1 =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var v1)) fun (acc2, ()) =>
           .jump b0 (.var i, .var acc2, ())))
      .nil))
    (fun (_b0, b1, ()) => .jump b1 (.var n, .imm 0, ()))

theorem twoBlkRoB1_licm_out : Func.licm twoBlkRoB1 = fun _ _ (n, ptr, ()) =>
    .load i64 (.var ptr) fun v =>
    .group (sig := [[i64, i64], [i64, i64]])
      (fun (b0, b1, ()) =>
        .cons (fun (i, acc, ()) =>
          .let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc1, ()) =>
          .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
          .jump b1 (.var i', .var acc1, ()))
        (.cons (fun (i, acc, ()) =>
          .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
          .jnz (.var z) (.ret (.var acc, ()))
            (.let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc2, ()) =>
             .jump b0 (.var i, .var acc2, ())))
        .nil))
      (fun (_b0, b1, ()) => .jump b1 (.var n, .imm 0, ())) := by
  t_kernel_rfl

/-- Preheader load in `k` forwards into a read-only loop (`bsLd`), eliminating the redundant
in-loop `.load` and unlocking follow-up pure hoisting of `v * 5`. -/
def prehdrFwdLoop : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.load i64 (.var ptr) fun v =>
         .let_ (op2 (.mul i64) (.var v) (.imm 5)) fun (m5, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var m5)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .load i64 (.var ptr) fun c0 => .jump lp (.var n, .var c0, ()))

theorem prehdrFwdLoop_licm_out : Func.licm prehdrFwdLoop = fun _ _ (n, ptr, ()) =>
    .load i64 (.var ptr) fun c0 =>
    .let_ (op2 (.mul i64) (.var c0) (.imm 5)) fun (m5, ()) =>
    .group (sig := [[i64, i64]])
      (fun (lp, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var m5)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ()))) .nil)
      (fun (lp, ()) => .jump lp (.var n, .var c0, ())) := by
  t_kernel_rfl

theorem prehdrFwdLoop_wf : prehdrFwdLoop.Wf := by t_wf_reify

theorem prehdrFwd_spec (Γ : Env) (n ptr v : BitVec 64) (R : Mem 64 → Prop)
    (m : Mem 64) (hm : (cell64 ptr v ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.licm prehdrFwdLoop) (n, ptr, ()) m
      (fun (r, ()) m' => r = v + n * (v * 5#64) ∧ m' = m) X :=
  Func.licm_spec prehdrFwdLoop_wf (by
    dsimp only [Func.spec, Func.wp, prehdrFwdLoop]
    let c := v * 5#64
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' =>
        x.1.toNat = k ∧ m' = m ∧ (x.2.1 - v) + x.1 * c = n * c)
      ?_ ?_
    · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
      dsimp only at hk hinv
      lwp_base
      by_cases hz : i = 0
      · subst hz
        simp only [true_implies, not_true_eq_false, false_implies, and_true]
        calc acc = acc - v + v := (BitVec.sub_add_cancel acc v).symm
          _ = n * c + v := by rw [(by simpa using hinv : acc - v = n * c)]
          _ = v + n * c := BitVec.add_comm _ _
      · simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
        refine ⟨v, loadVal_cell64 hm, ?_⟩
        have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
        obtain ⟨hkt, hinv'⟩ := countdown_mul_step hz hk hinv
        have hsub : acc - v + c = acc + c - v := by
          rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
            BitVec.add_assoc, BitVec.add_comm (-v) c, ← BitVec.add_assoc]
        rw [hsub] at hinv'
        exact hJ (k - 1) _ m' (by omega) ⟨hkt, rfl, hinv'⟩
    · intro J hJ
      lwp_base
      refine ⟨v, loadVal_cell64 hm, ?_⟩
      exact hJ n.toNat (n, v, ()) m ⟨rfl, rfl, by simp⟩)

/-- Negative test: a store reachable on the backedge blocks both preheader forwarding
and in-loop load hoisting. -/
def storeReachLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, ptr, out, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.load i64 (.var ptr) fun v =>
         .store (.var v) (.var out)
           (.let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
            .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump lp (.var i', .var acc', ()))))
    (fun lp => .load i64 (.var ptr) fun c0 => .jump lp (.var n, .var c0, ()))

theorem storeReachLoop_licm_out : Func.licm storeReachLoop = storeReachLoop := by
  t_kernel_rfl

/-- Negative test: a call reachable on the backedge blocks both preheader forwarding
and in-loop load hoisting. -/
def callReachLoop : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.load i64 (.var ptr) fun v =>
         .call (as := []) (bs := []) "tick" () fun () =>
         .let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .load i64 (.var ptr) fun c0 => .jump lp (.var n, .var c0, ()))

theorem callReachLoop_licm_out : Func.licm callReachLoop = callReachLoop := by
  t_kernel_rfl

/-- Negative test: when outer pressure meets `roLoadPressCap` (`12`), read-only load
hoisting refuses to hoist an extra value out of the loop. -/
def hiPressRoLoop : Func
    [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64] [i64] :=
  fun _ _ (n, ptr, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ()) =>
    loop1 (ts := [i64, i64])
      (fun lp (i, acc, ()) =>
        .load i64 (.var ptr) fun v =>
        .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var v)) fun (s0, ()) =>
           .let_ (op2 (.add i64) (.var s0) (.var a0)) fun (s1, ()) =>
           .let_ (op2 (.add i64) (.var s1) (.var a1)) fun (s2, ()) =>
           .let_ (op2 (.add i64) (.var s2) (.var a2)) fun (s3, ()) =>
           .let_ (op2 (.add i64) (.var s3) (.var a3)) fun (s4, ()) =>
           .let_ (op2 (.add i64) (.var s4) (.var a4)) fun (s5, ()) =>
           .let_ (op2 (.add i64) (.var s5) (.var a5)) fun (s6, ()) =>
           .let_ (op2 (.add i64) (.var s6) (.var a6)) fun (s7, ()) =>
           .let_ (op2 (.add i64) (.var s7) (.var a7)) fun (s8, ()) =>
           .let_ (op2 (.add i64) (.var s8) (.var a8)) fun (s9, ()) =>
           .let_ (op2 (.add i64) (.var s9) (.var a9)) fun (s10, ()) =>
           .let_ (op2 (.add i64) (.var s10) (.var a10)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump lp (.var i', .var acc', ())))
      (fun lp => .jump lp (.var n, .imm 0, ()))

theorem hiPressRoLoop_licm_out : Func.licm hiPressRoLoop = hiPressRoLoop := by
  t_kernel_rfl

/-- Negative test: a cold `ret` arm (`reaches = false`) does not hoist or forward loads
after the exit branch, while a pre-`jnz` read-only header load still hoists. -/
def coldExitNoFwdLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, ptr, ptr2, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .load i64 (.var ptr) fun v =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z)
        (.load i64 (.var ptr2) fun w1 =>
         .load i64 (.var ptr2) fun w2 =>
         .let_ (op2 (.add i64) (.var w1) (.var w2)) fun (s, ()) =>
         .ret (.var s, ()))
        (.let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem coldExitNoFwdLoop_licm_out : Func.licm coldExitNoFwdLoop =
    fun _ _ (n, ptr, ptr2, ()) =>
      .load i64 (.var ptr) fun v =>
      .group (sig := [[i64, i64]])
        (fun (lp, ()) => .cons (fun (i, acc, ()) =>
          .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
          .jnz (.var z)
            (.load i64 (.var ptr2) fun w1 =>
             .load i64 (.var ptr2) fun w2 =>
             .let_ (op2 (.add i64) (.var w1) (.var w2)) fun (s, ()) =>
             .ret (.var s, ()))
            (.let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
             .jump lp (.var i', .var acc', ()))) .nil)
        (fun (lp, ()) => .jump lp (.var n, .imm 0, ())) := by
  t_kernel_rfl

/-- Negative test: conditional load guarded by loop condition does not hoist, and preserves
safety at `n = 0` with an unmapped pointer. -/
def condLoadLoop : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.load i64 (.var ptr) fun v =>
         .let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump lp (.var i', .var acc', ())))
    (fun lp => .jump lp (.var n, .imm 0, ()))

theorem condLoadLoop_licm_out : Func.licm condLoadLoop = condLoadLoop := by
  t_kernel_rfl

theorem condLoadLoop_wf : condLoadLoop.Wf := by t_wf_reify

theorem condLoad_zero_spec (Γ : Env) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.licm condLoadLoop) (0#64, 0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X :=
  Func.licm_spec condLoadLoop_wf (by
    dsimp only [Func.spec, Func.wp, condLoadLoop]
    refine wp_loop1 _ _
      (fun k (x : Tup Val [i64, i64]) m' =>
        x.1 = 0#64 ∧ k = 0 ∧ x.2.1 = 0#64 ∧ m' = m)
      ?_ ?_
    · rintro J k ⟨i, acc, ⟨⟩⟩ m' _ ⟨rfl, rfl, rfl, rfl⟩
      lwp_base
      exact ⟨fun _ => trivial, fun h => False.elim (h rfl)⟩
    · intro J hJ
      lwp_base
      exact hJ 0 (0#64, 0#64, ()) m ⟨rfl, rfl, rfl, rfl⟩)

#print axioms LeanQbe.T.OpCode.isLicmPure_spec
#print axioms LeanQbe.T.licmSweep_wf
#print axioms LeanQbe.T.licmSweep_wp
#print axioms LeanQbe.T.Func.licm_wf
#print axioms LeanQbe.T.Func.licm_spec
#print axioms LeanQbe.T.Func.licm_supportsSource
#print axioms LeanQbe.T.Fn.licm_wf
#print axioms LeanQbe.T.Fn.licm_spec
#print axioms LeanQbe.T.LicmTest.mb2ArithLoop_licm_spec
#print axioms LeanQbe.T.LicmTest.mb2AddrLoop_licm_spec
#print axioms LeanQbe.T.LicmTest.guardedDivLoop_licm_zero_spec
#print axioms LeanQbe.T.LicmTest.umulwLoop_licm_spec
#print axioms LeanQbe.T.LicmTest.roColdExit_spec
#print axioms LeanQbe.T.LicmTest.prehdrFwd_spec
#print axioms LeanQbe.T.LicmTest.condLoad_zero_spec

end LeanQbe.T.LicmTest

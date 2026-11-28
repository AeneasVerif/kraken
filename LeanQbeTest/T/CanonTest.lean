module

import LeanQbe.T.CanonLemmas
import LeanQbe.T.GvnLemmas
import LeanQbe.T.DceLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.Rules
meta import LeanQbe.T.Canon

/-!
# Tests of `LeanQbe.T.Canon` and `FlatLemmas.Func.renorm_spec`

Tests:
1. Commutative canonicalization (`c + x → x + c`, `b + a → a + b`) and CSE after `canon` + `gvn`.
2. Comparison swapping (`5 < x → x > 5`, variable key ordering, `#guard` on `CmpOp.swap`).
3. Associative constant-chain reassociation `(x + 3) + 7 → x + 10`, 64-bit wraparound
   `(x + (2^64 - 3)) + 7 → x + 4`, `mul`/`and`/`or`/`xor`, `.bool`, and nested `.pair` (`v4i32`).
4. Non-reassociation of shifts (`(x <<< 60) <<< 60` kept untouched), mixed ops, and floats.
5. `group` + `jnz` + `load`/`store` preservation, `Func.canon_wf`, `Func.canon_spec`.
6. `Func.renorm_wf` and `Func.renorm_spec` round-trip verification.
7. Axiom audit (`#print axioms`) confirming only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

namespace LeanQbe.T.CanonTest

open LeanQbe.T

/-! ## 1. Unit `#guard` checks on `CmpOp.swap` and `AssocOp.eval` -/

#guard CmpOp.eq.swap == .eq
#guard CmpOp.ne.swap == .ne
#guard CmpOp.slt.swap == .sgt
#guard CmpOp.sgt.swap == .slt
#guard CmpOp.sle.swap == .sge
#guard CmpOp.sge.swap == .sle
#guard CmpOp.ult.swap == .ugt
#guard CmpOp.ugt.swap == .ult
#guard CmpOp.ule.swap == .uge
#guard CmpOp.uge.swap == .ule

#guard AssocOp.add.eval i64 0xfffffffffffffffd#64 7#64 == 4#64
#guard AssocOp.mul.eval i64 3#64 5#64 == 15#64
#guard AssocOp.and.eval i64 0xf0#64 0x3c#64 == 0x30#64
#guard AssocOp.or.eval i64 1#64 4#64 == 5#64
#guard AssocOp.xor.eval i64 0xff#64 0x0f#64 == 0xf0#64
#guard AssocOp.add.eval .bool true true == false
#guard AssocOp.mul.eval .bool true false == false

/-! ## 2. Commutative canonicalization (`a + b` vs `b + a`) + GVN CSE -/

/-- `s1 = a + b; s2 = b + a; c1 = 10 + a; c2 = a + 10; ret (s1 + s2, c1 + c2)` -/
def commCseProg : Func [i64, i64] [i64, i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  .let_ (op2 (.add i64) (.var a) (.var b)) fun s1 =>
  .let_ (op2 (.add i64) (.var b) (.var a)) fun s2 =>
  .let_ (op2 (.add i64) (.imm 10) (.var a)) fun c1 =>
  .let_ (op2 (.add i64) (.var a) (.imm 10)) fun c2 =>
  .let_ (op2 (.add i64) (.var s1.1) (.var s2.1)) fun sum =>
  .let_ (op2 (.add i64) (.var c1.1) (.var c2.1)) fun csum =>
  .ret (.var sum.1, .var csum.1, ())

theorem commCse_canon_out : Func.canon commCseProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    .let_ (op2 (.add i64) (.var a) (.var b)) fun s1 =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun s2 =>
    .let_ (op2 (.add i64) (.var a) (.imm 10)) fun c1 =>
    .let_ (op2 (.add i64) (.var a) (.imm 10)) fun c2 =>
    .let_ (op2 (.add i64) (.var s1.1) (.var s2.1)) fun sum =>
    .let_ (op2 (.add i64) (.var c1.1) (.var c2.1)) fun csum =>
    .ret (.var sum.1, .var csum.1, ()) := by
  t_kernel_rfl

/-- Running `gvn` after `canon` merges both `b + a` and `a + 10` duplicates. -/
theorem commCse_canonGvn_out : Func.gvn (Func.canon commCseProg) = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    .let_ (op2 (.add i64) (.var a) (.var b)) fun s1 =>
    .let_ (op2 (.add i64) (.var a) (.imm 10)) fun c1 =>
    .let_ (op2 (.add i64) (.var s1.1) (.var s1.1)) fun sum =>
    .let_ (op2 (.add i64) (.var c1.1) (.var c1.1)) fun csum =>
    .ret (.var sum.1, .var csum.1, ()) := by
  t_kernel_rfl

theorem commCseProg_wf : commCseProg.Wf := by t_wf_reify

theorem commCse_canon_wf : (Func.canon commCseProg).Wf := Func.canon_wf commCseProg_wf

theorem commCse_canonGvn_spec (Γ : Env) (a b : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.gvn (Func.canon commCseProg)) (a, b, ()) m
      (fun (r0, r1, ()) m' => r0 = (a + b) + (a + b) ∧ r1 = (a + 10) + (a + 10) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.gvn_spec (Func.canon_wf commCseProg_wf)
  apply Func.canon_spec commCseProg_wf
  dsimp only [Func.spec, Func.wp, commCseProg]
  wp_unfold_all
  simp [BitVec.add_comm]

/-! ## 3. Comparison swapping (`5 < x → x > 5`, variable key ordering) -/

def cmpSwapProg : Func [i64, i64] [.bool, .bool, .bool, .bool] := fun _ _ p =>
  let x := p.1
  let y := p.2.1
  .let_ (op2 (.slt i64) (.imm 5) (.var x)) fun c1 =>
  .let_ (op2 (.ule i64) (.imm 9) (.var y)) fun c2 =>
  .let_ (op2 (.ult i64) (.var y) (.var x)) fun c3 =>
  .let_ (op2 (.eq i64) (.var y) (.var x)) fun c4 =>
  .ret (.var c1.1, .var c2.1, .var c3.1, .var c4.1, ())

theorem cmpSwap_canon_out : Func.canon cmpSwapProg = fun _ _ p =>
    let x := p.1
    let y := p.2.1
    .let_ (op2 (.sgt i64) (.var x) (.imm 5)) fun c1 =>
    .let_ (op2 (.uge i64) (.var y) (.imm 9)) fun c2 =>
    .let_ (op2 (.ugt i64) (.var x) (.var y)) fun c3 =>
    .let_ (op2 (.eq i64) (.var x) (.var y)) fun c4 =>
    .ret (.var c1.1, .var c2.1, .var c3.1, .var c4.1, ()) := by
  t_kernel_rfl

theorem cmpSwapProg_wf : cmpSwapProg.Wf := by t_wf_reify

theorem cmpSwap_canon_spec (Γ : Env) (x y : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.canon cmpSwapProg) (x, y, ()) m
      (fun (c1, c2, c3, c4, ()) m' =>
        c1 = (5#64).slt x ∧ c2 = (9#64).ule y ∧ c3 = y.ult x ∧ c4 = decide (x = y) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.canon_spec cmpSwapProg_wf
  dsimp only [Func.spec, Func.wp, cmpSwapProg]
  wp_unfold_all
  by_cases h : x = y
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## 4. Associative constant-chain reassociation + 64-bit wraparound -/

/-- `(x + 3) + 7 → x + 10`, `(x + (2^64 - 3)) + 7 → x + 4`, `3 + (x + 7) → x + 10`,
`(x * 3) * 5 → x * 15`, `(x &&& 0xf0) &&& 0x3c → x &&& 0x30`, and `bool` + `v4i32` chains. -/
def reassocProg : Func [i64, .bool, v4i32] [i64, i64, i64, i64, .bool, v4i32] :=
  fun _ _ p =>
  let x := p.1
  let b := p.2.1
  let v := p.2.2.1
  .let_ (op2 (.add i64) (.var x) (.imm 3)) fun a1 =>
  .let_ (op2 (.add i64) (.var a1.1) (.imm 7)) fun a2 =>
  .let_ (op2 (.add i64) (.var x) (.imm 0xfffffffffffffffd#64)) fun w1 =>
  .let_ (op2 (.add i64) (.imm 7#64) (.var w1.1)) fun w2 =>
  .let_ (op2 (.mul i64) (.imm 3) (.var x)) fun m1 =>
  .let_ (op2 (.mul i64) (.var m1.1) (.imm 5)) fun m2 =>
  .let_ (op2 (.and i64) (.var x) (.imm 0xf0)) fun n1 =>
  .let_ (op2 (.and i64) (.var n1.1) (.imm 0x3c)) fun n2 =>
  .let_ (op2 (.xor .bool) (.var b) (.imm true)) fun bx1 =>
  .let_ (op2 (.xor .bool) (.imm true) (.var bx1.1)) fun bx2 =>
  .let_ (op2 (.add v4i32) (.var v) (.imm ((1#32, 2#32), (3#32, 4#32)))) fun v1 =>
  .let_ (op2 (.add v4i32) (.var v1.1) (.imm ((10#32, 20#32), (30#32, 40#32)))) fun v2 =>
  .ret (.var a2.1, .var w2.1, .var m2.1, .var n2.1, .var bx2.1, .var v2.1, ())

theorem reassoc_canon_out : Func.canon reassocProg = fun _ _ p =>
    let x := p.1
    let b := p.2.1
    let v := p.2.2.1
    .let_ (op2 (.add i64) (.var x) (.imm 3)) fun _a1 =>
    .let_ (op2 (.add i64) (.var x) (.imm 10)) fun a2 =>
    .let_ (op2 (.add i64) (.var x) (.imm 0xfffffffffffffffd#64)) fun _w1 =>
    .let_ (op2 (.add i64) (.var x) (.imm 4)) fun w2 =>
    .let_ (op2 (.mul i64) (.var x) (.imm 3)) fun _m1 =>
    .let_ (op2 (.mul i64) (.var x) (.imm 15)) fun m2 =>
    .let_ (op2 (.and i64) (.var x) (.imm 0xf0)) fun _n1 =>
    .let_ (op2 (.and i64) (.var x) (.imm 0x30)) fun n2 =>
    .let_ (op2 (.xor .bool) (.var b) (.imm true)) fun _bx1 =>
    .let_ (op2 (.xor .bool) (.var b) (.imm false)) fun bx2 =>
    .let_ (op2 (.add v4i32) (.var v) (.imm ((1#32, 2#32), (3#32, 4#32)))) fun _v1 =>
    .let_ (op2 (.add v4i32) (.var v) (.imm ((11#32, 22#32), (33#32, 44#32)))) fun v2 =>
    .ret (.var a2.1, .var w2.1, .var m2.1, .var n2.1, .var bx2.1, .var v2.1, ()) := by
  have h0 : Func.canon reassocProg = fun _ _ p =>
      let x := p.1
      let b := p.2.1
      let v := p.2.2.1
      .let_ (op2 (.add i64) (.var x) (.imm 3)) fun _a1 =>
      .let_ (op2 (.add i64) (.var x) (.imm 10)) fun a2 =>
      .let_ (op2 (.add i64) (.var x) (.imm 0xfffffffffffffffd#64)) fun _w1 =>
      .let_ (op2 (.add i64) (.var x) (.imm 4)) fun w2 =>
      .let_ (op2 (.mul i64) (.var x) (.imm 3)) fun _m1 =>
      .let_ (op2 (.mul i64) (.var x) (.imm 15)) fun m2 =>
      .let_ (op2 (.and i64) (.var x) (.imm 0xf0)) fun _n1 =>
      .let_ (op2 (.and i64) (.var x) (.imm (0xf0#64 &&& 0x3c#64))) fun n2 =>
      .let_ (op2 (.xor .bool) (.var b) (.imm true)) fun _bx1 =>
      .let_ (op2 (.xor .bool) (.var b) (.imm false)) fun bx2 =>
      .let_ (op2 (.add v4i32) (.var v) (.imm ((1#32, 2#32), (3#32, 4#32)))) fun _v1 =>
      .let_ (op2 (.add v4i32) (.var v) (.imm ((11#32, 22#32), (33#32, 44#32)))) fun v2 =>
      .ret (.var a2.1, .var w2.1, .var m2.1, .var n2.1, .var bx2.1, .var v2.1, ()) := by
    t_kernel_rfl
  rw [show (0xf0#64 &&& 0x3c#64 : BitVec 64) = 0x30 from by t_kernel_rfl] at h0
  exact h0

theorem reassocProg_wf : reassocProg.Wf := by t_wf_reify

theorem reassoc_canon_wf : (Func.canon reassocProg).Wf := Func.canon_wf reassocProg_wf

theorem reassoc_canon_spec (Γ : Env) (x : BitVec 64) (b : Bool) (v : Val v4i32) (m : Mem 64) :
    Func.spec Γ (Func.canon reassocProg) (x, b, v, ()) m
      (fun (r0, r1, r2, r3, rb, _, ()) m' =>
        r0 = x + 10#64 ∧ r1 = x + 4#64 ∧ r2 = x * 15#64 ∧ r3 = x &&& 0x30#64 ∧
        rb = b ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.canon_spec reassocProg_wf
  dsimp only [Func.spec, Func.wp, reassocProg]
  wp_unfold_all
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.add_assoc]; rfl
  · rw [BitVec.add_comm 7#64, BitVec.add_assoc]; rfl
  · rw [BitVec.mul_comm (3 : BitVec 64) x, BitVec.mul_assoc]; rfl
  · rw [BitVec.and_assoc, show ((240 : BitVec 64) &&& 60) = 48#64 from by decide]
  · cases b <;> rfl

/-! ## 5. Shifts and mixed ops must not reassociate; `group`/`jnz` preservation -/

/-- `(x <<< 60) <<< 60` on `i64` evaluates to `0`, NOT `x <<< 56`; `Canon` keeps both shifts.
Also tests that `(x + 3) * 5` is NOT reassociated, and `group`/`jnz` preserves lexical canon. -/
def shiftAndGroupProg : Func [i64, .bool] [i64, i64] := fun _ _ p =>
  let x := p.1
  let c := p.2.1
  .let_ (op2 (.shl i64) (.var x) (.imm 60)) fun s1 =>
  .let_ (op2 (.shl i64) (.var s1.1) (.imm 60)) fun s2 =>
  .let_ (op2 (.add i64) (.imm 3) (.var x)) fun a1 =>
  .let_ (op2 (.mul i64) (.imm 5) (.var a1.1)) fun m1 =>
  .group (sig := [[i64]])
    (fun (_blk, ()) =>
      .cons (fun z =>
        .let_ (op2 (.add i64) (.imm 7) (.var z.1)) fun g1 =>
        .let_ (op2 (.add i64) (.var g1.1) (.imm 2)) fun g2 =>
        .ret (.var s2.1, .var g2.1, ()))
      .nil)
    (fun (blk, ()) =>
      .jnz (.var c) (.jump blk (.var m1.1, ())) (.ret (.var s2.1, .var m1.1, ())))

theorem shiftAndGroup_canon_out : Func.canon shiftAndGroupProg = fun _ _ p =>
    let x := p.1
    let c := p.2.1
    .let_ (op2 (.shl i64) (.var x) (.imm 60)) fun s1 =>
    .let_ (op2 (.shl i64) (.var s1.1) (.imm 60)) fun s2 =>
    .let_ (op2 (.add i64) (.var x) (.imm 3)) fun a1 =>
    .let_ (op2 (.mul i64) (.var a1.1) (.imm 5)) fun m1 =>
    .group (sig := [[i64]])
      (fun (_blk, ()) =>
        .cons (fun z =>
          .let_ (op2 (.add i64) (.var z.1) (.imm 7)) fun _g1 =>
          .let_ (op2 (.add i64) (.var z.1) (.imm 9)) fun g2 =>
          .ret (.var s2.1, .var g2.1, ()))
        .nil)
      (fun (blk, ()) =>
        .jnz (.var c) (.jump blk (.var m1.1, ())) (.ret (.var s2.1, .var m1.1, ()))) := by
  t_kernel_rfl

theorem shiftAndGroupProg_wf : shiftAndGroupProg.Wf := by t_wf_reify

theorem shiftAndGroup_canon_wf : (Func.canon shiftAndGroupProg).Wf :=
  Func.canon_wf shiftAndGroupProg_wf

/-! ## 6. `Func.renorm_spec` / `Func.renorm_wf` round-trip tests -/

theorem commCse_renorm_wf : (denoteFunc (as := [i64, i64]) (reifyFunc commCseProg)).Wf :=
  Func.renorm_wf commCseProg

theorem commCse_renorm_spec (Γ : Env) (a b : BitVec 64) (m : Mem 64) :
    Func.wp Γ (denoteFunc (as := [i64, i64]) (reifyFunc commCseProg)) (a, b, ()) m
      (fun (r0, r1, ()) m' => r0 = (a + b) + (a + b) ∧ r1 = (a + 10) + (a + 10) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.renorm_spec commCseProg_wf
  dsimp only [Func.wp, commCseProg]
  wp_unfold_all
  simp [BitVec.add_comm]

theorem shiftAndGroup_renorm_spec (Γ : Env) (x : BitVec 64) (c : Bool) (m : Mem 64) :
    Func.wp Γ (denoteFunc (as := [i64, .bool]) (reifyFunc shiftAndGroupProg)) (x, c, ()) m
      (fun (r0, _, ()) m' => r0 = 0#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.renorm_spec shiftAndGroupProg_wf
  dsimp only [Func.wp, shiftAndGroupProg]
  wp_unfold_all
  have hsh : x <<< 60 <<< 60 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
    by_cases h1 : i < 64
    · by_cases h2 : i < 60 <;> simp [h1, h2, show i - 60 < 60 by omega]
    · simp [h1]
  simp only [wp, vals, Arg.val, hsh]
  intro Js hcl
  revert hcl
  wp_unfold_all
  intro hcl
  exact ⟨fun _ => hcl.1 (5 * (3 + x), ()) m (by wp_unfold_all), fun _ => by simp⟩

/-! ## 7. Axiom audit -/

#print axioms LeanQbe.T.denote_wp
#print axioms LeanQbe.T.renorm_wp
#print axioms LeanQbe.T.Func.renorm_wf
#print axioms LeanQbe.T.Func.renorm_spec
#print axioms LeanQbe.T.canon_wp
#print axioms LeanQbe.T.canon_wf
#print axioms LeanQbe.T.Func.canon_wf
#print axioms LeanQbe.T.Func.canon_spec
#print axioms LeanQbe.T.CanonTest.commCse_canon_out
#print axioms LeanQbe.T.CanonTest.commCse_canonGvn_out
#print axioms LeanQbe.T.CanonTest.commCse_canonGvn_spec
#print axioms LeanQbe.T.CanonTest.cmpSwap_canon_out
#print axioms LeanQbe.T.CanonTest.cmpSwap_canon_spec
#print axioms LeanQbe.T.CanonTest.reassoc_canon_out
#print axioms LeanQbe.T.CanonTest.reassoc_canon_spec
#print axioms LeanQbe.T.CanonTest.shiftAndGroup_canon_out
#print axioms LeanQbe.T.CanonTest.commCse_renorm_spec
#print axioms LeanQbe.T.CanonTest.shiftAndGroup_renorm_spec

/-! ## 8. Subtraction constant-chain canonicalization -/

def subChainProg : Func [i64, i64] [i64, i64] :=
  fun _ _ (x, y, ()) =>
  .let_ (op2 (.sub i64) (.var x) (.imm 3#64)) fun (s0, ()) =>
  .let_ (op2 (.sub i64) (.var s0) (.imm 5#64)) fun (r0, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 10#64)) fun (a0, ()) =>
  .let_ (op2 (.sub i64) (.var a0) (.imm 3#64)) fun (r1, ()) =>
  .let_ (op2 (.sub i64) (.var y) (.imm 10#64)) fun (_) =>
  .ret (.var r0, .var r1, ())

theorem subChain_canon_out :
    Func.canon subChainProg = fun _ _ (x, y, ()) =>
      .let_ (op2 (.sub i64) (.var x) (.imm 3#64)) fun (_, ()) =>
      .let_ (op2 (.sub i64) (.var x) (.imm 8#64)) fun (r0, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 10#64)) fun (_, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 7#64)) fun (r1, ()) =>
      .let_ (op2 (.sub i64) (.var y) (.imm 10#64)) fun (_, ()) =>
      .ret (.var r0, .var r1, ()) := by
  have h0 : Func.canon subChainProg = fun _ _ (x, y, ()) =>
      .let_ (op2 (.sub i64) (.var x) (.imm 3#64)) fun (_, ()) =>
      .let_ (op2 (.sub i64) (.var x) (.imm (-((-3#64 : BitVec 64) + (-5#64))))) fun (r0, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 10#64)) fun (_, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm (10#64 + (-3#64 : BitVec 64)))) fun (r1, ()) =>
      .let_ (op2 (.sub i64) (.var y) (.imm 10#64)) fun (_, ()) =>
      .ret (.var r0, .var r1, ()) := by
    t_kernel_rfl
  rw [show (-((-3#64 : BitVec 64) + (-5#64))) = 8#64 from by simp,
    show (10#64 + (-3#64 : BitVec 64)) = 7#64 from by simp] at h0
  exact h0

theorem subChainProg_wf : subChainProg.Wf := by t_wf_reify

theorem subChain_canon_wf : (Func.canon subChainProg).Wf :=
  Func.canon_wf subChainProg_wf

theorem subChain_canon_spec (Γ : Env) (x y : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.canon subChainProg) (x, y, ()) m
      (fun (r0, r1, ()) m' =>
        r0 = (x - 3#64) - 5#64 ∧ r1 = (x + 10#64) - 3#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.canon_spec subChainProg_wf
  dsimp only [Func.spec, Func.wp, subChainProg]
  wp_unfold_all

def subAddBoolProg : Func [i64, .bool] [i64, i64, .bool] :=
  fun _ _ (x, b, ()) =>
  .let_ (op2 (.sub i64) (.var x) (.imm 3#64)) fun (s0, ()) =>
  .let_ (op2 (.add i64) (.var s0) (.imm 10#64)) fun (r0, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 5#64)) fun (a1, ()) =>
  .let_ (op2 (.sub i64) (.imm 20#64) (.var a1)) fun (r1, ()) =>
  .let_ (op2 (.sub .bool) (.var b) (.imm true)) fun (sb, ()) =>
  .let_ (op2 (.sub .bool) (.var sb) (.imm false)) fun (r2, ()) =>
  .ret (.var r0, .var r1, .var r2, ())

theorem subAddBool_canon_out :
    Func.canon subAddBoolProg = fun _ _ (x, b, ()) =>
      .let_ (op2 (.sub i64) (.var x) (.imm 3#64)) fun (_, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 7#64)) fun (r0, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 5#64)) fun (_, ()) =>
      .let_ (op2 (.sub i64) (.imm 15#64) (.var x)) fun (r1, ()) =>
      .let_ (op2 (.sub .bool) (.var b) (.imm true)) fun (_, ()) =>
      .let_ (op2 (.sub .bool) (.var b) (.imm true)) fun (r2, ()) =>
      .ret (.var r0, .var r1, .var r2, ()) := by
  have h0 : Func.canon subAddBoolProg = fun _ _ (x, b, ()) =>
      .let_ (op2 (.sub i64) (.var x) (.imm 3#64)) fun (_, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm ((-3#64 : BitVec 64) + 10#64))) fun (r0, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 5#64)) fun (_, ()) =>
      .let_ (op2 (.sub i64) (.imm (20#64 + (-5#64 : BitVec 64))) (.var x)) fun (r1, ()) =>
      .let_ (op2 (.sub .bool) (.var b) (.imm true)) fun (_, ()) =>
      .let_ (op2 (.sub .bool) (.var b) (.imm true)) fun (r2, ()) =>
      .ret (.var r0, .var r1, .var r2, ()) := by
    t_kernel_rfl
  rw [show ((-3#64 : BitVec 64) + 10#64) = 7#64 from by simp,
    show (20#64 + (-5#64 : BitVec 64)) = 15#64 from by simp] at h0
  exact h0

theorem subAddBoolProg_wf : subAddBoolProg.Wf := by t_wf_reify

theorem subAddBool_canon_wf : (Func.canon subAddBoolProg).Wf :=
  Func.canon_wf subAddBoolProg_wf

theorem subAddBool_canon_spec (Γ : Env) (x : BitVec 64) (b : Bool) (m : Mem 64) :
    Func.spec Γ (Func.canon subAddBoolProg) (x, b, ()) m
      (fun (r0, r1, r2, ()) m' =>
        r0 = (x - 3#64) + 10#64 ∧ r1 = 20#64 - (x + 5#64) ∧
        r2 = (b ^^ true) ^^ false ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.canon_spec subAddBoolProg_wf
  dsimp only [Func.spec, Func.wp, subAddBoolProg]
  wp_unfold_all
  simp

#print axioms LeanQbe.T.CanonTest.subChain_canon_spec
#print axioms LeanQbe.T.CanonTest.subAddBool_canon_spec

end LeanQbe.T.CanonTest

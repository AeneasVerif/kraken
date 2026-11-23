module

public import LeanQbe.T.IfOptLemmas
public import LeanQbe.T.SimplifyGroupPlanLemmas
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas

/-!
# Arbitrary-Position `IfOptBits` & `SimplifyGroupPlan` Tests

Covers:
1. Arbitrary-position nested diamond inside an outer `.jnz` arm after `.load`, targeting an
   enclosing `.group` binder (`tagLabels` + `tryJnzDiamond`).
2. Tail `.ret` diamond converted directly by `Func.ifOptBits` without a `.group`.
3. Negative guard: mismatched arms (`.jump J` vs `.ret`) remain untouched.
4. Kernel output checks (`t_kernel_rfl`), `.checkTFlat`, `.Wf`, `Func.ifOptBits_spec`,
   `Func.ifOptBits_callsOk`, and clean `#print axioms` (`std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.IfOptB5Test

open LeanQbe.T

/-- Nested diamond inside an outer `.jnz` arm after `.load`, targeting a `.group` binder `J`. -/
def nestedTagDiamond : Func [.bool, .bool, i64] [i64] := fun _ _ (c0, c1, ptr, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c0)
        (.load i64 (.var ptr) fun mv =>
         .jnz (.var c1)
           (.let_ (op2 (.add i64) (.var mv) (.imm 1)) fun (t, ()) => .jump J (.var t, ()))
           (.jump J (.var mv, ())))
        (.jump J (.imm 99, ())))

theorem nestedTagDiamond_ifOptBits_out : Func.ifOptBits nestedTagDiamond =
    fun _ _ (c0, c1, ptr, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
      (fun (J, ()) =>
        .jnz (.var c0)
          (.load i64 (.var ptr) fun mv =>
           .let_ (op2 (.add i64) (.var mv) (.imm 1)) fun (t, ()) =>
           .let_ (op3 (.select i64) (.var c1) (.var t) (.var mv)) fun (s, ()) =>
           .jump J (.var s, ()))
          (.jump J (.imm 99, ()))) := by
  t_kernel_rfl

theorem nestedTagDiamond_wf : nestedTagDiamond.Wf := by t_wf_reify

theorem nestedTagDiamond_ifOptBits_wf : (Func.ifOptBits nestedTagDiamond).Wf :=
  Func.ifOptBits_wf nestedTagDiamond_wf

theorem nestedTagDiamond_ifOptBits_checkTFlat :
    (Func.ifOptBits nestedTagDiamond).checkTFlat = true := by
  t_kernel_rfl

theorem nestedTag_callsOk :
    ((Func.ifOptBits nestedTagDiamond) (fun _ => Unit) (fun _ => Unit)
      (Tup.units [.bool, .bool, i64])).callsOk [] [] :=
  Func.ifOptBits_callsOk nestedTagDiamond_wf ⟨⟨trivial, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩

/-- Tail `.ret` diamond converted by `Func.ifOptBits` without needing an enclosing `.group`. -/
def retDiamondProg : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.add i64) (.var x) (.imm 5)) fun (t, ()) => .ret (.var t, ()))
    (.let_ (op2 (.sub i64) (.var x) (.imm 5)) fun (e, ()) => .ret (.var e, ()))

theorem retDiamondProg_ifOptBits_out : Func.ifOptBits retDiamondProg = fun _ _ (c, x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 5)) fun (t, ()) =>
    .let_ (op2 (.sub i64) (.var x) (.imm 5)) fun (e, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var t) (.var e)) fun (s, ()) =>
    .ret (.var s, ()) := by
  t_kernel_rfl

theorem retDiamondProg_wf : retDiamondProg.Wf := by t_wf_reify

theorem retDiamondProg_ifOptBits_spec (Γ : Env) (c : Bool) (x : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.ifOptBits retDiamondProg) (c, x, ()) m
      (fun (r, ()) m' => r = (if c then x + 5#64 else x - 5#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.ifOptBits_spec retDiamondProg_wf
  dsimp only [Func.spec, Func.wp, retDiamondProg, wp, Op.wp, OpCode.wp,
    op2, vals, Arg.val, lift2, i64]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

/-- Mismatched targets (one `.jump J`, one `.ret`) MUST NOT be hoisted by `Func.ifOptBits`. -/
def nestedMixedNotHoisted : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (t, ()) => .jump J (.var t, ()))
        (.ret (.var x, ())))

theorem nestedMixedNotHoisted_unchanged :
    Func.ifOptBits nestedMixedNotHoisted = nestedMixedNotHoisted := by
  t_kernel_rfl

#print axioms LeanQbe.T.Func.ifOptBits_wf
#print axioms LeanQbe.T.Func.ifOptBits_spec
#print axioms LeanQbe.T.Func.ifOptBits_callsOk

end LeanQbeTest.T.IfOptB5Test

private abbrev retDiamondSpec := @LeanQbeTest.T.IfOptB5Test.retDiamondProg_ifOptBits_spec
private abbrev nestedTagCallsOk := @LeanQbeTest.T.IfOptB5Test.nestedTag_callsOk

#print axioms retDiamondSpec
#print axioms nestedTagCallsOk

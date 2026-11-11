module

public import LeanQbe.OptLemmas
public import LeanQbeTest.GvnTest

/-! Test of the mid-end pipeline `Func.opt` (uses `kernel_rfl` from `LeanQbeTest.GvnTest`). -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.OptTest

/-- `x = add 1 2; y = add a x; z = add a 3; ret [y, z]`: folding exposes the common subexpression. -/
def prog : Func := fun _ _ =>
  .param fun a =>
  .let_ (.bin .l .add (.imm 1) (.imm 2)) fun x =>
  .let_ (.bin .l .add (.var a) (.var x)) fun y =>
  .let_ (.bin .l .add (.var a) (.imm 3)) fun z =>
  .ret [.var y, .var z]

theorem opt_prog_out : Func.opt prog = fun _ _ =>
    .param fun a => .let_ (.bin .l .add (.var a) (.imm 3)) fun y => .ret [.var y, .var y] := by
  kernel_rfl

theorem prog_wf : prog.Wf := by wf_tac

theorem opt_prog_wf : (Func.opt prog).Wf := Func.opt_wf prog_wf

end LeanQbe.OptTest

module

public import LeanQbe.FoldLemmas
public import LeanQbe.WPLemmas

/-! Tests of `Func.fold`: the output on a concrete program, by `rfl`, and the closed theorems applied. -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.FoldTest

/-- `x = add 1 2; y = copy.l x; z = add a y; c = cult y 4; jnz c, ret z, ret 0` -/
def prog : Func := fun _ _ =>
  .param fun a =>
  .let_ (.bin .l .add (.imm 1) (.imm 2)) fun x =>
  .let_ (.copy .l (.var x)) fun y =>
  .let_ (.bin .l .add (.var a) (.var y)) fun z =>
  .let_ (.cmp .l .ult (.var y) (.imm 4)) fun c =>
  .jnz (.var c) (.ret [.var z]) (.ret [.imm 0])

/-- Folded: `z = add a 3; ret z`. -/
example : Func.fold prog = fun _ _ => .param fun a => .let_ (.bin .l .add (.var a) (.imm 3)) fun z =>
    .ret [.var z] := rfl

theorem prog_wf : prog.Wf := by wf_tac

theorem fold_prog_wf : (Func.fold prog).Wf := Func.fold_wf prog_wf

/-- A pending label is not folded across (junk shape: `label`, then an instruction). -/
example : Func.fold (fun _ _ => .label fun _ => .let_ (.copy .l (.imm 7)) fun x => .ret [.var x]) =
    fun _ _ => .label fun _ => .let_ (.copy .l (.imm 7)) fun x => .ret [.var x] := rfl

theorem prog_fold_spec (Γ : Env) (a : Val) (m : Mem 64) :
    Func.spec Γ (Func.fold prog) [a] m (fun r m' => r = [a + 3] ∧ m' = m) (fun _ _ _ => False) := by
  apply Func.fold_spec prog_wf
  simp [Func.spec, prog, wp, Op.wp, Op.eval, BinOp.eval, CmpOp.eval, boolVal, Truthy, Arg.val,
    Cls.trunc]

end LeanQbe.FoldTest

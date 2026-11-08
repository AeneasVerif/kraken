module

import Kraken.X64.Concat
import Kraken.X64.Parser

open Kraken.X64.Parser

def incRax : Directive := .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64))))
def jmpFoo : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label "foo") .after_current_instruction))))

example : parse("inc %rax") = [incRax] := rfl
example : parse("jmp foo") = [jmpFoo] := rfl

section
variable (layout : Layout) (labels : Labels) (f : Int64) (hf : labels "foo" = some f) (s : MachineData)

theorem inc_spec :
    Eventually (step1 (layout [incRax]) labels)
      (fun st => st.pc = layout.start + .ofNat (layout.instrSize 0) ∧ st.data.regs.rax = s.regs.rax + 1)
      ⟨s, layout.start⟩ := by
  apply layout.eventually_single
  simp [incRax, Labels.guard, Directive.labels, Operation.labels, RegOrMem.labels, Directive.interp,
    Instr.interp, Operation.interp, Effects.All, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get, Reg64s.set, Reg64s.get64, Reg64s.set64, Reg.base, Reg.offset,
    BitVec.take, BitVec.drop, Kraken.Layout.size]

include hf in
theorem jmp_foo_spec :
    Eventually (step1 (layout [jmpFoo]) labels)
      (fun st => st.pc = f ∧ st.data = s) ⟨s, layout.start⟩ := by
  apply layout.eventually_single
  simp [jmpFoo, Labels.guard, Directive.labels, Operation.labels, RelRegOrMem.labels,
    ConstExpr.labels, Directive.interp, Instr.interp, Operation.interp, Effects.All, Labels.label,
    RelRegOrMem.interp, ConstExpr.interp, Kraken.Layout.size, hf]
  rw [Int64.add_comm, Int64.sub_add_cancel]

def body : Program := [incRax, incRax, jmpFoo]

include hf in
theorem body_spec (hfit : Directives.size (layout body).program < 2 ^ 64) :
    Eventually (step1 (layout body) labels)
      (fun st => st.pc = f ∧ st.data.regs.rax = s.regs.rax + 2) ⟨s, layout.start⟩ := by
  refine layout.eventually_seq (p := [incRax]) (q := [incRax, jmpFoo]) hfit (inc_spec layout labels s) ?_
  rintro ⟨s₁, pc₁⟩ ⟨rfl, _⟩
  refine (layout.after [incRax]).eventually_seq (p := [incRax]) (q := [jmpFoo])
    (layout.size_after_lt hfit) (inc_spec (layout.after [incRax]) labels s₁) ?_
  rintro ⟨s₂, pc₂⟩ ⟨rfl, _⟩
  exact eventually_weaken _ _ _ _ (by grind) (jmp_foo_spec _ labels f hf s₂)

def whole : Program := parse("
main:
  inc %rax
  inc %rax
  jmp foo
  mov $2, %rax
foo:
  nop")

theorem whole_spec (hfit : Directives.size (layout whole).program < 2 ^ 64)
    (hf : Executable.labels (layout whole) "foo" = some f) :
    Eventually (step1 (layout whole)) (fun st => st.pc = f ∧ st.data.regs.rax = s.regs.rax + 2)
      ⟨s, layout.start⟩ := by
  refine layout.eventually_infix_of_sub (q₁ := [.label "main"]) (p := body) (q₂ := whole.drop 4) (.refl _) hfit ?_
  have hbody := body_spec (layout.after [.label "main"]) (Executable.labels (layout whole)) f hf s
    (layout.size_after_lt (layout.size_left_lt (p := ([.label "main"] : Program) ++ body) (q := whole.drop 4) hfit))
  exact Int64.add_zero layout.start ▸ hbody

example : ∃ f, Executable.labels (layout whole) "foo" = some f := by
  dsimp only [CoeFun.coe, Executable.labels, Labels.label?]
  simp [whole, Kraken.Layout.apply]

end

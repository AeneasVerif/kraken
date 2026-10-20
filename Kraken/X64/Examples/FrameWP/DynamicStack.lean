module

/-
`dynamic_stack` in the separation wp: a frame is carved out of a 1024-byte
region below the stack pointer at an offset that depends on two registers, a
value is stored into and loaded back from a slot of that frame, and a value
saved below the entry stack pointer is restored at the end. The precondition
owns the region; the post fixes the three registers.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped Program.FrameWP

set_option experimental.vcgen true


def dynamic_stack : Program := parse("
  movq $99, -8(%rsp)
  movq %rsp, %rbp
  leaq -1024(%rsp, %r9, 8), %rsp
  movq $42, %rax
  movq %rax, 16(%rsp, %r15, 8)
  movq $0, %rax
  movq 16(%rsp, %r15, 8), %rax
  movq %rbp, %rsp
  movq -8(%rsp), %rbx
")

attribute [local grind ←] Lean.Order.le_ofProp MProp.SliceBound.intro MProp.le_mk_of
attribute [local grind =] Int.toBytes_length BitVec.ofInt_ofBytes_toBytes List.length_take List.length_drop

theorem dynamic_stack_correct [Host] (stack : List UInt8) (lstack : stack.length = 1024)
    (rsp₀ : UInt64) :
    ⦃ fun r z f => ⌜r.rsp = rsp₀ ∧ r.r9.toNat + r.r15.toNat < 125⌝
        ⊓ stack.AtM (r.rsp.toBitVec - 1024#64) ⦄
      dynamic_stack
    ⦃ fun _ r z f => ⌜r.rax = 42 ∧ r.rbx = 99 ∧ r.rsp = rsp₀⌝ ⦄ := by
  kvcgen64 [dynamic_stack] with finish

/-! ## The baseline statement

`dynamic_stack_correct` read back as the judgment of the baseline example
`dynamic_stack_example_correct`, over the same program text. -/

theorem dynamic_stack_example_correct [Host] (hp : dynamic_stack.IsInfix Host.prog) (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) (R : Mem 64 → Prop)
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.rax = 42 ∧ s'.data.regs.rbx = 99 ∧ s'.data.regs.rsp = s₀.regs.rsp)
      ⟨s₀, startAddr hp⟩ := by
  apply Program.FrameWP.step1_of_wp hp (List.get_AtM_sep h_mem)
  kvcgen64 [dynamic_stack] with finish

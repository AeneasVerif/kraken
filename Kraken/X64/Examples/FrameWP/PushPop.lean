module

/-
`p6` in the separation wp: `rax` is pushed, overwritten and popped back. The
precondition owns the stack slot below the stack pointer.
-/
import Kraken.SepFrameProc
import Kraken.X64.Parser

open Kraken.X64.Parser
open Kraken
open Std.WP
open Lean.Order
open scoped Program.FrameWP

set_option experimental.vcgen true

attribute [local grind ←] Lean.Order.le_ofProp MProp.SliceBound.intro MProp.le_mk_of
attribute [local grind =] Int.toBytes_length UInt64.toBytes_length BitVec.ofInt_ofBytes_toBytes
  List.length_take List.length_drop BitVec.add_zero

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

theorem p6_spec [Host] (stack : List UInt8) (h_len : stack.length = 8) (a sp : UInt64) :
    ⦃ fun r _ _ => ⌜r.rax = a ∧ r.rsp = sp⌝ ⊓ stack.AtM (r.rsp.toBitVec - 8#64) ⦄
      p6
    ⦃ fun _ r _ _ => ⌜r.rax = a ∧ r.rsp = sp⌝ ⦄ := by
  kvcgen64 [p6] with finish

/-! ## The baseline statement

`p6_spec` read back as the judgment of the baseline example `p6_correct`,
over the same program text. -/

theorem p6_correct [Host] (hp : p6.IsInfix Host.prog) (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.rax = s₀.regs.rax ∧ s'.data.regs.rsp = s₀.regs.rsp)
      ⟨s₀, startAddr hp⟩ := by
  apply Program.FrameWP.step1_of_wp hp (List.get_AtM_sep h_mem)
  kvcgen64 [p6] with finish

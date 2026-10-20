module

/-
`move_2_regs_to_heap` in the separation wp: two registers are stored into two
adjacent slots at `(%rdi)` and `8(%rdi)` and loaded back into two other
registers. The precondition owns both slots, separately: each instruction
touches one, and the other is its frame.
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

def move_2_regs_to_heap : Program := parse("
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
")

theorem move_2_regs_to_heap_spec [Host] (v1 v2 : UInt64) (a c d : UInt64) :
    ⦃ fun r _ _ => ⌜r.rax = a ∧ r.rcx = c ∧ r.rdi = d⌝
        ⊓ (v1.AtM r.rdi.toBitVec ∗ v2.AtM (r.rdi.toBitVec + 8#64)) ⦄
      move_2_regs_to_heap
    ⦃ fun _ r _ _ => ⌜r.r12 = a ∧ r.r13 = c ∧ r.rdi = d⌝ ⦄ := by
  kvcgen64 [move_2_regs_to_heap] with finish

/-! ## The baseline statement

`move_2_regs_to_heap_spec` read back as the judgment of the baseline example
`move_2_regs_to_heap_correct`, over the same program text. -/

theorem move_2_regs_to_heap_correct [Host] (hp : move_2_regs_to_heap.IsInfix Host.prog) (s₀ : MachineData)
  (v1 v2 : UInt64)
  (R : DataMem → Prop)
  (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R)
  : Eventually (step1 Host.exe)
      (fun s' =>
        s'.data.regs.r12 = s₀.regs.rax ∧
        s'.data.regs.r13 = s₀.regs.rcx ∧
        s'.data.regs.rdi = s₀.regs.rdi)
      ⟨s₀, startAddr hp⟩ := by
  apply Program.FrameWP.step1_of_wp hp (UInt64.get_AtM_sep_AtM_sep h_mem)
  kvcgen64 [move_2_regs_to_heap] with finish

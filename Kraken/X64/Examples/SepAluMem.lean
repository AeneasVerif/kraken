/-
`alu_mem_example` in the separation wp: the baseline's four-instruction
program, with the slot at `136(%rdx)` owned as a `UInt64`. The triple fixes
the register and owns the slot with the stored value. Read back through
`straightlineStep_of_sep_triple`, it is the baseline statement
`alu_mem_example_correct`, over the same program and any layout.
-/
import Kraken.SepFrameProc
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped SepWP

set_option experimental.vcgen true

attribute [local grind ←] Lean.Order.le_ofProp MProp.le_mk_of
attribute [local grind =] Int.toBytes_length UInt64.toBytes_length BitVec.ofInt_ofBytes_toBytes

namespace Sep

@[spec] theorem alu_mem_correct (v : UInt64) :
    ⦃ fun r _ _ => v.AtM (r.rdx.toBitVec + 136#64) ⦄
      alu_mem_example
    ⦃ fun _ r _ _ => ⌜r.rcx = 142⌝ ⊓ (Int.toBytes 8 42).AtM (r.rdx.toBitVec + 136#64) ⦄ := by
  kvcgen64 [alu_mem_example] with finish

/-- The statement of the baseline's `alu_mem_example_correct`. -/
theorem alu_mem_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (straightlineStep (layout alu_mem_example))
      (fun s' => s'.1.regs.rcx = 142)
      (s₀, layout.start) := by
  apply eventually_straightlineStep_of_sep_triple (UInt64.get_AtM_sep h_mem)
  kvcgen64 with finish

/-! ## A block of register writes

Nine writes to distinct registers, each read in the post. -/

def reg_block : Program := parse("
  movq $1, %rax
  movq $2, %rbx
  movq $3, %rcx
  movq $4, %rdx
  movq $5, %rsi
  movq $6, %rdi
  movq $7, %rbp
  movq $8, %r8
  movq $9, %r9
")

theorem reg_block_correct :
    ⦃ fun _ _ _ => MProp.emp ⦄
      reg_block
    ⦃ fun _ r _ _ => ⌜r.rax = 1 ∧ r.rbx = 2 ∧ r.rcx = 3 ∧ r.rdx = 4 ∧ r.rsi = 5 ∧ r.rdi = 6
        ∧ r.rbp = 7 ∧ r.r8 = 8 ∧ r.r9 = 9⌝ ⦄ := by
  kvcgen64 [reg_block] with finish

end Sep

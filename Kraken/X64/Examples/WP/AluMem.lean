module

/-
`alu_mem_example` in the state wp: the baseline's four-instruction program,
with the slot at `136(%rdx)` mapped and holding `v`. The proposition is the
baseline statement `alu_mem_example_correct`, over the same program and any
layout, proved by `kvcgen64` on the wp of the program at the start state.
-/
public import Kraken.X64.WP.Instance
import Kraken.SeparationMem
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

attribute [local grind =] UInt64.toBytes_length BitVec.ofInt_ofBytes_toBytes ofBytes_toBytes
  Mem.loadInt_storeInt

namespace State

/-- The statement of the baseline's `alu_mem_example_correct`. -/
theorem alu_mem_example_correct [Host] (hp : alu_mem_example.IsInfix Host.prog) (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.rcx = 142)
      ⟨s₀, startAddr hp⟩ := by
  have hload := Mem.loadInt_sep _ _ 8 _ _ h_mem (UInt64.toBytes_length v) (by decide)
  apply Program.WP.step1_of_wp hp
  kvcgen64 [alu_mem_example] with finish

end State

module

import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics
import Kraken.X64.WP.Basic

open Kraken (Layout WellFormedLayout)
open Kraken.X64.Parser

private def kprologueTestProgram : Program := []
private def kprologueOtherProgram : Program := ⸨prog| mov $1, %rax ⸩
private def kstepLabelProgram : Program := ⸨prog|
start:
  mov $1, %rax
  mov $2, %rax
⸩
private def kstepJumpProgram : Program := ⸨prog|
  mov $1, %rax
  jmp done
  mov $99, %rax
done:
  mov $42, %rax
⸩

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout kprologueTestProgram] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 kprologueTestProgram.toExecutable) (fun _ => P) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := r15
  have _ : RegZmms := zmms
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact .done _ hP

/--
error: kprologue: refusing to shadow existing locals: rax
-/
#guard_msgs in
example [layout : Layout kprologueTestProgram] (rax : UInt64) (s : MachineData) :
    Eventually (step1 kprologueTestProgram.toExecutable) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s

#guard_msgs (substring := true) in
/--
error: 'change' tactic failed
-/
example [layout : Layout kprologueTestProgram] [Layout kprologueOtherProgram] (s : MachineData) :
    Eventually (step1 kprologueTestProgram.toExecutable) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueOtherProgram with s

-- `kstep 1` skips leading zero-size `.label` directives and steps one instruction.
example [layout : WellFormedLayout kstepLabelProgram] (s : MachineData) :
    Eventually (step1 kstepLabelProgram.toExecutable)
      (fun s' => s'.pc = kstepLabelProgram.toExecutable.addrOf 2 ∧ s'.1.regs.rax = 1)
      ⟨s, layout.start⟩ := by
  kprologue kstepLabelProgram with s
  sym => kstep 1; tactic =>
  exact .done _ ⟨rfl, rfl⟩

-- `kstep` follows unconditional jumps to internal labels.
example [layout : WellFormedLayout kstepJumpProgram] (s : MachineData) :
    Eventually (step1 kstepJumpProgram.toExecutable)
      (fun s' => s'.pc = kstepJumpProgram.toExecutable.addrOf kstepJumpProgram.length ∧ s'.1.regs.rax = 42)
      ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  sym => kstep; tactic =>
  exact .done _ ⟨rfl, rfl⟩

private def gotLoad : Instr := ⸨instr| movq f@GOTPCREL(%rip), %rax ⸩

private def gotExecutable : Executable :=
  { startAddr := 0x20, program := [{ directive := .instr gotLoad, size := 6 }] }

private theorem gotLoad_all [Labels] (s : MachineData) (value : Int)
    (hslot : gotSlot? "f" = some 0x1000)
    (hmem : Mem.loadInt s.dmem 0x1000 8 = some value) :
    (gotLoad.interp s ⟨0x20, 0x26⟩
      (fun s' => .done ⟨s', 0x26⟩) (fun a s' => .done ⟨s', a⟩)).All
      (fun st => st.pc = 0x26 ∧ st.data.regs.rax.toBitVec = BitVec.ofInt 64 value) := by
  change (Effects.resolve_got_slot "f" _).All _
  rw [Effects.All_resolve_got_slot, hslot]
  simp only [ConstExpr.interp]
  change (s.load 0x1000 .W64 _).All _
  unfold MachineData.load
  rw [Effects.All_require_read_access, hmem]
  exact ⟨rfl, rfl⟩

example (slots : Label → Option Int64) (s : MachineData) (value : Int)
    (hslot : slots "f" = some 0x1000)
    (hmem : Mem.loadInt s.dmem 0x1000 8 = some value) :
    step1 gotExecutable slots ⟨s, 0x20⟩
      (fun st => st.pc = 0x26 ∧ st.data.regs.rax.toBitVec = BitVec.ofInt 64 value) := by
  letI := gotExecutable.labels slots
  have hd : gotExecutable.directivesAtAddress 0x20 =
      [{ directive := .instr gotLoad, size := 6 }] := by
    simp [gotExecutable, Kraken.Executable.directivesAtAddress,
      Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2]
  simpa [step1, Executable.step, hd, Directives.interp, Directive.interp] using
    gotLoad_all s value hslot hmem

example (s : MachineData) :
    (step1 gotExecutable) ⟨s, 0x20⟩ (fun _ => True) = False := by
  have hd : gotExecutable.directivesAtAddress 0x20 =
      [{ directive := .instr gotLoad, size := 6 }] := by
    simp [gotExecutable, Kraken.Executable.directivesAtAddress,
      Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2]
  simp [step1, Executable.step, hd, Directives.interp, Directive.interp,
    gotLoad, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    AddrExpr.interp, ConstExpr.interp, Effects.All, Labels.gotSlot?]

example [Host] {k : Nat} (s : MachineData) (value : Int)
    (hd : [.instr gotLoad].IsInfixAt Host.prog k)
    (hpc : Host.addrOf k = 0x20) (hnext : Host.addrOf (k + 1) = 0x26)
    (hslot : gotSlot? "f" = some 0x1000)
    (hmem : Mem.loadInt s.dmem 0x1000 8 = some value) :
    Eventually (step1 Host.exe Host.gotSlot)
      (fun st => st.pc = 0x26 ∧ st.data.regs.rax.toBitVec = BitVec.ofInt 64 value)
      ⟨s, Host.addrOf k⟩ := by
  apply Host.eventually_of_interp hd
  rw [hpc, hnext]
  exact gotLoad_all s value hslot hmem

private def gotAddressProgram : Program := ⸨prog| leaq f@GOTPCREL(%rip), %rax ⸩

example [layout : WellFormedLayout gotAddressProgram]
    (slots : Label → Option Int64) (slot : Int64) (s : MachineData)
    (hslot : @Labels.gotSlot? (Executable.labels gotAddressProgram.toExecutable slots) "f" = some slot) :
    Eventually (step1 gotAddressProgram.toExecutable slots) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue gotAddressProgram with s
  sym => kstep 1; tactic =>
  rw [hslot]
  exact .done _ trivial

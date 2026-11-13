module

import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics

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

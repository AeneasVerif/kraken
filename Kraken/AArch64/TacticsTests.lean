module

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.Tactics

open Kraken.AArch64
open Kraken.AArch64.Parser

private def kprologueTestProgram : Program := []
private def kprologueOtherProgram : Program := ⸨prog| mov x0, #1 ⸩
private def kstepLabelProgram : Program := ⸨prog|
start:
  mov x0, #1
  mov x0, #2
⸩
private def kstepJumpProgram : Program := ⸨prog|
  mov x0, #1
  b done
  mov x0, #99
done:
  mov x0, #42
⸩

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout kprologueTestProgram] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 kprologueTestProgram.toExecutable) (fun _ => P) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := X30
  have _ : UInt64 := SP
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact .done _ hP

/--
error: kprologue: refusing to shadow existing locals: X0
-/
#guard_msgs in
example [layout : Layout kprologueTestProgram] (X0 : UInt64) (s : MachineData) :
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
      (fun s' => s'.pc = kstepLabelProgram.toExecutable.addrOf 2 ∧ s'.1.regs.X0 = 1)
      ⟨s, layout.start⟩ := by
  kprologue kstepLabelProgram with s
  sym => kstep 1; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  bv_decide

-- `kstep` follows unconditional branches to internal labels.
example [layout : WellFormedLayout kstepJumpProgram] (s : MachineData) :
    Eventually (step1 kstepJumpProgram.toExecutable)
      (fun s' => s'.pc = kstepJumpProgram.toExecutable.addrOf kstepJumpProgram.length ∧ s'.1.regs.X0 = 42)
      ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 42) = 42#64 from rfl]
  bv_decide

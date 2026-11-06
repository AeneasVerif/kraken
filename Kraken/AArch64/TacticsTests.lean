module

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.Tactics

open Kraken.AArch64
open Kraken.AArch64.Parser

private def kprologueTestProgram : Program := []
private def kprologueOtherProgram : Program := parseAArch64("mov x0, #1")
private def kstepLabelProgram : Program := parseAArch64("start:\nmov x0, #1\nmov x0, #2")
private def kstepJumpProgram : Program := parseAArch64("mov x0, #1\nb done\nmov x0, #99\ndone:\nmov x0, #42")

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => P) ⟨s, layout.start⟩ := by
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
example [layout : Layout] (X0 : UInt64) (s : MachineData) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s

#guard_msgs (substring := true) in
/--
error: 'change' tactic failed
-/
example [layout : Layout] (s : MachineData) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueOtherProgram with s

-- `kstep 1` skips leading zero-size `.label` directives and steps one instruction.
example [layout : Layout] [layout.NoWrap kstepLabelProgram] (s : MachineData) :
    Eventually (step1 (layout kstepLabelProgram))
      (fun s' => s'.pc = (layout kstepLabelProgram).addrOf 2 ∧ s'.1.regs.X0 = 1)
      ⟨s, layout.start⟩ := by
  kprologue kstepLabelProgram with s
  sym => kstep 1; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  bv_decide

-- `kstep` follows unconditional branches to internal labels.
example [layout : Layout] [layout.NoWrap kstepJumpProgram] (s : MachineData) :
    Eventually (step1 (layout kstepJumpProgram))
      (fun s' => s'.pc = (layout kstepJumpProgram).addrOf kstepJumpProgram.length ∧ s'.1.regs.X0 = 42)
      ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 42) = 42#64 from rfl]
  bv_decide

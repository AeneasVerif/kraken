import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Semantics
import Kraken.Tactics

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    straightlineStep (layout kprologueTestProgram) (s, layout.start) (fun _ => P) := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := X30
  have _ : UInt64 := SP
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact hP

/--
error: kprologue: refusing to shadow existing locals: X0
-/
#guard_msgs in
example [layout : Layout] (X0 : UInt64) (s : MachineData) :
    straightlineStep (layout kprologueTestProgram) (s, layout.start) (fun _ => True) := by
  kprologue kprologueTestProgram with s

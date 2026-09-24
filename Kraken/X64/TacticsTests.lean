import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Semantics

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => P) (s, layout.start) := by
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
example [layout : Layout] (rax : UInt64) (s : MachineData) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => True) (s, layout.start) := by
  kprologue kprologueTestProgram with s

import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Semantics

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    straightlineStep (layout kprologueTestProgram) (s, layout.start) (fun _ => P) := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := r15
  have _ : RegZmms := zmms
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact hP

/--
error: kprologue: refusing to shadow existing locals: rax
-/
#guard_msgs in
example [layout : Layout] (rax : UInt64) (s : MachineData) :
    straightlineStep (layout kprologueTestProgram) (s, layout.start) (fun _ => True) := by
  kprologue kprologueTestProgram with s

-- The `kstep n` step budget errors on shortfall. Two instructions plus the
-- end of the listing consume three `Directives.interp` unfolds, so a budget
-- of five leaves two.
private def budgetTestProgram : Program :=
  [.instr (.regular .W64 .W64 (.nop 1)), .instr (.regular .W64 .W64 (.nop 1))]

/--
error: kstep could not step through the remaining 2 steps
-/
#guard_msgs (error, drop all) in
example [layout : Layout] (s : MachineData) :
    straightlineStep (layout budgetTestProgram) (s, layout.start) (fun _ => True) := by
  kprologue budgetTestProgram with s
  sym =>
  kstep 5

-- The stepping gate only normalizes the canonical monad instance. A goal
-- mentioning a different `Bind Effects` instance is left alone, so its
-- meaning survives `kstep` and the definitional closing step below.
private def customBind : Bind Effects := ⟨fun _ _ => .unimplemented "custom"⟩

example : ¬ Effects.All (fun _ : Nat => True)
    (@Bind.bind Effects customBind _ _ (.done 0) (fun n => .done n)) := by
  sym =>
  kstep
  tactic =>
  intro h
  exact h

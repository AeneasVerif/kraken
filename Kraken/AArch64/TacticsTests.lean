module

public meta import Lean
import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.Tactics

open Kraken (Layout)
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
example (layout : Layout) (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 (layout.apply kprologueTestProgram)) (fun _ => P) ⟨s, layout.start⟩ := by
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
example (layout : Layout) (X0 : UInt64) (s : MachineData) :
    Eventually (step1 (layout.apply kprologueTestProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s

#guard_msgs (substring := true) in
/--
error: 'change' tactic failed
-/
example (layout : Layout) (s : MachineData) :
    Eventually (step1 (layout.apply kprologueTestProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueOtherProgram with s

-- `kstep 1` skips leading zero-size `.label` directives and steps one instruction.
example (layout : Layout) [kstepLabelProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply kstepLabelProgram))
      (fun s' => s'.pc = (layout.apply kstepLabelProgram).addrOf 2 ∧ s'.1.regs.X0 = 1)
      ⟨s, layout.start⟩ := by
  kprologue kstepLabelProgram with s
  sym => kstep 1; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  bv_decide

-- `kstep` follows unconditional branches to internal labels.
example (layout : Layout) [kstepJumpProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram))
      (fun s' => s'.pc = (layout.apply kstepJumpProgram).addrOf kstepJumpProgram.length ∧ s'.1.regs.X0 = 42)
      ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 42) = 42#64 from rfl]
  bv_decide

/--
info: ⸨prog|
● movz x0, #1, lsl #0
  b done
  movz x0, #99, lsl #0
  done:
  movz x0, #42, lsl #0
⸩
Eventually (step1 (Layout.apply kstepJumpProgram layout)) (fun x => True)
  { data := ss✝, pc := (Layout.apply kstepJumpProgram layout).addrOf 0 }
---
info: END KSTEP: 0 sub-goals left
---
info: ⸨prog|
○ movz x0, #1, lsl #0
● b done
  movz x0, #99, lsl #0
  done:
  movz x0, #42, lsl #0
⸩
Eventually (step1 (Layout.apply kstepJumpProgram layout)) (fun x => True)
  {
    data :=
      {
        regs :=
          have v := { toBitVec := res✝ };
          { X0 := v, X1 := X1, X2 := X2, X3 := X3, X4 := X4, X5 := X5, X6 := X6, X7 := X7, X8 := X8, X9 := X9,
            X10 := X10, X11 := X11, X12 := X12, X13 := X13, X14 := X14, X15 := X15, X16 := X16, X17 := X17, X18 := X18,
            X19 := X19, X20 := X20, X21 := X21, X22 := X22, X23 := X23, X24 := X24, X25 := X25, X26 := X26, X27 := X27,
            X28 := X28, X29 := X29, X30 := X30, SP := SP },
        status := flags, dmem := mem },
    pc := (Layout.apply kstepJumpProgram layout).addrOf 1 }
---
info: END KSTEP: 0 sub-goals left
---
info: ⸨prog|
  ...
○ b done
  movz x0, #99, lsl #0
● done:
  movz x0, #42, lsl #0
⸩
Eventually (step1 (Layout.apply kstepJumpProgram layout)) (fun x => True)
  {
    data :=
      {
        regs :=
          have v := { toBitVec := res✝ };
          { X0 := v, X1 := X1, X2 := X2, X3 := X3, X4 := X4, X5 := X5, X6 := X6, X7 := X7, X8 := X8, X9 := X9,
            X10 := X10, X11 := X11, X12 := X12, X13 := X13, X14 := X14, X15 := X15, X16 := X16, X17 := X17, X18 := X18,
            X19 := X19, X20 := X20, X21 := X21, X22 := X22, X23 := X23, X24 := X24, X25 := X25, X26 := X26, X27 := X27,
            X28 := X28, X29 := X29, X30 := X30, SP := SP },
        status := flags, dmem := mem },
    pc := (Layout.apply kstepJumpProgram layout).addrOf 3 }
-/
#guard_msgs in
example (layout : Layout) [kstepJumpProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  sym => kstep 1; tactic =>
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  sym => kstep 1; tactic =>
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  exact .done _ trivial

local elab "#inspect_widgets " cmd:command : command => do
  let nBefore := (← Lean.Elab.getInfoTrees).size
  Lean.Elab.Command.elabCommand cmd
  let trees := (← Lean.Elab.getInfoTrees).toArray[nBefore:]
  let widgets := trees.foldl (init := #[]) fun acc t =>
    Lean.Elab.InfoTree.foldInfo (init := acc) (fun _ info ws =>
      match info with
      | .ofUserWidgetInfo uwi => ws.push (uwi.id, (uwi.props.run {}).1.compress)
      | _ => ws) t
  Lean.logInfo m!"widgets: {widgets.size}"
  for (id, payload) in widgets do
    Lean.logInfo m!"widget: {id} {payload}"

/--
info: END KSTEP: 0 sub-goals left
---
info: END KSTEP: 0 sub-goals left
---
info: widgets: 3
---
info: widget: Kraken.krakenProgramWidget {"after":5,"before":2,"curr":0,"directives":["movz x0, #1, lsl #0","b done","movz x0, #99, lsl #0","done:","movz x0, #42, lsl #0"],"name":"kstepJumpProgram","prev":null}
---
info: widget: Kraken.krakenProgramWidget {"after":5,"before":2,"curr":1,"directives":["movz x0, #1, lsl #0","b done","movz x0, #99, lsl #0","done:","movz x0, #42, lsl #0"],"name":"kstepJumpProgram","prev":0}
---
info: widget: Kraken.krakenProgramWidget {"after":5,"before":2,"curr":3,"directives":["movz x0, #1, lsl #0","b done","movz x0, #99, lsl #0","done:","movz x0, #42, lsl #0"],"name":"kstepJumpProgram","prev":1}
-/
#guard_msgs in
set_option pp.kraken.program "widget" in
#inspect_widgets
example (layout : Layout) [kstepJumpProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  sym => kstep 1; tactic =>
  sym => kstep 1; tactic =>
  exact .done _ trivial

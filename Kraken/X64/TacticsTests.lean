module

public meta import Lean
import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics

open Kraken (Layout)
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
example (layout : Layout) (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 (layout.apply kprologueTestProgram)) (fun _ => P) ⟨s, layout.start⟩ := by
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
example (layout : Layout) (rax : UInt64) (s : MachineData) :
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
      (fun s' => s'.pc = (layout.apply kstepLabelProgram).addrOf 2 ∧ s'.1.regs.rax = 1)
      ⟨s, layout.start⟩ := by
  kprologue kstepLabelProgram with s
  sym => kstep 1; tactic =>
  exact .done _ ⟨rfl, rfl⟩

-- `kstep` follows unconditional jumps to internal labels.
example (layout : Layout) [kstepJumpProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram))
      (fun s' => s'.pc = (layout.apply kstepJumpProgram).addrOf kstepJumpProgram.length ∧ s'.1.regs.rax = 42)
      ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  sym => kstep; tactic =>
  exact .done _ ⟨rfl, rfl⟩

private def longJumpProgram : Program := ⸨prog|
  mov $1, %rax
  jmp done
  mov $10, %rbx
  mov $20, %rcx
  mov $30, %rdx
  mov $40, %rsi
  mov $50, %rdi
  mov $60, %r8
done:
  mov $42, %rax
⸩

/--
info: ⸨prog|
● movq $1, %rax
  jmp done
  movq $10, %rbx
  movq $20, %rcx
  movq $30, %rdx
  movq $40, %rsi
  ...
⸩
Eventually (step1 (Layout.apply longJumpProgram layout)) (fun x => True)
  { data := ss✝, pc := (Layout.apply longJumpProgram layout).addrOf 0 }
---
info: END KSTEP: 0 sub-goals left
---
info: ⸨prog|
○ movq $1, %rax
● jmp done
  movq $10, %rbx
  movq $20, %rcx
  movq $30, %rdx
  movq $40, %rsi
  movq $50, %rdi
  ...
⸩
Eventually (step1 (Layout.apply longJumpProgram layout)) (fun x => True)
  {
    data :=
      {
        regs :=
          have v := { toBitVec := 1#64 };
          { rax := v, rbx := rbx, rcx := rcx, rdx := rdx, rsi := rsi, rdi := rdi, rsp := rsp, rbp := rbp, r8 := r8,
            r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 },
        zmms := zmms, status := flags, df := df, dmem := mem },
    pc := (Layout.apply longJumpProgram layout).addrOf 1 }
---
info: END KSTEP: 0 sub-goals left
---
info: ⸨prog|
  ...
○ jmp done
  ...
  movq $50, %rdi
  movq $60, %r8
● done:
  movq $42, %rax
⸩
Eventually (step1 (Layout.apply longJumpProgram layout)) (fun x => True)
  {
    data :=
      {
        regs :=
          have v := { toBitVec := 1#64 };
          { rax := v, rbx := rbx, rcx := rcx, rdx := rdx, rsi := rsi, rdi := rdi, rsp := rsp, rbp := rbp, r8 := r8,
            r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 },
        zmms := zmms, status := flags, df := df, dmem := mem },
    pc := (Layout.apply longJumpProgram layout).addrOf 8 }
---
info: END KSTEP: 0 sub-goals left
---
info: ⸨prog|
  ...
○ done:
  movq $42, %rax
●
⸩
Eventually (step1 (Layout.apply longJumpProgram layout)) (fun x => True)
  {
    data :=
      {
        regs :=
          have v := { toBitVec := 42#64 };
          { rax := v, rbx := rbx, rcx := rcx, rdx := rdx, rsi := rsi, rdi := rdi, rsp := rsp, rbp := rbp, r8 := r8,
            r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 },
        zmms := zmms, status := flags, df := df, dmem := mem },
    pc := (Layout.apply longJumpProgram layout).addrOf 10 }
-/
#guard_msgs in
example (layout : Layout) [longJumpProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply longJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue longJumpProgram with s
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  sym => kstep 1; tactic =>
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  sym => kstep 1; tactic =>
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  sym => kstep; tactic =>
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  exact .done _ trivial

-- Custom window via `kprologue (before := ...) (after := ...)` and rewriting `pc` outside `kstep`.
/--
info: ⸨prog|
● movq $1, %rax
  jmp done
  ...
⸩
Eventually (step1 (Layout.apply longJumpProgram layout)) (fun x => True)
  { data := ss✝, pc := (Layout.apply longJumpProgram layout).addrOf 0 }
---
info: ⸨prog|
  ...
  movq $10, %rbx
● movq $20, %rcx
  movq $30, %rdx
  ...
⸩
Eventually (step1 (Layout.apply longJumpProgram layout)) (fun x => True)
  { data := ss✝, pc := (Layout.apply longJumpProgram layout).addrOf 3 }
-/
#guard_msgs in
example (layout : Layout) (s : MachineData)
    (h : (layout.apply longJumpProgram).addrOf 0 = (layout.apply longJumpProgram).addrOf 3) :
    Eventually (step1 (layout.apply longJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue (before := 1) (after := 1) longJumpProgram with s
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  rw [h]
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

-- `pp.kraken.program "none"` disables the program header; untagged goals are also unaffected,
-- and neither `"delab"` nor `"none"` emits any user widget info.
/--
info: Eventually (step1 (Layout.apply kstepJumpProgram layout)) (fun x => True) { data := s, pc := layout.start }
---
info: Eventually (step1 (Layout.apply kstepJumpProgram layout)) (fun x => True)
  { data := ss✝, pc := (Layout.apply kstepJumpProgram layout).addrOf 0 }
---
info: widgets: 0
-/
#guard_msgs in
#inspect_widgets
example (layout : Layout) (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  kprologue kstepJumpProgram with s
  set_option pp.kraken.program "none" in
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  exact .done _ trivial

-- `pp.kraken.program "widget"` omits the inline delaborator header and emits panel widget JSON
-- on `kprologue` and each `kstep`.
/--
info: Eventually (step1 (Layout.apply kstepJumpProgram layout)) (fun x => True)
  { data := ss✝, pc := (Layout.apply kstepJumpProgram layout).addrOf 0 }
---
info: END KSTEP: 0 sub-goals left
---
info: END KSTEP: 0 sub-goals left
---
info: widgets: 3
---
info: widget: Kraken.krakenProgramWidget {"after":2,"before":1,"curr":0,"directives":["movq $1, %rax","jmp done","movq $99, %rax","done:","movq $42, %rax"],"name":"kstepJumpProgram","prev":null}
---
info: widget: Kraken.krakenProgramWidget {"after":2,"before":1,"curr":1,"directives":["movq $1, %rax","jmp done","movq $99, %rax","done:","movq $42, %rax"],"name":"kstepJumpProgram","prev":0}
---
info: widget: Kraken.krakenProgramWidget {"after":2,"before":1,"curr":3,"directives":["movq $1, %rax","jmp done","movq $99, %rax","done:","movq $42, %rax"],"name":"kstepJumpProgram","prev":1}
-/
#guard_msgs in
set_option pp.kraken.program "widget" in
#inspect_widgets
example (layout : Layout) [kstepJumpProgram.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue (before := 1) (after := 2) kstepJumpProgram with s
  run_tac Lean.Elab.Tactic.withMainContext do Lean.logInfo m!"{← (← Lean.Elab.Tactic.getMainGoal).getType}"
  sym => kstep 1; tactic =>
  sym => kstep 1; tactic =>
  exact .done _ trivial

-- Unrecognized `pp.kraken.program` values produce a clear error.
/--
error: invalid value 'bogus' for option 'pp.kraken.program'; expected one of: "delab", "widget", "none"
-/
#guard_msgs in
set_option pp.kraken.program "bogus" in
example (layout : Layout) (s : MachineData) :
    Eventually (step1 (layout.apply kstepJumpProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kstepJumpProgram with s
  exact .done _ trivial

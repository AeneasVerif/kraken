import Kraken.X64.Semantics

/-!
Regression coverage for executable locations and single-instruction stepping.
The aliases must not add synthetic directives or turn one step into a block.
-/

private def stepProgram : Program := [
  .label "entry",
  .label "entry_alias",
  .instr (.regular .W64 .W64 (.nop 1)),
  .label "second",
  .instr (.regular .W64 .W64 (.nop 2))
]

private def runStep (e : Executable) (pc : Int64) : Option Int64 :=
  match e.step (({}, pc) : MachineState) .done with
  | .require_exec_access range ok =>
      match ok () with
      | .done (_, nextPC) =>
          if range.lower == pc && range.upper == nextPC then some nextPC else none
      | _ => none
  | _ => none

/-- info: true -/
#guard_msgs in
#eval
  let exe := stepProgram.fakeLayout
  let entry := exe.labels.label "entry"
  let entryAlias := exe.labels.label "entry_alias"
  let second := exe.labels.label "second"
  exe.locatedDirectives.length == stepProgram.length &&
    exe.withAddresses.length == stepProgram.length &&
    entry == entryAlias &&
    (exe.directivesAtAddress entry).length == 1 &&
    runStep exe entry == some second &&
    runStep exe second == some (second + 2)

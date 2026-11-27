module

public import Kraken.Layout
public import Kraken.OmniSemantics
public meta import Lean
public meta import Kraken.Layout
public meta import Kraken.OmniSemantics

/-!
Metadata tagging and windowing helpers for displaying the current assembly program with directive
cursors (`●` for current, `○` for previous) right above `Eventually` goals.
-/

namespace Kraken

open Lean Meta

public meta section

register_option pp.kraken.program : Bool := {
  defValue := true
  descr := "Render the program listing with directive cursors above tagged `Eventually` goals."
}

/-- `MData` key used to tag `Eventually` goals for program-cursor delaboration. -/
def showProgramMDataKey : Name := `Kraken.showProgram

/-- Display metadata stored on a tagged `Eventually` goal. -/
structure ShowProgramMeta where
  /-- Current directive index (0-based; `p.length` means end of program). -/
  idx : Nat
  /-- Directive index before the most recent `kstep`, if any. -/
  prev? : Option Nat := none
  /-- Number of context lines to show before `idx`. -/
  before : Nat := 2
  /-- Number of context lines to show after `idx`. -/
  after : Nat := 5
  deriving Repr, BEq

def ShowProgramMeta.encode (m : ShowProgramMeta) : String :=
  let prevStr := match m.prev? with
    | some p => toString p
    | none => "-"
  s!"{m.idx}:{prevStr}:{m.before}:{m.after}"

def ShowProgramMeta.decode? (s : String) : Option ShowProgramMeta := do
  match s.splitOn ":" with
  | [idxStr, prevStr, beforeStr, afterStr] =>
    let idx ← idxStr.toNat?
    let prev? ←
      if prevStr == "-" then some none
      else some (some (← prevStr.toNat?))
    let before ← beforeStr.toNat?
    let after ← afterStr.toNat?
    return { idx, prev?, before, after }
  | _ => none

/-- Build a single-entry `MData` map so Lean's `delabMData` dispatches to `mdata.Kraken.showProgram`. -/
def mkShowProgramMData (m : ShowProgramMeta) : MData :=
  KVMap.empty.insert showProgramMDataKey (.ofString m.encode)

/-- Decode `ShowProgramMeta` from an `MData` map if it carries `showProgramMDataKey`. -/
def getShowProgramMData? (d : MData) : Option ShowProgramMeta := do
  let .ofString s ← d.find showProgramMDataKey | none
  ShowProgramMeta.decode? s

/-- Wrap `e` with `showProgramMDataKey` metadata (replacing any existing outer tag). -/
def attachShowProgramMData (m : ShowProgramMeta) (e : Expr) : Expr :=
  let inner := match e with
    | .mdata d body => if (d.find showProgramMDataKey).isSome then body else e
    | _ => e
  .mdata (mkShowProgramMData m) inner

/-- Strip an outer `showProgramMDataKey` `MData` wrapper if present. -/
def stripShowProgramMData (e : Expr) : Option ShowProgramMeta × Expr :=
  match e with
  | .mdata d body =>
    match getShowProgramMData? d with
    | some m => (some m, body)
    | none => (none, e)
  | _ => (none, e)

/-- Match `Eventually (step1 (Kraken.Layout.apply p l)) post state`, returning
    `(instrType, p, pcIdx?)` where `pcIdx?` is `some k` when `state` is `⟨_, exe.addrOf k⟩`
    with `k` a concrete `Nat` literal. -/
def extractEventuallyProgramAndPc? (e : Expr) : Option (Expr × Expr × Option Nat) := do
  let_expr Eventually _ trans _ state := e | none
  guard (trans.isAppOfArity `step1 1)
  let exe := trans.getArg! 0
  let_expr Kraken.Layout.apply instrType _ p _ := exe | none
  let pcIdx? : Option Nat := do
    guard (state.isAppOfArity `MachineState.mk 2)
    let pc := state.getArg! 1
    let_expr Kraken.Executable.addrOf _ _ _ kExpr := pc | none
    kExpr.nat? <|> kExpr.rawNatLit?
  return (instrType, p, pcIdx?)

/-- Unfold a concrete `Program` (`List Directive`) into its array of directive expressions. -/
partial def unfoldDirectiveList? (p : Expr) : MetaM (Option (Array Expr)) :=
  go p #[]
where
  go (xs : Expr) (acc : Array Expr) : MetaM (Option (Array Expr)) := do
    let xs ← whnf xs
    match_expr xs with
    | List.cons _ hd tl => go tl (acc.push hd)
    | List.nil _ => return some acc
    | _ => return none

/-- A single rendered line in the windowed program listing. -/
inductive ProgramLineKind where
  | ellipsis
  | dir (idx : Nat) (marker : Option Bool) -- `some true` = `●`, `some false` = `○`, `none` = plain
  | endCursor (isCurr : Bool)              -- cursor at `idx == numDirs` (after the last directive)
  deriving Repr, BEq

/-- Compute the windowed lines to display for a program of length `numDirs`, showing `●` at `curr`
    and `○` at `prev?` (when distinct from `curr`), with `before`/`after` context around `curr`. -/
def computeProgramWindow (numDirs curr : Nat) (prev? : Option Nat) (before after : Nat) :
    Array ProgramLineKind := Id.run do
  let curr := min curr numDirs
  let prev? := prev?.filter (fun p => p != curr && p ≤ numDirs)
  if numDirs == 0 then
    return #[.endCursor true]

  let mkLine (i : Nat) : ProgramLineKind :=
    if i == numDirs then
      .endCursor (i == curr)
    else
      let marker :=
        if i == curr then some true
        else if prev? == some i then some false
        else none
      .dir i marker

  let maxIdx := if curr == numDirs then numDirs else numDirs - 1
  let mut lo := curr - before
  let mut hi := min maxIdx (curr + after)
  let mut pre : Option Nat := none
  let mut post : Option Nat := none

  if let some prev := prev? then
    if prev < lo then
      if prev + 1 == lo then
        lo := prev
      else
        pre := some prev
    else if prev > hi then
      if prev == hi + 1 then
        hi := prev
      else
        post := some prev

  let mut lines : Array ProgramLineKind := #[]
  if let some prev := pre then
    if prev > 0 then lines := lines.push .ellipsis
    lines := lines.push (mkLine prev)
    lines := lines.push .ellipsis
  else
    if lo > 0 then lines := lines.push .ellipsis

  for i in [lo : hi + 1] do
    lines := lines.push (mkLine i)

  if let some prev := post then
    lines := lines.push .ellipsis
    lines := lines.push (mkLine prev)
    if prev + 1 < numDirs then lines := lines.push .ellipsis
  else
    if hi + 1 < numDirs then lines := lines.push .ellipsis

  return lines

end

end Kraken

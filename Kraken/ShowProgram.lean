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

/-- Rendering mode for tagged `Eventually` program listings. -/
inductive ShowProgramMode where
  | none
  | delab
  | widget
  deriving Repr, BEq

register_option pp.kraken.program : String := {
  defValue := "delab"
  descr := "How to render the program listing with directive cursors on tagged `Eventually` goals: \"delab\" (inline in the goal), \"widget\" (separate Infoview panel), or \"none\" (disabled)."
}

def parseShowProgramMode (s : String) : Except String ShowProgramMode :=
  match s with
  | "none" => .ok .none
  | "delab" => .ok .delab
  | "widget" => .ok .widget
  | _ => .error s!"invalid value '{s}' for option 'pp.kraken.program'; expected one of: \"delab\", \"widget\", \"none\""

def getShowProgramMode? (o : Options) : Option ShowProgramMode :=
  (parseShowProgramMode (pp.kraken.program.get o)).toOption

def getShowProgramModeM {m : Type → Type} [Monad m] [MonadOptions m] [MonadError m] : m ShowProgramMode := do
  let val := pp.kraken.program.get (← getOptions)
  match parseShowProgramMode val with
  | .ok mode => return mode
  | .error msg => throwError "{msg}"

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

/-- Render a single `Kraken.Directive` expression into clean assembly text by invoking whichever
    architecture-specific directive delaborator is imported, stripping outer `⸨dir| ... ⸩`
    delimiters when present. -/
def renderDirectiveText (d : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.set `pp.explicit false) (Meta.ppExpr d)
  let s := fmt.pretty.trimAscii.toString
  let s :=
    if s.startsWith "⸨dir|" && s.endsWith "⸩" then
      ((s.dropPrefix "⸨dir|").dropSuffix "⸩").trimAscii.toString
    else
      s
  return s

/-- Derive a short display name for a program expression. -/
def programDisplayName (progExpr : Expr) : String :=
  match progExpr.getAppFn.constName? with
  | some n =>
    if n == ``List.cons || n == ``List.nil then "<program>"
    else (Lean.privateToUserName n).toString
  | none => "<program>"

/-- Build the JSON props payload for the Infoview program widget. -/
def buildProgramWidgetJson (progExpr : Expr) (m : ShowProgramMeta) : MetaM (Option Json) := do
  let some dirs ← unfoldDirectiveList? progExpr | return none
  let dirTexts ← dirs.mapM renderDirectiveText
  let prevJson : Json := match m.prev? with
    | some p => Json.num p
    | none => Json.null
  return some <| Json.mkObj [
    ("name", Json.str (programDisplayName progExpr)),
    ("directives", Json.arr (dirTexts.map Json.str)),
    ("curr", Json.num m.idx),
    ("prev", prevJson),
    ("before", Json.num m.before),
    ("after", Json.num m.after)
  ]

end

end Kraken

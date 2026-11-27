module

public import Std.Data.HashSet

/-!
# Target-Generic Loop-Header Alignment Helper (`PrintAlignCommon`)

Architecture-neutral backward-branch loop-header detection and assembly alignment printer
parameterized by `labelOf?`, `jmpTarget?`, and per-directive / plain printers.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.PrintAlignCommon

open Std

/-- True iff `l` is a function-local block label (`.L*` or `{fn}.L*`) rather than a function
entry label. Resetting `seen` at function-entry labels prevents cross-function and self
tail-calls from being misclassified as intra-function loop headers. -/
def isLocalLabel (l : String) : Bool :=
  l.startsWith ".L" || (l.splitOn ".L").length > 1

/-- Collect labels targeted by at least one intra-function backward jump/branch in `p`. -/
def loopHeaderSet {α : Type} (labelOf? jmpTarget? : α → Option String)
    (p : List α) : HashSet String :=
  let (_, hdrs) := p.foldl (init := (({} : HashSet String), ({} : HashSet String)))
    fun (seen, hdrs) d =>
      match labelOf? d with
      | some l => if isLocalLabel l then (seen.insert l, hdrs) else ({}, hdrs)
      | none =>
        match jmpTarget? d with
        | some tgt => if seen.contains tgt then (seen, hdrs.insert tgt) else (seen, hdrs)
        | none => (seen, hdrs)
  hdrs

/-- Return whether `l` is a backward-branch loop header in `p`. -/
def isLoopHeader {α : Type} (labelOf? jmpTarget? : α → Option String)
    (p : List α) (l : String) : Bool :=
  (loopHeaderSet labelOf? jmpTarget? p).contains l

/-- Return all backward-branch loop-header labels in `p` in order of appearance. -/
def detectLoopHeaders {α : Type} (labelOf? jmpTarget? : α → Option String)
    (p : List α) : List String :=
  let hdrs := loopHeaderSet labelOf? jmpTarget? p
  (p.foldl (init := (#[], ({} : HashSet String))) fun (acc, emitted) d =>
    match labelOf? d with
    | some l =>
      if hdrs.contains l && !emitted.contains l then (acc.push l, emitted.insert l)
      else (acc, emitted)
    | none => (acc, emitted)).1.toList

/-- Print `p`, optionally inserting `alignDir?` before backward-branch loop-header labels.
When `alignDir? = none`, delegates directly to `printPlain p`. -/
def printWithAlign {α : Type} (labelOf? jmpTarget? : α → Option String)
    (printPlain : List α → String) (printDir : α → String)
    (alignDir? : Option String) (p : List α) : String :=
  match alignDir? with
  | none => printPlain p
  | some alignDir =>
    let hdrs := loopHeaderSet labelOf? jmpTarget? p
    let lines := p.foldl (init := #[]) fun out d =>
      let out := match labelOf? d with
        | some l => if hdrs.contains l then out.push alignDir else out
        | none => out
      out.push (printDir d)
    String.intercalate "\n" lines.toList

end LeanQbe.T.PrintAlignCommon

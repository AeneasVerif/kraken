module

public import Kraken.X64.PrintATT
import Std.Data.HashSet

/-!
# x86-64 Loop-Header Alignment AT&T Printer (`PrintATTAlign`)

Wraps `Kraken.X64.ATT.directive` with a deterministic backward-branch loop-header detector over
`List Kraken.X64.Directive`, emitting `.p2align 5,,12` (32-byte alignment with max 12-byte skip)
immediately before loop-header `.label` directives only.

This pass operates purely on assembly text downstream of `LinkedCert` (`Kraken.X64.toATT` and
`LeanQbe.T.Amd64.PrintAsm0Lemmas` remain untouched), modifying zero instructions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std
open Kraken.X64

/-- GNU assembler alignment directive emitted before x86-64 backward-branch loop headers. -/
def loopAlignDirective : String := ".p2align 5,,12"

/-- Extract the target label of a direct jump or conditional branch directive, if any. -/
private def jmpTarget? : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | .instr (.regular _ _ (.jmp (.rel (.label l)))) => some l
  | .instr (.regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction)))) => some l
  | _ => none

/-- Collect the set of labels targeted by at least one backward jump/branch in `p`. -/
private def loopHeaderSet (p : List Directive) : HashSet Label :=
  let (_, hdrs) := p.foldl (init := (({} : HashSet Label), ({} : HashSet Label)))
    fun (seen, hdrs) d =>
      match d with
      | .label l => (seen.insert l, hdrs)
      | _ =>
        match jmpTarget? d with
        | some tgt => if seen.contains tgt then (seen, hdrs.insert tgt) else (seen, hdrs)
        | none => (seen, hdrs)
  hdrs

/-- Return whether `l` is a backward-branch loop header in `p`. -/
def isLoopHeader (p : List Directive) (l : Label) : Bool :=
  (loopHeaderSet p).contains l

/-- Return all backward-branch loop-header labels in `p` in order of appearance. -/
def detectLoopHeaders (p : List Directive) : List Label :=
  let hdrs := loopHeaderSet p
  (p.foldl (init := (#[], ({} : HashSet Label))) fun (acc, emitted) d =>
    match d with
    | .label l =>
      if hdrs.contains l && !emitted.contains l then (acc.push l, emitted.insert l)
      else (acc, emitted)
    | _ => (acc, emitted)).1.toList

/-- Print `p` in AT&T syntax, optionally inserting `alignDir?` before backward-branch loop-header
labels. When `alignDir? = none`, output matches `Kraken.X64.toATT p` verbatim. -/
def toATTWithAlign (alignDir? : Option String) (p : List Directive) : String :=
  match alignDir? with
  | none => Kraken.X64.toATT p
  | some alignDir =>
    let hdrs := loopHeaderSet p
    let lines := p.foldl (init := #[]) fun out d =>
      let out := match d with
        | .label l => if hdrs.contains l then out.push alignDir else out
        | _ => out
      out.push (ATT.directive d)
    String.intercalate "\n" lines.toList

/-- Print `p` in AT&T syntax with `.p2align 5,,12` before backward-branch loop headers. -/
def toATTAligned (p : List Directive) : String :=
  toATTWithAlign (some loopAlignDirective) p

end LeanQbe.T.Amd64

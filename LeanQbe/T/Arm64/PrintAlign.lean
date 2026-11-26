module

public import Kraken.AArch64.Print
import Std.Data.HashSet

/-!
# AArch64 Loop-Header Alignment Assembly Printer (`PrintAlign`)

Wraps `Kraken.AArch64.Print.directive` with a deterministic backward-branch loop-header detector
over `List Kraken.AArch64.Directive`, emitting `.p2align 4` (16-byte alignment) immediately before
loop-header `.label` directives only.

This pass operates purely on assembly text downstream of `LinkedCert` (`Kraken.AArch64.Print`
remains untouched), modifying zero instructions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std
open Kraken.AArch64

/-- GNU assembler alignment directive emitted before AArch64 backward-branch loop headers. -/
def loopAlignDirective : String := ".p2align 4"

/-- Extract the target label of a direct branch instruction directive, if any. -/
private def jmpTarget? : Directive → Option String
  | .instr ⟨_, .B (.label l)⟩ => some l
  | .instr ⟨_, .B_cond _ (.label l)⟩ => some l
  | .instr ⟨_, .CBZ _ (.label l)⟩ => some l
  | .instr ⟨_, .CBNZ _ (.label l)⟩ => some l
  | .instr ⟨_, .TBZ _ _ (.label l)⟩ => some l
  | .instr ⟨_, .TBNZ _ _ (.label l)⟩ => some l
  | _ => none

/-- True iff `l` is a function-local block label (`.L*` or `{fn}.L*`) rather than a function
entry label. Resetting `seen` at function-entry labels prevents cross-function and self
tail-calls (`b fn`) from being misclassified as intra-function loop headers. -/
private def isLocalLabel (l : String) : Bool :=
  l.startsWith ".L" || (l.splitOn ".L").length > 1

/-- Collect labels targeted by at least one intra-function backward branch in `p`. -/
private def loopHeaderSet (p : List Directive) : HashSet String :=
  let (_, hdrs) := p.foldl (init := (({} : HashSet String), ({} : HashSet String)))
    fun (seen, hdrs) d =>
      match d with
      | .label l => if isLocalLabel l then (seen.insert l, hdrs) else ({}, hdrs)
      | _ =>
        match jmpTarget? d with
        | some tgt => if seen.contains tgt then (seen, hdrs.insert tgt) else (seen, hdrs)
        | none => (seen, hdrs)
  hdrs

/-- Return whether `l` is a backward-branch loop header in `p`. -/
def isLoopHeader (p : List Directive) (l : String) : Bool :=
  (loopHeaderSet p).contains l

/-- Return all backward-branch loop-header labels in `p` in order of appearance. -/
def detectLoopHeaders (p : List Directive) : List String :=
  let hdrs := loopHeaderSet p
  (p.foldl (init := (#[], ({} : HashSet String))) fun (acc, emitted) d =>
    match d with
    | .label l =>
      if hdrs.contains l && !emitted.contains l then (acc.push l, emitted.insert l)
      else (acc, emitted)
    | _ => (acc, emitted)).1.toList

/-- Print `p` as newline-separated AArch64 assembly text without alignment insertion. -/
def toAsm (p : List Directive) : String :=
  String.intercalate "\n" (p.map Print.directive)

/-- Print `p` as AArch64 assembly, optionally inserting `alignDir?` before backward-branch
loop-header labels. When `alignDir? = none`, output matches `toAsm p` verbatim. -/
def toAsmWithAlign (alignDir? : Option String) (p : List Directive) : String :=
  match alignDir? with
  | none => toAsm p
  | some alignDir =>
    let hdrs := loopHeaderSet p
    let lines := p.foldl (init := #[]) fun out d =>
      let out := match d with
        | .label l => if hdrs.contains l then out.push alignDir else out
        | _ => out
      out.push (Print.directive d)
    String.intercalate "\n" lines.toList

/-- Print `p` as AArch64 assembly with `.p2align 4` before backward-branch loop headers. -/
def toAsmAligned (p : List Directive) : String :=
  toAsmWithAlign (some loopAlignDirective) p

end LeanQbe.T.Arm64

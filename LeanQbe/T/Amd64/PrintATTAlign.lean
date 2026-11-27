module

public import LeanQbe.T.PrintAlignCommon
public import Kraken.X64.PrintATT

/-!
# x86-64 Loop-Header Alignment AT&T Printer (`PrintATTAlign`)

Thin x86-64 instantiation of `LeanQbe.T.PrintAlignCommon`, emitting `.p2align 5,,12` immediately
before backward-branch loop-header `.label` directives only.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Kraken.X64
open LeanQbe.T

/-- GNU assembler alignment directive emitted before x86-64 backward-branch loop headers. -/
def loopAlignDirective : String := ".p2align 5,,12"

private def labelOf? : Directive → Option Label
  | .label l => some l
  | _ => none

private def jmpTarget? : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | .instr (.regular _ _ (.jmp (.rel (.label l)))) => some l
  | .instr (.regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction)))) => some l
  | _ => none

/-- Return whether `l` is a backward-branch loop header in `p`. -/
def isLoopHeader (p : List Directive) (l : Label) : Bool :=
  PrintAlignCommon.isLoopHeader labelOf? jmpTarget? p l

/-- Return all backward-branch loop-header labels in `p` in order of appearance. -/
def detectLoopHeaders (p : List Directive) : List Label :=
  PrintAlignCommon.detectLoopHeaders labelOf? jmpTarget? p

/-- Print `p` in AT&T syntax, optionally inserting `alignDir?` before backward-branch loop-header
labels. When `alignDir? = none`, output matches `Kraken.X64.toATT p` verbatim. -/
def toATTWithAlign (alignDir? : Option String) (p : List Directive) : String :=
  PrintAlignCommon.printWithAlign labelOf? jmpTarget? Kraken.X64.toATT ATT.directive alignDir? p

/-- Print `p` in AT&T syntax with `.p2align 5,,12` before backward-branch loop headers. -/
def toATTAligned (p : List Directive) : String :=
  toATTWithAlign (some loopAlignDirective) p

end LeanQbe.T.Amd64

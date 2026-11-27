module

public import LeanQbe.T.PrintAlignCommon
public import Kraken.AArch64.Print

/-!
# AArch64 Loop-Header Alignment Assembly Printer (`PrintAlign`)

Thin AArch64 instantiation of `LeanQbe.T.PrintAlignCommon`, emitting `.p2align 4` immediately
before backward-branch loop-header `.label` directives only.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Kraken.AArch64
open LeanQbe.T

/-- GNU assembler alignment directive emitted before AArch64 backward-branch loop headers. -/
def loopAlignDirective : String := ".p2align 4"

private def labelOf? : Directive → Option String
  | .label l => some l
  | _ => none

private def jmpTarget? : Directive → Option String
  | .instr ⟨_, .B (.label l)⟩ => some l
  | .instr ⟨_, .B_cond _ (.label l)⟩ => some l
  | .instr ⟨_, .CBZ _ (.label l)⟩ => some l
  | .instr ⟨_, .CBNZ _ (.label l)⟩ => some l
  | .instr ⟨_, .TBZ _ _ (.label l)⟩ => some l
  | .instr ⟨_, .TBNZ _ _ (.label l)⟩ => some l
  | _ => none

/-- Return whether `l` is a backward-branch loop header in `p`. -/
def isLoopHeader (p : List Directive) (l : String) : Bool :=
  PrintAlignCommon.isLoopHeader labelOf? jmpTarget? p l

/-- Return all backward-branch loop-header labels in `p` in order of appearance. -/
def detectLoopHeaders (p : List Directive) : List String :=
  PrintAlignCommon.detectLoopHeaders labelOf? jmpTarget? p

/-- Print `p` as newline-separated AArch64 assembly text without alignment insertion. -/
def toAsm (p : List Directive) : String :=
  String.intercalate "\n" (p.map Print.directive)

/-- Print `p` as AArch64 assembly, optionally inserting `alignDir?` before backward-branch
loop-header labels. When `alignDir? = none`, output matches `toAsm p` verbatim. -/
def toAsmWithAlign (alignDir? : Option String) (p : List Directive) : String :=
  PrintAlignCommon.printWithAlign labelOf? jmpTarget? toAsm Print.directive alignDir? p

/-- Print `p` as AArch64 assembly with `.p2align 4` before backward-branch loop headers. -/
def toAsmAligned (p : List Directive) : String :=
  toAsmWithAlign (some loopAlignDirective) p

end LeanQbe.T.Arm64

module

public import LeanQbe.T.Amd64.PrintATTAlign
public import LeanQbe.T.Amd64.DebugAsm
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Examples.LitmusProgs
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Driver
public import LeanQbe.T.Notation
public import Kraken.X64.PrintATT
meta import LeanQbe.T.Amd64.PrintATTAlign
meta import LeanQbe.T.Amd64.DebugAsm
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.LitmusProgs
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Examples.ChaCha
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Notation
meta import Kraken.X64.PrintATT

/-!
# x86-64 Loop-Header Alignment Printer Tests (`PrintATTAlignX64Test`)

Unit and compiled-IR `#guard` checks for `LeanQbe.T.Amd64.PrintATTAlign`:
* straight-line and forward-only branches emit zero `.p2align` directives and match
  `Kraken.X64.toATT` verbatim;
* backward `.jcc`, `.jmp (.rel (.label _))`, and `.jmp (.rel (.sub (.label _) ...))` emit
  `.p2align 5,,12` immediately before the target loop-header label only;
* mixed forward + multiple backward jumps to the same loop header emit exactly one `.p2align`;
* real compiled `LeanQbe.T` programs (`sumto`, `chacha20Block`, `mul4x4`, `lratBytesFns`)
  align loop headers cleanly while leaving unrolled straight-line `mul4x4` untouched.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.PrintATTAlignX64Test

open Kraken.X64
open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Notation

private def mkJcc (cc : CondCode) (l : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jcc cc l))

private def mkJmpLabel (l : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.rel (.label l))))

private def mkJmpSub (l : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label l) .after_current_instruction))))

private def mkRet : Directive :=
  .instr (.regular .W64 .W64 .ret)

private def mkNop : Directive :=
  .instr (.regular .W64 .W64 (.nop 1))

private def straightProg : List Directive :=
  [.label "fn", mkNop, mkRet]

private def forwardOnlyProg : List Directive :=
  [ .label "fn"
  , mkJcc .z "fn.Lexit"
  , mkNop
  , mkJmpSub "fn.Ljoin"
  , .label "fn.Ljoin"
  , mkNop
  , .label "fn.Lexit"
  , mkRet
  ]

private def backJccProg : List Directive :=
  [ .label "fn"
  , .label "fn.Lloop"
  , mkNop
  , mkJcc .nz "fn.Lloop"
  , .label "fn.Lexit"
  , mkRet
  ]

private def backJmpLabelProg : List Directive :=
  [ .label "fn"
  , .label "fn.Lhdr"
  , mkNop
  , mkJmpLabel "fn.Lhdr"
  , .label "fn.Lcold"
  , mkRet
  ]

private def backJmpSubProg : List Directive :=
  [ .label "fn"
  , mkJmpSub "fn.Lhdr"
  , .label "fn.Lhdr"
  , mkJcc .z "fn.Lexit"
  , mkNop
  , mkJmpSub "fn.Lhdr"
  , mkJcc .nz "fn.Lhdr"
  , .label "fn.Lexit"
  , mkRet
  ]

private def multiLoopProg : List Directive :=
  [ .label "fn"
  , .label "fn.Louter"
  , .label "fn.Linner"
  , mkJcc .nz "fn.Linner"
  , mkJmpSub "fn.Louter"
  , .label "fn.Lcold"
  , mkRet
  ]

private def compileFns (fns : List Fn) : List Directive :=
  let hs := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  match compile x64Target.toIsa x64LegalTarget fns hs with
  | .ok ds => ds
  | .error _ => []

private def allAlignsBeforeLabels (asm : String) : Bool :=
  let lines := asm.splitOn "\n"
  let rec go : List String → Bool
    | [] => true
    | ln :: rest =>
      if ln.trimAscii.toString == loopAlignDirective then
        match rest with
        | nxt :: _ => nxt.endsWith ":" && go rest
        | [] => false
      else
        go rest
  go lines

private def countAligns (asm : String) : Nat :=
  (asm.splitOn "\n").foldl (fun acc ln =>
    if ln.trimAscii.toString == loopAlignDirective then acc + 1 else acc) 0

-- 1. Empty and straight-line programs match Kraken.X64.toATT verbatim.
#guard toATTAligned [] == Kraken.X64.toATT []
#guard detectLoopHeaders [] == []
#guard toATTAligned straightProg == Kraken.X64.toATT straightProg
#guard detectLoopHeaders straightProg == []

-- 2. Forward-only branches do NOT emit .p2align and match Kraken.X64.toATT.
#guard detectLoopHeaders forwardOnlyProg == []
#guard toATTAligned forwardOnlyProg == Kraken.X64.toATT forwardOnlyProg

-- 3. `toATTWithAlign none` always matches Kraken.X64.toATT verbatim.
#guard toATTWithAlign none backJccProg == Kraken.X64.toATT backJccProg
#guard toATTWithAlign none multiLoopProg == Kraken.X64.toATT multiLoopProg

-- 4. Backward jcc, jmp (.label), and jmp (.sub (.label) ...) emit exact .p2align 5,,12.
#guard detectLoopHeaders backJccProg == ["fn.Lloop"]
#guard toATTAligned backJccProg ==
  "fn:\n.p2align 5,,12\nfn.Lloop:\nnop\njne fn.Lloop\nfn.Lexit:\nret"

#guard detectLoopHeaders backJmpLabelProg == ["fn.Lhdr"]
#guard toATTAligned backJmpLabelProg ==
  "fn:\n.p2align 5,,12\nfn.Lhdr:\nnop\njmp fn.Lhdr\nfn.Lcold:\nret"

#guard detectLoopHeaders backJmpSubProg == ["fn.Lhdr"]
#guard toATTAligned backJmpSubProg ==
  "fn:\njmp fn.Lhdr\n.p2align 5,,12\nfn.Lhdr:\nje fn.Lexit\n" ++
  "nop\njmp fn.Lhdr\njne fn.Lhdr\nfn.Lexit:\nret"

-- 5. Nested loops emit one .p2align per header and skip cold labels.
#guard detectLoopHeaders multiLoopProg == ["fn.Louter", "fn.Linner"]
#guard countAligns (toATTAligned multiLoopProg) == 2
#guard allAlignsBeforeLabels (toATTAligned multiLoopProg)

-- 6. Real compiled programs: sumto, chacha20Block, mul4x4, lratBytes.
private def sumtoCode : List Directive := compileFns [LeanQbe.T.Examples.Litmus.sumto]
private def chachaCode : List Directive := compileFns LeanQbe.T.Examples.ChaCha.chacha20Module.fns
private def mul4x4Code : List Directive := compileFns LeanQbe.T.Examples.Bignum.mul4x4Module.fns
private def lratCode : List Directive := compileFns LeanQbe.T.Examples.LratBytes.lratBytesFns

#guard !(detectLoopHeaders sumtoCode).isEmpty
#guard allAlignsBeforeLabels (toATTAligned sumtoCode)
#guard countAligns (toATTAligned sumtoCode) == (detectLoopHeaders sumtoCode).length

#guard (detectLoopHeaders chachaCode).length == 1
#guard allAlignsBeforeLabels (toATTAligned chachaCode)

#guard (detectLoopHeaders mul4x4Code).isEmpty
#guard toATTAligned mul4x4Code == Kraken.X64.toATT mul4x4Code

#guard (detectLoopHeaders lratCode).length >= 20
#guard allAlignsBeforeLabels (toATTAligned lratCode)
#guard countAligns (toATTAligned lratCode) == (detectLoopHeaders lratCode).length

-- 7. DebugAsm alignment parity (non-leaf loop function).
private def dbgLoopFn : Fn := tqbe $dbg_loop(%n:l, %acc:l) -> l {
  loop @lp(%i:l = %n, %s:l = %acc) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %r =l call $c_probe(%i, %s)
      %s1 =l add %s, %r
      %i1 =l sub %i, 1
      continue @lp(%i1, %s1)
    }, {
      ret %s
    }
  }
}

private def dbgLoopCheck : Bool :=
  let hs := [Fn.computeHints x64Target.toIsa x64LegalTarget dbgLoopFn]
  match compile x64Target.toIsa x64LegalTarget [dbgLoopFn] hs with
  | .error _ => false
  | .ok dirs =>
    match emitX64DebugAsmChecked [dbgLoopFn] dirs (some hs) [] false true,
          emitX64DebugAsmChecked [dbgLoopFn] dirs (some hs) [] false false with
    | .ok aOn, .ok aOff =>
      countAligns aOn == (detectLoopHeaders dirs).length &&
      countAligns aOn >= 1 &&
      allAlignsBeforeLabels aOn &&
      countAligns aOff == 0
    | _, _ => false

#guard dbgLoopCheck

end LeanQbeTest.T.PrintATTAlignX64Test

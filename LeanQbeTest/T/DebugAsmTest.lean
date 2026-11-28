module

import LeanQbe.T.Amd64.DebugAsm
import LeanQbe.T.Amd64.Frame
import LeanQbe.T.Amd64.PrintATTAlign
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Driver
import LeanQbe.T.Examples.LitmusProgs
import LeanQbe.T.Notation
import Kraken.X64.PrintATT
meta import LeanQbe.T.Amd64.DebugAsm
meta import LeanQbe.T.Amd64.Frame
meta import LeanQbe.T.Amd64.PrintATTAlign
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Examples.LitmusProgs
meta import Kraken.X64.PrintATT

/-!
# X64 Debug Assembly & CFI Unit Checks

Checks `emitX64DebugAsmChecked` across the 10 typed-IR litmus modules, a synthetic
multi-exit callee-saved function (`multi_exit`), and a large-frame (`!x64FitsImm31`) case:
* both `hints? := some hs` and `hints? := none` succeed and produce identical output;
* ELF `.type ..., %function`, `.size ..., .-...`, `.cfi_startproc` / `.cfi_endproc` appear;
* `.cfi_remember_state` and `.cfi_restore_state` balance on intermediate exits;
* zero `{fn}.L{digits}:` local block labels appear un-prefixed.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.DebugAsmTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Litmus LeanQbe.T.Notation Kraken.X64

private def multiExit : Fn := tqbe $multi_exit(%n:l, %a:l, %b:l, %c:l) -> l {
  %w =w trunc %n
  %z =b cnew %w, 0
  jnz %z, {
    %m =l sub %n, 1
    %wm =w trunc %m
    %nz =b cnew %wm, 0
    jnz %nz, {
      %r =l call $probe(%n, %a)
      %s1 =l add %a, %b
      %s2 =l add %s1, %c
      %s3 =l add %s2, %r
      ret %s3
    }, {
      exit $abort_hook(%a)
    }
  }, {
    ret 42
  }
}

private def probeFn : Fn := tqbe $probe(%x:l, %y:l) -> l {
  %z =l add %x, %y
  ret %z
}

private def simpleFn : Fn := tqbe $big_fn(%x:l, %y:l) -> l {
  %z =l add %x, %y
  ret %z
}

private def containsSub (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def countSub (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

private def hasUnscrubbedLabel (fn asm : String) : Bool :=
  let lines := asm.splitOn "\n"
  lines.any fun ln =>
    if ln.startsWith (fn ++ ".L") && ln.endsWith ":" then true
    else false

private def checkModule (m : Module) : Except String Unit := do
  let hs := m.fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← compile x64Target.toIsa x64LegalTarget m.fns hs
  let asmSome ← emitX64DebugAsmChecked m.fns dirs (some hs) m.exits true
  let asmNone ← emitX64DebugAsmChecked m.fns dirs none m.exits true
  if asmSome != asmNone then
    throw s!"hints/auto mismatch for module {m.fns.map (·.name)}"
  for f in m.fns do
    if !containsSub asmSome s!"\t.type {f.name}, %function" then
      throw s!"missing .type for {f.name}"
    if !containsSub asmSome s!"\t.size {f.name}, .-{f.name}" then
      throw s!"missing .size for {f.name}"
    if hasUnscrubbedLabel f.name asmSome then
      throw s!"unscrubbed local label in {f.name}"
  let starts := countSub asmSome "\t.cfi_startproc"
  let ends := countSub asmSome "\t.cfi_endproc"
  if starts != m.fns.length || ends != m.fns.length then
    throw s!"CFI start/end count mismatch: {starts}/{ends} vs {m.fns.length}"
  let rems := countSub asmSome "\t.cfi_remember_state"
  let rests := countSub asmSome "\t.cfi_restore_state"
  if rems != rests then
    throw s!"remember/restore mismatch: {rems} vs {rests}"

private def checkBigFrame : Except String Unit := do
  let base := Fn.computeHints x64Target.toIsa x64LegalTarget simpleFn
  let bigHint : X64Hints :=
    { base with nslots := 268435456, saved := [.rbx, .r12] }
  let dirs ← compile x64Target.toIsa x64LegalTarget [simpleFn] [bigHint]
  let asmSome ← emitX64DebugAsmChecked [simpleFn] dirs (some [bigHint]) [] true
  let asmNone ← emitX64DebugAsmChecked [simpleFn] dirs none [] true
  if asmSome != asmNone then
    throw "big-frame hints/auto mismatch"
  if !containsSub asmSome "\t.cfi_offset %rbx" || !containsSub asmSome "\t.cfi_restore %rbx" then
    throw "missing big-frame callee-save CFI"
  if !containsSub asmSome "\t.cfi_def_cfa_offset 8\n" then
    throw "missing big-frame epilogue cfa_offset"

private def checkMultiExitSaved : Except String Unit := do
  let meHint : X64Hints :=
    { Fn.computeHints x64Target.toIsa x64LegalTarget multiExit with
      saved := [.rbx, .rbp, .r12, .r13] }
  let prHint := Fn.computeHints x64Target.toIsa x64LegalTarget probeFn
  let fns := [probeFn, multiExit]
  let hs := [prHint, meHint]
  let dirs ← compile x64Target.toIsa x64LegalTarget fns hs
  let asmSome ← emitX64DebugAsmChecked fns dirs (some hs) ["abort_hook"] true
  let asmNone ← emitX64DebugAsmChecked fns dirs none ["abort_hook"] true
  if asmSome != asmNone then
    throw "multi-exit hints/auto mismatch"
  let rems := countSub asmSome "\t.cfi_remember_state"
  let rests := countSub asmSome "\t.cfi_restore_state"
  if rems < 2 || rems != rests then
    throw s!"expected >=2 remember/restore pairs, got {rems}/{rests}"
  for reg in ["%rbx", "%rbp", "%r12", "%r13"] do
    if countSub asmSome s!"\t.cfi_offset {reg}" != 1 then
      throw s!"expected 1 cfi_offset for {reg}"
    if countSub asmSome s!"\t.cfi_restore {reg}" != 3 then
      throw s!"expected 3 cfi_restore (3 exits) for {reg}"

private def callZeroFn : Fn := tqbe $call_zero(%x:l) -> l {
  %r =l call $probe(%x, 1:l)
  ret %r
}

private def checkNonLeafZeroSlot : Except String Unit := do
  let prHint := Fn.computeHints x64Target.toIsa x64LegalTarget probeFn
  let czHint := Fn.computeHints x64Target.toIsa x64LegalTarget callZeroFn
  if czHint.nslots != 0 || !czHint.saved.isEmpty then
    throw s!"expected totalSlots=0 for call_zero, got {czHint.nslots}/{czHint.saved.length}"
  let fns := [probeFn, callZeroFn]
  let hs := [prHint, czHint]
  let dirs ← compile x64Target.toIsa x64LegalTarget fns hs
  let asmSome ← emitX64DebugAsmChecked fns dirs (some hs) [] true
  let asmNone ← emitX64DebugAsmChecked fns dirs none [] true
  if asmSome != asmNone then
    throw "call_zero hints/auto mismatch"
  if !containsSub asmSome "# fn call_zero: frame=8B cfa=rsp+16 saved=[]" then
    throw "missing non-leaf 0-slot header for call_zero"
  if !containsSub asmSome "subq $8, %rsp\n\t.cfi_def_cfa_offset 16\n" then
    throw "missing call_zero prologue cfi_def_cfa_offset 16"
  if !containsSub asmSome "addq $8, %rsp\n\t.cfi_def_cfa_offset 8\n" then
    throw "missing call_zero epilogue cfi_def_cfa_offset 8"

private def checkZeroFrameLeaves : Except String Unit := do
  let leafFns := [evenodd, sumto]
  let leafHs := leafFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  for (f, h) in leafFns.zip leafHs do
    if h.nslots != 0 || !h.saved.isEmpty then
      throw s!"expected totalSlots=0 for {f.name}, got {h.nslots}/{h.saved.length}"
  let dirs ← compile x64Target.toIsa x64LegalTarget leafFns leafHs
  let asmSome ← emitX64DebugAsmChecked leafFns dirs (some leafHs) [] true
  let asmNone ← emitX64DebugAsmChecked leafFns dirs none [] true
  if asmSome != asmNone then
    throw "zero-frame leaf hints/auto mismatch"
  for nm in ["evenodd", "sumto"] do
    if !containsSub asmSome s!"# fn {nm}: frame=0B cfa=rsp+8 saved=[]" then
      throw s!"missing zero-frame header for {nm}"
  if containsSub asmSome "\t.cfi_def_cfa_offset" then
    throw "unexpected .cfi_def_cfa_offset in zero-frame leaves"
  if containsSub asmSome "%rsp" then
    throw "unexpected %rsp manipulation in zero-frame leaves"
  let hdrCount := (detectLoopHeaders dirs).length
  if hdrCount == 0 then
    throw "expected loop headers in zero-frame leaf suite"
  if countSub asmSome s!"\n{loopAlignDirective}\n" != hdrCount then
    throw s!"loop align count mismatch in zero-frame leaves (expected {hdrCount})"
  let noAlignSome ← emitX64DebugAsmChecked leafFns dirs (some leafHs) [] true false
  let noAlignNone ← emitX64DebugAsmChecked leafFns dirs none [] true false
  if noAlignSome != noAlignNone || containsSub noAlignSome loopAlignDirective then
    throw "loopAlign=false failed on zero-frame leaves"
  let chkHint := Fn.computeHints x64Target.toIsa x64LegalTarget check
  if chkHint.nslots != 0 || !chkHint.saved.isEmpty then
    throw "expected totalSlots=0 for check"
  let chkDirs ← compile x64Target.toIsa x64LegalTarget [check] [chkHint]
  let chkSome ← emitX64DebugAsmChecked [check] chkDirs (some [chkHint]) ["fail"] true
  let chkNone ← emitX64DebugAsmChecked [check] chkDirs none ["fail"] true
  if chkSome != chkNone then
    throw "check hints/auto mismatch"
  if !containsSub chkSome "# fn check: frame=0B cfa=rsp+8 saved=[]" then
    throw "missing zero-frame header for exit-bearing leaf check"
  if containsSub chkSome "%rsp" || containsSub chkSome "\t.cfi_def_cfa_offset" then
    throw "unexpected frame directives in exit-bearing leaf check"

private def checkNegativePrologues : Except String Unit := do
  let hZero := Fn.computeHints x64Target.toIsa x64LegalTarget simpleFn
  if hZero.nslots != 0 || !hZero.saved.isEmpty then
    throw "expected totalSlots=0 for simpleFn"
  let badCallCode := [.label "big_fn", x64CallD "probe", x64RetD]
  match emitX64DebugAsmChecked [simpleFn] badCallCode (some [hZero]) ["probe"] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on 0-slot non-leaf without prologue"
  match emitX64DebugAsmChecked [simpleFn] badCallCode none ["probe"] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on 0-slot non-leaf without prologue"
  let badProCode := [.label "big_fn", x64SubSpD 4, x64RetD]
  match emitX64DebugAsmChecked [simpleFn] badProCode (some [hZero]) [] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on subq $4, %rsp"
  match emitX64DebugAsmChecked [simpleFn] badProCode none [] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on subq $4, %rsp"

def checkIndirectTailCFI : Except String Unit := do
  let hZero := Fn.computeHints x64Target.toIsa x64LegalTarget simpleFn
  let leafIndTail : List Directive :=
    [.label "big_fn", .instr (.regular .W64 .W64 (.jmp (.reg (q .rax))))]
  let leafSome ← emitX64DebugAsmChecked [simpleFn] leafIndTail (some [hZero]) [] true
  let leafNone ← emitX64DebugAsmChecked [simpleFn] leafIndTail none [] true
  if leafSome != leafNone then
    throw "x64 indirect tail leaf hints/auto mismatch"
  if !containsSub leafSome "# fn big_fn: frame=0B cfa=rsp+8 saved=[]" then
    throw "missing zero-frame header for x64 indirect tail leaf"
  if !containsSub leafSome "\njmp *%rax\n" then
    throw "missing jmp *%rax in x64 indirect tail leaf"
  let badIndCall : List Directive :=
    [.label "big_fn", .instr (.regular .W64 .W64 (.call (.reg (q .rax)))), x64RetD]
  match emitX64DebugAsmChecked [simpleFn] badIndCall (some [hZero]) [] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on 0-slot indirect call *%rax without prologue"
  match emitX64DebugAsmChecked [simpleFn] badIndCall none [] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on 0-slot indirect call *%rax without prologue"
  let frameIndTail : List Directive :=
    [.label "big_fn"] ++ (x64Frame.prologue 0).1 ++ (x64Frame.epilogue 0).1 ++
    [.instr (.regular .W64 .W64 (.jmp (.reg (q .r11)))), .label "big_fn.L0"] ++
    (x64Frame.epilogue 0).1 ++ [x64RetD]
  let multiSome ← emitX64DebugAsmChecked [simpleFn] frameIndTail (some [hZero]) [] true
  let multiNone ← emitX64DebugAsmChecked [simpleFn] frameIndTail none [] true
  if multiSome != multiNone then
    throw "x64 multi-exit indirect tail hints/auto mismatch"
  if !containsSub multiSome "\t# epilogue (jmp *%r11)\n\t.cfi_remember_state\n" then
    throw "missing epilogue/remember_state for x64 indirect tail jump"
  let badRspTail : List Directive :=
    [.label "big_fn", .instr (.regular .W64 .W64 (.jmp (.mem ⟨some (.reg .rsp), none, .int64 0⟩)))]
  match emitX64DebugAsmChecked [simpleFn] badRspTail (some [hZero]) [] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on 0-slot jmp *(%rsp) without prologue"
  let memIndTail : List Directive :=
    [.label "big_fn"] ++ (x64Frame.prologue 0).1 ++ (x64Frame.epilogue 0).1 ++
    [.instr (.regular .W64 .W64 (.jmp (.mem ⟨some (.reg .rax), none, .int64 8⟩))),
      .label "big_fn.L0"] ++
    (x64Frame.epilogue 0).1 ++ [x64RetD]
  let memSome ← emitX64DebugAsmChecked [simpleFn] memIndTail (some [hZero]) [] true
  let memNone ← emitX64DebugAsmChecked [simpleFn] memIndTail none [] true
  if memSome != memNone then
    throw "x64 multi-exit mem indirect tail hints/auto mismatch"
  if !containsSub memSome "\t# epilogue (jmp *8(%rax))\n\t.cfi_remember_state\n" then
    throw "missing epilogue/remember_state for x64 indirect mem tail jump"

/-- Run all pure x64 DebugAsm verification checks. -/
def runAllChecks : Except String Unit := do
  for m in allModules do
    checkModule m
  let stressMod : Module := ⟨[probeFn, multiExit], [], ["abort_hook"]⟩
  checkModule stressMod
  checkMultiExitSaved
  checkBigFrame
  checkNonLeafZeroSlot
  checkZeroFrameLeaves
  checkNegativePrologues
  checkIndirectTailCFI

/-- Executable entrypoint running `runAllChecks`. -/
public def main : IO Unit := do
  match runAllChecks with
  | .ok () => IO.println "DebugAsmTest: all checks passed"
  | .error e => throw (IO.userError e)

end LeanQbeTest.T.DebugAsmTest

/-- Standalone entrypoint for `lean --run LeanQbeTest/T/DebugAsmTest.lean`. -/
public def main : IO Unit := LeanQbeTest.T.DebugAsmTest.main

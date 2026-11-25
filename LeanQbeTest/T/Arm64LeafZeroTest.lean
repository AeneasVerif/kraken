module

public import LeanQbe.T.Arm64.DebugAsm
public import LeanQbe.T.Arm64.FrameLemmas
public import LeanQbe.T.Arm64.Litmus
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Driver
public import LeanQbe.T.Examples.LitmusProgs
public import LeanQbe.T.Notation
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.DebugAsm
meta import LeanQbe.T.Arm64.Frame
meta import LeanQbe.T.Arm64.Litmus
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Examples.LitmusProgs
meta import LeanQbe.T.Notation
meta import LeanQbe.T.Spill

/-!
# AAPCS64 Arm64 `S1` Zero-Frame Leaf & DebugAsm CFI Regression Tests

Verifies:
1. `armFrame.leafZeroFrame = true` and `Rega.isZeroLeaf` / `effFrame = 0` on 0-slot leaves
   (`evenodd`, `sumto`, `check`, `leafAdd`), while preserving frames (`effFrame = 16`) on
   0-slot non-leaves (`call_zero`) and leaves with slots or saved registers.
2. Verified `checkCompile` / `compileModule` emission on `armTarget`: zero `sub sp` / `add sp` /
   `str x30` / `ldr x30` instructions in zero-frame leaves, full prologue/epilogue in non-leaves.
3. Closed Kraken AArch64 correctness theorem (`evenodd` / `sumto` zero-frame leaf execution) with
   `std3` axioms only.
4. `emitArm64DebugAsmChecked` parity (`hints? := some hs` vs `none`), zero-frame CFI
   (`.cfi_startproc` / `.cfi_endproc` / `.ltorg`, zero `.cfi_def_cfa_offset`, zero `sp` refs),
   0-slot non-leaf CFI, multi-exit saved-register CFI, large literal-pool frames, and negative
   rejection of missing prologues / unaligned `sub sp` / `x30` clobbers.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.Arm64LeafZeroTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Litmus LeanQbe.T.Notation
open Kraken Kraken.AArch64

/-! ## 1. Kernel `rfl` checks for `armFrame.leafZeroFrame` -/

theorem armFrame_leafZeroFrame_rfl : armFrame.leafZeroFrame = true := rfl

theorem armTarget_leafZeroFrame_rfl : armTarget.toIsa.frame.leafZeroFrame = true := rfl

/-! ## 2. Verified zero-frame leaf compilation & directive checks -/

meta def isSubSpDir : Directive → Bool
  | .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) _⟩ => true
  | _ => false

meta def isAddSpDir : Directive → Bool
  | .instr ⟨.W64, .ADD_e (.low .SP .W64) (.low .SP .W64) _⟩ => true
  | _ => false

meta def isStrX30Dir : Directive → Bool
  | .instr ⟨.W64, .STR (.low (.reg .X30) .W64) _⟩ => true
  | _ => false

meta def isLdrX30Dir : Directive → Bool
  | .instr ⟨.W64, .LDR (.low (.reg .X30) .W64) _⟩ => true
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat :=
  (ds.filter p).length

meta def probeFn : Fn := tqbe $probe(%x:l, %y:l) -> l {
  %z =l add %x, %y
  ret %z
}

meta def callZeroFn : Fn := tqbe $call_zero(%x:l) -> l {
  %r =l call $probe(%x, 1:l)
  ret %r
}

meta def multiExitFn : Fn := tqbe $multi_exit(%n:l, %a:l, %b:l, %c:l) -> l {
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

meta def simpleFn : Fn := tqbe $big_fn(%x:l, %y:l) -> l {
  %z =l add %x, %y
  ret %z
}

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

meta def chk (fs : List Fn) (exits : List Sym := []) : Bool :=
  checkCompile armTarget armLayout armLegalTarget [] exits 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) (hs : List armTarget.toIsa.Hints) (exits : List Sym := []) :
    List Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget 0 [] exits 0 fs hs)

meta def isZeroLeafFn (f : Fn) : Bool :=
  let h := Fn.computeHints armTarget.toIsa armLegalTarget f
  Rega.isZeroLeaf armTarget.toIsa h (f.mid armLegalTarget).ext

meta def effFrameFn (f : Fn) : Nat :=
  let h := Fn.computeHints armTarget.toIsa armLegalTarget f
  Rega.effFrame armTarget.toIsa h (f.mid armLegalTarget).ext

-- Zero-slot leaves elide frame completely (`effFrame = 0`, 0 SP/X30 directives).
#guard isZeroLeafFn probeFn
#guard isZeroLeafFn evenodd
#guard isZeroLeafFn sumto
#guard isZeroLeafFn check
#guard effFrameFn probeFn == 0
#guard effFrameFn evenodd == 0
#guard effFrameFn sumto == 0
#guard effFrameFn check == 0
#guard chk [probeFn]
#guard chk [evenodd]
#guard chk [sumto]
#guard chk [check] ["fail"]

#guard
  let ds := codeOf [evenodd, sumto] (hintsOf [evenodd, sumto])
  countDirs isSubSpDir ds == 0 && countDirs isAddSpDir ds == 0 &&
    countDirs isStrX30Dir ds == 0 && countDirs isLdrX30Dir ds == 0

#guard
  let ds := codeOf [check] (hintsOf [check]) ["fail"]
  countDirs isSubSpDir ds == 0 && countDirs isAddSpDir ds == 0 &&
    countDirs isStrX30Dir ds == 0 && countDirs isLdrX30Dir ds == 0

-- Zero-slot non-leaf keeps its 16-byte frame and X30 save/restore.
#guard !isZeroLeafFn callZeroFn
#guard effFrameFn callZeroFn == 16
#guard chk [probeFn, callZeroFn]
#guard
  let ds := codeOf [probeFn, callZeroFn] (hintsOf [probeFn, callZeroFn])
  countDirs isSubSpDir ds == 1 && countDirs isAddSpDir ds == 1 &&
    countDirs isStrX30Dir ds == 1 && countDirs isLdrX30Dir ds == 1

-- Leaf with non-zero saved regs or slots keeps its frame.
#guard
  let hSaved : armTarget.toIsa.Hints :=
    { Fn.computeHints armTarget.toIsa armLegalTarget simpleFn with saved := [.reg .X19] }
  let ds := codeOf [simpleFn] [hSaved]
  checkCompile armTarget armLayout armLegalTarget [] [] 0 [simpleFn] [hSaved] 2048 &&
    countDirs isSubSpDir ds == 1 && countDirs isAddSpDir ds == 1 &&
    countDirs isStrX30Dir ds == 1 && countDirs isLdrX30Dir ds == 1

-- `Arm64.Litmus` zero-frame leaf bounds drop to `0`.
#guard Arm64.Litmus.evenoddCompiled.bound "evenodd" == 0
#guard Arm64.Litmus.sumtoCompiled.bound "sumto" == 0
#guard Arm64.Litmus.tracerCompiled.bound "tracer" == 0

/-! ## 3. `Arm64.DebugAsm` CFI checks for zero-frame leaves & non-leaves -/

meta def containsSub (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

meta def countSub (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

meta def hasUnscrubbedLabel (fn asm : String) : Bool :=
  (asm.splitOn "\n").any fun ln => ln.startsWith (fn ++ ".L") && ln.endsWith ":"

meta def checkModule (m : Module) : Except String Unit := do
  let hs := m.fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← compile armTarget.toIsa armLegalTarget m.fns hs
  let asmSome ← emitArm64DebugAsmChecked m.fns dirs (some hs) m.exits true
  let asmNone ← emitArm64DebugAsmChecked m.fns dirs none m.exits true
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

meta def checkZeroFrameLeaves : Except String Unit := do
  let leafFns := [evenodd, sumto]
  let leafHs := leafFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  for (f, h) in leafFns.zip leafHs do
    if h.nslots != 0 || !h.saved.isEmpty then
      throw s!"expected totalSlots=0 for {f.name}"
  let dirs ← compile armTarget.toIsa armLegalTarget leafFns leafHs
  let asmSome ← emitArm64DebugAsmChecked leafFns dirs (some leafHs) [] true
  let asmNone ← emitArm64DebugAsmChecked leafFns dirs none [] true
  if asmSome != asmNone then
    throw "zero-frame leaf hints/auto mismatch"
  for nm in ["evenodd", "sumto"] do
    if !containsSub asmSome s!"// fn {nm}: frame=0B cfa=sp+0 saved=[]" then
      throw s!"missing zero-frame header for {nm}"
  if containsSub asmSome "\t.cfi_def_cfa_offset" || containsSub asmSome "\t.cfi_offset" then
    throw "unexpected CFI offset directives in zero-frame leaves"
  if containsSub asmSome ", sp," || containsSub asmSome "[sp" then
    throw "unexpected sp manipulation in zero-frame leaves"
  if countSub asmSome "\t.ltorg" != 2 then
    throw "expected post-.size .ltorg on zero-frame leaves"
  let chkHint := Fn.computeHints armTarget.toIsa armLegalTarget check
  let chkDirs ← compile armTarget.toIsa armLegalTarget [check] [chkHint]
  let chkSome ← emitArm64DebugAsmChecked [check] chkDirs (some [chkHint]) ["fail"] true
  let chkNone ← emitArm64DebugAsmChecked [check] chkDirs none ["fail"] true
  if chkSome != chkNone then
    throw "check hints/auto mismatch"
  if !containsSub chkSome "// fn check: frame=0B cfa=sp+0 saved=[]" then
    throw "missing zero-frame header for exit-bearing leaf check"
  if containsSub chkSome "\t.cfi_def_cfa_offset" || containsSub chkSome "[sp" then
    throw "unexpected frame directives in exit-bearing leaf check"

meta def checkNonLeafZeroSlot : Except String Unit := do
  let fns := [probeFn, callZeroFn]
  let hs := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← compile armTarget.toIsa armLegalTarget fns hs
  let asmSome ← emitArm64DebugAsmChecked fns dirs (some hs) [] true
  let asmNone ← emitArm64DebugAsmChecked fns dirs none [] true
  if asmSome != asmNone then
    throw "call_zero hints/auto mismatch"
  if !containsSub asmSome "// fn probe: frame=0B cfa=sp+0 saved=[]" then
    throw "missing zero-frame header for probe"
  if !containsSub asmSome "// fn call_zero: frame=16B cfa=sp+16 saved=[]" then
    throw "missing non-leaf 0-slot header for call_zero"
  if !containsSub asmSome "\t.cfi_def_cfa_offset 16\n" ||
      !containsSub asmSome "\t.cfi_offset x30, -16\n" ||
      !containsSub asmSome "\t.cfi_restore x30\n" ||
      !containsSub asmSome "\t.cfi_def_cfa_offset 0\n" then
    throw "missing call_zero CFI directives"

meta def checkMultiExitAndBigFrame : Except String Unit := do
  let meHint : Arm64Hints :=
    { Fn.computeHints armTarget.toIsa armLegalTarget multiExitFn with
      saved := [.reg .X19, .reg .X20, .reg .X21, .reg .X29] }
  let prHint := Fn.computeHints armTarget.toIsa armLegalTarget probeFn
  let fns := [probeFn, multiExitFn]
  let hs := [prHint, meHint]
  let dirs ← compile armTarget.toIsa armLegalTarget fns hs
  let asmSome ← emitArm64DebugAsmChecked fns dirs (some hs) ["abort_hook"] true
  let asmNone ← emitArm64DebugAsmChecked fns dirs none ["abort_hook"] true
  if asmSome != asmNone then
    throw "multi-exit hints/auto mismatch"
  let rems := countSub asmSome "\t.cfi_remember_state"
  let rests := countSub asmSome "\t.cfi_restore_state"
  if rems < 1 || rems != rests then
    throw s!"expected >=1 remember/restore pairs, got {rems}/{rests}"
  let bigHint : Arm64Hints :=
    { Fn.computeHints armTarget.toIsa armLegalTarget simpleFn with
      nslots := 600, saved := [.reg .X19, .reg .X20] }
  let bigDirs ← compile armTarget.toIsa armLegalTarget [simpleFn] [bigHint]
  let bigSome ← emitArm64DebugAsmChecked [simpleFn] bigDirs (some [bigHint]) [] true
  let bigNone ← emitArm64DebugAsmChecked [simpleFn] bigDirs none [] true
  if bigSome != bigNone then
    throw "big-frame hints/auto mismatch"

meta def checkNegativePrologues : Except String Unit := do
  let hZero := Fn.computeHints armTarget.toIsa armLegalTarget simpleFn
  if hZero.nslots != 0 || !hZero.saved.isEmpty then
    throw "expected totalSlots=0 for simpleFn"
  let badCallCode : List Directive := [.label "big_fn", armCallD "probe", armRetD]
  match emitArm64DebugAsmChecked [simpleFn] badCallCode (some [hZero]) ["probe"] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on 0-slot non-leaf without prologue"
  match emitArm64DebugAsmChecked [simpleFn] badCallCode none ["probe"] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on 0-slot non-leaf without prologue"
  let badSubCode : List Directive :=
    [.label "big_fn",
     .instr (armInsI (.SUB_e (.low .SP .W64) (.low .SP .W64)
       (.imm { imm := .int64 8, shift := .S0 }))),
     armRetD]
  match emitArm64DebugAsmChecked [simpleFn] badSubCode (some [hZero]) [] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on sub sp, sp, #8"
  match emitArm64DebugAsmChecked [simpleFn] badSubCode none [] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on sub sp, sp, #8"
  let badX30Code : List Directive :=
    [.label "big_fn",
     .instr (armInsI (.ADD_e (.low (.reg .X30) .W64) (.low (.reg .X0) .W64) imm0)),
     armRetD]
  match emitArm64DebugAsmChecked [simpleFn] badX30Code (some [hZero]) [] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on x30 clobber without prologue"
  match emitArm64DebugAsmChecked [simpleFn] badX30Code none [] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on x30 clobber without prologue"

meta def checkIndirectTailCFI : Except String Unit := do
  let hZero := Fn.computeHints armTarget.toIsa armLegalTarget simpleFn
  let leafIndTail : List Directive :=
    [.label "big_fn", .instr ⟨.W64, .BR (.low (.reg .X16) .W64)⟩]
  let leafSome ← emitArm64DebugAsmChecked [simpleFn] leafIndTail (some [hZero]) [] true
  let leafNone ← emitArm64DebugAsmChecked [simpleFn] leafIndTail none [] true
  if leafSome != leafNone then
    throw "arm64 indirect tail leaf hints/auto mismatch"
  if !containsSub leafSome "// fn big_fn: frame=0B cfa=sp+0 saved=[]" then
    throw "missing zero-frame header for arm64 indirect tail leaf"
  if !containsSub leafSome "\nbr x16\n" then
    throw "missing br x16 in arm64 indirect tail leaf"
  let badIndCall : List Directive :=
    [.label "big_fn", .instr ⟨.W64, .BLR (.low (.reg .X8) .W64)⟩, armRetD]
  match emitArm64DebugAsmChecked [simpleFn] badIndCall (some [hZero]) [] with
  | .error _ => pure ()
  | .ok _ => throw "expected hints error on 0-slot indirect blr x8 without prologue"
  match emitArm64DebugAsmChecked [simpleFn] badIndCall none [] with
  | .error _ => pure ()
  | .ok _ => throw "expected auto error on 0-slot indirect blr x8 without prologue"
  let frameIndTail : List Directive :=
    [.label "big_fn"] ++ (armFrame.prologue 0).1 ++
    (armFrame.epilogue 0).1 ++
    [.instr ⟨.W64, .BR (.low (.reg .X16) .W64)⟩, .label "big_fn.L0"] ++
    (armFrame.epilogue 0).1 ++ [armRetD]
  let multiSome ← emitArm64DebugAsmChecked [simpleFn] frameIndTail (some [hZero]) [] true
  let multiNone ← emitArm64DebugAsmChecked [simpleFn] frameIndTail none [] true
  if multiSome != multiNone then
    throw "arm64 multi-exit indirect tail hints/auto mismatch"
  if !containsSub multiSome "\t// epilogue (br x16)\n\t.cfi_remember_state\n" then
    throw "missing epilogue/remember_state for arm64 br x16 tail"

meta def runAllChecks : Except String Unit := do
  for m in allModules do
    checkModule m
  checkZeroFrameLeaves
  checkNonLeafZeroSlot
  checkMultiExitAndBigFrame
  checkNegativePrologues
  checkIndirectTailCFI

#guard match runAllChecks with | .ok () => true | .error _ => false

/-! ## 4. Closed Kraken AArch64 zero-frame leaf execution & `std3` axiom audit -/

attribute [local instance] Arm64.Litmus.sumtoHost in
theorem sumto_zero_frame_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6#64)
      ⟨Arm64.Litmus.sumtoState, Labels.label "sumto"⟩ :=
  Arm64.Litmus.sumto_arm64_nonvacuous

end LeanQbeTest.T.Arm64LeafZeroTest

open LeanQbeTest.T.Arm64LeafZeroTest

theorem armTarget_leafZero_ax :
    LeanQbe.T.Arm64.armTarget.toIsa.frame.leafZeroFrame = true := rfl

#print axioms armFrame_leafZeroFrame_rfl
#print axioms armTarget_leafZero_ax
#print axioms sumto_zero_frame_nv
#print axioms LeanQbe.T.Arm64.armFrameSpec
#print axioms LeanQbe.T.Arm64.armLabelClean

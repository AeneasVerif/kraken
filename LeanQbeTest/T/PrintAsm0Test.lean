module

public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Amd64.PrintAsm0Lemmas
public import LeanQbe.T.Amd64.Isa
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLRC.ToT
public import LeanQbe.T.Main
public import LeanQbe.T.Spill
public import Kraken.X64.PrintATT
meta import Lean
meta import LeanQbe.T.Amd64.PrintAsm0
meta import LeanQbe.T.Amd64.PrintAsm0Lemmas
meta import LeanQbe.T.Amd64.Isa
meta import LeanQbe.T.Frontend.C0.Elab
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLRC.ToT
meta import LeanQbe.T.Main
meta import LeanQbe.T.Spill
meta import Kraken.X64.PrintATT

/-!
# Verification Suite for Stage B Minimal AT&T Assembly Printer (`PrintAsm0`)

Verifies `LeanQbe.T.Amd64.PrintAsm0` and `LeanQbe.T.Amd64.PrintAsm0Lemmas`:
1. Kernel `rfl` and `#guard` parity checks across all `27` Stage-A `leanqbe0` operations, all `19`
   `x64ScalarTarget` GPR extras, all `16` GPRs (+ high-byte `ah..dh`) across `W8/W16/W32/W64`,
   all `16` `CondCode`s, all addressing modes, and `Int64` edge values (`0`, `±1`, `INT64_MIN/MAX`).
2. End-to-end compilation of dummy `Frontend.C0.TFlatFn` functions (`dummy_add`, `dummy_sum_to`)
   through `LeanQbe.T.compile x64Isa x64LegalTarget`, verifying `DirSubset0` membership and exact
   bit-for-bit parity with `Kraken.X64.toATT` / `LeanQbe.T.Driver.emitAsm`.
3. `CheckLeanQbe0Clean` LCNF gates on `printAsm0LcMod`: `0` closures (`papTargets = []`,
   `maxAp = 0`), `0` globals (`consts/strs/bigNats = []`), `≤ 80` decls, `Func.checkTFlat`,
   `Module.checkAcyclic = true`, and `< 250` compiled x64 directives per lowered function.
4. Single-line `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) plus MetaM
   `Lean.collectAxioms` and import-closure isolation (`0` `Arm64`/`Kraken.AArch64` imports, `0`
   `IselVec`/`*Lemmas*`/`PrintATT` leaks in `PrintAsm0`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.PrintAsm0Test

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.LeanLCNF
open Kraken.X64

/-! ## 1. Exhaustive Corpus Across All `leanqbe0` & Scalar `x64` Directive Forms -/

abbrev i64Max : Int64 := 9223372036854775807
abbrev i64Min : Int64 := -9223372036854775808

abbrev addrBase0 : AddrExpr := atReg .rax
abbrev addrDispPos : AddrExpr := atDisp .rsp 8
abbrev addrDispNeg : AddrExpr := atDisp .rbp (-16)
abbrev addrSpR10 : AddrExpr := { base := some (.reg .rsp), idx := some ⟨.r10, .W8⟩ }
abbrev addrScaled : AddrExpr :=
  { base := some (.reg .rax), idx := some ⟨.rcx, .W64⟩, disp := .int64 16 }
abbrev addrRipRel : AddrExpr :=
  { base := some .rip, idx := none, disp := .sub (.label "sym") .after_current_instruction }
abbrev addrIdxOnly : AddrExpr :=
  { base := none, idx := some ⟨.rbx, .W32⟩, disp := .int64 0 }
abbrev addrAbs : AddrExpr := { base := none, idx := none, disp := .int64 4096 }

/-- Corpus exercising all `46` scalar operations (`27` Stage-A `leanqbe0` + `19` scalar extras),
all `4` widths, all `16` GPRs + `ah..dh`, all `16` condition codes, addressing modes, and `Int64`
boundary immediates. -/
@[expose] def allFormsProg : List Directive :=
  [ .label "dummy_add"
  , .label ".L_1_0"
  -- Data movement, subregisters, addressing modes, Int64 edge values
  , ins (.mov (.reg (q .rax)) (.reg (q .rdi)))
  , ins (.mov (.reg (q .r8)) (.imm (.int64 0)))
  , ins (.mov (.reg (q .r9)) (.imm (.int64 1)))
  , ins (.mov (.reg (q .r10)) (.imm (.int64 (-1))))
  , ins (.mov (.reg (q .r11)) (.imm (.int64 i64Max)))
  , ins (.mov (.reg (q .r12)) (.imm (.int64 i64Min)))
  , ins32 (.mov (.reg (d .r13)) (.reg (d .r14)))
  , ins16 (.mov (.reg (h16 .r15)) (.reg (h16 .rbx)))
  , ins8 (.mov (.reg (b8 .rsi)) (.reg (b8 .rdi)))
  , ins8 (.mov (.reg (b8 .rsp)) (.reg (b8 .rbp)))
  , ins8 (.mov (.reg .ah) (.reg .bh))
  , ins8 (.mov (.reg .ch) (.reg .dh))
  , ins (.mov (.reg (q .rax)) (.mem addrBase0))
  , ins (.mov (.reg (q .rcx)) (.mem addrDispPos))
  , ins (.mov (.mem addrDispNeg) (.reg (q .rdx)))
  , ins (.mov (.reg (q .rsi)) (.mem addrSpR10))
  , ins (.mov (.mem addrScaled) (.reg (q .r8)))
  , ins (.mov (.reg (q .r9)) (.mem addrRipRel))
  , ins (.mov (.reg (q .r10)) (.mem addrIdxOnly))
  , ins (.mov (.reg (q .r11)) (.mem addrAbs))
  , ins32 (.movzx (.reg (d .rax)) (.reg (b8 .rcx)))
  , ins32 (.movzx (.reg (d .rdx)) (.reg (h16 .rsi)))
  , ins32 (.movzx (.reg (d .rdi)) (.mem addrBase0 : RegOrMem .W8))
  , ins32 (.movzx (.reg (d .r8)) (.mem addrDispPos : RegOrMem .W16))
  , ins (.movsx (.reg (q .rax)) (.reg (b8 .r9)))
  , ins (.movsx (.reg (q .rbx)) (.reg (h16 .r10)))
  , ins (.movsx (.reg (q .rcx)) (.reg (d .r11)))
  , ins32 (.movsx (.reg (d .rdx)) (.mem addrBase0 : RegOrMem .W8))
  , ins (.movsx (.reg (q .rsi)) (.mem addrDispPos : RegOrMem .W32))
  , ins (.lea (q .rdi) addrScaled)
  -- Basic ALU, cmp, test, unary, imul
  , ins (.add (.reg (q .rax)) (.reg (q .rsi)))
  , ins (.add (.reg (q .rsp)) (.imm (.int64 16)))
  , ins (.sub (.reg (q .rsp)) (.imm (.int64 16)))
  , ins32 (.and (.reg (d .rcx)) (.imm (.int64 31)))
  , ins16 (.or (.reg (h16 .r12)) (.reg (h16 .r13)))
  , ins8 (.xor (.reg (b8 .r14)) (.reg (b8 .r15)))
  , ins (.cmp (.reg (q .rdi)) (.reg (q .rsi)))
  , ins8 (.test (.reg (b8 .rax)) (.reg (b8 .rax)))
  , ins (.neg (.reg (q .rbx)))
  , ins32 (.not (.reg (d .rcx)))
  , ins (.imul none (.reg (q .rdx)) (.reg (q .rsi)))
  -- Mul/div/carry/inc/dec
  , ins (.mul (.reg (q .r8)))
  , ins (.div (.reg (q .r9)))
  , ins (.idiv (.reg (q .r10)))
  , ins (.imul1 (.reg (q .r11)))
  , ins (.mulx (q .rdx) (q .rax) (.reg (q .rcx)))
  , ins (.adc (.reg (q .rax)) (.reg (q .rbx)))
  , ins (.sbb (.reg (q .rcx)) (.imm (.int64 1)))
  , ins (.adcx (q .rdx) (.reg (q .rsi)))
  , ins (.adox (q .rdi) (.reg (q .r8)))
  , ins (.inc (.reg (q .r9)))
  , ins32 (.dec (.reg (d .r10)))
  -- Shifts, rotates, funnel shifts
  , ins (.shl (.reg (q .rax)) .cl)
  , ins32 (.shr (.reg (d .rbx)) (.imm8 (.int64 4)))
  , ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63)))
  , ins16 (.rol (.reg (h16 .rcx)) (.imm8 (.int64 8)))
  , ins8 (.ror (.reg (b8 .rdx)) .cl)
  , ins (.shld (.reg (q .rax)) (q .rbx) (.imm8 (.int64 12)))
  , ins32 (.shrd (.reg (d .rcx)) (d .rdx) .cl)
  -- Bitcnt, bswap, BMI2
  , ins (.bswap (q .rax))
  , ins32 (.bswap (d .r8))
  , ins (.lzcnt (q .rax) (.reg (q .rbx)))
  , ins32 (.tzcnt (d .rcx) (.reg (d .rdx)))
  , ins (.popcnt (q .rsi) (.reg (q .rdi)))
  , ins (.shlx (q .r8) (.reg (q .r9)) (q .r10))
  , ins32 (.shrx (d .r11) (.reg (d .r12)) (d .r13))
  , ins (.sarx (q .r14) (.reg (q .r15)) (q .rax))
  , ins (.rorx (q .rbx) (.reg (q .rcx)) (.int64 7))
  -- All 16 condition codes via setcc, cmovcc, jcc
  , ins8 (.setcc .o (.reg (b8 .rax)))
  , ins8 (.setcc .no (.reg (b8 .rbx)))
  , ins8 (.setcc .c (.reg (b8 .rcx)))
  , ins8 (.setcc .nc (.reg (b8 .rdx)))
  , ins8 (.setcc .z (.reg (b8 .rsi)))
  , ins8 (.setcc .nz (.reg (b8 .rdi)))
  , ins8 (.setcc .be (.reg (b8 .r8)))
  , ins8 (.setcc .a (.reg (b8 .r9)))
  , ins8 (.setcc .s (.reg (b8 .r10)))
  , ins8 (.setcc .ns (.reg (b8 .r11)))
  , ins8 (.setcc .p (.reg (b8 .r12)))
  , ins8 (.setcc .np (.reg (b8 .r13)))
  , ins8 (.setcc .l (.reg (b8 .r14)))
  , ins8 (.setcc .ge (.reg (b8 .r15)))
  , ins (.cmovcc .le (q .rax) (.reg (q .rbx)))
  , ins (.cmovcc .g (q .rcx) (.reg (q .rdx)))
  , ins (.jcc .c ".L_1_0")
  , ins (.jcc .nc ".L_1_0")
  , ins (.jcc .z ".L_1_0")
  , ins (.jcc .nz ".L_1_0")
  -- Control flow targets
  , x64JmpD ".L_1_0"
  , ins (.jmp (.reg (q .rax)))
  , ins (.jmp (.mem addrDispPos))
  , x64CallD "dummy_add"
  , ins (.call (.reg (q .rax)))
  , ins (.call (.mem addrDispPos))
  , x64RetD ]

/-- Kernel `rfl` check: every directive in `allFormsProg` lies in `DirSubset0`. -/
theorem allFormsProg_dirSubset0_rfl : allFormsProg.all isDir0 = true := rfl

/-- Kernel `rfl` check on `INT64_MIN` decimal serialization (`-9223372036854775808`). -/
theorem printAmd64Asm0_i64Min_rfl :
    printAmd64Asm0NoTrail [ins (.mov (.reg (q .rax)) (.imm (.int64 i64Min)))] =
      "movq $-9223372036854775808, %rax".toUTF8 := rfl

/-- Kernel `rfl` check on `movzbl (%rax), %eax` (`.mem` source suffixing & `disp = 0` omission). -/
theorem printAmd64Asm0_movzbl_rfl :
    printAmd64Asm0NoTrail [ins32 (.movzx (.reg (d .rax)) (.mem addrBase0 : RegOrMem .W8))] =
      "movzbl (%rax), %eax".toUTF8 := rfl

/-- Kernel `rfl` check on indexed stack slot `movq (%rsp,%r10,1), %r15`. -/
theorem printAmd64Asm0_slotIdx_rfl :
    printAmd64Asm0NoTrail [ins (.mov (.reg (q .r15)) (.mem addrSpR10))] =
      "movq (%rsp,%r10,1), %r15".toUTF8 := rfl

/-- Kernel `rfl` check on `movsx %eax, %rax` (`.reg` source unsuffixed form). -/
theorem printAmd64Asm0_movsx_reg_rfl :
    printAmd64Asm0NoTrail [ins (.movsx (.reg (q .rax)) (.reg (d .rax)))] =
      "movsx %eax, %rax".toUTF8 := rfl

/-- Kernel `rfl` check on `call *%rax` indirect register target. -/
theorem printAmd64Asm0_callInd_rfl :
    printAmd64Asm0NoTrail [ins (.call (.reg (q .rax)))] = "call *%rax".toUTF8 := rfl

#guard printAsm0
    [ins (.call (.reg (q .rax))), ins (.call (.mem addrDispPos)),
     ins (.jmp (.reg (q .r11))), ins (.jmp (.mem addrBase0))] ==
  "call *%rax\ncall *8(%rsp)\njmp *%r11\njmp *(%rax)"

/-- Kernel `rfl` check on minimal `.text\nret\n` emission through `printDir0Asm0`. -/
theorem printDir0Asm0_minimal_rfl :
    printDir0Asm0 [] [x64RetD] = ".text\nret\n".toUTF8 := rfl

#guard printDir0Asm0 ["f0"] [.label "f0", x64RetD] == ".text\n.globl f0\nf0:\nret\n".toUTF8

#guard allFormsProg.all isDir0
#guard printAsm0 allFormsProg == Kraken.X64.toATT allFormsProg
#guard printAmd64Asm0 allFormsProg == (Kraken.X64.toATT allFormsProg ++ "\n").toUTF8
#guard printAmd64Asm0NoTrail allFormsProg == (Kraken.X64.toATT allFormsProg).toUTF8
#guard printModule0 ["dummy_add", "dummy_sum_to"] allFormsProg ==
  ".text\n.globl dummy_add\n.globl dummy_sum_to\n" ++ Kraken.X64.toATT allFormsProg ++ "\n"
#guard printAsm0 [] == ""
#guard printAmd64Asm0 [] == ByteArray.empty
#guard printDir0Asm0 [] [] == ".text\n".toUTF8

/-! ## 2. Dummy `TFlatFn` End-to-End Compilation & `PrintAsm0` Emission -/

/-- Dummy `Frontend.C0.TFlatFn`: `dummy_add(a, b) = a + b`. -/
@[expose] def dummyAddTFlatFn : Frontend.C0.TFlatFn where
  name := "dummy_add"
  as := [i64, i64]
  rs := [i64]
  flat :=
    .let_ { code := .add i64, args := (.var 1, .var 0, ()) }
      (.ret (.var 0, ()))

/-- Dummy `Frontend.C0.TFlatFn`: `dummy_sum_to(n) = 0 + 1 + ... + (n - 1)` via `.group` loop. -/
@[expose] def dummySumToTFlatFn : Frontend.C0.TFlatFn where
  name := "dummy_sum_to"
  as := [i64]
  rs := [i64]
  flat :=
    let loopBody : TFlat [i64] :=
      -- var 0 = acc, var 1 = i, var 2 = n
      .let_ { code := .cmp .ult i64, args := (.var 1, .var 2, ()) }
        (.jnz (.var 0)
          (.let_ { code := .add i64, args := (.var 1, .var 2, ()) }
            (.let_ { code := .add i64, args := (.var 3, .imm 1#64, ()) }
              (.jump (ts := [i64, i64]) 0 (.var 0, .var 1, ()))))
          (.ret (.var 1, ())))
    .group (sig := [[i64, i64]]) (.cons loopBody .nil)
      (.jump (ts := [i64, i64]) 0 (.imm 0#64, .imm 0#64, ()))

/-- Reified dummy `Fn` module (`dummy_add` + `dummy_sum_to`). -/
def dummyFns : List Fn :=
  [dummyAddTFlatFn.toFn, dummySumToTFlatFn.toFn]

/-- Compiled x86-64 directives for `dummyFns` via `LeanQbe.T.compile x64Isa x64LegalTarget`. -/
def dummyCompiledDirs : Except String (List Directive) :=
  let hints := dummyFns.map fun f => Spill.hints x64Isa (f.mid x64LegalTarget)
  compile x64Isa x64LegalTarget dummyFns hints

/-- AT&T `.s` module emitted by `printModule0` on `dummyFns`. -/
def dummyModAsm : Except String String :=
  dummyCompiledDirs.map fun dirs => printModule0 (dummyFns.map (·.name)) dirs

#guard dummyAddTFlatFn.flat.wfCheck (pushTypes dummyAddTFlatFn.as []) []
#guard dummySumToTFlatFn.flat.wfCheck (pushTypes dummySumToTFlatFn.as []) []
#guard match dummyCompiledDirs with
  | .ok dirs =>
    !dirs.isEmpty &&
    dirs.all isDir0 &&
    printModule0 (dummyFns.map (·.name)) dirs ==
      LeanQbe.T.Driver.emitAsm (I := x64Isa) (fun code => Kraken.X64.toATT code ++ "\n")
        dummyFns dirs
  | .error _ => false

/-! ## 3. `CheckLeanQbe0Clean` LCNF Verification Gate on `printAsm0LcMod` -/

private def topoSortDecls (ds : List LcDecl) : List LcDecl :=
  let rec go (fuel : Nat) (rem acc : List LcDecl) : List LcDecl :=
    match fuel with
    | 0 => acc ++ rem
    | fuel' + 1 =>
      let known := acc.map (·.name)
      let (ready, rest) := rem.partition fun d =>
        d.body.refs.1.all fun c => c == d.name || known.contains c || !rem.any (·.name == c)
      if ready.isEmpty then acc ++ rem
      else go fuel' rest (acc ++ ready)
  go (ds.length + 1) ds []

private def printAsm0GlobalsCount : Nat :=
  let consts := printAsm0LcMod.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar
  let allLits := printAsm0LcMod.decls.map (·.body.lits)
  let strs := dedupStr (allLits.flatMap (·.1))
  let bigNats := dedupNat (allLits.flatMap (·.2))
  consts.length + strs.length + bigNats.length

private def printAsm0Lowered : Except String (List Frontend.C0.TFlatFn) :=
  lowerModule { printAsm0LcMod with decls := topoSortDecls printAsm0LcMod.decls }

private def printAsm0MaxCompiledDirs : Except String Nat := do
  let tfs ← printAsm0Lowered
  let fns := LeanLRC.tflatFnsToFns tfs
  let mut maxD := 0
  for f in fns do
    let h := Spill.hints x64Isa (f.mid x64LegalTarget)
    let dirs ← compile x64Isa x64LegalTarget [f] [h]
    if dirs.length > maxD then maxD := dirs.length
  pure maxD

#guard printAsm0LcMod.papTargets.isEmpty
#guard printAsm0LcMod.maxAp == 0
#guard printAsm0GlobalsCount == 0
#guard printAsm0LcMod.decls.length <= 80
#guard match printAsm0Lowered with
  | .ok tfs =>
    let fns := LeanLRC.tflatFnsToFns tfs
    let mod : Module := { fns, externs := rtExterns, exits := rtExitSyms }
    fns.length <= 80 && fns.all (fun f => Func.checkTFlat f.body) && mod.checkAcyclic
  | .error _ => false
#guard match printAsm0MaxCompiledDirs with
  | .ok maxD => maxD < 250
  | .error _ => false

/-! ## 4. `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Amd64.emitDir0_eq
#print axioms LeanQbe.T.Amd64.printAmd64Asm0_eq_toATT
#print axioms LeanQbe.T.Amd64.printAmd64Asm0NoTrail_eq_toATT
#print axioms LeanQbe.T.Amd64.printAsm0_eq_toATT
#print axioms LeanQbe.T.Amd64.printDir0Asm0_eq_emitAsm
#print axioms LeanQbe.T.Amd64.printModule0_eq_toATT
#print axioms LeanQbe.T.Amd64.printModule0_eq_driver_emitAsm

/-! ## 5. MetaM `collectAxioms` & Import-Closure Isolation Assertions -/

meta section

open Lean

private def allowedStdAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private def isForbiddenArchMod (m : Name) : Bool :=
  let s := m.toString
  (s.splitOn "Arm64").length > 1 || s.startsWith "Kraken.AArch64"

private def isForbiddenPrintAsm0Mod (m : Name) : Bool :=
  let s := m.toString
  isForbiddenArchMod m ||
  (s.splitOn "IselVec").length > 1 ||
  ((s.startsWith "LeanQbe." || s.startsWith "Kraken.") &&
    (s.splitOn "Lemmas").length > 1) ||
  s == "Kraken.X64.PrintATT" ||
  s == "Kraken.X64.PrintIntel"

#eval show MetaM Unit from do
  -- 1. Import-closure isolation on `PrintAsm0` and `PrintAsm0Lemmas`.
  let env0 ← importModules #[{ module := `LeanQbe.T.Amd64.PrintAsm0 }] {}
  let mods0 := env0.header.moduleNames
  let bad0 := mods0.filter isForbiddenPrintAsm0Mod
  if !bad0.isEmpty then
    throwError "PrintAsm0 import closure contains forbidden modules: {bad0.toList}"
  let envL ← importModules #[{ module := `LeanQbe.T.Amd64.PrintAsm0Lemmas }] {}
  let modsL := envL.header.moduleNames
  let badL := modsL.filter isForbiddenArchMod
  if !badL.isEmpty then
    throwError "PrintAsm0Lemmas import closure contains Arm64/AArch64 modules: {badL.toList}"
  let testBad := (← getEnv).header.moduleNames.filter isForbiddenArchMod
  if !testBad.isEmpty then
    throwError "PrintAsm0Test import closure contains Arm64/AArch64 modules: {testBad.toList}"
  -- 2. `collectAxioms` across all headline theorems and public `PrintAsm0` definitions.
  let targets : List Name :=
    [ ``LeanQbe.T.Amd64.emitDir0
    , ``LeanQbe.T.Amd64.printAmd64Asm0
    , ``LeanQbe.T.Amd64.printAmd64Asm0NoTrail
    , ``LeanQbe.T.Amd64.printDir0Asm0
    , ``LeanQbe.T.Amd64.printAsm0
    , ``LeanQbe.T.Amd64.printModule0
    , ``LeanQbe.T.Amd64.emitDir0_eq
    , ``LeanQbe.T.Amd64.printAmd64Asm0_eq_toATT
    , ``LeanQbe.T.Amd64.printAmd64Asm0NoTrail_eq_toATT
    , ``LeanQbe.T.Amd64.printAsm0_eq_toATT
    , ``LeanQbe.T.Amd64.printDir0Asm0_eq_emitAsm
    , ``LeanQbe.T.Amd64.printModule0_eq_toATT
    , ``LeanQbe.T.Amd64.printModule0_eq_driver_emitAsm
    ]
  for nm in targets do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then
      throwError "Declaration {nm} depends on disallowed axioms: {badAx.toList}"

end

end LeanQbeTest.T.PrintAsm0Test

module

public import LeanQbe.T.Bootstrap0.PrintDir0
public import LeanQbe.T.Bootstrap0.PrintDir0Lemmas
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbe.T.Bootstrap0.Dummies0
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Amd64.PrintAsm0
public import Kraken.X64.PrintATT
public import LeanQbeBootstrap0Test.Bootstrap0CleanTest
meta import Lean
meta import LeanQbe.T.Bootstrap0.PrintDir0
meta import LeanQbe.T.Bootstrap0.PrintDir0Lemmas
meta import LeanQbe.T.Bootstrap0.Bridge0
meta import LeanQbe.T.Bootstrap0.Compiler0
meta import LeanQbe.T.Bootstrap0.Dummies0
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Amd64.Targ
meta import Kraken.X64.PrintATT
meta import LeanQbeBootstrap0Test.Bootstrap0CleanTest

/-!
# Verification Suite for Closure-Free `Dir0 → ByteArray` Printer (`PrintDir0`)

Verifies `LeanQbe.T.Bootstrap0.PrintDir0` and `LeanQbe.T.Bootstrap0.PrintDir0Lemmas`:
1. `printDir0LcMod` passes the strict `leanqbe0` LCNF gate: `0` closures, `0` globals, `0` `_boxed`
   wrappers, `params.length ≤ 5`, `checkTFlat`, `checkAcyclic`, and `≤ 260` directives/fn.
2. Concrete round-trip `#guard`s across ALL `27` `Dir0` constructors and compiled dummy modules.
3. Single-line `#print axioms` plus MetaM import-closure isolation, `collectAxioms`, and `0`
   opaque/unsafe checks.
-/

set_option autoImplicit false

public section

namespace LeanQbeBootstrap0Test.PrintDir0Test

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0
open LeanQbeBootstrap0Test.Bootstrap0CleanTest

/-! ## 1. Strict `leanqbe0` LCNF & `Compiler0.leanqbe0Compile` Gate -/

private def topoSortDecls (ds : List LcDecl) : List LcDecl :=
  let rec go (fuel : Nat) (rem acc : List LcDecl) : List LcDecl :=
    match fuel with
    | 0 => acc ++ rem
    | fuel' + 1 =>
      let known := acc.map (·.name)
      let (ready, rest) := rem.partition fun d =>
        d.body.refs.1.all fun c => c == d.name || known.contains c || !rem.any (·.name == c)
      if ready.isEmpty then acc ++ rem else go fuel' rest (acc ++ ready)
  go (ds.length + 1) ds []

private def printDir0Lowered : Except String (List Frontend.C0.TFlatFn) :=
  lowerModule { printDir0LcMod with decls := topoSortDecls printDir0LcMod.decls }

private def checkLeanqbe0Gate : Except String (Nat × Nat) := do
  let tfs ← printDir0Lowered
  let (m0, tbl) ← ofTFlatModule tfs
  match leanqbe0Compile m0 with
  | .err ec fn => throw s!"leanqbe0Compile whole err {ec} at {fn}"
  | .ok _ _ =>
    let allExt : List ExtSig0 :=
      m0.externs ++ m0.fns.map fun f => { name := f.name, as := f.as, rs := f.rs }
    let mut maxD := 0
    for fn0 in m0.fns do
      let otherExts := allExt.filter fun e => e.name != fn0.name
      match leanqbe0Compile { fns := [fn0], externs := otherExts, exits := m0.exits } with
      | .err ec fi => throw s!"leanqbe0Compile single err {ec} at {symNameOf tbl fn0.name} ({fi})"
      | .ok dirs _ => maxD := Nat.max maxD dirs.length
    pure (m0.fns.length, maxD)

#guard printDir0LcMod.papTargets.isEmpty && printDir0LcMod.maxAp == 0 &&
  lcGlobalsCount printDir0LcMod == 0 &&
  (printDir0LcMod.decls.all fun d => !d.name.endsWith "_boxed" && d.params.length <= 5)
#guard match printDir0Lowered with
  | .ok tfs =>
    let fns := LeanLRC.tflatFnsToFns tfs
    let mod : Module := { fns, externs := rtExterns, exits := rtExitSyms }
    fns.length == printDir0LcMod.decls.length &&
      fns.all (fun f => Func.checkTFlat f.body) && mod.checkAcyclic
  | .error _ => false
#guard match checkLeanqbe0Gate with | .ok (n, maxD) => n == 54 && maxD <= 260 | .error _ => false

/-! ## 2. Concrete Round-Trip `#guard`s Across All `27` `Dir0` Constructors -/

private def testNames : List String := ["fn_main", "helper_0", "abort_panic", "l_ext_foo"]

private def testSymTab : ByteArray × Array Nat :=
  testNames.foldl (fun (bytes, offs) nm =>
    let bs := nm.toUTF8
    (bytes ++ bs, (offs.push bytes.size).push bs.size)) (ByteArray.empty, #[])

private def testSymName (s : Sym0) : Sym := testNames.getD s.toNat s!"sym_{s.toNat}"

private def dir0MatchesATT (d : Dir0) : Bool :=
  printDir0Bytes testSymTab.1 testSymTab.2 d ByteArray.empty ==
    (Kraken.X64.toATT (dir0ToAmd64 testSymName d)).toUTF8

/-- Corpus covering ALL `27` `Dir0` constructors and edge variants. -/
def all27Dir0Corpus : List Dir0 :=
  [ .label (.sym 0), .label (.loc 12 34),
    .movRR .W8 .rax .rcx, .movRR .W16 .rdx .rbx, .movRR .W32 .r8 .r9, .movRR .W64 .rdi .rsi,
    .movRI .rax 0, .movRI .r8 42, .movRI .r9 0x100000000, .movRI .r10 0x8000000000000000,
    .movzx32 .W8 .rax .rcx, .movzx32 .W16 .rdx .rsi,
    .movzx32 .W32 .r8 .r9, .movzx32 .W64 .r10 .r11,
    .movsx .W64 .rax .W8 .r12, .movsx .W64 .rbx .W16 .r13, .movsx .W64 .rcx .W32 .r14,
    .movsx .W64 .rdx .W64 .r15, .movsx .W32 .rsi .W8 .rdi, .movsx .W32 .rbp .W16 .rax,
    .movsx .W32 .r8 .W32 .r9, .movsx .W16 .r10 .W8 .r11,
    .ldMem .W8 .rax .rdi, .ldMem .W16 .rcx .rsi, .ldMem .W32 .rdx .r8, .ldMem .W64 .r9 .rsp,
    .stMem .W8 .rdi .rax, .stMem .W16 .rsi .rcx, .stMem .W32 .r8 .rdx, .stMem .W64 .rbp .r15,
    .ldSlot .rax 0, .ldSlot .r11 24, .stSlot 0 .rcx, .stSlot 40 .r12,
    .ldSlotIdx .r15 .r10, .stSlotIdx .r10 .r14,
    .spAdd true 16, .spAdd false 24, .spAddReg true .r10, .spAddReg false .r11,
    .aluRR .W64 .add .rax .rdi, .aluRR .W32 .sub .rcx .rsi, .aluRR .W8 .mul .rdx .rbx,
    .aluRR .W16 .and .r8 .r9, .aluRR .W64 .or .r10 .r11, .aluRR .W32 .xor .r12 .r13,
    .unary .W64 true .rax, .unary .W32 false .r8,
    .shiftCl .W8 .shl .rax, .shiftCl .W16 .lshr .rbx, .shiftCl .W32 .ashr .r8,
    .shiftCl .W64 .rotl .r9, .shiftCl .W64 .rotr .r10, .shMaskCl 63,
    .cmpRR .W64 .rdi .rsi, .cmpRR .W8 .rax .rdx, .testbRR .rax .rax,
    .setcc .z .rax, .setcc .l .r15, .cmovcc .W64 .nz .rax .rbx, .cmovcc .W32 .ge .r8 .r9,
    .divCore .W64 true .rcx, .divCore .W64 false .r8, .divCore .W32 true .rsi,
    .divCore .W32 false .r9, .divCore .W16 true .rbx, .divCore .W8 false .rdi,
    .mulq .r11, .jmp (.sym 1), .jmp (.loc 3 7),
    .jcc .nz (.sym 2), .jcc .be (.loc 5 9), .callSym 3, .ret ]

#guard all27Dir0Corpus.all dir0MatchesATT &&
  printDirs0Bytes testSymTab.1 testSymTab.2 all27Dir0Corpus ByteArray.empty ==
    (Kraken.X64.toATT (toAmd64Program testSymName all27Dir0Corpus)).toUTF8 &&
  printDirs0LinesBytes testSymTab.1 testSymTab.2 all27Dir0Corpus ByteArray.empty ==
    (Kraken.X64.toATT (toAmd64Program testSymName all27Dir0Corpus) ++ "\n").toUTF8 &&
  printModule0Bytes testSymTab.1 testSymTab.2 [0, 1] all27Dir0Corpus ==
    printDir0Asm0 [testSymName 0, testSymName 1] (toAmd64Program testSymName all27Dir0Corpus) &&
  printDirs0Bytes testSymTab.1 testSymTab.2 [] ByteArray.empty == ByteArray.empty &&
  printModule0Bytes testSymTab.1 testSymTab.2 [] [] == ".text\n".toUTF8

private def compiledModMatchesATT (m : TFlatModule0) : Bool :=
  match leanqbe0Compile m with
  | .ok dirs _ =>
    let symNs := [0, 1, 2]
    printModule0Bytes testSymTab.1 testSymTab.2 symNs dirs ==
      printDir0Asm0 (symNs.map testSymName) (toAmd64Program testSymName dirs)
  | .err _ _ => false

#guard [dummyAddMod0, dummyLoopMod0, dummyCallTailMod0].all compiledModMatchesATT

/-! ## 3. Single-Line `#print axioms` Audit (`[propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Bootstrap0.dir0ToAmd64_dirSubset0
#print axioms LeanQbe.T.Bootstrap0.printDir0Bytes_eq_toATT
#print axioms LeanQbe.T.Bootstrap0.printDir0Bytes_eq_printAsm0
#print axioms LeanQbe.T.Bootstrap0.printDirs0Bytes_eq_toATT
#print axioms LeanQbe.T.Bootstrap0.printDirs0LinesBytes_eq_toATT
#print axioms LeanQbe.T.Bootstrap0.printGlobl0Bytes_eq
#print axioms LeanQbe.T.Bootstrap0.printModule0Bytes_eq_toATT

/-! ## 4. MetaM Isolation, `collectAxioms`, Opaque/Unsafe, & LCNF Gate Diagnostics -/

meta section

open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

private def isForbiddenArchMod (m : Name) : Bool :=
  let s := m.toString
  (s.splitOn "Arm64").length > 1 || s.startsWith "Kraken.AArch64"

private def isForbiddenPrintDir0Mod (m : Name) : Bool :=
  let s := m.toString
  isForbiddenArchMod m || (s.splitOn "IselVec").length > 1 ||
  ((s.startsWith "LeanQbe." || s.startsWith "Kraken.") && (s.splitOn "Lemmas").length > 1) ||
  s == "Kraken.X64.PrintATT" || s == "Kraken.X64.PrintIntel"

private def checkForbiddenImports (env : Environment) (pred : Name → Bool) (msg : String) :
    MetaM Unit := do
  let bad := env.header.moduleNames.filter pred
  if !bad.isEmpty then throwError "{msg}: {bad.toList}"

#eval show MetaM Unit from do
  checkForbiddenImports (← importModules #[{ module := `LeanQbe.T.Bootstrap0.PrintDir0 }] {})
    isForbiddenPrintDir0Mod "PrintDir0 import closure contains forbidden modules"
  checkForbiddenImports
    (← importModules #[{ module := `LeanQbe.T.Bootstrap0.PrintDir0Lemmas }] {})
    isForbiddenArchMod "PrintDir0Lemmas import closure contains Arm64/AArch64 modules"
  let env ← getEnv
  checkForbiddenImports env isForbiddenArchMod
    "PrintDir0Test import closure contains Arm64/AArch64 modules"
  let targets : List Name :=
    [ ``LeanQbe.T.Bootstrap0.printDir0Bytes, ``LeanQbe.T.Bootstrap0.printDirs0Bytes
    , ``LeanQbe.T.Bootstrap0.printDirs0LinesBytes, ``LeanQbe.T.Bootstrap0.printGlobl0Bytes
    , ``LeanQbe.T.Bootstrap0.printModule0Bytes, ``LeanQbe.T.Bootstrap0.dir0ToAmd64_dirSubset0
    , ``LeanQbe.T.Bootstrap0.printDir0Bytes_eq_toATT
    , ``LeanQbe.T.Bootstrap0.printDir0Bytes_eq_printAsm0
    , ``LeanQbe.T.Bootstrap0.printDirs0Bytes_eq_toATT
    , ``LeanQbe.T.Bootstrap0.printDirs0LinesBytes_eq_toATT
    , ``LeanQbe.T.Bootstrap0.printGlobl0Bytes_eq
    , ``LeanQbe.T.Bootstrap0.printModule0Bytes_eq_toATT ]
  for nm in targets do
    let badAx := (← Lean.collectAxioms nm).filter (!allowedStdAxioms.contains ·)
    if !badAx.isEmpty then
      throwError "Declaration {nm} depends on disallowed axioms: {badAx.toList}"
    match env.find? nm with
    | some (.opaqueInfo _) => throwError "Declaration {nm} is opaque"
    | some ci => if ci.isUnsafe then throwError "Declaration {nm} is unsafe"
    | none => throwError "Missing declaration {nm}"
  match checkLeanqbe0Gate with
  | .ok (nFns, maxD) =>
    let g := lcGlobalsCount printDir0LcMod
    IO.println s!"PrintDir0 LCNF gate PASS: fns={nFns} maxDirs={maxD} globals={g}"
  | .error e => throwError "LCNF gate fail: {e}"

end

end LeanQbeBootstrap0Test.PrintDir0Test

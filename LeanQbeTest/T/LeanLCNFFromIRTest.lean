module

import LeanQbe.T.LeanLCNF.FromIR
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.FlatLemmas
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
meta import Lean
meta import LeanQbe.T.LeanLCNF.FromIR
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLCNF.Demo
meta import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.Driver
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Cross-Module `Lean.IR` → `LcModule` Extractor Tests (`LeanQbe.T.LeanLCNF.FromIR`)

* Kernel `lcnf_ir_of_lean!` splicing of a small cross-module closure (`Demo.rbBench`,
  `Demo.sortBench`, `Demo.usizeSum`), lowering via `lowerModule`, `Func.checkTFlat`, `PrintCpp`,
  `PrintQbe`, and formal `Func.Wf` proof (`ir_demo_wf`) with `#print axioms` (standard axioms).
* Live cross-module IR extraction via `extractIRClosure` and `readLcModuleIR` across:
  - multi-module `Demo` + `Coverage` closures (`0` missing, `0` opaque, `0` conversion errors);
  - full compiler core `LeanQbe.T.compile` (`2,000+` decls, `0` missing, `0` conversion errors);
  - full driver entry `LeanQbe.T.Driver.main` (`4,000+` decls, `0` missing, `0` conversion errors).
* Negative tests verifying clean `Except.error` reporting on missing decls, opaque stubs, and
  unsupported `Lean.IR.IRType`s (`float32`, `struct`, `union`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LeanLCNFFromIRTest

open LeanQbe.T hiding TFlatFn
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## 1. Small Cross-Module Closure Splicing, Lowering, and `Func.Wf` -/

lcnf_ir_of_lean! irSmallMod
  [LeanQbe.T.LeanLCNF.Demo.rbBench,
   LeanQbe.T.LeanLCNF.Demo.sortBench,
   LeanQbe.T.LeanLCNF.Demo.usizeSum]

def irSmallTfs : List TFlatFn :=
  (lowerModule irSmallMod).toOption.getD []

def irSmallFns : List Fn :=
  Frontend.C0.tflatFnsToFns irSmallTfs

theorem ir_demo_wf : ∀ f ∈ irSmallFns, f.Wf :=
  Frontend.C0.tflatFnsToFns_wf irSmallTfs

#guard irSmallMod.decls.length ≥ 60
#guard irSmallMod.snaps.isEmpty
#guard (irSmallMod.decls.map (·.name)).contains "LeanQbe.T.LeanLCNF.Demo.rbBench"
#guard (irSmallMod.decls.map (·.name)).contains "USize.add._boxed"
#guard !irSmallMod.papTargets.isEmpty
#guard (lowerModule irSmallMod).isOk
#guard !irSmallFns.isEmpty
#guard irSmallFns.all fun f => Func.checkTFlat f.body
#guard (PrintCpp.ppTModule (lcnfTModule irSmallTfs)).isOk
#guard (PrintQbe.module (lcnfTModule irSmallTfs)).isOk

#print axioms ir_demo_wf

/-! ## 2. Cross-Module `LeanQbe.T` Compiler Closure & Error Tests -/

meta section

open Lean

private def checkErrContains {α : Type} (label : String) (r : Except String α) (needle : String) :
    IO Unit := do
  match r with
  | .ok _ => throw <| IO.userError s!"{label}: expected error containing '{needle}', got ok"
  | .error msg =>
    if !msg.contains needle then
      throw <| IO.userError s!"{label}: error '{msg}' does not contain '{needle}'"

private def allNamesUnique (m : LcModule) : Bool :=
  let s := m.decls.foldl (fun acc d => acc.insert d.name) ({} : Std.HashSet String)
  s.size == m.decls.length

private def declModules (env : Environment) (cls : IRClosure) : Std.HashSet String :=
  cls.fdecls.foldl (init := {}) fun acc d =>
    match env.getModuleIdxFor? d.name with
    | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some modNm => acc.insert modNm.toString
      | none => acc
    | none => acc

private def checkClosure (env : Environment) (label : String) (roots : List Name)
    (minDecls minMods : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let cls ← IO.ofExcept (extractIRClosure env roots)
  if !cls.missing.isEmpty then
    throw <| IO.userError s!"{label}: {cls.missing.size} missing decls"
  if !cls.opaqueStubs.isEmpty then
    throw <| IO.userError s!"{label}: {cls.opaqueStubs.size} opaque stubs"
  let m ← IO.ofExcept (irClosureToLcModule label cls)
  let t1 ← IO.monoMsNow
  let mods := declModules env cls
  if m.decls.length != cls.fdecls.size || m.externs.length != cls.externs.size then
    throw <| IO.userError s!"{label}: decl/extern count mismatch"
  if m.decls.length < minDecls then
    throw <| IO.userError s!"{label}: expected >= {minDecls} decls, got {m.decls.length}"
  if mods.size < minMods then
    throw <| IO.userError s!"{label}: expected >= {minMods} modules, got {mods.size}"
  if !m.snaps.isEmpty || !allNamesUnique m then
    throw <| IO.userError s!"{label}: snaps non-empty or duplicate decl names"
  if !mods.toList.any (·.startsWith "Init.") then
    throw <| IO.userError s!"{label}: expected Init.* module in cross-module closure"
  IO.println <|
    s!"[FromIR] {label}: decls={m.decls.length} exts={m.externs.length} " ++
    s!"mods={mods.size} ({t1 - t0} ms)"

private def runFromIRChecks (env : Environment) : IO Unit := do
  checkClosure env "demo_cov"
    [``LeanQbe.T.LeanLCNF.Demo.rbBench, ``LeanQbe.T.LeanLCNF.Coverage.floatBench] 100 3
  checkClosure env "compile" [``LeanQbe.T.compile] 2000 30
  checkClosure env "driver_main" [``LeanQbe.T.Driver.main] 4000 40
  let mCompile ← IO.ofExcept (readLcModuleIR env "compile" [``LeanQbe.T.compile])
  if !mCompile.decls.any (fun d => d.name == "LeanQbe.T.compile") then
    throw <| IO.userError "compile module missing root LeanQbe.T.compile"
  if mCompile.papTargets.isEmpty then
    throw <| IO.userError "compile module expected non-empty papTargets"
  -- Error-reporting checks
  checkErrContains "missing" (readLcModuleIR env "bad" [`LeanQbe.NoSuchIRDecl]) "missing IR decl"
  checkErrContains "float32" (irTy .float32) "float32"
  checkErrContains "struct" (irTy (.struct (some `S) #[])) "IRType.struct"
  checkErrContains "union" (irTy (.union `U #[])) "IRType.union"
  checkErrContains "opaque"
    (irClosureToLcModule "op"
      { roots := [`Foo], fdecls := #[], externs := #[],
        missing := #[], opaqueStubs := #[`Foo.helper] })
    "opaque IR stub"
  let dummyExt : IR.Decl := .extern `extFn #[] .void { entries := [.standard `all "ext_fn"] }
  let dummyFdecl : IR.Decl := .fdecl `fn #[] .void .unreachable { maxJp := 0, maxVar := 0 }
  checkErrContains "extern_as_fdecl" (irDeclToLcDecl dummyExt) "expected fdecl"
  checkErrContains "fdecl_as_extern" (irDeclToLcExtern dummyFdecl) "expected extern"

#eval show CoreM Unit from do
  runFromIRChecks (← getEnv)

end

end LeanQbeTest.T.LeanLCNFFromIRTest

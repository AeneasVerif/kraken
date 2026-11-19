module

public import LeanQbe.T.Examples.LitmusProgsLemmas
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
public import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.Examples.LitmusProgs
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification and Stock-QBE Smoke Tests for `LeanQbe.T.Examples.Litmus` (`W3.1`)

* Kernel `t_kernel_rfl` checks on `isLegal`, `supportsSource`, and `checkAcyclic`.
* `#print axioms` audit on all source contracts, `*_moduleOk` theorems, and `tracer_nonvacuous`.
* Runnable `PrintQbe` `.ssa` generator + optional stock-QBE smoke runner against `test/*_main.c`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LitmusProgsTest

open LeanQbe.T
open LeanQbe.T.Examples.Litmus

/-! ## 1. Kernel `t_kernel_rfl` checks (`isLegal`, `supportsSource`, `checkAcyclic`) -/

theorem allFns_isLegal_aarch64 :
    allFns.all (fun f => f.body.isLegal LegalTarget.aarch64) = true := by t_kernel_rfl

theorem allFns_isLegal_x64SSE :
    allFns.all (fun f => f.body.isLegal LegalTarget.x64SSE) = true := by t_kernel_rfl

theorem allFns_supportsSource_aarch64 :
    allFns.all (fun f => f.body.supportsSource LegalTarget.aarch64) = true := by t_kernel_rfl

theorem allFns_supportsSource_x64SSE :
    allFns.all (fun f => f.body.supportsSource LegalTarget.x64SSE) = true := by t_kernel_rfl

theorem allModules_checkAcyclic :
    allModules.all Module.checkAcyclic = true := by t_kernel_rfl

theorem tracer_isLegal_aarch64  : tracer.body.isLegal LegalTarget.aarch64  = true := by t_kernel_rfl
theorem ifelse_isLegal_aarch64  : ifelse.body.isLegal LegalTarget.aarch64  = true := by t_kernel_rfl
theorem sumto_isLegal_aarch64   : sumto.body.isLegal LegalTarget.aarch64   = true := by t_kernel_rfl
theorem evenodd_isLegal_aarch64 : evenodd.body.isLegal LegalTarget.aarch64 = true := by t_kernel_rfl
theorem nested_isLegal_aarch64  : nested.body.isLegal LegalTarget.aarch64  = true := by t_kernel_rfl
theorem swap_isLegal_aarch64    : swap.body.isLegal LegalTarget.aarch64    = true := by t_kernel_rfl
theorem inc_isLegal_aarch64     : inc.body.isLegal LegalTarget.aarch64     = true := by t_kernel_rfl
theorem callinc_isLegal_aarch64 : callinc.body.isLegal LegalTarget.aarch64 = true := by t_kernel_rfl
theorem check_isLegal_aarch64   : check.body.isLegal LegalTarget.aarch64   = true := by t_kernel_rfl
theorem twice_isLegal_aarch64   : twice.body.isLegal LegalTarget.aarch64   = true := by t_kernel_rfl
theorem spill10_isLegal_aarch64 : spill10.body.isLegal LegalTarget.aarch64 = true := by t_kernel_rfl
theorem sumcall_isLegal_aarch64 : sumcall.body.isLegal LegalTarget.aarch64 = true := by t_kernel_rfl

theorem tracer_supportsSource_x64SSE  : tracer.body.supportsSource LegalTarget.x64SSE  = true := by t_kernel_rfl
theorem nested_supportsSource_x64SSE  : nested.body.supportsSource LegalTarget.x64SSE  = true := by t_kernel_rfl
theorem twice_supportsSource_x64SSE   : twice.body.supportsSource LegalTarget.x64SSE   = true := by t_kernel_rfl
theorem sumcall_supportsSource_x64SSE : sumcall.body.supportsSource LegalTarget.x64SSE = true := by t_kernel_rfl

#guard (PrintQbe.module tracerModule).isOk = true
#guard (PrintQbe.module ifelseModule).isOk = true
#guard (PrintQbe.module sumtoModule).isOk = true
#guard (PrintQbe.module evenoddModule).isOk = true
#guard (PrintQbe.module nestedModule).isOk = true
#guard (PrintQbe.module swapModule).isOk = true
#guard (PrintQbe.module spill10Module).isOk = true
#guard (PrintQbe.module callincModule).isOk = true
#guard (PrintQbe.module twiceModule).isOk = true
#guard (PrintQbe.module sumcallModule).isOk = true

#guard (PrintQbe.module ⟨twiceModule.fns.map (Fn.legal LegalTarget.aarch64),
    twiceModule.externs, twiceModule.exits⟩).isOk = true
#guard (PrintQbe.module ⟨sumcallModule.fns.map (Fn.legal LegalTarget.x64SSE),
    sumcallModule.externs, sumcallModule.exits⟩).isOk = true

/-! ## 2. Axiom audit (`#print axioms`) -/

#print axioms tracer_wf
#print axioms nested_wf
#print axioms sumcall_wf

#print axioms tracer_spec
#print axioms ifelse_spec
#print axioms sumto_spec
#print axioms evenodd_spec
#print axioms nested_spec
#print axioms swap_spec
#print axioms inc_spec
#print axioms callinc_spec
#print axioms check_spec
#print axioms twice_spec
#print axioms spill10_spec
#print axioms sumcall_spec

#print axioms tracer_moduleOk
#print axioms ifelse_moduleOk
#print axioms sumto_moduleOk
#print axioms evenodd_moduleOk
#print axioms nested_moduleOk
#print axioms swap_moduleOk
#print axioms spill10_moduleOk
#print axioms callinc_moduleOk
#print axioms twice_moduleOk
#print axioms sumcall_moduleOk
#print axioms tracer_nonvacuous

/-! ## 3. Runnable `PrintQbe` `.ssa` emitter + stock-QBE smoke check -/

def litmusModulesNamed : List (String × Module) :=
  [ ("tracer",  tracerModule)
  , ("ifelse",  ifelseModule)
  , ("sumto",   sumtoModule)
  , ("evenodd", evenoddModule)
  , ("nested",  nestedModule)
  , ("swap",    swapModule)
  , ("spill10", spill10Module)
  , ("callinc", callincModule)
  , ("twice",   twiceModule)
  , ("sumcall", sumcallModule)
  ]

/-- Emit `.ssa` files for all 10 litmus modules into `outDir`. -/
public def runGenerate (outDir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let mut ok := true
  for (name, mod) in litmusModulesNamed do
    match PrintQbe.module mod with
    | .error err =>
      IO.eprintln s!"PrintQbe error for {name}: {err}"
      ok := false
    | .ok text =>
      IO.FS.writeFile (outDir / s!"{name}.ssa") text
  pure (if ok then 0 else 1)

/-- Emit `.ssa` files and, when `QBE` env var (or `--qbe <path>`) is provided, compile with stock
QBE + `cc` and run each binary against `test/<name>_main.c` under `timeout 60`. -/
public def main (args : List String) : IO UInt32 := do
  let (outDir, qbeArg?) := match args with
    | ["--qbe", q, d] => (System.FilePath.mk d, some q)
    | ["--qbe", q]    => (System.FilePath.mk "/tmp/leanqbe-litmus-qbe", some q)
    | [d]             => (System.FilePath.mk d, none)
    | _               => (System.FilePath.mk "/tmp/leanqbe-litmus-qbe", none)
  let rc ← runGenerate outDir
  if rc != 0 then return rc
  let qbeBin? ← match qbeArg? with
    | some q => pure (some q)
    | none => IO.getEnv "QBE"
  let some qbeBin := qbeBin? | return 0
  for (name, _) in litmusModulesNamed do
    let ssa := (outDir / s!"{name}.ssa").toString
    let asm := (outDir / s!"{name}.s").toString
    let exe := (outDir / name).toString
    let drv := s!"test/{name}_main.c"
    let r1 ← IO.Process.output { cmd := "timeout", args := #["60", qbeBin, "-o", asm, ssa] }
    if r1.exitCode != 0 then
      IO.eprintln s!"qbe failed for {name}: {r1.stderr}"; return 1
    let r2 ← IO.Process.output { cmd := "timeout", args := #["60", "cc", "-o", exe, drv, asm] }
    if r2.exitCode != 0 then
      IO.eprintln s!"cc failed for {name}: {r2.stderr}"; return 1
    let r3 ← IO.Process.output { cmd := "timeout", args := #["60", exe] }
    if r3.exitCode != 0 then
      IO.eprintln s!"run failed for {name} (exit {r3.exitCode}):\n{r3.stdout}\n{r3.stderr}"; return 1
    IO.println s!"PASS {name}"
  pure 0

end LeanQbeTest.T.LitmusProgsTest

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.LitmusProgsTest.main args

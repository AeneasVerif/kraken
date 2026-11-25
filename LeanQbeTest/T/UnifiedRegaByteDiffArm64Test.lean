module

public import LeanQbe.T.Unified.Backend.Rega
public import LeanQbe.T.Unified.Frontend.C0
public import LeanQbe.T.Arm64.Targ
public import Kraken.AArch64.Print
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.Unified.Backend.Rega
public meta import LeanQbe.T.Unified.Frontend.C0
public meta import LeanQbe.T.Arm64.Targ
public meta import Kraken.AArch64.Print
public meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public meta import LeanQbe.T.Spill

/-!
# 413-Fn `FullM7Fidelity` AArch64 Byte-Exact Regression Gate (`UnifiedRegaByteDiffArm64Test`)

AArch64 companion to `UnifiedRegaByteDiffTest` (isolated from `CoreHub` and `Kraken.X64`):
1. Verifies zero X64/Amd64 imports.
2. Compiles ALL `413` functions of `FullM7Fidelity` (`m7FidelityModule`) through BOTH:
   * `unified c0FnFrontend armLegalTarget (regaBackend armTarget hfn)` (`Stage.mapM`), and
   * legacy `compileModule armTarget.toIsa armLegalTarget ... m7FidelityModule.fns hints`,
   and asserts **`0` byte diff** between their `Kraken.AArch64.print` outputs (both full module
   stream and every individual function against `compileFn`).
3. Proves the kernel module-level byte-identity instantiation
   `m7Fidelity_unified_eq_compileModule_arm` (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedRegaByteDiffArm64Test

open LeanQbe.T LeanQbe.T.Unified LeanQbe.T.Arm64
open LeanQbe.T.Examples.Kissat.FullM7Fidelity (m7FidelityModule m7FidelityFns_length)

/-! ## 1. Arch-Isolation Check (`0` X64 / Amd64 Imports) -/

#eval show Lean.CoreM Unit from do
  let curMods := (← Lean.getEnv).allImportedModuleNames
  let x64Leaks := curMods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64Leaks.isEmpty then
    throwError "UnifiedRegaByteDiffArm64Test leaked X64 import: {x64Leaks.toList}"

/-! ## 2. 413-Fn `m7FidelityModule` AArch64 `Kraken.AArch64.print` Byte-Exact Diff Gate -/

meta def firstByteDiff (a b : ByteArray) : Option (Nat × Option UInt8 × Option UInt8) := Id.run do
  let n := Nat.min a.size b.size
  for i in [:n] do
    if a[i]! != b[i]! then
      return some (i, some a[i]!, some b[i]!)
  if a.size != b.size then
    return some (n, if n < a.size then some a[n]! else none,
      if n < b.size then some b[n]! else none)
  return none

#eval show IO Unit from do
  let fns := m7FidelityModule.fns
  if fns.length != 413 then
    throw <| IO.userError s!"Expected 413 m7FidelityModule fns, got {fns.length}"
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let hintMap := Std.HashMap.ofList ((fns.map Fn.name).zip hints)
  let hfn : Fn → armTarget.toIsa.Hints :=
    fun fn => hintMap.getD fn.name (Spill.hints armTarget.toIsa fn)
  let pipe := unified c0FnFrontend armLegalTarget (regaBackend armTarget hfn)
  let perFn ← IO.ofExcept (pipe.mapM fns)
  let (legacyCode, bounds) ← IO.ofExcept
    (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0 fns hints)
  if perFn.length != 413 || bounds.length != 413 then
    throw <| IO.userError
      s!"Unexpected count: perFn={perFn.length}, bounds={bounds.length}"
  let unifiedCode := perFn.flatten
  if unifiedCode.length != legacyCode.length then
    throw <| IO.userError
      s!"Arm64 directive count mismatch: unified={unifiedCode.length} vs legacy={legacyCode.length}"
  -- Per-function byte-exact verification against `compileFn` across all 413 functions
  let mut idx := 0
  for (fn, h, uDirs) in fns.zip (hints.zip perFn) |>.map (fun (f, (h, u)) => (f, h, u)) do
    let lDirs ← IO.ofExcept (compileFn armTarget.toIsa armLegalTarget h fn)
    let uBytes := (Kraken.AArch64.print uDirs).toUTF8
    let lBytes := (Kraken.AArch64.print lDirs).toUTF8
    if let some (pos, bu, bl) := firstByteDiff uBytes lBytes then
      throw <| IO.userError
        s!"Arm64 per-fn print diff on #{idx} '{fn.name}' at byte {pos}: {bu} vs {bl}"
    idx := idx + 1
  -- Full-module byte-exact verification against `compileModule`
  let unifiedBytes := (Kraken.AArch64.print unifiedCode).toUTF8
  let legacyBytes := (Kraken.AArch64.print legacyCode).toUTF8
  if let some (pos, bu, bl) := firstByteDiff unifiedBytes legacyBytes then
    throw <| IO.userError
      s!"Arm64 full-module print diff at byte {pos}: {bu} vs {bl}"
  let msg :=
    s!"OK: 413/413 FullM7Fidelity Arm64 print byte-exact ({unifiedCode.length} dirs, " ++
      s!"{unifiedBytes.size} B, 0 byte diff)"
  IO.println msg

/-! ## 3. Kernel Byte-Identity Theorem for `m7FidelityModule` on `armTarget` -/

theorem m7Fidelity_unified_eq_compileModule_arm
    (hints : List armTarget.toIsa.Hints) (hfn : Fn → armTarget.toIsa.Hints)
    (hh : ∀ i (hi : i < m7FidelityModule.fns.length) (hj : i < hints.length),
      hfn ((m7FidelityModule.fns[i]'hi).mid armLegalTarget) = hints[i]'hj)
    {code : List armTarget.Directive} {bounds : List (Sym × Nat)}
    (hcm : compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0
      m7FidelityModule.fns hints = .ok (code, bounds)) :
    ∃ perFn,
      (unified c0FnFrontend armLegalTarget (regaBackend armTarget hfn)).mapM
          m7FidelityModule.fns = .ok perFn ∧
        perFn.flatten = code :=
  c0Fn_unified_rega_mapM_eq_compileModule_code armTarget armLegalTarget [] [] 0
    m7FidelityModule.fns hints hfn hh hcm

theorem m7Fidelity_count_413_arm : m7FidelityModule.fns.length = 413 :=
  m7FidelityFns_length

#print axioms m7Fidelity_unified_eq_compileModule_arm
#print axioms m7Fidelity_count_413_arm

end LeanQbeTest.T.UnifiedRegaByteDiffArm64Test

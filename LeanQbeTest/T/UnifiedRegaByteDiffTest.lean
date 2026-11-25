module

public import LeanQbe.T.Unified.Backend.Rega
public import LeanQbe.T.Unified.Frontend.C0
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.Unified.Backend.Rega
public meta import LeanQbe.T.Unified.Frontend.C0
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.PrintAsm0
public meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public meta import LeanQbe.T.Spill

/-!
# 413-Fn `FullM7Fidelity` x86-64 Byte-Exact Regression Gate (`UnifiedRegaByteDiffTest`)

Isolated from `CoreHub` (keeping Kissat imports out of `LeanQbe.T.CoreHub`):
1. Verifies zero Arm64 imports.
2. Compiles ALL `413` functions of `FullM7Fidelity` (`m7FidelityModule`) through BOTH:
   * `unified c0FnFrontend x64LegalTarget (regaBackend x64Target hfn)` (`Stage.mapM`), and
   * legacy `compileModule x64Target.toIsa x64LegalTarget ... m7FidelityModule.fns hints`,
   and asserts **`0` byte diff** between their `PrintAsm0` (`printAsm0`) outputs (both full module
   stream and every individual function against `compileFn`).
3. Proves the kernel module-level byte-identity instantiation
   `m7Fidelity_unified_eq_compileModule_x64` (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedRegaByteDiffTest

open LeanQbe.T LeanQbe.T.Unified LeanQbe.T.Amd64
open LeanQbe.T.Examples.Kissat.FullM7Fidelity (m7FidelityModule m7FidelityFns_length)

/-! ## 1. Arch-Isolation Check (`0` Arm64 Imports) -/

#eval show Lean.CoreM Unit from do
  let curMods := (← Lean.getEnv).allImportedModuleNames
  let armLeaks := curMods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !armLeaks.isEmpty then
    throwError "UnifiedRegaByteDiffTest leaked Arm64 import: {armLeaks.toList}"

/-! ## 2. 413-Fn `m7FidelityModule` x86-64 `PrintAsm0` Byte-Exact Diff Gate -/

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
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let hintMap := Std.HashMap.ofList ((fns.map Fn.name).zip hints)
  let hfn : Fn → x64Target.toIsa.Hints :=
    fun fn => hintMap.getD fn.name (Spill.hints x64Target.toIsa fn)
  let pipe := unified c0FnFrontend x64LegalTarget (regaBackend x64Target hfn)
  let perFn ← IO.ofExcept (pipe.mapM fns)
  let (legacyCode, bounds) ← IO.ofExcept
    (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fns hints)
  if perFn.length != 413 || bounds.length != 413 then
    throw <| IO.userError
      s!"Unexpected count: perFn={perFn.length}, bounds={bounds.length}"
  let unifiedCode := perFn.flatten
  if unifiedCode.length != legacyCode.length then
    throw <| IO.userError
      s!"x64 directive count mismatch: unified={unifiedCode.length} vs legacy={legacyCode.length}"
  -- Per-function byte-exact verification against `compileFn` across all 413 functions
  let mut idx := 0
  for (fn, h, uDirs) in fns.zip (hints.zip perFn) |>.map (fun (f, (h, u)) => (f, h, u)) do
    let lDirs ← IO.ofExcept (compileFn x64Target.toIsa x64LegalTarget h fn)
    let uBytes := (printAsm0 uDirs).toUTF8
    let lBytes := (printAsm0 lDirs).toUTF8
    if let some (pos, bu, bl) := firstByteDiff uBytes lBytes then
      throw <| IO.userError
        s!"x64 per-fn PrintAsm0 diff on #{idx} '{fn.name}' at byte {pos}: {bu} vs {bl}"
    idx := idx + 1
  -- Full-module byte-exact verification against `compileModule`
  let unifiedBytes := (printAsm0 unifiedCode).toUTF8
  let legacyBytes := (printAsm0 legacyCode).toUTF8
  if let some (pos, bu, bl) := firstByteDiff unifiedBytes legacyBytes then
    throw <| IO.userError
      s!"x64 full-module PrintAsm0 diff at byte {pos}: {bu} vs {bl}"
  let msg :=
    s!"OK: 413/413 FullM7Fidelity x64 PrintAsm0 byte-exact ({unifiedCode.length} dirs, " ++
      s!"{unifiedBytes.size} B, 0 byte diff)"
  IO.println msg

/-! ## 3. Kernel Byte-Identity Theorem for `m7FidelityModule` on `x64Target` -/

theorem m7Fidelity_unified_eq_compileModule_x64
    (hints : List x64Target.toIsa.Hints) (hfn : Fn → x64Target.toIsa.Hints)
    (hh : ∀ i (hi : i < m7FidelityModule.fns.length) (hj : i < hints.length),
      hfn ((m7FidelityModule.fns[i]'hi).mid x64LegalTarget) = hints[i]'hj)
    {code : List x64Target.Directive} {bounds : List (Sym × Nat)}
    (hcm : compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0
      m7FidelityModule.fns hints = .ok (code, bounds)) :
    ∃ perFn,
      (unified c0FnFrontend x64LegalTarget (regaBackend x64Target hfn)).mapM
          m7FidelityModule.fns = .ok perFn ∧
        perFn.flatten = code :=
  c0Fn_unified_rega_mapM_eq_compileModule_code x64Target x64LegalTarget [] [] 0
    m7FidelityModule.fns hints hfn hh hcm

theorem m7Fidelity_count_413_x64 : m7FidelityModule.fns.length = 413 :=
  m7FidelityFns_length

#print axioms m7Fidelity_unified_eq_compileModule_x64
#print axioms m7Fidelity_count_413_x64

end LeanQbeTest.T.UnifiedRegaByteDiffTest

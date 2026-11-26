/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import LeanQbe.T.CompileGuard
meta import LeanQbe.T.Amd64.Isa
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep7
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# KissatFidelity (`499` fns) SysV x64 Fail-Closed Preflight Compile Guard

Pure `IO` preflight verifying that `FullFidelityAssembly.fidModule` (`499` fns, matching
`FullFidelityInl`) under `fidInlPolicy` passes acyclicity, legal signatures, `supportsSource`,
`Spill.hints`, `Rega.lowerFn`, `checkAndBoundExt <= 2048`, and `progSmall` on SysV x64.

Also includes a fast single-fn tripwire against `FullFidelityStep7.fidStep7BvaUpdLitFn`:
`FullFidelityStep7.lean:1495` declares `full_bva_upd_lit_fid` with `7` arguments
(`[i64, i64, i64, i64, i32, i64, i32]`), exceeding `x64Isa.assignArgs`'s `6`-GPR SysV ABI limit.
Once `full_bva_upd_lit_fid` drops to `≤ 6` args (or `x64Isa` handles stack args), flip both
this guard and `Amd64.KissatFidelityParam` onto `fidStep7Module` (`501` fns).
-/

set_option autoImplicit false

private meta def x64GuardDirSize : LeanQbe.T.Amd64.x64Isa.Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

#eval show IO Unit from do
  LeanQbe.T.CompileGuard.runModuleGuard
    LeanQbe.T.Amd64.x64Isa
    LeanQbe.T.Amd64.x64LegalTarget
    x64GuardDirSize
    LeanQbe.T.Examples.Kissat.FullFidelityAssembly.fidModule
    LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy
    { label := "KissatFidelity-x64"
      maxBound := 2048
      entryFn? := some "kissat_solve_bytes" }
  -- Negative tripwire (<5ms): verify `full_bva_upd_lit_fid` still triggers `fn: abi` on x64
  try
    let exts := List.filterMap
      (fun (f : LeanQbe.T.Fn) =>
        if f.name == "full_bva_upd_lit_fid" then none else some ⟨f.name, f.as, f.rs⟩)
      LeanQbe.T.Examples.Kissat.FullFidelityStep7.fidStep7ModuleFns
    LeanQbe.T.CompileGuard.runModuleGuard
      LeanQbe.T.Amd64.x64Isa
      LeanQbe.T.Amd64.x64LegalTarget
      x64GuardDirSize
      { fns := [LeanQbe.T.Examples.Kissat.FullFidelityStep7.fidStep7BvaUpdLitFn]
        externs := exts }
      LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy
      { label := "KissatFidelity-x64-step7-tripwire"
        maxBound := 2048
        entryFn? := none }
    throw <| IO.userError
      "[KissatFidelity-x64] full_bva_upd_lit_fid now passes x64 ABI; switch guard to step7"
  catch e =>
    let msg := toString e
    if (msg.splitOn "fn: abi").length < 2 then
      throw <| IO.userError s!"[KissatFidelity-x64] unexpected tripwire failure: {msg}"

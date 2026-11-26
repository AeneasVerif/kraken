/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import LeanQbe.T.CompileGuard
meta import LeanQbe.T.Amd64.Isa
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# KissatFidelity (`504` fns) SysV x64 Fail-Closed Preflight Compile Guard

Pure `IO` preflight verifying that `FullFidelityAssemblyStep9.fidStep9Module` (`504` fns)
under `fidInlPolicy` passes acyclicity, legal signatures, `fnNameOk`, `stringsNodup`,
`supportsSource`, `Spill.hints`, `Rega.lowerFn`, `checkAndBoundExt <= 2048`, and `progSmall`
on SysV x64 (including 6-arg packed `full_bva_upd_lit_fid`).
-/

set_option autoImplicit false

private meta def x64GuardDirSize : LeanQbe.T.Amd64.x64Isa.Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

#eval show IO Unit from
  LeanQbe.T.CompileGuard.runModuleGuard
    LeanQbe.T.Amd64.x64Isa
    LeanQbe.T.Amd64.x64LegalTarget
    x64GuardDirSize
    LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9.fidStep9Module
    LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy
    { label := "KissatFidelity-x64"
      maxBound := 2048
      entryFn? := some "kissat_solve_bytes" }

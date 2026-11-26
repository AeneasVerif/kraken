/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import LeanQbe.T.CompileGuard
meta import LeanQbe.T.Arm64.Isa
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# KissatFidelity (`501` fns) AAPCS64 Arm64 Fail-Closed Preflight Compile Guard

Pure `IO` preflight verifying that `fidStep7Module` under `fidInlPolicy` passes acyclicity,
legal signatures, `supportsSource`, `Spill.hints`, `Rega.lowerFn`, `checkAndBoundExt <= 2048`,
and `progSmall` on AAPCS64 Arm64. Emits zero declarations and zero axioms; fails
`lake build --wfail` via `IO.userError` on any regression.
-/

set_option autoImplicit false

private meta def armGuardDirSize : LeanQbe.T.Arm64.armIsa.Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

#eval show IO Unit from
  LeanQbe.T.CompileGuard.runModuleGuard
    LeanQbe.T.Arm64.armIsa
    LeanQbe.T.Arm64.armLegalTarget
    armGuardDirSize
    LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7.fidStep7Module
    LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy
    { label := "KissatFidelity-arm64"
      maxBound := 2048
      entryFn? := some "kissat_solve_bytes" }

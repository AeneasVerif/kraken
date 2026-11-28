/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import LeanQbeTest.T.KissatBoundsDumpCommon
meta import LeanQbe.T.Arm64.Isa
meta import LeanQbe.T.Examples.Kissat.Src.Full
meta import LeanQbe.T.Examples.Kissat.Src.InlPolicy
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat AAPCS64 Arm64 Single-Pass `--bounds-json` Dumper Leaf

Pure `#eval IO` leaf modeled on `KissatFidelityCompileGuardArm64`: computes exact per-function
`{name, as, rs, bound, callees}` bounds in one pass on AAPCS64 Arm64 (`armIsa` / `armLegalTarget`).

* Normal `lake build --wfail`: silent fail-closed bounds verification (zero declarations, zero
  axioms, zero filesystem side effects).
* Dumping JSON for `scripts/gen_cert_slices.py --bounds-json`:
  ```
  LEANQBE_BOUNDS_JSON_OUT=/tmp/kissat_arm64_bounds.json \
    LEANQBE_BOUNDS_TARGET=full \
    lake env lean LeanQbeTest/T/KissatBoundsDumpArm64.lean
  ```
  Supported `LEANQBE_BOUNDS_TARGET` values: `"full"` (default, 418 fns) and `"plain"` (59 fns).
-/

set_option autoImplicit false

#eval show IO Unit from do
  let target := (← IO.getEnv "LEANQBE_BOUNDS_TARGET").getD "full"
  match target with
  | "full" =>
    LeanQbeTest.T.BoundsDump.runModuleBoundsDump
      LeanQbe.T.Arm64.armIsa
      LeanQbe.T.Arm64.armLegalTarget
      LeanQbe.T.Examples.Kissat.Src.Full.kissatModule
      (some LeanQbe.T.Examples.Kissat.Src.InlPolicy.kissatInlPolicy)
      { label := "KissatBoundsDump-full-arm64", maxBound := 2048 }
  | "plain" =>
    LeanQbeTest.T.BoundsDump.runModuleBoundsDump
      LeanQbe.T.Arm64.armIsa
      LeanQbe.T.Arm64.armLegalTarget
      LeanQbe.T.Examples.Kissat.Plain.plainModule
      none
      { label := "KissatBoundsDump-plain-arm64", maxBound := 2048 }
  | other =>
    throw <| IO.userError
      s!"[KissatBoundsDumpArm64] unknown LEANQBE_BOUNDS_TARGET '{other}' (expected full|plain)"

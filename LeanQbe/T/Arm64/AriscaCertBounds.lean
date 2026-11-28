/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Main
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.Examples.Arisca.Build.Flat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Arisca.Build.Flat

/-!
# Exported Stack-Bound Prefix Table for `ariscaModule` (AAPCS64 Arm64)

Materializes `ariscaArm64AllExt : List (SigEntry × Nat)` via `eval_prefix_ext!` across all `45`
functions in `ariscaFlatMod.fns` on `armTarget` (`0` externs, `0` exits), allowing parallel
compilation slices `AriscaCertS0`..`S4` to resolve callee stack bounds.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.Examples.Arisca.Build

eval_prefix_ext! ariscaArm64AllExt armTarget armLegalTarget ariscaFlatMod.fns (flat := true)

/-- Pre-verified callee accumulator `(sig, stackBound)` covering `ariscaModule.fns.take k`. -/
@[expose] def ariscaArm64ExtBefore (k : Nat) : List (SigEntry × Nat) :=
  ariscaArm64AllExt.drop (45 - k)

end LeanQbe.T.Arm64

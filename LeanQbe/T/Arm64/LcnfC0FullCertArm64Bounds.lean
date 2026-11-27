module

public import LeanQbe.T.Main
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.LeanLCNF.LcnfC0FullFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full

/-!
# Exported Stack-Bound Prefix Table for `rtC0CoreMod` (AAPCS64 Arm64)

Materializes `rtC0CoreArm64AllExt : List (SigEntry × Nat)` via `eval_prefix_ext!` across all `80`
functions in `rtC0CoreMod.fns` on `armTarget` (`exits := ["lcnf_panic"]`, `nX := 64`),
allowing parallel compilation slices `LcnfC0FullCertArm64S1`..`S7` to resolve callee stack bounds.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

eval_prefix_ext! rtC0CoreArm64AllExt armTarget armLegalTarget rtC0CoreFlatMod.fns
  (exits := rtExitSyms) (nX := 64) (flat := true)

/-- Pre-verified callee accumulator `(sig, stackBound)` covering `rtC0CoreMod.fns.take k`. -/
@[expose] def rtC0Arm64ExtBefore (k : Nat) : List (SigEntry × Nat) :=
  rtC0CoreArm64AllExt.drop (80 - k)

end LeanQbe.T.Arm64

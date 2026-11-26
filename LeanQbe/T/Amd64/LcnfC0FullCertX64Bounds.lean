module

public import LeanQbe.T.Main
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.LeanLCNF.LcnfC0FullFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full

/-!
# Exported Stack-Bound Prefix Table for `rtC0CoreMod`

Materializes `rtC0CoreAllExt : List (SigEntry × Nat)` via `eval_prefix_ext!` across all `86`
functions in `rtC0CoreMod.fns` on `x64Target` (`exits := ["lcnf_panic"]`, `nX := 64`),
allowing parallel compilation slices `LcnfC0FullCertX64S1`..`S7` to resolve callee stack bounds.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

eval_prefix_ext! rtC0CoreAllExt x64Target x64LegalTarget rtC0CoreFlatMod.fns
  (exits := rtExitSyms) (nX := 64) (flat := true)

/-- Pre-verified callee accumulator `(sig, stackBound)` covering `rtC0CoreMod.fns.take k`. -/
@[expose] def rtC0ExtBefore (k : Nat) : List (SigEntry × Nat) :=
  rtC0CoreAllExt.drop (86 - k)

end LeanQbe.T.Amd64

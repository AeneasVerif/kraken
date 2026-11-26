module

public import LeanQbe.T.Main
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
import LeanQbe.T.Bootstrap0.Mod0
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# Exported Stack-Bound Prefix Table for `leanqbe0Mod0`

Materializes `leanqbe0AllExt : List (SigEntry × Nat)` via `eval_prefix_ext!` across all `124`
functions in `leanqbe0Mod0.fns` starting from `rtC0CoreAllExt`, allowing parallel compilation
slices `Cert1`..`Cert12` to resolve callee stack bounds cleanly.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

eval_prefix_ext! leanqbe0AllExt x64Target x64LegalTarget leanqbe0Mod0.fns
  (ext := rtC0CoreAllExt) (exits := rtExitSyms) (nX := 64) (flat := true)

/-- Pre-verified callee accumulator `(sig, stackBound)` covering `leanqbe0Mod0.fns.take k`. -/
@[expose] def extBefore0 (k : Nat) : List (SigEntry × Nat) :=
  leanqbe0AllExt.drop (124 - k)

end LeanQbe.T.Bootstrap0

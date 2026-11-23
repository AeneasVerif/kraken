module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-!
# KissatM7Fidelity Auto-Computed Prefix Bounds on AAPCS64 Arm64

Precomputes `(SigEntry × Nat)` stack bounds across all `413` functions of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` (hub `LeanQbe.T.Examples.Kissat.M5Hub`)
via `eval_prefix_ext!`, enabling flat 1-tier parallel slice certificates via `<prefix>ExtPrefix`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityBounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM7FidelityInl

-- Auto-computed reversed `(sig, bound)` accumulator and prefix slicer for the module.
eval_prefix_ext! m7FidelityAllExt armTarget armLegalTarget m7FidInlFns
  (prefixDef := m7FidelityExtPrefix)

end LeanQbe.T.Arm64.KissatM7FidelityBounds

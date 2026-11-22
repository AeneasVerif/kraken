module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Examples.Kissat.FullM4
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# KissatM4 Auto-Computed Prefix Bounds on AAPCS64 Arm64

Precomputes `(SigEntry × Nat)` stack bounds across all `231` functions of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` (hub `LeanQbe.T.Examples.Kissat.M4Hub`) via
`eval_prefix_ext!`, enabling flat 1-tier parallel slice certificates via `<prefix>ExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Bounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM4

-- Auto-computed reversed `(sig, bound)` accumulator for the full module.
eval_prefix_ext! m4AllExt armTarget armLegalTarget m4Fns

/-- Exported callee signatures and stack bounds for prefix `[0, k)`. -/
def m4ExtPrefix (k : Nat) : List (SigEntry × Nat) :=
  m4AllExt.drop (m4Fns.length - k)

end LeanQbe.T.Arm64.KissatM4Bounds

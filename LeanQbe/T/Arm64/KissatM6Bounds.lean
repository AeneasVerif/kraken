module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Examples.Kissat.FullM6Inl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# KissatM6 Auto-Computed Prefix Bounds on AAPCS64 Arm64

Precomputes `(SigEntry × Nat)` stack bounds across all `382` functions of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` (hub `LeanQbe.T.Examples.Kissat.M5Hub`) via
`eval_prefix_ext!`, enabling flat 1-tier parallel slice certificates via `<prefix>ExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Bounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM6Inl

-- Auto-computed reversed `(sig, bound)` accumulator for the full module.
eval_prefix_ext! m6AllExt armTarget armLegalTarget m6InlFns

/-- Exported callee signatures and stack bounds for prefix `[0, k)`. -/
def m6ExtPrefix (k : Nat) : List (SigEntry × Nat) :=
  m6AllExt.drop (m6AllExt.length - k)

end LeanQbe.T.Arm64.KissatM6Bounds

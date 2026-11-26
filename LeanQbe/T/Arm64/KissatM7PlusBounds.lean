module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# KissatM7Plus Auto-Computed Prefix Bounds on AAPCS64 Arm64

Precomputes `(SigEntry × Nat)` stack bounds across all `410` functions of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` (hub `LeanQbe.T.Examples.Kissat.M5Hub`) via
`eval_prefix_ext!`, enabling flat 1-tier parallel slice certificates via `<prefix>ExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusBounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM7PlusInl

-- Auto-computed reversed `(sig, bound)` accumulator for the full module.
eval_prefix_ext! m7PlusAllExt armTarget armLegalTarget m7PlusInlFns

/-- Exported callee signatures and stack bounds for prefix `[0, k)`. -/
def m7PlusExtPrefix (k : Nat) : List (SigEntry × Nat) :=
  m7PlusAllExt.drop (m7PlusAllExt.length - k)

end LeanQbe.T.Arm64.KissatM7PlusBounds

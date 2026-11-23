module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# KissatM7Plus Auto-Computed Prefix Bounds on SysV x64

Precomputes `(SigEntry × Nat)` stack bounds across all `410` functions of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` (hub `LeanQbe.T.Examples.Kissat.M5Hub`) via
`eval_prefix_ext!`, enabling flat 1-tier parallel slice certificates via `<prefix>ExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusBounds

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM7PlusInl

-- Auto-computed reversed `(sig, bound)` accumulator for the full module.
eval_prefix_ext! m7PlusAllExt x64Target x64LegalTarget m7PlusInlFns

/-- Exported callee signatures and stack bounds for prefix `[0, k)`. -/
def m7PlusExtPrefix (k : Nat) : List (SigEntry × Nat) :=
  m7PlusAllExt.drop (m7PlusInlFns.length - k)

end LeanQbe.T.Amd64.KissatM7PlusBounds

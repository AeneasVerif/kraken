module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Auto-Computed Prefix Bounds on SysV x64

Precomputes `(SigEntry × Nat)` stack bounds across all `270` functions of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` via `eval_prefix_ext!`, enabling flat 1-tier
parallel slice certificates via `<prefix>ExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Bounds

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM5InlB5

-- Auto-computed reversed `(sig, bound)` accumulator for the full module.
eval_prefix_ext! m5AllExt x64Target x64LegalTarget m5InlB5Fns

/-- Exported callee signatures and stack bounds for prefix `[0, k)`. -/
def m5ExtPrefix (k : Nat) : List (SigEntry × Nat) :=
  m5AllExt.drop (m5InlB5Fns.length - k)

end LeanQbe.T.Amd64.KissatM5Bounds

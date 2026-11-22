module

public import LeanQbe.T.MainCert
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Single-Pass Prefix Bounds on AAPCS64 Arm64

Evaluates `m3AllExt : List (SigEntry × Nat)` once in `O(N)` meta time (`evalOneFnBound`) and
exposes `m3ExtPrefix (k : Nat) := m3AllExt.drop (204 - k)` for all parallel `KissatM3Cert*`
slices on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM3Bounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

eval_prefix_ext! m3AllExt armTarget armLegalTarget m3Fns (prefixDef := m3ExtPrefix)

end LeanQbe.T.Arm64.KissatM3Bounds

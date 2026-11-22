module

public import LeanQbe.T.MainCert
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Single-Pass Prefix Bounds on SysV x64

Evaluates `m3AllExt : List (SigEntry × Nat)` once in `O(N)` meta time (`evalOneFnBound`) and
exposes `m3ExtPrefix (k : Nat) := m3AllExt.drop (204 - k)` for all parallel `KissatM3Cert*`
slices on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM3Bounds

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

eval_prefix_ext! m3AllExt x64Target x64LegalTarget m3Fns (prefixDef := m3ExtPrefix)

end LeanQbe.T.Amd64.KissatM3Bounds

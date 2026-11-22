module

public import LeanQbe.T.MainCert
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` (`Plain`) Single-Pass Prefix Bounds on AAPCS64 Arm64

Evaluates `plainAllExt : List (SigEntry × Nat)` once in `O(N)` meta time (`evalOneFnBound`) and
exposes `plainExtPrefix (k : Nat) := plainAllExt.drop (59 - k)` for all parallel
`KissatPlainCert*` slices on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatPlainBounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

eval_prefix_ext! plainAllExt armTarget armLegalTarget plainFns (prefixDef := plainExtPrefix)

end LeanQbe.T.Arm64.KissatPlainBounds

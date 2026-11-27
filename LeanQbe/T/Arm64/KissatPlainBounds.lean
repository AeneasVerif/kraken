module

public import LeanQbe.T.Main
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatPlainBounds

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

eval_prefix_ext! plainAllExt armTarget armLegalTarget plainFns (prefixDef := plainExtPrefix)

end LeanQbe.T.Arm64.KissatPlainBounds

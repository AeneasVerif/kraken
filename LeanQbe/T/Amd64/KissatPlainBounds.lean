module

public import LeanQbe.T.Main
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatPlainBounds

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain

eval_prefix_ext! plainAllExt x64Target x64LegalTarget plainFns (prefixDef := plainExtPrefix)

end LeanQbe.T.Amd64.KissatPlainBounds

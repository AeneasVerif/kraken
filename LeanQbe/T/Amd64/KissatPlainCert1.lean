module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatPlainCert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain

@[expose] def slice1Mod : Module := { fns := plainFns.take 15, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 4 (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert1

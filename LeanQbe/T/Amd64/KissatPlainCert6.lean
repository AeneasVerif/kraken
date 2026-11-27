module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Amd64.KissatPlainBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Amd64.KissatPlainBounds

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatPlainCert6

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Amd64.KissatPlainBounds

@[expose] def slice6Mod : Module :=
  { fns := plainFns.drop 52, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert6
  x64Target x64Layout x64LegalTarget x64LabelClean slice6Mod 4
  (ext := plainExtPrefix 52) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert6

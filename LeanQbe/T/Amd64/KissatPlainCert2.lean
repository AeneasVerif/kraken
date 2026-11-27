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

namespace LeanQbe.T.Amd64.KissatPlainCert2

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Amd64.KissatPlainBounds

@[expose] def slice2Mod : Module :=
  { fns := (plainFns.drop 15).take 14, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert2
  x64Target x64Layout x64LegalTarget x64LabelClean slice2Mod 4
  (ext := plainExtPrefix 15) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert2

module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Arm64.KissatPlainBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Arm64.KissatPlainBounds

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatPlainCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Arm64.KissatPlainBounds

@[expose] def slice4Mod : Module :=
  { fns := (plainFns.drop 40).take 7, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert4
  armTarget armLayout armLegalTarget armLabelClean slice4Mod 4
  (ext := plainExtPrefix 40) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert4

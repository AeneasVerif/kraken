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

namespace LeanQbe.T.Arm64.KissatPlainCert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Arm64.KissatPlainBounds

@[expose] def slice6Mod : Module :=
  { fns := plainFns.drop 52, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert6
  armTarget armLayout armLegalTarget armLabelClean slice6Mod 4
  (ext := plainExtPrefix 52) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert6

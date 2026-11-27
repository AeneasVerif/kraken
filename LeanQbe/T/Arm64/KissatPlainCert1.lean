module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatPlainCert1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

@[expose] def slice1Mod : Module := { fns := plainFns.take 15, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert1
  armTarget armLayout armLegalTarget armLabelClean slice1Mod 4 (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert1

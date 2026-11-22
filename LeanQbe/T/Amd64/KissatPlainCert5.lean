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

/-!
# Kissat `D-Plain` Certificate Slice 5/6 on SysV x64

Kernel-checked native compilation certificate (`cert5`) for slice `[47, 52)` (`5` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `x64Target`, with prefix bounds from
`KissatPlainBounds.plainExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatPlainCert5

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Amd64.KissatPlainBounds

/-- Slice 5 sub-module (`[47, 52)`, `5` functions). -/
def slice5Mod : Module :=
  { fns := (plainFns.drop 47).take 5, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert5
  x64Target x64Layout x64LegalTarget x64LabelClean slice5Mod 4
  (ext := plainExtPrefix 47) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert5

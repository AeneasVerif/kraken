module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` Certificate Slice 1/6 on SysV x64

Kernel-checked native compilation certificate (`cert1`) for slice `[0, 15)` (`15` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatPlainCert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain

/-- Slice 1 sub-module (`[0, 15)`, `15` functions). -/
def slice1Mod : Module := { fns := plainFns.take 15, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 4 (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert1

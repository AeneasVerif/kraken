module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# KissatM7Plus Certificate Slice 1/56 on SysV x64

Kernel-checked compilation cert (`cert1`) for slice `[0, 12)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 1 sub-module (`[0, 12)`, `12` functions). -/
noncomputable def slice1Mod : Module := { fns := m7PlusInlFns.take 12 }

compile_linked_chunks! cert1 x64Target x64Layout x64LegalTarget x64LabelClean
  slice1Mod 4 (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert1

module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Certificate Slice 1/34 on SysV x64

Kernel-checked compilation cert (`cert1`) for slice `[0, 12)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Cert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 1 sub-module (`[0, 12)`, `12` functions). -/
noncomputable def slice1Mod : Module := { fns := m5InlB5Fns.take 12 }

compile_linked_chunks! cert1 x64Target x64Layout x64LegalTarget x64LabelClean
  slice1Mod 4 (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM5Cert1

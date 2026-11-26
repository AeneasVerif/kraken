module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM5Bounds
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM5Bounds
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Certificate Slice 19/34 on SysV x64

Kernel-checked compilation cert (`cert19`) for slice `[164, 174)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Cert19

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 19 sub-module (`[164, 174)`, `10` functions). -/
noncomputable def slice19Mod : Module := { fns := (m5InlB5Fns.drop 164).take 10 }

compile_linked_chunks! cert19 x64Target x64Layout x64LegalTarget x64LabelClean
  slice19Mod 4 (ext := m5ExtPrefix 164) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM5Cert19

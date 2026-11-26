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
# KissatM5 Certificate Slice 20/34 on SysV x64

Kernel-checked compilation cert (`cert20`) for slice `[174, 175)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Cert20

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 20 sub-module (`[174, 175)`, `1` functions). -/
noncomputable def slice20Mod : Module := { fns := (m5InlB5Fns.drop 174).take 1 }

compile_linked_chunks! cert20 x64Target x64Layout x64LegalTarget x64LabelClean
  slice20Mod 4 (ext := m5ExtPrefix 174) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM5Cert20

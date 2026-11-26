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
# KissatM5 Certificate Slice 30/34 on SysV x64

Kernel-checked compilation cert (`cert30`) for slice `[227, 228)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Cert30

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 30 sub-module (`[227, 228)`, `1` functions). -/
noncomputable def slice30Mod : Module := { fns := (m5InlB5Fns.drop 227).take 1 }

compile_linked_chunks! cert30 x64Target x64Layout x64LegalTarget x64LabelClean
  slice30Mod 4 (ext := m5ExtPrefix 227) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM5Cert30

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
# KissatM5 Certificate Slice 7/34 on SysV x64

Kernel-checked compilation cert (`cert7`) for slice `[53, 65)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Cert7

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 7 sub-module (`[53, 65)`, `12` functions). -/
noncomputable def slice7Mod : Module := { fns := (m5InlB5Fns.drop 53).take 12 }

compile_linked_chunks! cert7 x64Target x64Layout x64LegalTarget x64LabelClean
  slice7Mod 4 (ext := m5ExtPrefix 53) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM5Cert7

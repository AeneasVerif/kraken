module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM6Bounds
public import LeanQbe.T.Examples.Kissat.FullM6Inl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM6Bounds
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# KissatM6 Certificate Slice 16/51 on SysV x64

Kernel-checked compilation cert (`cert16`) for slice `[121, 133)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert16

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 16 sub-module (`[121, 133)`, `12` functions). -/
noncomputable def slice16Mod : Module := { fns := (m6InlFns.drop 121).take 12 }

compile_linked_chunks! cert16 x64Target x64Layout x64LegalTarget x64LabelClean
  slice16Mod 4 (ext := m6ExtPrefix 121) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert16

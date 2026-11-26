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
# KissatM6 Certificate Slice 44/51 on SysV x64

Kernel-checked compilation cert (`cert44`) for slice `[335, 336)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert44

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 44 sub-module (`[335, 336)`, `1` functions). -/
noncomputable def slice44Mod : Module := { fns := (m6InlFns.drop 335).take 1 }

compile_linked_chunks! cert44 x64Target x64Layout x64LegalTarget x64LabelClean
  slice44Mod 4 (ext := m6ExtPrefix 335) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert44

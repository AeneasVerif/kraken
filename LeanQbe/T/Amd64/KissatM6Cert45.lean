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
# KissatM6 Certificate Slice 45/51 on SysV x64

Kernel-checked compilation cert (`cert45`) for slice `[336, 339)` (`3` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert45

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 45 sub-module (`[336, 339)`, `3` functions). -/
noncomputable def slice45Mod : Module := { fns := (m6InlFns.drop 336).take 3 }

compile_linked_chunks! cert45 x64Target x64Layout x64LegalTarget x64LabelClean
  slice45Mod 4 (ext := m6ExtPrefix 336) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert45

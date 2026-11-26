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
# KissatM6 Certificate Slice 28/51 on SysV x64

Kernel-checked compilation cert (`cert28`) for slice `[242, 251)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert28

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 28 sub-module (`[242, 251)`, `9` functions). -/
noncomputable def slice28Mod : Module := { fns := (m6InlFns.drop 242).take 9 }

compile_linked_chunks! cert28 x64Target x64Layout x64LegalTarget x64LabelClean
  slice28Mod 4 (ext := m6ExtPrefix 242) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert28

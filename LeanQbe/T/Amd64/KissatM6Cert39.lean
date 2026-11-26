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
# KissatM6 Certificate Slice 39/51 on SysV x64

Kernel-checked compilation cert (`cert39`) for slice `[303, 311)` (`8` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert39

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 39 sub-module (`[303, 311)`, `8` functions). -/
noncomputable def slice39Mod : Module := { fns := (m6InlFns.drop 303).take 8 }

compile_linked_chunks! cert39 x64Target x64Layout x64LegalTarget x64LabelClean
  slice39Mod 4 (ext := m6ExtPrefix 303) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert39

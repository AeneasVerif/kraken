module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM6Bounds
public import LeanQbe.T.Examples.Kissat.FullM6Inl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM6Bounds
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# KissatM6 Certificate Slice 9/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert9`) for slice `[81, 82)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert9

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 9 sub-module (`[81, 82)`, `1` functions). -/
noncomputable def slice9Mod : Module := { fns := (m6InlFns.drop 81).take 1 }

compile_linked_chunks! cert9 armTarget armLayout armLegalTarget armLabelClean
  slice9Mod 4 (ext := m6ExtPrefix 81) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert9

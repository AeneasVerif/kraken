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
# KissatM6 Certificate Slice 16/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert16`) for slice `[121, 133)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert16

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 16 sub-module (`[121, 133)`, `12` functions). -/
noncomputable def slice16Mod : Module := { fns := (m6InlFns.drop 121).take 12 }

compile_linked_chunks! cert16 armTarget armLayout armLegalTarget armLabelClean
  slice16Mod 4 (ext := m6ExtPrefix 121) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert16

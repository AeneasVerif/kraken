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
# KissatM6 Certificate Slice 26/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert26`) for slice `[222, 230)` (`8` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert26

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 26 sub-module (`[222, 230)`, `8` functions). -/
noncomputable def slice26Mod : Module := { fns := (m6InlFns.drop 222).take 8 }

compile_linked_chunks! cert26 armTarget armLayout armLegalTarget armLabelClean
  slice26Mod 4 (ext := m6ExtPrefix 222) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert26

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
# KissatM6 Certificate Slice 50/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert50`) for slice `[368, 375)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert50

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 50 sub-module (`[368, 375)`, `7` functions). -/
noncomputable def slice50Mod : Module := { fns := (m6InlFns.drop 368).take 7 }

compile_linked_chunks! cert50 armTarget armLayout armLegalTarget armLabelClean
  slice50Mod 4 (ext := m6ExtPrefix 368) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert50

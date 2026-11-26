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
# KissatM6 Certificate Slice 14/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert14`) for slice `[114, 120)` (`6` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert14

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 14 sub-module (`[114, 120)`, `6` functions). -/
noncomputable def slice14Mod : Module := { fns := (m6InlFns.drop 114).take 6 }

compile_linked_chunks! cert14 armTarget armLayout armLegalTarget armLabelClean
  slice14Mod 4 (ext := m6ExtPrefix 114) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert14

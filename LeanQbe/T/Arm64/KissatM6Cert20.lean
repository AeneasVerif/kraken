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
# KissatM6 Certificate Slice 20/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert20`) for slice `[168, 180)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert20

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 20 sub-module (`[168, 180)`, `12` functions). -/
noncomputable def slice20Mod : Module := { fns := (m6InlFns.drop 168).take 12 }

compile_linked_chunks! cert20 armTarget armLayout armLegalTarget armLabelClean
  slice20Mod 4 (ext := m6ExtPrefix 168) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert20

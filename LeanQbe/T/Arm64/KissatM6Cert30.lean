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
# KissatM6 Certificate Slice 30/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert30`) for slice `[252, 254)` (`2` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert30

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 30 sub-module (`[252, 254)`, `2` functions). -/
noncomputable def slice30Mod : Module := { fns := (m6InlFns.drop 252).take 2 }

compile_linked_chunks! cert30 armTarget armLayout armLegalTarget armLabelClean
  slice30Mod 4 (ext := m6ExtPrefix 252) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert30

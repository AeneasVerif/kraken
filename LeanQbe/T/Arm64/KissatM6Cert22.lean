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
# KissatM6 Certificate Slice 22/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert22`) for slice `[187, 192)` (`5` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert22

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 22 sub-module (`[187, 192)`, `5` functions). -/
noncomputable def slice22Mod : Module := { fns := (m6InlFns.drop 187).take 5 }

compile_linked_chunks! cert22 armTarget armLayout armLegalTarget armLabelClean
  slice22Mod 4 (ext := m6ExtPrefix 187) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert22

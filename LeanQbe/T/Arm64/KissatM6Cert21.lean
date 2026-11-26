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
# KissatM6 Certificate Slice 21/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert21`) for slice `[180, 187)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert21

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 21 sub-module (`[180, 187)`, `7` functions). -/
noncomputable def slice21Mod : Module := { fns := (m6InlFns.drop 180).take 7 }

compile_linked_chunks! cert21 armTarget armLayout armLegalTarget armLabelClean
  slice21Mod 4 (ext := m6ExtPrefix 180) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert21

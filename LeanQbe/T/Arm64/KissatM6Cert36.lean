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
# KissatM6 Certificate Slice 36/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert36`) for slice `[276, 286)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert36

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 36 sub-module (`[276, 286)`, `10` functions). -/
noncomputable def slice36Mod : Module := { fns := (m6InlFns.drop 276).take 10 }

compile_linked_chunks! cert36 armTarget armLayout armLegalTarget armLabelClean
  slice36Mod 4 (ext := m6ExtPrefix 276) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert36

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
# KissatM6 Certificate Slice 48/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert48`) for slice `[355, 356)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert48

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 48 sub-module (`[355, 356)`, `1` functions). -/
def slice48Mod : Module := { fns := (m6InlFns.drop 355).take 1 }

compile_linked_chunks! cert48 armTarget armLayout armLegalTarget armLabelClean
  slice48Mod 4 (ext := m6ExtPrefix 355) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert48

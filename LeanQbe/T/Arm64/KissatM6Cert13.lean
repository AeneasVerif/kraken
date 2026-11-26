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
# KissatM6 Certificate Slice 13/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert13`) for slice `[103, 114)` (`11` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert13

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 13 sub-module (`[103, 114)`, `11` functions). -/
noncomputable def slice13Mod : Module := { fns := (m6InlFns.drop 103).take 11 }

compile_linked_chunks! cert13 armTarget armLayout armLegalTarget armLabelClean
  slice13Mod 4 (ext := m6ExtPrefix 103) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert13

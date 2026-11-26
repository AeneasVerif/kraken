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
# KissatM6 Certificate Slice 32/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert32`) for slice `[255, 264)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert32

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 32 sub-module (`[255, 264)`, `9` functions). -/
noncomputable def slice32Mod : Module := { fns := (m6InlFns.drop 255).take 9 }

compile_linked_chunks! cert32 armTarget armLayout armLegalTarget armLabelClean
  slice32Mod 4 (ext := m6ExtPrefix 255) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert32

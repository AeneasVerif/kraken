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
# KissatM6 Certificate Slice 40/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert40`) for slice `[311, 320)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert40

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 40 sub-module (`[311, 320)`, `9` functions). -/
def slice40Mod : Module := { fns := (m6InlFns.drop 311).take 9 }

compile_linked_chunks! cert40 armTarget armLayout armLegalTarget armLabelClean
  slice40Mod 4 (ext := m6ExtPrefix 311) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert40

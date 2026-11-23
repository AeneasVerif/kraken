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
# KissatM6 Certificate Slice 45/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert45`) for slice `[336, 339)` (`3` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert45

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 45 sub-module (`[336, 339)`, `3` functions). -/
def slice45Mod : Module := { fns := (m6InlFns.drop 336).take 3 }

compile_linked_chunks! cert45 armTarget armLayout armLegalTarget armLabelClean
  slice45Mod 4 (ext := m6ExtPrefix 336) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert45

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
# KissatM6 Certificate Slice 29/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert29`) for slice `[251, 252)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert29

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 29 sub-module (`[251, 252)`, `1` functions). -/
def slice29Mod : Module := { fns := (m6InlFns.drop 251).take 1 }

compile_linked_chunks! cert29 armTarget armLayout armLegalTarget armLabelClean
  slice29Mod 4 (ext := m6ExtPrefix 251) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert29

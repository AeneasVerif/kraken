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
# KissatM6 Certificate Slice 19/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert19`) for slice `[156, 168)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert19

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 19 sub-module (`[156, 168)`, `12` functions). -/
def slice19Mod : Module := { fns := (m6InlFns.drop 156).take 12 }

compile_linked_chunks! cert19 armTarget armLayout armLegalTarget armLabelClean
  slice19Mod 4 (ext := m6ExtPrefix 156) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert19

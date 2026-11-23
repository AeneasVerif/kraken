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
# KissatM6 Certificate Slice 41/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert41`) for slice `[320, 332)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert41

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 41 sub-module (`[320, 332)`, `12` functions). -/
def slice41Mod : Module := { fns := (m6InlFns.drop 320).take 12 }

compile_linked_chunks! cert41 armTarget armLayout armLegalTarget armLabelClean
  slice41Mod 4 (ext := m6ExtPrefix 320) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert41

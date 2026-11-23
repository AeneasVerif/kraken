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
# KissatM6 Certificate Slice 49/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert49`) for slice `[356, 368)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert49

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 49 sub-module (`[356, 368)`, `12` functions). -/
def slice49Mod : Module := { fns := (m6InlFns.drop 356).take 12 }

compile_linked_chunks! cert49 armTarget armLayout armLegalTarget armLabelClean
  slice49Mod 4 (ext := m6ExtPrefix 356) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert49

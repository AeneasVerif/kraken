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
# KissatM6 Certificate Slice 27/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert27`) for slice `[230, 242)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert27

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 27 sub-module (`[230, 242)`, `12` functions). -/
def slice27Mod : Module := { fns := (m6InlFns.drop 230).take 12 }

compile_linked_chunks! cert27 armTarget armLayout armLegalTarget armLabelClean
  slice27Mod 4 (ext := m6ExtPrefix 230) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert27

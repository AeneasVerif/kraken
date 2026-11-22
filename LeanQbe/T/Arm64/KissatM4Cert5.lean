module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM4Bounds
public import LeanQbe.T.Examples.Kissat.FullM4
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM4Bounds
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# KissatM4 Certificate Slice 5/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert5`) for slice `[47, 48)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 5 sub-module (`[47, 48)`, `1` functions). -/
def slice5Mod : Module := { fns := (m4Fns.drop 47).take 1 }

compile_linked_chunks! cert5 armTarget armLayout armLegalTarget armLabelClean
  slice5Mod 4 (ext := m4ExtPrefix 47) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert5

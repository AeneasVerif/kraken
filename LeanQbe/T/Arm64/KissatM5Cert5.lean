module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM5Bounds
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM5Bounds
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Certificate Slice 5/34 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert5`) for slice `[40, 52)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5Cert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 5 sub-module (`[40, 52)`, `12` functions). -/
noncomputable def slice5Mod : Module := { fns := (m5InlB5Fns.drop 40).take 12 }

compile_linked_chunks! cert5 armTarget armLayout armLegalTarget armLabelClean
  slice5Mod 4 (ext := m5ExtPrefix 40) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM5Cert5

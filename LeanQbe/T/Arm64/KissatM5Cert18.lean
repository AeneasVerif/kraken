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
# KissatM5 Certificate Slice 18/34 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert18`) for slice `[155, 164)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5Cert18

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 18 sub-module (`[155, 164)`, `9` functions). -/
noncomputable def slice18Mod : Module := { fns := (m5InlB5Fns.drop 155).take 9 }

compile_linked_chunks! cert18 armTarget armLayout armLegalTarget armLabelClean
  slice18Mod 4 (ext := m5ExtPrefix 155) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM5Cert18

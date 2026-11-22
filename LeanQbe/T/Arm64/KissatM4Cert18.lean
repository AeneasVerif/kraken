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
# KissatM4 Certificate Slice 18/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert18`) for slice `[160, 164)` (`4` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert18

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 18 sub-module (`[160, 164)`, `4` functions). -/
def slice18Mod : Module := { fns := (m4Fns.drop 160).take 4 }

compile_linked_chunks! cert18 armTarget armLayout armLegalTarget armLabelClean
  slice18Mod 4 (ext := m4ExtPrefix 160) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert18

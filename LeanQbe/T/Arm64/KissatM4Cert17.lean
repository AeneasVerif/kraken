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
# KissatM4 Certificate Slice 17/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert17`) for slice `[159, 160)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert17

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 17 sub-module (`[159, 160)`, `1` functions). -/
def slice17Mod : Module := { fns := (m4Fns.drop 159).take 1 }

compile_linked_chunks! cert17 armTarget armLayout armLegalTarget armLabelClean
  slice17Mod 4 (ext := m4ExtPrefix 159) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert17

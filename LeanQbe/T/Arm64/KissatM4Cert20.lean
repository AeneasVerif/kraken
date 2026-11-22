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
# KissatM4 Certificate Slice 20/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert20`) for slice `[170, 175)` (`5` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert20

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 20 sub-module (`[170, 175)`, `5` functions). -/
def slice20Mod : Module := { fns := (m4Fns.drop 170).take 5 }

compile_linked_chunks! cert20 armTarget armLayout armLegalTarget armLabelClean
  slice20Mod 4 (ext := m4ExtPrefix 170) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert20

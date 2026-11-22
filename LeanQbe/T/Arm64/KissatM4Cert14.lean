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
# KissatM4 Certificate Slice 14/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert14`) for slice `[127, 139)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert14

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 14 sub-module (`[127, 139)`, `12` functions). -/
def slice14Mod : Module := { fns := (m4Fns.drop 127).take 12 }

compile_linked_chunks! cert14 armTarget armLayout armLegalTarget armLabelClean
  slice14Mod 4 (ext := m4ExtPrefix 127) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert14

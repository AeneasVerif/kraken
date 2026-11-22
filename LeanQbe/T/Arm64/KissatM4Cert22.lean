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
# KissatM4 Certificate Slice 22/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert22`) for slice `[183, 184)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert22

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 22 sub-module (`[183, 184)`, `1` functions). -/
def slice22Mod : Module := { fns := (m4Fns.drop 183).take 1 }

compile_linked_chunks! cert22 armTarget armLayout armLegalTarget armLabelClean
  slice22Mod 4 (ext := m4ExtPrefix 183) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert22

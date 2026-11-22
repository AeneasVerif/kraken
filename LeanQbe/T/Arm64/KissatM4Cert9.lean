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
# KissatM4 Certificate Slice 9/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert9`) for slice `[81, 91)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert9

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 9 sub-module (`[81, 91)`, `10` functions). -/
def slice9Mod : Module := { fns := (m4Fns.drop 81).take 10 }

compile_linked_chunks! cert9 armTarget armLayout armLegalTarget armLabelClean
  slice9Mod 4 (ext := m4ExtPrefix 81) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert9

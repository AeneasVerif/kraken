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
# KissatM4 Certificate Slice 21/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert21`) for slice `[175, 183)` (`8` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert21

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 21 sub-module (`[175, 183)`, `8` functions). -/
def slice21Mod : Module := { fns := (m4Fns.drop 175).take 8 }

compile_linked_chunks! cert21 armTarget armLayout armLegalTarget armLabelClean
  slice21Mod 4 (ext := m4ExtPrefix 175) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert21

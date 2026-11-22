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
# KissatM4 Certificate Slice 25/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert25`) for slice `[197, 209)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert25

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 25 sub-module (`[197, 209)`, `12` functions). -/
def slice25Mod : Module := { fns := (m4Fns.drop 197).take 12 }

compile_linked_chunks! cert25 armTarget armLayout armLegalTarget armLabelClean
  slice25Mod 4 (ext := m4ExtPrefix 197) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert25

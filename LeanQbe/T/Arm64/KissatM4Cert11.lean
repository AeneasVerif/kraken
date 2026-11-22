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
# KissatM4 Certificate Slice 11/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert11`) for slice `[103, 112)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert11

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 11 sub-module (`[103, 112)`, `9` functions). -/
def slice11Mod : Module := { fns := (m4Fns.drop 103).take 9 }

compile_linked_chunks! cert11 armTarget armLayout armLegalTarget armLabelClean
  slice11Mod 4 (ext := m4ExtPrefix 103) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert11

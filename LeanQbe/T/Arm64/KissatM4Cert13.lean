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
# KissatM4 Certificate Slice 13/27 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert13`) for slice `[120, 127)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert13

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 13 sub-module (`[120, 127)`, `7` functions). -/
def slice13Mod : Module := { fns := (m4Fns.drop 120).take 7 }

compile_linked_chunks! cert13 armTarget armLayout armLegalTarget armLabelClean
  slice13Mod 4 (ext := m4ExtPrefix 120) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM4Cert13

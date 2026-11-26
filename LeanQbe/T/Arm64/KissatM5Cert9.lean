module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM5Bounds
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM5Bounds
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Certificate Slice 9/34 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert9`) for slice `[72, 79)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5Cert9

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 9 sub-module (`[72, 79)`, `7` functions). -/
noncomputable def slice9Mod : Module := { fns := (m5InlB5Fns.drop 72).take 7 }

compile_linked_chunks! cert9 armTarget armLayout armLegalTarget armLabelClean
  slice9Mod 4 (ext := m5ExtPrefix 72) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM5Cert9

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
# KissatM5 Certificate Slice 6/34 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert6`) for slice `[52, 53)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5Cert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 6 sub-module (`[52, 53)`, `1` functions). -/
noncomputable def slice6Mod : Module := { fns := (m5InlB5Fns.drop 52).take 1 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := m5ExtPrefix 52) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM5Cert6

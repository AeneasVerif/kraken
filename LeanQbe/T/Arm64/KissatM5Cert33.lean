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
# KissatM5 Certificate Slice 33/34 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert33`) for slice `[248, 260)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5Cert33

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 33 sub-module (`[248, 260)`, `12` functions). -/
def slice33Mod : Module := { fns := (m5InlB5Fns.drop 248).take 12 }

compile_linked_chunks! cert33 armTarget armLayout armLegalTarget armLabelClean
  slice33Mod 4 (ext := m5ExtPrefix 248) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM5Cert33

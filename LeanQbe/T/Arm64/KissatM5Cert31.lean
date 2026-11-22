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
# KissatM5 Certificate Slice 31/34 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert31`) for slice `[228, 237)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5Cert31

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 31 sub-module (`[228, 237)`, `9` functions). -/
def slice31Mod : Module := { fns := (m5InlB5Fns.drop 228).take 9 }

compile_linked_chunks! cert31 armTarget armLayout armLegalTarget armLabelClean
  slice31Mod 4 (ext := m5ExtPrefix 228) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM5Cert31

module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM6Bounds
public import LeanQbe.T.Examples.Kissat.FullM6Inl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM6Bounds
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# KissatM6 Certificate Slice 43/51 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert43`) for slice `[333, 335)` (`2` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM6Cert43

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 43 sub-module (`[333, 335)`, `2` functions). -/
def slice43Mod : Module := { fns := (m6InlFns.drop 333).take 2 }

compile_linked_chunks! cert43 armTarget armLayout armLegalTarget armLabelClean
  slice43Mod 4 (ext := m6ExtPrefix 333) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM6Cert43

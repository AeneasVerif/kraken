module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM7FidelityBounds
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM7FidelityBounds
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-!
# KissatM7Fidelity Certificate Slice 21/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert21`) for slice `[170, 176)` (`6` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert21

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 21 sub-module (`[170, 176)`, `6` functions). -/
abbrev slice21Mod : Module := { fns := (m7FidInlFns.drop 170).take 6 }

compile_linked_chunks! cert21 armTarget armLayout armLegalTarget armLabelClean
  slice21Mod 4 (ext := m7FidelityExtPrefix 170) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert21

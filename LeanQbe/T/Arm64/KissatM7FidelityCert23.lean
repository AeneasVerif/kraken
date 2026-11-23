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
# KissatM7Fidelity Certificate Slice 23/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert23`) for slice `[340, 345)` (`5` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert23

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 23 sub-module (`[340, 345)`, `5` functions). -/
abbrev slice23Mod : Module := { fns := (m7FidInlFns.drop 340).take 5 }

compile_linked_chunks! cert23 armTarget armLayout armLegalTarget armLabelClean
  slice23Mod 4 (ext := m7FidelityExtPrefix 340) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert23

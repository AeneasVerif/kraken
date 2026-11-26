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
# KissatM7Fidelity Certificate Slice 28/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert28`) for slice `[351, 353)` (`2` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert28

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 28 sub-module (`[351, 353)`, `2` functions). -/
noncomputable abbrev slice28Mod : Module := { fns := (m7FidInlFns.drop 351).take 2 }

compile_linked_chunks! cert28 armTarget armLayout armLegalTarget armLabelClean
  slice28Mod 4 (ext := m7FidelityExtPrefix 351) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert28

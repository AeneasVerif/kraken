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
# KissatM7Fidelity Certificate Slice 37/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert37`) for slice `[382, 383)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert37

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 37 sub-module (`[382, 383)`, `1` functions). -/
noncomputable abbrev slice37Mod : Module := { fns := (m7FidInlFns.drop 382).take 1 }

compile_linked_chunks! cert37 armTarget armLayout armLegalTarget armLabelClean
  slice37Mod 4 (ext := m7FidelityExtPrefix 382) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert37

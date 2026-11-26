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
# KissatM7Fidelity Certificate Slice 39/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert39`) for slice `[385, 386)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert39

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 39 sub-module (`[385, 386)`, `1` functions). -/
noncomputable abbrev slice39Mod : Module := { fns := (m7FidInlFns.drop 385).take 1 }

compile_linked_chunks! cert39 armTarget armLayout armLegalTarget armLabelClean
  slice39Mod 4 (ext := m7FidelityExtPrefix 385) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert39

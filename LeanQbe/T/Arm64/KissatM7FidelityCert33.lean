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
# KissatM7Fidelity Certificate Slice 33/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert33`) for slice `[366, 370)` (`4` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert33

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 33 sub-module (`[366, 370)`, `4` functions). -/
noncomputable abbrev slice33Mod : Module := { fns := (m7FidInlFns.drop 366).take 4 }

compile_linked_chunks! cert33 armTarget armLayout armLegalTarget armLabelClean
  slice33Mod 4 (ext := m7FidelityExtPrefix 366) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert33

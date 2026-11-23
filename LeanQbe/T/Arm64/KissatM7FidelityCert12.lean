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
# KissatM7Fidelity Certificate Slice 12/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert12`) for slice `[131, 136)` (`5` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert12

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 12 sub-module (`[131, 136)`, `5` functions). -/
abbrev slice12Mod : Module := { fns := (m7FidInlFns.drop 131).take 5 }

compile_linked_chunks! cert12 armTarget armLayout armLegalTarget armLabelClean
  slice12Mod 4 (ext := m7FidelityExtPrefix 131) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert12

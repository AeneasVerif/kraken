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
# KissatM7Fidelity Certificate Slice 40/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert40`) for slice `[386, 391)` (`5` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert40

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 40 sub-module (`[386, 391)`, `5` functions). -/
abbrev slice40Mod : Module := { fns := (m7FidInlFns.drop 386).take 5 }

compile_linked_chunks! cert40 armTarget armLayout armLegalTarget armLabelClean
  slice40Mod 4 (ext := m7FidelityExtPrefix 386) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert40

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
# KissatM7Fidelity Certificate Slice 47/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert47`) for slice `[406, 408)` (`2` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert47

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 47 sub-module (`[406, 408)`, `2` functions). -/
abbrev slice47Mod : Module := { fns := (m7FidInlFns.drop 406).take 2 }

compile_linked_chunks! cert47 armTarget armLayout armLegalTarget armLabelClean
  slice47Mod 4 (ext := m7FidelityExtPrefix 406) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert47

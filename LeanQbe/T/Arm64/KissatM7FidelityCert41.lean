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
# KissatM7Fidelity Certificate Slice 41/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert41`) for slice `[391, 395)` (`4` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert41

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 41 sub-module (`[391, 395)`, `4` functions). -/
noncomputable abbrev slice41Mod : Module := { fns := (m7FidInlFns.drop 391).take 4 }

compile_linked_chunks! cert41 armTarget armLayout armLegalTarget armLabelClean
  slice41Mod 4 (ext := m7FidelityExtPrefix 391) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert41

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
# KissatM7Fidelity Certificate Slice 44/49 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert44`) for slice `[401, 404)` (`3` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7FidelityCert44

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 44 sub-module (`[401, 404)`, `3` functions). -/
abbrev slice44Mod : Module := { fns := (m7FidInlFns.drop 401).take 3 }

compile_linked_chunks! cert44 armTarget armLayout armLegalTarget armLabelClean
  slice44Mod 4 (ext := m7FidelityExtPrefix 401) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7FidelityCert44

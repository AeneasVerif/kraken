module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM7FidelityBounds
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM7FidelityBounds
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-!
# KissatM7Fidelity Certificate Slice 10/49 on SysV x64

Kernel-checked compilation cert (`cert10`) for slice `[119, 120)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert10

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 10 sub-module (`[119, 120)`, `1` functions). -/
noncomputable abbrev slice10Mod : Module := { fns := (m7FidInlFns.drop 119).take 1 }

compile_linked_chunks! cert10 x64Target x64Layout x64LegalTarget x64LabelClean
  slice10Mod 4 (ext := m7FidelityExtPrefix 119) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert10

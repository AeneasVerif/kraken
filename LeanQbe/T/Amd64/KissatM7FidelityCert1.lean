module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-!
# KissatM7Fidelity Certificate Slice 1/49 on SysV x64

Kernel-checked compilation cert (`cert1`) for slice `[0, 7)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 1 sub-module (`[0, 7)`, `7` functions). -/
noncomputable abbrev slice1Mod : Module := { fns := m7FidInlFns.take 7 }

compile_linked_chunks! cert1 x64Target x64Layout x64LegalTarget x64LabelClean
  slice1Mod 4 (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert1

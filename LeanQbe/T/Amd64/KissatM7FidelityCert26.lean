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
# KissatM7Fidelity Certificate Slice 26/49 on SysV x64

Kernel-checked compilation cert (`cert26`) for slice `[349, 350)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert26

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 26 sub-module (`[349, 350)`, `1` functions). -/
noncomputable abbrev slice26Mod : Module := { fns := (m7FidInlFns.drop 349).take 1 }

compile_linked_chunks! cert26 x64Target x64Layout x64LegalTarget x64LabelClean
  slice26Mod 4 (ext := m7FidelityExtPrefix 349) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert26

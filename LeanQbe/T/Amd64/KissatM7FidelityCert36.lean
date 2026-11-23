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
# KissatM7Fidelity Certificate Slice 36/49 on SysV x64

Kernel-checked compilation cert (`cert36`) for slice `[380, 382)` (`2` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert36

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 36 sub-module (`[380, 382)`, `2` functions). -/
abbrev slice36Mod : Module := { fns := (m7FidInlFns.drop 380).take 2 }

compile_linked_chunks! cert36 x64Target x64Layout x64LegalTarget x64LabelClean
  slice36Mod 4 (ext := m7FidelityExtPrefix 380) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert36

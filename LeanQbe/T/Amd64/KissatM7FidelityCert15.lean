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
# KissatM7Fidelity Certificate Slice 15/49 on SysV x64

Kernel-checked compilation cert (`cert15`) for slice `[139, 140)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert15

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 15 sub-module (`[139, 140)`, `1` functions). -/
abbrev slice15Mod : Module := { fns := (m7FidInlFns.drop 139).take 1 }

compile_linked_chunks! cert15 x64Target x64Layout x64LegalTarget x64LabelClean
  slice15Mod 4 (ext := m7FidelityExtPrefix 139) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert15

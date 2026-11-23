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
# KissatM7Fidelity Certificate Slice 16/49 on SysV x64

Kernel-checked compilation cert (`cert16`) for slice `[160, 161)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert16

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 16 sub-module (`[160, 161)`, `1` functions). -/
abbrev slice16Mod : Module := { fns := (m7FidInlFns.drop 160).take 1 }

compile_linked_chunks! cert16 x64Target x64Layout x64LegalTarget x64LabelClean
  slice16Mod 4 (ext := m7FidelityExtPrefix 160) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert16

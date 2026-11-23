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
# KissatM7Fidelity Certificate Slice 13/49 on SysV x64

Kernel-checked compilation cert (`cert13`) for slice `[136, 137)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert13

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 13 sub-module (`[136, 137)`, `1` functions). -/
abbrev slice13Mod : Module := { fns := (m7FidInlFns.drop 136).take 1 }

compile_linked_chunks! cert13 x64Target x64Layout x64LegalTarget x64LabelClean
  slice13Mod 4 (ext := m7FidelityExtPrefix 136) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert13

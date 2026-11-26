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
# KissatM7Fidelity Certificate Slice 22/49 on SysV x64

Kernel-checked compilation cert (`cert22`) for slice `[176, 179)` (`3` functions) of
`LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM7FidelityCert22

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-- Slice 22 sub-module (`[176, 179)`, `3` functions). -/
noncomputable abbrev slice22Mod : Module := { fns := (m7FidInlFns.drop 176).take 3 }

compile_linked_chunks! cert22 x64Target x64Layout x64LegalTarget x64LabelClean
  slice22Mod 4 (ext := m7FidelityExtPrefix 176) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7FidelityCert22

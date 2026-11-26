module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM7PlusBounds
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM7PlusBounds
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# KissatM7Plus Certificate Slice 36/56 on SysV x64

Kernel-checked compilation cert (`cert36`) for slice `[285, 286)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert36

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 36 sub-module (`[285, 286)`, `1` functions). -/
noncomputable def slice36Mod : Module := { fns := (m7PlusInlFns.drop 285).take 1 }

compile_linked_chunks! cert36 x64Target x64Layout x64LegalTarget x64LabelClean
  slice36Mod 4 (ext := m7PlusExtPrefix 285) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert36

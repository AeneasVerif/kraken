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
# KissatM7Plus Certificate Slice 26/56 on SysV x64

Kernel-checked compilation cert (`cert26`) for slice `[209, 221)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert26

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 26 sub-module (`[209, 221)`, `12` functions). -/
noncomputable def slice26Mod : Module := { fns := (m7PlusInlFns.drop 209).take 12 }

compile_linked_chunks! cert26 x64Target x64Layout x64LegalTarget x64LabelClean
  slice26Mod 4 (ext := m7PlusExtPrefix 209) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert26

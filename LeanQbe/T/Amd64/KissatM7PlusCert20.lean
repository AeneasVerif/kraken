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
# KissatM7Plus Certificate Slice 20/56 on SysV x64

Kernel-checked compilation cert (`cert20`) for slice `[150, 160)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert20

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 20 sub-module (`[150, 160)`, `10` functions). -/
noncomputable def slice20Mod : Module := { fns := (m7PlusInlFns.drop 150).take 10 }

compile_linked_chunks! cert20 x64Target x64Layout x64LegalTarget x64LabelClean
  slice20Mod 4 (ext := m7PlusExtPrefix 150) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert20

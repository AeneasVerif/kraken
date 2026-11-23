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
# KissatM7Plus Certificate Slice 48/56 on SysV x64

Kernel-checked compilation cert (`cert48`) for slice `[349, 350)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert48

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 48 sub-module (`[349, 350)`, `1` functions). -/
def slice48Mod : Module := { fns := (m7PlusInlFns.drop 349).take 1 }

compile_linked_chunks! cert48 x64Target x64Layout x64LegalTarget x64LabelClean
  slice48Mod 4 (ext := m7PlusExtPrefix 349) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert48

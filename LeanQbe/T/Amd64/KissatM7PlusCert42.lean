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
# KissatM7Plus Certificate Slice 42/56 on SysV x64

Kernel-checked compilation cert (`cert42`) for slice `[325, 332)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert42

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 42 sub-module (`[325, 332)`, `7` functions). -/
def slice42Mod : Module := { fns := (m7PlusInlFns.drop 325).take 7 }

compile_linked_chunks! cert42 x64Target x64Layout x64LegalTarget x64LabelClean
  slice42Mod 4 (ext := m7PlusExtPrefix 325) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert42

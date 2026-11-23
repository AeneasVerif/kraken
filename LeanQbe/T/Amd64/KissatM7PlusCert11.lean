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
# KissatM7Plus Certificate Slice 11/56 on SysV x64

Kernel-checked compilation cert (`cert11`) for slice `[86, 95)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCert11

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 11 sub-module (`[86, 95)`, `9` functions). -/
def slice11Mod : Module := { fns := (m7PlusInlFns.drop 86).take 9 }

compile_linked_chunks! cert11 x64Target x64Layout x64LegalTarget x64LabelClean
  slice11Mod 4 (ext := m7PlusExtPrefix 86) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM7PlusCert11

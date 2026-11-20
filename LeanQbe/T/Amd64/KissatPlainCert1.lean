module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain1
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1

/-!
# Kissat `D-Plain` Part 1 (`plain1Module`) Compilation Certificate on SysV x64 (`Stage 3`)

Compiles and links the first 39 functions (`dimacs_fns ++ plain1_fns`) of Kissat `D-Plain`
on `x64Target` (`x64LegalTarget`, `x64Layout`, `x64LabelClean`) via `compile_linked_chunks!`:
* `plainPart1`: `LinkedCert` for `plain1Module` with `plainPart1.exportedExt`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatPlainCert1

open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Amd64

open scoped LeanQbe.T in
compile_linked_chunks! plainPart1
  x64Target x64Layout x64LegalTarget x64LabelClean plain1Module 4 (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert1

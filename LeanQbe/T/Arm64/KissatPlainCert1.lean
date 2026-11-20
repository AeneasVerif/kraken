module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain1
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1

/-!
# Kissat `D-Plain` Part 1 (`plain1Module`) Compilation Certificate on AArch64 (`Stage 3`)

Compiles and links the first 39 functions (`dimacs_fns ++ plain1_fns`) of Kissat `D-Plain`
on `armTarget` (`armLegalTarget`, `armLayout`, `armLabelClean`) via `compile_linked_chunks!`:
* `plainPart1`: `LinkedCert` for `plain1Module` with `plainPart1.exportedExt`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert1

open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Arm64

open scoped LeanQbe.T in
compile_linked_chunks! plainPart1
  armTarget armLayout armLegalTarget armLabelClean plain1Module 4 (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert1

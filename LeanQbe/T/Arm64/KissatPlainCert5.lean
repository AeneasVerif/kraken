module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` Certificate Slice 5/6 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert5`) for slice `[47, 52)` (`5` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `armTarget`, with prefix bounds computed via
`eval_prefix_ext!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

open scoped LeanQbe.T in
eval_prefix_ext! ext5 armTarget armLegalTarget (plainFns.take 47)

/-- Slice 5 sub-module (`[47, 52)`, `5` functions). -/
def slice5Mod : Module :=
  { fns := (plainFns.drop 47).take 5, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert5
  armTarget armLayout armLegalTarget armLabelClean slice5Mod 4
  (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert5

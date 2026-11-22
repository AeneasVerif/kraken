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
# Kissat `D-Plain` Certificate Slice 3/6 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert3`) for slice `[29, 40)` (`11` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `armTarget`, with prefix bounds computed via
`eval_prefix_ext!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert3

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

open scoped LeanQbe.T in
eval_prefix_ext! ext3 armTarget armLegalTarget (plainFns.take 29)

/-- Slice 3 sub-module (`[29, 40)`, `11` functions). -/
def slice3Mod : Module :=
  { fns := (plainFns.drop 29).take 11, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert3
  armTarget armLayout armLegalTarget armLabelClean slice3Mod 4
  (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert3

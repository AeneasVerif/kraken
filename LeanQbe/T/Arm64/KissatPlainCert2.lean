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
# Kissat `D-Plain` Certificate Slice 2/6 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2`) for slice `[15, 29)` (`14` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `armTarget`, with prefix bounds computed via
`eval_prefix_ext!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

open scoped LeanQbe.T in
eval_prefix_ext! ext2 armTarget armLegalTarget (plainFns.take 15)

/-- Slice 2 sub-module (`[15, 29)`, `14` functions). -/
def slice2Mod : Module :=
  { fns := (plainFns.drop 15).take 14, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert2
  armTarget armLayout armLegalTarget armLabelClean slice2Mod 4
  (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert2

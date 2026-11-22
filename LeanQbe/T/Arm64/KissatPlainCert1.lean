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
# Kissat `D-Plain` Certificate Slice 1/6 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1`) for slice `[0, 15)` (`15` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain

/-- Slice 1 sub-module (`[0, 15)`, `15` functions). -/
def slice1Mod : Module := { fns := plainFns.take 15, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert1
  armTarget armLayout armLegalTarget armLabelClean slice1Mod 4 (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert1

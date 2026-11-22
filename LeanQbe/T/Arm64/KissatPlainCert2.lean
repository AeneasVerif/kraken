module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Arm64.KissatPlainBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Arm64.KissatPlainBounds

/-!
# Kissat `D-Plain` Certificate Slice 2/6 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2`) for slice `[15, 29)` (`14` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `armTarget`, with prefix bounds from
`KissatPlainBounds.plainExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Arm64.KissatPlainBounds

/-- Slice 2 sub-module (`[15, 29)`, `14` functions). -/
def slice2Mod : Module :=
  { fns := (plainFns.drop 15).take 14, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert2
  armTarget armLayout armLegalTarget armLabelClean slice2Mod 4
  (ext := plainExtPrefix 15) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert2

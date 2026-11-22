module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Arm64.KissatPlainBounds
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Arm64.KissatPlainBounds

/-!
# Kissat `D-Plain` Certificate Slice 4/6 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert4`) for slice `[40, 47)` (`7` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `armTarget`, with prefix bounds from
`KissatPlainBounds.plainExtPrefix`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Arm64.KissatPlainBounds

/-- Slice 4 sub-module (`[40, 47)`, `7` functions). -/
def slice4Mod : Module :=
  { fns := (plainFns.drop 40).take 7, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert4
  armTarget armLayout armLegalTarget armLabelClean slice4Mod 4
  (ext := plainExtPrefix 40) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatPlainCert4

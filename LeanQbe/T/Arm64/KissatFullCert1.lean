module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Kissat `D-Full` Native Certificate Slice 1/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1`) for slice `[0, 38)` (`38` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

/-- Slice 1 sub-module (`[0, 38)`, `38` functions). -/
def slice1Mod : Module := { fns := fullFns.take 38 }

compile_linked_chunks! cert1 armTarget armLayout armLegalTarget armLabelClean
  slice1Mod 4 (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert1

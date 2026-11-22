module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1a/19 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1a`) for slice `[0, 16)` (`16`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert1a

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Slice 1a sub-module (`[0, 16)`, `16` functions). -/
def slice1aMod : Module := { fns := m3Fns.take 16 }

compile_linked_chunks! cert1a armTarget armLayout armLegalTarget armLabelClean
  slice1aMod 4 (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert1a

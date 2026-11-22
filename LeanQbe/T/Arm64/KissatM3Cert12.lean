module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Arm64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Arm64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 12/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert12`) for slice `[152, 158)` (`6`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert12

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 12 sub-module (`[152, 158)`, `6` functions). -/
def slice12Mod : Module := { fns := (m3Fns.drop 152).take 6 }

compile_linked_chunks! cert12 armTarget armLayout armLegalTarget armLabelClean
  slice12Mod 4 (ext := m3ExtPrefix 152) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert12

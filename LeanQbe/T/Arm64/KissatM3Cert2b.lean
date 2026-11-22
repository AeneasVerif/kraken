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
# Kissat M3 (`FullM3`) Certificate Slice 2b/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2b`) for slice `[48, 59)` (`11`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert2b

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 2b sub-module (`[48, 59)`, `11` functions). -/
def slice2bMod : Module := { fns := (m3Fns.drop 48).take 11 }

compile_linked_chunks! cert2b armTarget armLayout armLegalTarget armLabelClean
  slice2bMod 4 (ext := m3ExtPrefix 48) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert2b

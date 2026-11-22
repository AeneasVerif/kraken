module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Arm64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Arm64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1b/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1b`) for slice `[16, 32)` (`16`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert1b

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 1b sub-module (`[16, 32)`, `16` functions). -/
def slice1bMod : Module := { fns := (m3Fns.drop 16).take 16 }

compile_linked_chunks! cert1b armTarget armLayout armLegalTarget armLabelClean
  slice1bMod 4 (ext := m3ExtPrefix 16) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert1b

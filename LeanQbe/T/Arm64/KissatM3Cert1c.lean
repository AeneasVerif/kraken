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
# Kissat M3 (`FullM3`) Certificate Slice 1c/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1c`) for slice `[32, 47)` (`15`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert1c

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 1c sub-module (`[32, 47)`, `15` functions). -/
def slice1cMod : Module := { fns := (m3Fns.drop 32).take 15 }

compile_linked_chunks! cert1c armTarget armLayout armLegalTarget armLabelClean
  slice1cMod 4 (ext := m3ExtPrefix 32) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert1c

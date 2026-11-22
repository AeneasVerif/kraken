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
# Kissat M3 (`FullM3`) Certificate Slice 14/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert14`) for slice `[167, 175)` (`8`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert14

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 14 sub-module (`[167, 175)`, `8` functions). -/
def slice14Mod : Module := { fns := (m3Fns.drop 167).take 8 }

compile_linked_chunks! cert14 armTarget armLayout armLegalTarget armLabelClean
  slice14Mod 4 (ext := m3ExtPrefix 167) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert14

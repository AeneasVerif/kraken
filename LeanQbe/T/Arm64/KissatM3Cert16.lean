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
# Kissat M3 (`FullM3`) Certificate Slice 16/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert16`) for slice `[183, 195)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert16

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 16 sub-module (`[183, 195)`, `12` functions). -/
def slice16Mod : Module := { fns := (m3Fns.drop 183).take 12 }

compile_linked_chunks! cert16 armTarget armLayout armLegalTarget armLabelClean
  slice16Mod 4 (ext := m3ExtPrefix 183) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert16

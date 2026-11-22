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
# Kissat M3 (`FullM3`) Certificate Slice 11/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert11`) for slice `[140, 152)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert11

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 11 sub-module (`[140, 152)`, `12` functions). -/
def slice11Mod : Module := { fns := (m3Fns.drop 140).take 12 }

compile_linked_chunks! cert11 armTarget armLayout armLegalTarget armLabelClean
  slice11Mod 4 (ext := m3ExtPrefix 140) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert11

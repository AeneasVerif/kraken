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
# Kissat M3 (`FullM3`) Certificate Slice 10/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert10`) for slice `[129, 140)` (`11`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert10

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 10 sub-module (`[129, 140)`, `11` functions). -/
def slice10Mod : Module := { fns := (m3Fns.drop 129).take 11 }

compile_linked_chunks! cert10 armTarget armLayout armLegalTarget armLabelClean
  slice10Mod 4 (ext := m3ExtPrefix 129) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert10

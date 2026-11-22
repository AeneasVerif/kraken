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
# Kissat M3 (`FullM3`) Certificate Slice 17a/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert17a`) for slice `[195, 199)` (`4`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert17a

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 17a sub-module (`[195, 199)`, `4` functions). -/
def slice17aMod : Module := { fns := (m3Fns.drop 195).take 4 }

compile_linked_chunks! cert17a armTarget armLayout armLegalTarget armLabelClean
  slice17aMod 4 (ext := m3ExtPrefix 195) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert17a

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
# Kissat M3 (`FullM3`) Certificate Slice 2a/21 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2a`) for slice `[47, 48)` (`1` heavy
function: `full_prop_lit_raw`) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert2a

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Arm64.KissatM3Bounds

/-- Slice 2a sub-module (`[47, 48)`, `1` function: `full_prop_lit_raw`). -/
def slice2aMod : Module := { fns := (m3Fns.drop 47).take 1 }

compile_linked_chunks! cert2a armTarget armLayout armLegalTarget armLabelClean
  slice2aMod 4 (ext := m3ExtPrefix 47) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert2a

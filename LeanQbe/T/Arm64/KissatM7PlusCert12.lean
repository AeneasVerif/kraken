module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatM7PlusBounds
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM7PlusBounds
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# KissatM7Plus Certificate Slice 12/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert12`) for slice `[95, 102)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert12

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 12 sub-module (`[95, 102)`, `7` functions). -/
noncomputable def slice12Mod : Module := { fns := (m7PlusInlFns.drop 95).take 7 }

compile_linked_chunks! cert12 armTarget armLayout armLegalTarget armLabelClean
  slice12Mod 4 (ext := m7PlusExtPrefix 95) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert12

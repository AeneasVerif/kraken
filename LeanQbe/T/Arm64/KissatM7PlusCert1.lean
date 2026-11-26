module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# KissatM7Plus Certificate Slice 1/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert1`) for slice `[0, 12)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 1 sub-module (`[0, 12)`, `12` functions). -/
noncomputable def slice1Mod : Module := { fns := m7PlusInlFns.take 12 }

compile_linked_chunks! cert1 armTarget armLayout armLegalTarget armLabelClean
  slice1Mod 4 (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert1

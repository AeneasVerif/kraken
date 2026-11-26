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
# KissatM7Plus Certificate Slice 45/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert45`) for slice `[340, 346)` (`6` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert45

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 45 sub-module (`[340, 346)`, `6` functions). -/
noncomputable def slice45Mod : Module := { fns := (m7PlusInlFns.drop 340).take 6 }

compile_linked_chunks! cert45 armTarget armLayout armLegalTarget armLabelClean
  slice45Mod 4 (ext := m7PlusExtPrefix 340) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert45

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
# KissatM7Plus Certificate Slice 46/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert46`) for slice `[346, 347)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert46

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 46 sub-module (`[346, 347)`, `1` functions). -/
noncomputable def slice46Mod : Module := { fns := (m7PlusInlFns.drop 346).take 1 }

compile_linked_chunks! cert46 armTarget armLayout armLegalTarget armLabelClean
  slice46Mod 4 (ext := m7PlusExtPrefix 346) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert46

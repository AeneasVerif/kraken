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
# KissatM7Plus Certificate Slice 3/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert3`) for slice `[24, 36)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert3

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 3 sub-module (`[24, 36)`, `12` functions). -/
noncomputable def slice3Mod : Module := { fns := (m7PlusInlFns.drop 24).take 12 }

compile_linked_chunks! cert3 armTarget armLayout armLegalTarget armLabelClean
  slice3Mod 4 (ext := m7PlusExtPrefix 24) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert3

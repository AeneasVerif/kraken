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
# KissatM7Plus Certificate Slice 33/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert33`) for slice `[261, 262)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert33

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 33 sub-module (`[261, 262)`, `1` functions). -/
noncomputable def slice33Mod : Module := { fns := (m7PlusInlFns.drop 261).take 1 }

compile_linked_chunks! cert33 armTarget armLayout armLegalTarget armLabelClean
  slice33Mod 4 (ext := m7PlusExtPrefix 261) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert33

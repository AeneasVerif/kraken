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
# KissatM7Plus Certificate Slice 17/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert17`) for slice `[121, 130)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert17

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 17 sub-module (`[121, 130)`, `9` functions). -/
noncomputable def slice17Mod : Module := { fns := (m7PlusInlFns.drop 121).take 9 }

compile_linked_chunks! cert17 armTarget armLayout armLegalTarget armLabelClean
  slice17Mod 4 (ext := m7PlusExtPrefix 121) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert17

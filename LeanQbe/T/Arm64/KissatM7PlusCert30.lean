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
# KissatM7Plus Certificate Slice 30/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert30`) for slice `[249, 258)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert30

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 30 sub-module (`[249, 258)`, `9` functions). -/
noncomputable def slice30Mod : Module := { fns := (m7PlusInlFns.drop 249).take 9 }

compile_linked_chunks! cert30 armTarget armLayout armLegalTarget armLabelClean
  slice30Mod 4 (ext := m7PlusExtPrefix 249) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert30

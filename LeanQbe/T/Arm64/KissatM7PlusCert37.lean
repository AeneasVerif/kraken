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
# KissatM7Plus Certificate Slice 37/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert37`) for slice `[286, 287)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert37

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 37 sub-module (`[286, 287)`, `1` functions). -/
noncomputable def slice37Mod : Module := { fns := (m7PlusInlFns.drop 286).take 1 }

compile_linked_chunks! cert37 armTarget armLayout armLegalTarget armLabelClean
  slice37Mod 4 (ext := m7PlusExtPrefix 286) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert37

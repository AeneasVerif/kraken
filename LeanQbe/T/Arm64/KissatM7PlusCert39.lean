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
# KissatM7Plus Certificate Slice 39/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert39`) for slice `[298, 308)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert39

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 39 sub-module (`[298, 308)`, `10` functions). -/
noncomputable def slice39Mod : Module := { fns := (m7PlusInlFns.drop 298).take 10 }

compile_linked_chunks! cert39 armTarget armLayout armLegalTarget armLabelClean
  slice39Mod 4 (ext := m7PlusExtPrefix 298) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert39

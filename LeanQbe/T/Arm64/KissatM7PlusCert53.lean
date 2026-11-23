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
# KissatM7Plus Certificate Slice 53/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert53`) for slice `[370, 382)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert53

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 53 sub-module (`[370, 382)`, `12` functions). -/
def slice53Mod : Module := { fns := (m7PlusInlFns.drop 370).take 12 }

compile_linked_chunks! cert53 armTarget armLayout armLegalTarget armLabelClean
  slice53Mod 4 (ext := m7PlusExtPrefix 370) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert53

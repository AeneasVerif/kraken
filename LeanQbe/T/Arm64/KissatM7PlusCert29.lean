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
# KissatM7Plus Certificate Slice 29/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert29`) for slice `[239, 249)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert29

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 29 sub-module (`[239, 249)`, `10` functions). -/
def slice29Mod : Module := { fns := (m7PlusInlFns.drop 239).take 10 }

compile_linked_chunks! cert29 armTarget armLayout armLegalTarget armLabelClean
  slice29Mod 4 (ext := m7PlusExtPrefix 239) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert29

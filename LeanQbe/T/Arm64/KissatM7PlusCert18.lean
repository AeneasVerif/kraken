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
# KissatM7Plus Certificate Slice 18/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert18`) for slice `[130, 140)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert18

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 18 sub-module (`[130, 140)`, `10` functions). -/
def slice18Mod : Module := { fns := (m7PlusInlFns.drop 130).take 10 }

compile_linked_chunks! cert18 armTarget armLayout armLegalTarget armLabelClean
  slice18Mod 4 (ext := m7PlusExtPrefix 130) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert18

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
# KissatM7Plus Certificate Slice 47/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert47`) for slice `[347, 349)` (`2` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert47

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 47 sub-module (`[347, 349)`, `2` functions). -/
def slice47Mod : Module := { fns := (m7PlusInlFns.drop 347).take 2 }

compile_linked_chunks! cert47 armTarget armLayout armLegalTarget armLabelClean
  slice47Mod 4 (ext := m7PlusExtPrefix 347) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert47

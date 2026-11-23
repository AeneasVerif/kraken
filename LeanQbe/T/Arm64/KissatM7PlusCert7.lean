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
# KissatM7Plus Certificate Slice 7/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert7`) for slice `[71, 83)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert7

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 7 sub-module (`[71, 83)`, `12` functions). -/
def slice7Mod : Module := { fns := (m7PlusInlFns.drop 71).take 12 }

compile_linked_chunks! cert7 armTarget armLayout armLegalTarget armLabelClean
  slice7Mod 4 (ext := m7PlusExtPrefix 71) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert7

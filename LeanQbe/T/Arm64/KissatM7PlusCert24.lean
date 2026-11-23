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
# KissatM7Plus Certificate Slice 24/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert24`) for slice `[187, 197)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert24

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 24 sub-module (`[187, 197)`, `10` functions). -/
def slice24Mod : Module := { fns := (m7PlusInlFns.drop 187).take 10 }

compile_linked_chunks! cert24 armTarget armLayout armLegalTarget armLabelClean
  slice24Mod 4 (ext := m7PlusExtPrefix 187) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert24

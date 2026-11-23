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
# KissatM7Plus Certificate Slice 20/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert20`) for slice `[150, 160)` (`10` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert20

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 20 sub-module (`[150, 160)`, `10` functions). -/
def slice20Mod : Module := { fns := (m7PlusInlFns.drop 150).take 10 }

compile_linked_chunks! cert20 armTarget armLayout armLegalTarget armLabelClean
  slice20Mod 4 (ext := m7PlusExtPrefix 150) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert20

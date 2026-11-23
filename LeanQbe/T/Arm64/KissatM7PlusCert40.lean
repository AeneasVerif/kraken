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
# KissatM7Plus Certificate Slice 40/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert40`) for slice `[308, 316)` (`8` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert40

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 40 sub-module (`[308, 316)`, `8` functions). -/
def slice40Mod : Module := { fns := (m7PlusInlFns.drop 308).take 8 }

compile_linked_chunks! cert40 armTarget armLayout armLegalTarget armLabelClean
  slice40Mod 4 (ext := m7PlusExtPrefix 308) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert40

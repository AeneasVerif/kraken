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
# KissatM7Plus Certificate Slice 41/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert41`) for slice `[316, 325)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert41

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 41 sub-module (`[316, 325)`, `9` functions). -/
def slice41Mod : Module := { fns := (m7PlusInlFns.drop 316).take 9 }

compile_linked_chunks! cert41 armTarget armLayout armLegalTarget armLabelClean
  slice41Mod 4 (ext := m7PlusExtPrefix 316) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert41

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
# KissatM7Plus Certificate Slice 4/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert4`) for slice `[36, 47)` (`11` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 4 sub-module (`[36, 47)`, `11` functions). -/
def slice4Mod : Module := { fns := (m7PlusInlFns.drop 36).take 11 }

compile_linked_chunks! cert4 armTarget armLayout armLegalTarget armLabelClean
  slice4Mod 4 (ext := m7PlusExtPrefix 36) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert4

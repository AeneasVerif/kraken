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
# KissatM7Plus Certificate Slice 55/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert55`) for slice `[394, 401)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert55

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 55 sub-module (`[394, 401)`, `7` functions). -/
def slice55Mod : Module := { fns := (m7PlusInlFns.drop 394).take 7 }

compile_linked_chunks! cert55 armTarget armLayout armLegalTarget armLabelClean
  slice55Mod 4 (ext := m7PlusExtPrefix 394) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert55

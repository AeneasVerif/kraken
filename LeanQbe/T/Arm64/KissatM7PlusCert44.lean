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
# KissatM7Plus Certificate Slice 44/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert44`) for slice `[333, 340)` (`7` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert44

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 44 sub-module (`[333, 340)`, `7` functions). -/
def slice44Mod : Module := { fns := (m7PlusInlFns.drop 333).take 7 }

compile_linked_chunks! cert44 armTarget armLayout armLegalTarget armLabelClean
  slice44Mod 4 (ext := m7PlusExtPrefix 333) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert44

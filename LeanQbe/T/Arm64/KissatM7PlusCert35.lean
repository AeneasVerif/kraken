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
# KissatM7Plus Certificate Slice 35/56 on AAPCS64 Arm64

Kernel-checked compilation cert (`cert35`) for slice `[273, 285)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCert35

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusBounds
open LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-- Slice 35 sub-module (`[273, 285)`, `12` functions). -/
def slice35Mod : Module := { fns := (m7PlusInlFns.drop 273).take 12 }

compile_linked_chunks! cert35 armTarget armLayout armLegalTarget armLabelClean
  slice35Mod 4 (ext := m7PlusExtPrefix 273) (maxDirs := 600)

end LeanQbe.T.Arm64.KissatM7PlusCert35

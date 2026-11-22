module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 6/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert6`) for slice `[122, 144)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext5 armTarget armLegalTarget (fastFns.take 122)

/-- Slice 6 sub-module (`[122, 144)`, `22` functions). -/
def slice6Mod : Module := { fns := (fastFns.drop 122).take 22 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert6

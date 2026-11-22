module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 3/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert3`) for slice `[56, 78)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert3

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext2 armTarget armLegalTarget (fastFns.take 56)

/-- Slice 3 sub-module (`[56, 78)`, `22` functions). -/
def slice3Mod : Module := { fns := (fastFns.drop 56).take 22 }

compile_linked_chunks! cert3 armTarget armLayout armLegalTarget armLabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert3

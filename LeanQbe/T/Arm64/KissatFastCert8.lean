module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 8/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert8`) for slice `[166, 184)` (`18`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert8

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext7 armTarget armLegalTarget (fastFns.take 166)

/-- Slice 8 sub-module (`[166, 184)`, `18` functions). -/
def slice8Mod : Module := { fns := (fastFns.drop 166).take 18 }

compile_linked_chunks! cert8 armTarget armLayout armLegalTarget armLabelClean
  slice8Mod 4 (ext := ext7) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert8

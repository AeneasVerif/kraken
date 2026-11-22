module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 9/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert9`) for slice `[184, 196)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert9

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext8 armTarget armLegalTarget (fastFns.take 184)

/-- Slice 9 sub-module (`[184, 196)`, `12` functions). -/
def slice9Mod : Module := { fns := fastFns.drop 184 }

compile_linked_chunks! cert9 armTarget armLayout armLegalTarget armLabelClean
  slice9Mod 4 (ext := ext8) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert9

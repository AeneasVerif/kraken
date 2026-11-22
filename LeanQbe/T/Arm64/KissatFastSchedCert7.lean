module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 7/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert7`) for slice `[152, 173)` (`21`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastSchedCert7

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFastSched

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext6 armTarget armLegalTarget (schedSplicedFns.take 152)

/-- Slice 7 sub-module (`[152, 173)`, `21` functions). -/
def slice7Mod : Module := { fns := schedSplicedFns.drop 152 }

compile_linked_chunks! cert7 armTarget armLayout armLegalTarget armLabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastSchedCert7

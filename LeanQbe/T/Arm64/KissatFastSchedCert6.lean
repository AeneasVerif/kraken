module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 6/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert6`) for slice `[130, 152)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastSchedCert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFastSched

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext5 armTarget armLegalTarget (schedSplicedFns.take 130)

/-- Slice 6 sub-module (`[130, 152)`, `22` functions). -/
def slice6Mod : Module := { fns := (schedSplicedFns.drop 130).take 22 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastSchedCert6

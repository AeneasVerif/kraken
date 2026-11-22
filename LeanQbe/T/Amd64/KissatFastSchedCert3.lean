module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 3/7 on SysV x64

Kernel-checked native compilation certificate (`cert3`) for slice `[61, 84)` (`23`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastSchedCert3

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFastSched

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext2 x64Target x64LegalTarget (schedSplicedFns.take 61)

/-- Slice 3 sub-module (`[61, 84)`, `23` functions). -/
def slice3Mod : Module := { fns := (schedSplicedFns.drop 61).take 23 }

compile_linked_chunks! cert3 x64Target x64Layout x64LegalTarget x64LabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastSchedCert3

module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 4/9 on SysV x64

Kernel-checked native compilation certificate (`cert4`) for slice `[78, 100)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert4

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext3 x64Target x64LegalTarget (fastFns.take 78)

/-- Slice 4 sub-module (`[78, 100)`, `22` functions). -/
def slice4Mod : Module := { fns := (fastFns.drop 78).take 22 }

compile_linked_chunks! cert4 x64Target x64Layout x64LegalTarget x64LabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastCert4

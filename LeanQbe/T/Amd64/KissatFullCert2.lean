module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 2/7 on SysV x64

Kernel-checked native compilation certificate (`cert2`) for slice `[38, 67)` (`29` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFullCert2

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Full

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext1 x64Target x64LegalTarget (fullFns.take 38)

/-- Slice 2 sub-module (`[38, 67)`, `29` functions). -/
def slice2Mod : Module := { fns := (fullFns.drop 38).take 29 }

compile_linked_chunks! cert2 x64Target x64Layout x64LegalTarget x64LabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFullCert2

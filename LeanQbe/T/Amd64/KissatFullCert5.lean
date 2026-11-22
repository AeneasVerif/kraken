module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 5/7 on SysV x64

Kernel-checked native compilation certificate (`cert5`) for slice `[111, 128)` (`17` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFullCert5

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Full

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext4 x64Target x64LegalTarget (fullFns.take 111)

/-- Slice 5 sub-module (`[111, 128)`, `17` functions). -/
def slice5Mod : Module := { fns := (fullFns.drop 111).take 17 }

compile_linked_chunks! cert5 x64Target x64Layout x64LegalTarget x64LabelClean
  slice5Mod 4 (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFullCert5

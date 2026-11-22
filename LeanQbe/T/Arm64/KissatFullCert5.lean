module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 5/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert5`) for slice `[111, 128)` (`17` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext4 armTarget armLegalTarget (fullFns.take 111)

/-- Slice 5 sub-module (`[111, 128)`, `17` functions). -/
def slice5Mod : Module := { fns := (fullFns.drop 111).take 17 }

compile_linked_chunks! cert5 armTarget armLayout armLegalTarget armLabelClean
  slice5Mod 4 (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert5

module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Kissat `D-Full` Native Certificate Slice 4/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert4`) for slice `[88, 111)` (`23` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext3 armTarget armLegalTarget (fullFns.take 88)

/-- Slice 4 sub-module (`[88, 111)`, `23` functions). -/
def slice4Mod : Module := { fns := (fullFns.drop 88).take 23 }

compile_linked_chunks! cert4 armTarget armLayout armLegalTarget armLabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert4

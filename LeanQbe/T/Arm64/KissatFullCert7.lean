module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Kissat `D-Full` Native Certificate Slice 7/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert7`) for slice `[147, 166)` (`19` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert7

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext6 armTarget armLegalTarget (fullFns.take 147)

/-- Slice 7 sub-module (`[147, 166)`, `19` functions). -/
def slice7Mod : Module := { fns := fullFns.drop 147 }

compile_linked_chunks! cert7 armTarget armLayout armLegalTarget armLabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert7

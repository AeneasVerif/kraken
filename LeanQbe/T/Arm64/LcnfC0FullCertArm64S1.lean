module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0FullFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full

/-!
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 1/7 (`[0, 15)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS1`) for `[0, 15)` (`15` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 1 sub-module (`[0, 15)`, `15` functions). -/
@[expose] noncomputable def rtC0Arm64Slice1Mod : Module :=
  { fns := rtC0CoreFlatMod.fns.take 15, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS1 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice1Mod 8 (exits := rtExitSyms) (nX := 64) (maxDirs := 600) (flat := true)

end LeanQbe.T.Arm64

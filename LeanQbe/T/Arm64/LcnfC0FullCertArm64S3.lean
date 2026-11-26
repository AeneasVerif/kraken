module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0FullFlat
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds

/-!
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 3/7 (`[30, 35)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS3`) for `[30, 35)` (`5` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 3 sub-module (`[30, 35)`, `5` functions). -/
@[expose] noncomputable def rtC0Arm64Slice3Mod : Module :=
  { fns := (rtC0CoreFlatMod.fns.drop 30).take 5, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS3 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice3Mod 4 (ext := rtC0Arm64ExtBefore 30) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 600) (flat := true)

end LeanQbe.T.Arm64

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
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 4/7 (`[35, 39)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS4`) for `[35, 39)` (`4` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 4 sub-module (`[35, 39)`, `4` functions). -/
@[expose] noncomputable def rtC0Arm64Slice4Mod : Module :=
  { fns := (rtC0CoreFlatMod.fns.drop 35).take 4, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS4 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice4Mod 4 (ext := rtC0Arm64ExtBefore 35) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 500) (flat := true)

end LeanQbe.T.Arm64

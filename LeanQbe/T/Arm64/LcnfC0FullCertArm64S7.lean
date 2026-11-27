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
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 7/7 (`[72, 80)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS7`) for `[72, 80)` (`8` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 7 sub-module (`[72, 80)`, `8` functions). -/
@[expose] noncomputable def rtC0Arm64Slice7Mod : Module :=
  { fns := rtC0CoreFlatMod.fns.drop 72, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS7 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice7Mod 4 (ext := rtC0Arm64ExtBefore 72) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 600) (flat := true)

end LeanQbe.T.Arm64

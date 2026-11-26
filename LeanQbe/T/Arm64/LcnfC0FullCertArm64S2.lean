module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds

/-!
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 2/7 (`[15, 30)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS2`) for `[15, 30)` (`15` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 2 sub-module (`[15, 30)`, `15` functions). -/
@[expose] def rtC0Arm64Slice2Mod : Module :=
  { fns := (rtC0CoreMod.fns.drop 15).take 15, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS2 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice2Mod 8 (ext := rtC0Arm64ExtBefore 15) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 600)

end LeanQbe.T.Arm64

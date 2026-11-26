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
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 5/7 (`[39, 61)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS5`) for `[39, 61)` (`22` functions,
full R2 container slice) of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 5 sub-module (`[39, 61)`, `22` functions). -/
@[expose] def rtC0Arm64Slice5Mod : Module :=
  { fns := (rtC0CoreMod.fns.drop 39).take 22, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS5 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice5Mod 11 (ext := rtC0Arm64ExtBefore 39) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 500)

end LeanQbe.T.Arm64

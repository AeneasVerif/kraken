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
# `rtC0CoreMod` AAPCS64 Arm64 Certificate Slice 6/7 (`[61, 78)`)

Kernel-checked native compilation certificate (`rtC0Arm64CertS6`) for `[61, 78)` (`17` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 6 sub-module (`[61, 78)`, `17` functions). -/
@[expose] def rtC0Arm64Slice6Mod : Module :=
  { fns := (rtC0CoreMod.fns.drop 61).take 17, exits := rtExitSyms }

compile_linked_chunks! rtC0Arm64CertS6 armTarget armLayout armLegalTarget armLabelClean
  rtC0Arm64Slice6Mod 9 (ext := rtC0Arm64ExtBefore 61) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 500)

end LeanQbe.T.Arm64

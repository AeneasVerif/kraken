/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbeTest.T.BitblastCertArm64S4
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import LeanQbeTest.T.BitblastCertArm64S4

/-!
# Bitblast AAPCS64 Arm64 Certificate Slice 5/6 (`[54, 64)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertArm64S5`) for functions `[54, 64)`
of `bitblastFlatMod` on `armTarget` against `bitblastCertArm64S4.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64S5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertArm64S4

/-- Slice 5 sub-module (`[54, 64)`, `10` functions). -/
@[expose] noncomputable def bitblastSlice5ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.drop 54 }

compile_linked_chunks! bitblastCertArm64S5
  armTarget armLayout armLegalTarget armLabelClean
  bitblastSlice5ModArm64 4 (ext := bitblastCertArm64S4.exportedExt) (maxDirs := 2500)
  (flat := true)

end LeanQbeTest.T.BitblastCertArm64S5

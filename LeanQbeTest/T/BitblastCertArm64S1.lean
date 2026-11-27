/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbeTest.T.BitblastCertArm64S0
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import LeanQbeTest.T.BitblastCertArm64S0

/-!
# Bitblast AAPCS64 Arm64 Certificate Slice 1/2 (`[15, 30)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertArm64S1`) for functions `[15, 30)`
of `bitblastFlatMod` on `armTarget` against `bitblastCertArm64S0.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64S1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertArm64S0

/-- Slice 1 sub-module (`[15, 30)`, `15` functions). -/
@[expose] noncomputable def bitblastSlice1ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.drop 15 }

compile_linked_chunks! bitblastCertArm64S1
  armTarget armLayout armLegalTarget armLabelClean
  bitblastSlice1ModArm64 4 (ext := bitblastCertArm64S0.exportedExt) (maxDirs := 1200)
  (flat := true)

end LeanQbeTest.T.BitblastCertArm64S1

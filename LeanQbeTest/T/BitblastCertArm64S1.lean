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
# Bitblast AAPCS64 Arm64 Certificate Slice 1/6 (`[11, 22)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertArm64S1`) for functions `[11, 22)`
of `bitblastFlatMod` on `armTarget` against `bitblastCertArm64S0.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64S1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertArm64S0

/-- Slice 1 sub-module (`[11, 22)`, `11` functions). -/
@[expose] noncomputable def bitblastSlice1ModArm64 : Module :=
  { fns := (bitblastFlatMod.fns.drop 11).take 11 }

compile_linked_chunks! bitblastCertArm64S1
  armTarget armLayout armLegalTarget armLabelClean
  bitblastSlice1ModArm64 4 (ext := bitblastCertArm64S0.exportedExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertArm64S1

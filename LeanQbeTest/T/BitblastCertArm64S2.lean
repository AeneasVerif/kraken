/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbeTest.T.BitblastCertArm64S1
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import LeanQbeTest.T.BitblastCertArm64S1

/-!
# Bitblast AAPCS64 Arm64 Certificate Slice 2/6 (`[22, 33)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertArm64S2`) for functions `[22, 33)`
of `bitblastFlatMod` on `armTarget` against `bitblastCertArm64S1.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64S2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertArm64S1

/-- Slice 2 sub-module (`[22, 33)`, `11` functions). -/
@[expose] noncomputable def bitblastSlice2ModArm64 : Module :=
  { fns := (bitblastFlatMod.fns.drop 22).take 11 }

compile_linked_chunks! bitblastCertArm64S2
  armTarget armLayout armLegalTarget armLabelClean
  bitblastSlice2ModArm64 4 (ext := bitblastCertArm64S1.exportedExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertArm64S2

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbeTest.T.BitblastCertArm64S2
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import LeanQbeTest.T.BitblastCertArm64S2

/-!
# Bitblast AAPCS64 Arm64 Certificate Slice 3/6 (`[33, 44)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertArm64S3`) for functions `[33, 44)`
of `bitblastFlatMod` on `armTarget` against `bitblastCertArm64S2.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64S3

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertArm64S2

/-- Slice 3 sub-module (`[33, 44)`, `11` functions). -/
@[expose] noncomputable def bitblastSlice3ModArm64 : Module :=
  { fns := (bitblastFlatMod.fns.drop 33).take 11 }

compile_linked_chunks! bitblastCertArm64S3
  armTarget armLayout armLegalTarget armLabelClean
  bitblastSlice3ModArm64 4 (ext := bitblastCertArm64S2.exportedExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertArm64S3

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatPlainBounds
public import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatPlainBounds
meta import LeanQbe.T.Examples.Bitblast.Build.Flat

/-!
# Bitblast AAPCS64 Arm64 Certificate Slice 0/6 (`[0, 11)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertArm64S0`) for functions `[0, 11)`
of `bitblastFlatMod` on `armTarget` against `Arm64.KissatPlainBounds.plainAllExt`, exporting
`bitblastCertArm64S0.exportedExt` for Slice 1.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64S0

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Bitblast.Build

/-- Slice 0 sub-module (`[0, 11)`, `11` functions). -/
@[expose] noncomputable def bitblastSlice0ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.take 11 }

compile_linked_chunks! bitblastCertArm64S0
  armTarget armLayout armLegalTarget armLabelClean
  bitblastSlice0ModArm64 4 (ext := KissatPlainBounds.plainAllExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertArm64S0

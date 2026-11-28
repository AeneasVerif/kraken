/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Arisca.Build.Flat
public import LeanQbe.T.Arm64.AriscaCertBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Arisca.Build.Flat
meta import LeanQbe.T.Arm64.AriscaCertBounds

/-!
# `ariscaModule` AAPCS64 Arm64 Certificate Slice 3/5 (`[31, 39)`, `Driver` part 1)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.Examples.Arisca.Build

/-- Slice 3 sub-module (`[31, 39)`, `8` functions). -/
@[expose] noncomputable def ariscaArm64Slice3Mod : Module :=
  { fns := (ariscaFlatMod.fns.drop 31).take 8 }

compile_linked_chunks! ariscaArm64CertS3 armTarget armLayout armLegalTarget armLabelClean
  ariscaArm64Slice3Mod 4 (ext := ariscaArm64ExtBefore 31) (maxDirs := 600)
  (pruneExt := true) (flat := true)

end LeanQbe.T.Arm64

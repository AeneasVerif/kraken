/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Arisca.Build.Flat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Arisca.Build.Flat

/-!
# `ariscaModule` AAPCS64 Arm64 Certificate Slice 0/5 (`[0, 15)`, `Header ++ Parse`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.Examples.Arisca.Build

/-- Slice 0 sub-module (`[0, 15)`, `15` functions: `Header` + `Parse`). -/
@[expose] noncomputable def ariscaArm64Slice0Mod : Module :=
  { fns := ariscaFlatMod.fns.take 15 }

compile_linked_chunks! ariscaArm64CertS0 armTarget armLayout armLegalTarget armLabelClean
  ariscaArm64Slice0Mod 4 (maxDirs := 600) (pruneExt := true) (flat := true)

end LeanQbe.T.Arm64

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Arisca.Build.Flat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Arisca.Build.Flat

/-!
# `ariscaModule` SysV x86-64 Certificate Slice 0/5 (`[0, 15)`, `Header ++ Parse`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.Examples.Arisca.Build

/-- Slice 0 sub-module (`[0, 15)`, `15` functions: `Header` + `Parse`). -/
@[expose] noncomputable def ariscaX64Slice0Mod : Module :=
  { fns := ariscaFlatMod.fns.take 15 }

compile_linked_chunks! ariscaX64CertS0 x64Target x64Layout x64LegalTarget x64LabelClean
  ariscaX64Slice0Mod 4 (maxDirs := 600) (pruneExt := true) (flat := true)

end LeanQbe.T.Amd64

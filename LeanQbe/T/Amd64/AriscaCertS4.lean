/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Arisca.Build.Flat
public import LeanQbe.T.Amd64.AriscaCertBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Arisca.Build.Flat
meta import LeanQbe.T.Amd64.AriscaCertBounds

/-!
# `ariscaModule` SysV x86-64 Certificate Slice 4/5 (`[39, 45)`, `Driver` part 2)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.Examples.Arisca.Build

/-- Slice 4 sub-module (`[39, 45)`, `6` functions ending at `arisca_check_bytes`). -/
@[expose] noncomputable def ariscaX64Slice4Mod : Module :=
  { fns := ariscaFlatMod.fns.drop 39 }

compile_linked_chunks! ariscaX64CertS4 x64Target x64Layout x64LegalTarget x64LabelClean
  ariscaX64Slice4Mod 4 (ext := ariscaX64ExtBefore 39) (maxDirs := 600)
  (pruneExt := true) (flat := true)

end LeanQbe.T.Amd64

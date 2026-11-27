/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbeTest.T.BitblastCertX64S3
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import LeanQbeTest.T.BitblastCertX64S3

/-!
# Bitblast SysV x86-64 Certificate Slice 4/6 (`[44, 54)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertX64S4`) for functions `[44, 54)`
of `bitblastFlatMod` on `x64Target` against `bitblastCertX64S3.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertX64S4

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertX64S3

/-- Slice 4 sub-module (`[44, 54)`, `10` functions). -/
@[expose] noncomputable def bitblastSlice4ModX64 : Module :=
  { fns := (bitblastFlatMod.fns.drop 44).take 10 }

compile_linked_chunks! bitblastCertX64S4
  x64Target x64Layout x64LegalTarget x64LabelClean
  bitblastSlice4ModX64 4 (ext := bitblastCertX64S3.exportedExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertX64S4

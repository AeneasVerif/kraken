/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbeTest.T.BitblastCertX64S2
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import LeanQbeTest.T.BitblastCertX64S2

/-!
# Bitblast SysV x86-64 Certificate Slice 3/6 (`[33, 44)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertX64S3`) for functions `[33, 44)`
of `bitblastFlatMod` on `x64Target` against `bitblastCertX64S2.exportedExt`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertX64S3

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertX64S2

/-- Slice 3 sub-module (`[33, 44)`, `11` functions). -/
@[expose] noncomputable def bitblastSlice3ModX64 : Module :=
  { fns := (bitblastFlatMod.fns.drop 33).take 11 }

compile_linked_chunks! bitblastCertX64S3
  x64Target x64Layout x64LegalTarget x64LabelClean
  bitblastSlice3ModX64 4 (ext := bitblastCertX64S2.exportedExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertX64S3

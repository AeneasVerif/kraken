/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatPlainBounds
public import LeanQbe.T.Examples.Bitblast.Build.Flat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatPlainBounds
meta import LeanQbe.T.Examples.Bitblast.Build.Flat

/-!
# Bitblast SysV x86-64 Certificate Slice 0/6 (`[0, 11)`)

Kernel-checked native `(flat := true)` certificate (`bitblastCertX64S0`) for functions `[0, 11)`
of `bitblastFlatMod` on `x64Target` against `Amd64.KissatPlainBounds.plainAllExt`, exporting
`bitblastCertX64S0.exportedExt` for Slice 1.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertX64S0

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Bitblast.Build

/-- Slice 0 sub-module (`[0, 11)`, `11` functions). -/
@[expose] noncomputable def bitblastSlice0ModX64 : Module :=
  { fns := bitblastFlatMod.fns.take 11 }

compile_linked_chunks! bitblastCertX64S0
  x64Target x64Layout x64LegalTarget x64LabelClean
  bitblastSlice0ModX64 4 (ext := KissatPlainBounds.plainAllExt) (maxDirs := 2500)
  (compileExt := true) (flat := true)

end LeanQbeTest.T.BitblastCertX64S0

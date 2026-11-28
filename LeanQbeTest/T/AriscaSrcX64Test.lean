/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainFlat
import LeanQbe.T.Examples.Arisca.Src.Module
import LeanQbe.T.Amd64.Isa
import LeanQbe.T.Spill
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Examples.Arisca.Src.Module
meta import LeanQbe.T.Amd64.Isa
meta import LeanQbe.T.Spill

/-!
# SysV x86-64 `compileModuleFlat` Check for `Arisca.Src` (`AriscaSrcX64Test`)

Kept separate from `AriscaSrcArm64Test.lean` so `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` remain strictly isolated in separate Lean modules.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.AriscaSrcX64Test

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src.Module

private def ariscaFlatFns : List TFlatFn :=
  ariscaModule.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

private def compileX64Ok : Bool :=
  let hints := ariscaFlatFns.map fun ff =>
    Spill.hints Amd64.x64Isa (midStageFlat Amd64.x64LegalTarget (earlyOptFlat ff)).toFn
  match compileModuleFlat Amd64.x64Isa Amd64.x64LegalTarget
      Amd64.x64Isa.frame.raBytes [] [] 0 ariscaFlatFns hints with
  | .ok (code, bounds) => !code.isEmpty && bounds.length == ariscaModule.fns.length
  | .error _ => false

#guard compileX64Ok

end LeanQbeTest.T.AriscaSrcX64Test

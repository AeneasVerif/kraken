/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainFlat
public import LeanQbe.T.Examples.Arisca.Src.Module
public import LeanQbe.T.Arm64.Isa
public import LeanQbe.T.Spill
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.Examples.Arisca.Src.Module
public meta import LeanQbe.T.Arm64.Isa
public meta import LeanQbe.T.Spill

/-!
# AAPCS64 Arm64 `compileModuleFlat` Check for `Arisca.Src` (`AriscaSrcArm64Test`)

Kept separate from `AriscaSrcX64Test.lean` so `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` remain strictly isolated in separate Lean modules.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.AriscaSrcArm64Test

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src.Module

private def ariscaFlatFns : List TFlatFn :=
  ariscaModule.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

private def compileArm64Ok : Bool :=
  let hints := ariscaFlatFns.map fun ff =>
    Spill.hints Arm64.armIsa (midStageFlat Arm64.armLegalTarget (earlyOptFlat ff)).toFn
  match compileModuleFlat Arm64.armIsa Arm64.armLegalTarget
      Arm64.armIsa.frame.raBytes [] [] 0 ariscaFlatFns hints with
  | .ok (code, bounds) => !code.isEmpty && bounds.length == ariscaModule.fns.length
  | .error _ => false

#guard compileArm64Ok

end LeanQbeTest.T.AriscaSrcArm64Test

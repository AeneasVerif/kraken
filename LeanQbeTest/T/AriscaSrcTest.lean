/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainFlat
import LeanQbe.T.Examples.Arisca.Src.Module
meta import LeanQbe.T.Flat
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Examples.Arisca.Src.Module

/-!
# Target-Neutral `Func.Wf` and Module Invariant Tests for `Arisca.Src` (`AriscaSrcTest`)

Verifies:
- `ariscaModule` metadata (`44` functions, `0` externs, `0` exits, `checkAcyclic = true`,
  every fn `<= 6` args)
- `ariscaModule_wf : ∀ f ∈ ariscaModule.fns, f.Wf` (`<= std3`)
- `wfCheck = true` on every `TFlatFn` in `ariscaModule`.

Target-specific `compileModuleFlat` checks live in `AriscaSrcX64Test.lean` and
`AriscaSrcArm64Test.lean` (since `Kraken.X64` and `Kraken.AArch64` cannot be imported in the
same Lean module).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.AriscaSrcTest

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src.Module

private def ariscaFlatFns : List TFlatFn :=
  ariscaModule.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

#guard ariscaModule.fns.length == 44
#guard ariscaModule.externs.isEmpty
#guard ariscaModule.exits.isEmpty
#guard ariscaModule.checkAcyclic == true
#guard ariscaModule.fns.all (fun f => f.as.length <= 6)
#guard ariscaFlatFns.all TFlatFn.wfCheck

section

theorem audit_ariscaModule_wf : ∀ f ∈ ariscaModule.fns, f.Wf :=
  ariscaModule_wf

theorem audit_ariscaModule_acyclic : ariscaModule.checkAcyclic = true :=
  ariscaModule_checkAcyclic

#print axioms audit_ariscaModule_wf
#print axioms audit_ariscaModule_acyclic

end

end LeanQbeTest.T.AriscaSrcTest

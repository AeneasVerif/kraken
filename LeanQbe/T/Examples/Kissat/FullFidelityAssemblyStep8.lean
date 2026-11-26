/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 8 (`FullFidelityAssemblyStep8`, `501` fns)

Pure C0/IR assembly (`0` `*Proof*` imports, `0` `import all`, `0` `meta import` of
`PrintCpp`/`PrintQbe`/`Legal`) splicing the `5` Step-8 upstream-parity & hotspot-closure
replacements (`FullFidelityStep8.fidStep8Repls`) onto `fidStep7Module` (`501` fns).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.PatchModule

/-- Ordered `501`-fn Step-8 `KissatFidelity` function list (`fidStep7Fns` patched with
`FullFidelityStep8.fidStep8Repls`). -/
def fidStep8Fns : List Fn :=
  patchFns FullFidelityStep8.fidStep8Repls [] fidStep7Fns

/-- Closed `501`-function Gate-1 Step-8 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep8Module : LeanQbe.T.Module :=
  { fidStep7Module with fns := fidStep8Fns }

theorem fidStep8Fns_eq : fidStep8Module.fns = fidStep8Fns :=
  rfl

theorem fidStep8Fns_eq_step8 : fidStep8Fns = FullFidelityStep8.fidStep8ModuleFns :=
  rfl

theorem fidStep8Module_eq_step8 : fidStep8Module = FullFidelityStep8.fidStep8Module :=
  rfl

theorem fidStep8Module_wf : ∀ f ∈ fidStep8Module.fns, f.Wf :=
  patchFns_wf fidStep7Module_wf FullFidelityStep8.fidStep8Repls_wf (fun _ h => by simp at h)

theorem fidStep8_noExit : fidStep8Module.exits = [] :=
  fidStep7_noExit

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8

end

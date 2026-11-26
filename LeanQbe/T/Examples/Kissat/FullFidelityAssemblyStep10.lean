/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 10 (`FullFidelityAssemblyStep10`, `505` fns)

Pure C0/IR assembly (`0` `*Proof*` imports, `0` `import all`, `0` `meta import` of
`PrintCpp`/`PrintQbe`/`Legal`) splicing the `5` Step-10 audit-closure replacements
(`FullFidelityStep10.fidStep10Repls`) and `1` inserted helper (`full_learn_clause_m6` in
`FullFidelityStep10.fidStep10Befores`) onto `fidStep9Module` (`504 -> 505` fns).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Ordered `505`-fn Step-10 `KissatFidelity` function list (`fidStep9Fns` patched with
`FullFidelityStep10.fidStep10Repls` and `FullFidelityStep10.fidStep10Befores`). -/
def fidStep10Fns : List Fn :=
  patchFns FullFidelityStep10.fidStep10Repls FullFidelityStep10.fidStep10Befores fidStep9Fns

/-- Closed `505`-function Gate-1 Step-10 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep10Module : LeanQbe.T.Module :=
  { fidStep9Module with fns := fidStep10Fns }

end

public section

theorem fidStep10Fns_eq : fidStep10Module.fns = fidStep10Fns :=
  rfl

theorem fidStep10Fns_eq_step10 : fidStep10Fns = FullFidelityStep10.fidStep10ModuleFns :=
  rfl

theorem fidStep10Module_eq_step10 : fidStep10Module = FullFidelityStep10.fidStep10Module :=
  rfl

theorem fidStep10Module_wf : ∀ f ∈ fidStep10Module.fns, f.Wf :=
  patchFns_wf fidStep9Module_wf FullFidelityStep10.fidStep10Repls_wf
    FullFidelityStep10.fidStep10Befores_wf

theorem fidStep10_noExit : fidStep10Module.exits = [] :=
  fidStep9_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10

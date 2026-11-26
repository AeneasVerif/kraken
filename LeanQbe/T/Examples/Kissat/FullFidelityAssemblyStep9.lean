/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 9 (`FullFidelityAssemblyStep9`, `504` fns)

Pure C0/IR assembly (`0` `*Proof*` imports, `0` `import all`, `0` `meta import` of
`PrintCpp`/`PrintQbe`/`Legal`) splicing the `11` Step-9 upstream-parity & hotspot-closure
replacements (`FullFidelityStep9.fidStep9Repls`) and `3` inserted helpers
(`FullFidelityStep9.fidStep9Befores`) onto `fidStep8Module` (`501 -> 504` fns).
Experimental `S9-P0.3` (`MemShrinkV5`) is layered separately in
`LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.PatchModule

/-- Ordered `504`-fn Step-9 `KissatFidelity` function list (`fidStep8Fns` patched with
`FullFidelityStep9.fidStep9Repls` and `FullFidelityStep9.fidStep9Befores`). -/
def fidStep9Fns : List Fn :=
  patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores fidStep8Fns

/-- Closed `504`-function Gate-1 Step-9 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep9Module : LeanQbe.T.Module :=
  { fidStep8Module with fns := fidStep9Fns }

theorem fidStep9Fns_eq : fidStep9Module.fns = fidStep9Fns :=
  rfl

theorem fidStep9Fns_eq_step9 : fidStep9Fns = FullFidelityStep9.fidStep9ModuleFns :=
  rfl

theorem fidStep9Module_eq_step9 : fidStep9Module = FullFidelityStep9.fidStep9Module :=
  rfl

theorem fidStep9Module_wf : ∀ f ∈ fidStep9Module.fns, f.Wf :=
  patchFns_wf fidStep8Module_wf FullFidelityStep9.fidStep9Repls_wf
    FullFidelityStep9.fidStep9Befores_wf

theorem fidStep9_noExit : fidStep9Module.exits = [] :=
  fidStep8_noExit

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 12 Bundle C — Data-Pure Patch Lists (`FullFidelityStep12CRows`)

Data-only `fidStep12CRepls`, `fidStep12CBefores`, and spliced `fidStep12CModule` (`508` fns =
`505` Step-10 fns + `3` inserted helpers `full_watch_pop_c0`, `full_reduce_purge_c0`,
`full_viv_sift_counts_m6`; `0` `*Proof*` imports, `0` edits to existing `Full*` or
`FidelityHub.lean`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12C

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Exact `4`-function Step-12C replacement list over `fidStep10Fns`. -/
def fidStep12CRepls : List Fn :=
  [ fidStep12CAddClauseFn
  , fidStep12CSweepCopyFn
  , fidStep12CLearnClauseM6Fn
  , fidStep12CVivSortCountsM6Fn ]

/-- Ordered helper insertions (`+3` helpers, net `505 -> 508` functions). -/
def fidStep12CBefores : List (Sym × List Fn) :=
  [ ("full_add_clause", [fidStep12CWatchPopFn])
  , ("full_learn_clause_m6", [fidStep12CReducePurgeFn])
  , ("full_viv_sort_counts_m6", [fidStep12CVivSiftCountsM6Fn]) ]

/-- Ordered `508`-fn Step-12C `KissatFidelity` function list (`patchFns` over `fidStep10Fns`). -/
def fidStep12CModuleFns : List Fn :=
  patchFns fidStep12CRepls fidStep12CBefores fidStep10Fns

/-- Closed `508`-function Gate-1 Step-12C `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep12CModule : LeanQbe.T.Module :=
  { fidStep10Module with fns := fidStep12CModuleFns }

end

public section

theorem fidStep12CModuleFns_eq : fidStep12CModule.fns = fidStep12CModuleFns :=
  rfl

theorem fidStep12CRepls_wf : ∀ f ∈ fidStep12CRepls, f.Wf := by
  intro f hf
  simp only [fidStep12CRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_add_clause_step12c_wf
  · exact full_sweep_copy_step12c_wf
  · exact full_learn_clause_m6_step12c_wf
  · exact full_viv_sort_counts_m6_step12c_wf

theorem fidStep12CBefores_wf :
    ∀ h ∈ fidStep12CBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep12CBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact full_watch_pop_c0_step12c_wf
  · exact full_reduce_purge_c0_step12c_wf
  · exact full_viv_sift_counts_m6_step12c_wf

theorem fidStep12CModule_wf : ∀ f ∈ fidStep12CModule.fns, f.Wf :=
  patchFns_wf fidStep10Module_wf fidStep12CRepls_wf fidStep12CBefores_wf

theorem fidStep12C_noExit : fidStep12CModule.exits = [] :=
  fidStep10_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12C

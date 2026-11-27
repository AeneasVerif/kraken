/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatch
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnit
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 13 Shard S2 Data-Pure Patch Barrel (`FullFidelityStep13S2Rows`)

Data-pure barrel (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, passing
`check_firewall.py --require-isa --data-proof`) exporting the Shard `S2` replacement (`8` fns) &
insertion (`+2` helpers) lists, well-formedness proofs, and preview spliced module (`517 -> 519`
fns over `fidStep12Module`).

Proof rows (`fidStep13S2ReplRows`, `fidStep13S2BeforeRows`), `checkCallsOk`, and parametric
`*_impl` lemmas live in `FullFidelityStep13S2RowsProof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Combined `8` sig-preserving Shard `S2` replacement functions (`4` S2-A + `4` S2-B). -/
def fidStep13S2Repls : List Fn :=
  fidStep13S2BCPWatchRepls ++ fidStep13S2OTFSUnitRepls

/-- Combined `2` inserted Shard `S2` helper functions (`full_update_classify_fid`,
`full_propagate_beyond_m7`). -/
def fidStep13S2Befores : List (Sym × List Fn) :=
  fidStep13S2BCPWatchBefores ++ fidStep13S2OTFSUnitBefores

/-- Names of the `8` sig-preserving Shard `S2` replacement functions in exact order. -/
def fidStep13S2ReplNames : List Sym :=
  [ "full_watch_push_slow_m6"
  , "full_watch_push_m6"
  , "full_propagate_ignore_hot"
  , "full_propagate_ignore"
  , "full_otfs_large"
  , "full_one_lit_confl"
  , "full_eager_subsume"
  , "full_learn_clause_m6" ]

/-- Names of the `2` inserted Shard `S2` helper functions in exact order. -/
def fidStep13S2BeforeNames : List Sym :=
  [ "full_update_classify_fid"
  , "full_propagate_beyond_m7" ]

/-- Ordered `519`-fn preview function list (`fidStep12Fns` patched with Shard `S2`). -/
def fidStep13S2Fns : List Fn :=
  patchFns fidStep13S2Repls fidStep13S2Befores fidStep12Fns

/-- Closed `519`-fn Shard `S2` preview module (`0` externs, `0` exits). -/
def fidStep13S2Module : LeanQbe.T.Module :=
  { fidStep12Module with fns := fidStep13S2Fns }

end

public section

theorem fidStep13S2Repls_map_name :
    fidStep13S2Repls.map Fn.name = fidStep13S2ReplNames :=
  rfl

theorem fidStep13S2Befores_map_name :
    (fidStep13S2Befores.flatMap Prod.snd).map Fn.name = fidStep13S2BeforeNames :=
  rfl

theorem fidStep13S2ReplNames_nodup : fidStep13S2ReplNames.Nodup := by decide

theorem fidStep13S2BeforeNames_nodup : fidStep13S2BeforeNames.Nodup := by decide

theorem fidStep13S2Repls_wf : ∀ f ∈ fidStep13S2Repls, f.Wf := by
  intro f hf
  rw [fidStep13S2Repls, List.mem_append] at hf
  rcases hf with h1 | h2
  · exact fidStep13S2BCPWatchRepls_wf f h1
  · exact fidStep13S2OTFSUnitRepls_wf f h2

theorem fidStep13S2Befores_wf : ∀ f ∈ fidStep13S2Befores.flatMap Prod.snd, f.Wf := by
  intro f hf
  rw [fidStep13S2Befores, List.flatMap_append, List.mem_append] at hf
  rcases hf with h1 | h2
  · exact fidStep13S2BCPWatchBefores_wf f h1
  · exact fidStep13S2OTFSUnitBefores_wf f h2

theorem fidStep13S2Module_wf : ∀ f ∈ fidStep13S2Module.fns, f.Wf :=
  patchFns_wf fidStep12Module_wf fidStep13S2Repls_wf fidStep13S2Befores_wf

theorem fidStep13S2_noExit : fidStep13S2Module.exits = [] :=
  fidStep12_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

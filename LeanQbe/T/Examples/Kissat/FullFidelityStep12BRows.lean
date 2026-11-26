/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BCong
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BBveFwd
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 12B Data-Pure Patch Barrel (`FullFidelityStep12BRows`)

Data-pure barrel (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, passing
`check_firewall.py --require-isa --data-proof`) exporting the Step-12B replacement (`12` fns) &
insertion (`+3` helpers) lists, well-formedness proofs, and preview spliced module (`505 -> 508`
fns over `fidStep10Module`).

Proof rows (`fidStep12BReplRows`, `fidStep12BBeforeRows`), `checkCallsOk`, and parametric
`*_impl` lemmas live in `FullFidelityStep12BRowsProof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Combined `12` sig-preserving Step-12B replacement functions. -/
def fidStep12BRepls : List Fn :=
  fidStep12BCongRepls ++ fidStep12BBveFwdRepls

/-- Combined `3` inserted Step-12B helper functions (`2` congruence + `1` BVE). -/
def fidStep12BBefores : List (Sym × List Fn) :=
  fidStep12BCongBefores ++ fidStep12BBveFwdBefores

/-- Names of the `12` sig-preserving Step-12B replacement functions in exact order. -/
def fidStep12BReplNames : List Sym :=
  [ "full_cong_extract"
  , "full_cong_and_match"
  , "full_cong_enq_var"
  , "full_cong_eval_gate"
  , "full_cong_worklist"
  , "full_congruence_dense"
  , "full_backbone_sched_m6"
  , "full_backbone_m6"
  , "full_dense_prop_unit_m7"
  , "full_forward_sub_m7"
  , "full_bve_commit_res"
  , "full_bve_var_m7" ]

/-- Names of the `3` inserted Step-12B helper functions in exact order. -/
def fidStep12BBeforeNames : List Sym :=
  [ "full_cong_extract_and_clause_fid"
  , "full_cong_extract_from_fid"
  , "full_bve_weaken_unit_fid" ]

/-- Ordered `508`-fn preview function list (`fidStep10Fns` patched with Step 12B). -/
def fidStep12BFns : List Fn :=
  patchFns fidStep12BRepls fidStep12BBefores fidStep10Fns

/-- Closed `508`-fn Step-12B preview module (`0` externs, `0` exits). -/
def fidStep12BModule : LeanQbe.T.Module :=
  { fidStep10Module with fns := fidStep12BFns }

end

public section

theorem fidStep12BRepls_map_name :
    fidStep12BRepls.map Fn.name = fidStep12BReplNames :=
  rfl

theorem fidStep12BBefores_map_name :
    (fidStep12BBefores.flatMap Prod.snd).map Fn.name = fidStep12BBeforeNames :=
  rfl

theorem fidStep12BReplNames_nodup : fidStep12BReplNames.Nodup := by decide

theorem fidStep12BBeforeNames_nodup : fidStep12BBeforeNames.Nodup := by decide

theorem fidStep12BRepls_wf : ∀ f ∈ fidStep12BRepls, f.Wf := by
  intro f hf
  rw [fidStep12BRepls, List.mem_append] at hf
  rcases hf with h1 | h2
  · exact fidStep12BCongRepls_wf f h1
  · exact fidStep12BBveFwdRepls_wf f h2

theorem fidStep12BBefores_wf : ∀ f ∈ fidStep12BBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  rw [fidStep12BBefores, List.flatMap_append, List.mem_append] at hf
  rcases hf with h1 | h2
  · exact fidStep12BCongBefores_wf f h1
  · exact fidStep12BBveFwdBefores_wf f h2

theorem fidStep12BModule_wf : ∀ f ∈ fidStep12BModule.fns, f.Wf :=
  patchFns_wf fidStep10Module_wf fidStep12BRepls_wf fidStep12BBefores_wf

theorem fidStep12B_noExit : fidStep12BModule.exits = [] :=
  fidStep10_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B

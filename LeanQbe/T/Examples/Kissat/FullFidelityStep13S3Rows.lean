/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Walk
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestart
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 13 Shard S3 Data-Pure Patch Barrel (`FullFidelityStep13S3Rows`)

Data-pure barrel (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, passing
`check_firewall.py --require-isa --data-proof`) exporting the Step-13 S3 replacement (`30` fns =
`10` Walk/Warmup + `20` Search/Restart/EMAs/Compact/Seed) and insertion (`+2` helpers:
`full_randec_var_lvl_fid` and `kissat_solve_bytes_seeded`) lists, name lists, `Nodup`, and
well-formedness certificates.

Note for `S6` assembly: `full_restart` calls `full_randec_var_lvl_fid` (which calls
`full_m7_state_init` / `full_lcg_next_m7` / `full_m7_get64` / `full_m7_set64`), so `S6` should
ensure `full_restart` is ordered after `full_randec_var_lvl_fid` when checking module acyclicity.

Proof rows (`fidStep13S3ReplRows`, `fidStep13S3BeforeRows`), `32/32` kernel-checked `checkCallsOk`
certificates, and `32/32` callee-parametric `SpecEntry.Impl` proofs live in
`FullFidelityStep13S3RowsProof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Combined `30` sig-preserving Step-13 S3 replacement functions (`10` Walk + `20` Search). -/
def fidStep13S3Repls : List Fn :=
  fidStep13S3WalkRepls ++ fidStep13S3SearchRepls

/-- Combined `2` inserted Step-13 S3 helper functions (`full_randec_var_lvl_fid`,
`kissat_solve_bytes_seeded`). -/
def fidStep13S3Befores : List (Sym × List Fn) :=
  fidStep13S3SearchBefores

/-- Exact ordered names of all `30` Step-13 S3 replacement functions. -/
def fidStep13S3ReplNames : List Sym :=
  [ "full_walk_cb_inv_m7"
  , "full_walk_init_table_m7"
  , "full_walk_effort_m7"
  , "full_walk_collect_m7"
  , "full_walk_build_occ_m7"
  , "full_walk_break_m7"
  , "full_walk_pick_m7"
  , "full_walk_flip_m7"
  , "full_walk_m7"
  , "full_warmup_m7"
  , "full_scale_delta_m5"
  , "full_ema_update"
  , "full_scale_delta"
  , "full_zero_tables2"
  , "m6_hdr_dr_init"
  , "m6_hdr_dr_update"
  , "m6_hdr_dr_allow"
  , "full_rephase"
  , "full_restart_due"
  , "full_restart"
  , "full_init_fresh_var"
  , "full_compact_mark_live"
  , "full_compact_vars"
  , "full_m7_state_init"
  , "full_randec_var_m7"
  , "full_ema_swap_m7"
  , "full_switch_mode_m7"
  , "full_search_m6"
  , "kissat_solve_bytes_m6"
  , "kissat_solve_bytes" ]

/-- Exact ordered names of all `2` Step-13 S3 inserted functions. -/
def fidStep13S3BeforeNames : List Sym :=
  [ "full_randec_var_lvl_fid"
  , "kissat_solve_bytes_seeded" ]

end

public section

theorem fidStep13S3Repls_map_name :
    fidStep13S3Repls.map Fn.name = fidStep13S3ReplNames :=
  rfl

theorem fidStep13S3Befores_map_name :
    (fidStep13S3Befores.flatMap Prod.snd).map Fn.name = fidStep13S3BeforeNames :=
  rfl

theorem fidStep13S3ReplNames_nodup : fidStep13S3ReplNames.Nodup := by decide

theorem fidStep13S3BeforeNames_nodup : fidStep13S3BeforeNames.Nodup := by decide

theorem fidStep13S3Repls_wf : ∀ f ∈ fidStep13S3Repls, f.Wf := by
  intro f hf
  rw [fidStep13S3Repls, List.mem_append] at hf
  rcases hf with h1 | h2
  · exact fidStep13S3WalkRepls_wf f h1
  · exact fidStep13S3SearchRepls_wf f h2

theorem fidStep13S3Befores_wf : ∀ h ∈ fidStep13S3Befores.flatMap Prod.snd, h.Wf :=
  fidStep13S3SearchBefores_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

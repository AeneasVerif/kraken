/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3WalkProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3WalkProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3WalkProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3WalkProof3
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestartProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestartProof1a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestartProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestartProof2
public import LeanQbe.T.Examples.Kissat.FullSpec

/-!
# Kissat Fidelity Step 13 Shard S3 Proof Rows & Parametric `Impl` Barrel

Exports the `30` replacement specification rows (`fidStep13S3ReplRows`), the `2` inserted-helper
specification rows (`fidStep13S3BeforeRows`: `full_randec_var_lvl_fid` and
`kissat_solve_bytes_seeded`), name/signature/`noExit` alignment theorems, `32/32` kernel-checked
`checkCallsOk` certificates, and `32/32` callee-parametric `SpecEntry.Impl` lemmas (`0`
`import all`, `0` `@[expose]` on theorems/lemmas, `0` Step-7..12 back-imports, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Walk
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- The `30` sig-preserving replacement specification rows aligned 1-to-1 with
`fidStep13S3Repls` (`10` Walk/Warmup + `20` Search/Restart/EMAs/Compact/Seed). -/
def fidStep13S3ReplRows : List SpecEntry :=
  [ ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], step13WalkCbInvSpec, true⟩
  , ⟨"full_walk_init_table_m7", [i64, i64], [], step13WalkInitTableSpec, true⟩
  , ⟨"full_walk_effort_m7", [i64, i64], [i64], step13WalkEffortSpec, true⟩
  , ⟨"full_walk_collect_m7", [i64], [i64], m7CollectSpec, true⟩
  , ⟨"full_walk_build_occ_m7", [i64, i64], [i64], step13WalkBuildOccSpec, true⟩
  , ⟨"full_walk_break_m7", [i64, i32, i64], [i32], step13WalkBreakSpec, true⟩
  , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64], step13WalkPickSpec, true⟩
  , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64], step13WalkFlipSpec, true⟩
  , ⟨"full_walk_m7", [i64], [], step13WalkM7Spec, true⟩
  , ⟨"full_warmup_m7", [i64], [], step13WarmupM6Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩
  , ⟨"full_rephase", [i64], [], step13RephaseM6Spec, true⟩
  , ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  , ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], step13InitFreshVarSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], fullCompactMarkLiveSpec, true⟩
  , ⟨"full_compact_vars", [i64, i64, i64], [], fullCompactVarsSpec, true⟩
  , ⟨"full_m7_state_init", [i64], [], step13M7StateInitSpec, true⟩
  , ⟨"full_randec_var_m7", [i64], [i64], m7RandecVarSpec, true⟩
  , ⟨"full_ema_swap_m7", [i64, i64, i64], [], step13EmaSwapSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], step13SwitchModeM6Spec, true⟩
  , ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], step13SolveBytesSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], step13SolveBytesSpec, true⟩ ]

/-- The `2` inserted helper specification rows aligned 1-to-1 with `fidStep13S3Befores`. -/
def fidStep13S3BeforeRows : List SpecEntry :=
  [ ⟨"full_randec_var_lvl_fid", [i64, i64], [i64], step13RandecVarLvlSpec, true⟩
  , ⟨"kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64],
      step13SolveBytesSeededSpec, true⟩ ]

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep13S3ReplRows_names :
    fidStep13S3ReplRows.map SpecEntry.name = fidStep13S3ReplNames :=
  rfl

theorem fidStep13S3ReplRows_sigs :
    fidStep13S3ReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S3Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S3ReplRows_noExit :
    fidStep13S3ReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S3BeforeRows_names :
    fidStep13S3BeforeRows.map SpecEntry.name = fidStep13S3BeforeNames :=
  rfl

theorem fidStep13S3BeforeRows_sigs :
    fidStep13S3BeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep13S3Befores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S3BeforeRows_noExit :
    fidStep13S3BeforeRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`32/32`) -/

theorem full_walk_cb_inv_m7_s13_callsOk :
    fidStep13S3WalkCbInvFn.checkCallsOk
      [ ("f64u_div", [i64, i64], [i64])
      , ("f64u_from_u64", [i64], [i64])
      , ("f64u_sub", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_add", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_walk_init_table_m7_s13_callsOk :
    fidStep13S3WalkInitTableFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_walk_effort_m7_s13_callsOk :
    fidStep13S3WalkEffortFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_walk_collect_m7_s13_callsOk :
    fidStep13S3WalkCollectFn.checkCallsOk
      [ ("full_arena_next", [i64, i32], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_walk_build_occ_m7_s13_callsOk :
    fidStep13S3WalkBuildOccFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_walk_break_m7_s13_callsOk :
    fidStep13S3WalkBreakFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_walk_pick_m7_s13_callsOk :
    fidStep13S3WalkPickFn.checkCallsOk
      [ ("full_walk_break_m7", [i64, i32, i64], [i32])
      , ("f64u_add", [i64, i64], [i64])
      , ("f64u_from_u64", [i64], [i64])
      , ("f64u_mul", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_walk_flip_m7_s13_callsOk :
    fidStep13S3WalkFlipFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_walk_m7_s13_callsOk :
    fidStep13S3WalkM7Fn.checkCallsOk
      [ ("full_dense_bin_roundtrip_fid", [i64], [])
      , ("full_watch_large_clauses_fid", [i64], [])
      , ("full_walk_init_vals_m7", [i64], [])
      , ("full_walk_collect_m7", [i64], [i64])
      , ("full_walk_cb_inv_m7", [i64, i64, i64], [i64])
      , ("full_walk_build_occ_m7", [i64, i64], [i64])
      , ("full_walk_effort_m7", [i64, i64], [i64])
      , ("full_walk_pick_m7", [i64, i32, i64], [i64])
      , ("full_walk_flip_m7", [i64, i32, i64, i64], [i64])
      , ("full_walk_save_min_m7", [i64, i64, .bool], []) ] [] = true := by
  t_kernel_rfl

theorem full_warmup_m7_s13_callsOk :
    fidStep13S3WarmupM7Fn.checkCallsOk
      [ ("full_next_dec_var", [i64], [i64])
      , ("full_assign", [i64, i32, i32], [])
      , ("full_propagate_beyond_m7", [i64], [i64])
      , ("full_backtrack", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_scale_delta_m5_s13_callsOk :
    fidStep13S3ScaleDeltaM5Fn.checkCallsOk
      [ ("f64u_log10_u64", [i64], [i64])
      , ("f64u_sub", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_add", [i64, i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("f64u_from_u64", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_ema_update_s13_callsOk :
    fidStep13S3EmaUpdateFn.checkCallsOk
      [ ("f64u_from_u64", [i64], [i64])
      , ("f64u_add", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_sub", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_scale_delta_s13_callsOk :
    fidStep13S3ScaleDeltaFn.checkCallsOk
      [ ("f64u_log10_u64", [i64], [i64])
      , ("f64u_sub", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_add", [i64, i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("f64u_from_u64", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_zero_tables2_s13_callsOk :
    fidStep13S3ZeroTables2Fn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem m6_hdr_dr_init_s13_callsOk :
    fidStep13S3DrInitFn.checkCallsOk
      [ ("m6_ext_ensure_init", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem m6_hdr_dr_update_s13_callsOk :
    fidStep13S3DrUpdateFn.checkCallsOk
      [ ("m6_hdr_dr_init", [i64], [])
      , ("f64u_from_u64", [i64], [i64])
      , ("f64u_add", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_sub", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem m6_hdr_dr_allow_s13_callsOk :
    fidStep13S3DrAllowFn.checkCallsOk
      [ ("m6_ext_ensure_init", [i64], [])
      , ("f64u_sub", [i64, i64], [i64])
      , ("f64u_div", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_rephase_s13_callsOk :
    fidStep13S3RephaseFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_walk", [i64], [])
      , ("f64u_to_u64", [i64], [i64])
      , ("f64u_nlogpown", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_restart_due_s13_callsOk :
    fidStep13S3RestartDueFn.checkCallsOk
      [ ("f64u_mul", [i64, i64], [i64])
      , ("f64u_sub", [i64, i64], [i64])
      , ("f64u_log10_u64", [i64], [i64])
      , ("f64u_to_u64", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_restart_s13_callsOk :
    fidStep13S3RestartFn.checkCallsOk
      [ ("full_randec_var_lvl_fid", [i64, i64], [i64])
      , ("full_next_dec_var", [i64], [i64])
      , ("full_backtrack", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_init_fresh_var_s13_callsOk :
    fidStep13S3InitFreshVarFn.checkCallsOk
      [ ("full_heap_push", [i64, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_compact_mark_live_s13_callsOk :
    fidStep13S3CompactMarkLiveFn.checkCallsOk
      [ ("full_arena_next", [i64, i32], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_compact_vars_s13_callsOk :
    fidStep13S3CompactVarsFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_m7_state_init_s13_callsOk :
    fidStep13S3M7StateInitFn.checkCallsOk
      [ ("full_m7_get64", [i64, i64], [i64])
      , ("full_m7_set64", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_randec_var_lvl_fid_s13_callsOk :
    fidStep13S3RandecVarLvlFn.checkCallsOk
      [ ("full_m7_state_init", [i64], [])
      , ("full_m7_get64", [i64, i64], [i64])
      , ("full_m7_set64", [i64, i64, i64], [])
      , ("f64u_log10_u64", [i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("full_lcg_next_m7", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_randec_var_m7_s13_callsOk :
    fidStep13S3RandecVarM7Fn.checkCallsOk
      [ ("full_randec_var_lvl_fid", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_ema_swap_m7_s13_callsOk :
    fidStep13S3EmaSwapM7Fn.checkCallsOk
      [ ("full_m7_state_init", [i64], [])
      , ("full_m7_set64", [i64, i64, i64], [])
      , ("full_m7_get64", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_switch_mode_m7_s13_callsOk :
    fidStep13S3SwitchModeM7Fn.checkCallsOk
      [ ("m6_wm4_get", [i64], [i64])
      , ("m6_wm4_set", [i64, i64], [])
      , ("full_heap_up", [i64, i32], [])
      , ("full_heap_down", [i64, i32], [])
      , ("full_heap_push", [i64, i32], [])
      , ("f64u_to_u64", [i64], [i64])
      , ("f64u_nlogpown", [i64, i64], [i64])
      , ("full_ema_swap_m7", [i64, i64, i64], [])
      , ("m6_hdr_dr_init", [i64], [])
      , ("full_ilog10", [i64], [i64])
      , ("full_m7_get64", [i64, i64], [i64])
      , ("full_m7_set64", [i64, i64, i64], [])
      , ("f64u_log10_u64", [i64], [i64])
      , ("f64u_mul", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_search_m6_s13_callsOk :
    fidStep13S3SearchM6Fn.checkCallsOk
      [ ("full_lucky_late_m7", [i64], [i64])
      , ("full_update_classify_fid", [i64], [])
      , ("m6_hdr_set_watermark", [i64, i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_analyze_m6_hdr", [i64], [i64])
      , ("full_reduce_m6", [i64, .bool], [i64])
      , ("full_switch_mode_m7", [i64], [])
      , ("full_restart_due", [i64], [i64])
      , ("full_restart", [i64], [])
      , ("full_reorder_m6", [i64, i64], [i64])
      , ("full_rephase", [i64], [])
      , ("full_simplify_m6", [i64, .bool, .bool], [i64])
      , ("m6_hdr_decide_fid", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem kissat_solve_bytes_seeded_s13_callsOk :
    fidStep13S3SolveBytesSeededFn.checkCallsOk
      [ ("full_m6_mem_init", [i64, i64, i64, i64, i64], [i64])
      , ("full_parse_body", [i64, i64], [i64])
      , ("full_preprocess_m6", [i64], [i64])
      , ("full_search_m6", [i64], [i64])
      , ("full_extend", [i64], [])
      , ("kissat_check_model", [i64, i64, i64, i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem kissat_solve_bytes_m6_s13_callsOk :
    fidStep13S3SolveBytesM6Fn.checkCallsOk
      [ ("kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem kissat_solve_bytes_s13_callsOk :
    fidStep13S3SolveBytesFn.checkCallsOk
      [ ("kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`32/32`) -/

theorem full_walk_cb_inv_m7_s13_impl (Γ : Env)
    (hAdd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hDiv : EnvSpec Γ "f64u_div" f64uPure2Spec)
    (hFrom : EnvSpec Γ "f64u_from_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S3WalkCbInvFn (fidStep13S3ReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_cb_inv_m7_step13_wp Γ hAdd hSub hMul hDiv hFrom)

theorem full_walk_init_table_m7_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3WalkInitTableFn (fidStep13S3ReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_init_table_m7_step13_wp Γ)

theorem full_walk_effort_m7_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3WalkEffortFn (fidStep13S3ReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_effort_m7_step13_wp Γ)

theorem full_walk_collect_m7_s13_impl (Γ : Env)
    (hArenaNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec) :
    SpecEntry.Impl Γ fidStep13S3WalkCollectFn (fidStep13S3ReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_collect_m7_step13_wp Γ hArenaNext)

theorem full_walk_build_occ_m7_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3WalkBuildOccFn (fidStep13S3ReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_build_occ_m7_step13_wp Γ)

theorem full_walk_break_m7_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3WalkBreakFn (fidStep13S3ReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_break_m7_step13_wp Γ)

theorem full_walk_pick_m7_s13_impl (Γ : Env)
    (hBrk : EnvSpec Γ "full_walk_break_m7" step13WalkBreakSpec)
    (hAdd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hFrom : EnvSpec Γ "f64u_from_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S3WalkPickFn (fidStep13S3ReplRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_pick_m7_step13_wp Γ hBrk hAdd hMul hFrom)

theorem full_walk_flip_m7_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3WalkFlipFn (fidStep13S3ReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_flip_m7_step13_wp Γ)

theorem full_walk_m7_s13_impl (Γ : Env)
    (hRoundtrip : EnvSpec Γ "full_dense_bin_roundtrip_fid" step13WatchRoundtripSpec)
    (hWatchLarge : EnvSpec Γ "full_watch_large_clauses_fid" step13WatchRoundtripSpec)
    (hInitVals : EnvSpec Γ "full_walk_init_vals_m7" m7InitValsSpec)
    (hCollect : EnvSpec Γ "full_walk_collect_m7" m7CollectSpec)
    (hCbInv : EnvSpec Γ "full_walk_cb_inv_m7" step13WalkCbInvSpec)
    (hBuildOcc : EnvSpec Γ "full_walk_build_occ_m7" step13WalkBuildOccSpec)
    (hEffort : EnvSpec Γ "full_walk_effort_m7" step13WalkEffortSpec)
    (hPick : EnvSpec Γ "full_walk_pick_m7" step13WalkPickSpec)
    (hFlip : EnvSpec Γ "full_walk_flip_m7" step13WalkFlipSpec)
    (hSaveMin : EnvSpec Γ "full_walk_save_min_m7" m7SaveMinSpec) :
    SpecEntry.Impl Γ fidStep13S3WalkM7Fn (fidStep13S3ReplRows[8]'(by decide)) :=
  SpecEntry.Impl.of (full_walk_m7_step13_wp Γ hRoundtrip hWatchLarge hInitVals hCollect
    hCbInv hBuildOcc hEffort hPick hFlip hSaveMin)

theorem full_warmup_m7_s13_impl (Γ : Env)
    (hNDV : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hPropBey : EnvSpec Γ "full_propagate_beyond_m7" step13PropBeyondM6Spec)
    (hBT : EnvSpec Γ "full_backtrack" fullBacktrackSpec) :
    SpecEntry.Impl Γ fidStep13S3WarmupM7Fn (fidStep13S3ReplRows[9]'(by decide)) :=
  SpecEntry.Impl.of (full_warmup_m7_step13_wp Γ hNDV hAssign hPropBey hBT)

theorem full_scale_delta_m5_s13_impl (Γ : Env)
    (hLog : EnvSpec Γ "f64u_log10_u64" f64uPure1Spec)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hAdd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hFrom : EnvSpec Γ "f64u_from_u64" f64uPure1Spec)
    (hTo : EnvSpec Γ "f64u_to_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S3ScaleDeltaM5Fn (fidStep13S3ReplRows[10]'(by decide)) :=
  SpecEntry.Impl.of (full_scale_delta_m5_step13_wp Γ hLog hSub hMul hAdd hFrom hTo)

theorem full_ema_update_s13_impl (Γ : Env)
    (hFrom : EnvSpec Γ "f64u_from_u64" f64uPure1Spec)
    (hAdd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec) :
    SpecEntry.Impl Γ fidStep13S3EmaUpdateFn (fidStep13S3ReplRows[11]'(by decide)) :=
  SpecEntry.Impl.of (full_ema_update_step13_wp Γ hFrom hAdd hSub hMul)

theorem full_scale_delta_s13_impl (Γ : Env)
    (hLog : EnvSpec Γ "f64u_log10_u64" f64uPure1Spec)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hAdd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hFrom : EnvSpec Γ "f64u_from_u64" f64uPure1Spec)
    (hTo : EnvSpec Γ "f64u_to_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S3ScaleDeltaFn (fidStep13S3ReplRows[12]'(by decide)) :=
  SpecEntry.Impl.of (full_scale_delta_step13_wp Γ hLog hSub hMul hAdd hFrom hTo)

theorem full_zero_tables2_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3ZeroTables2Fn (fidStep13S3ReplRows[13]'(by decide)) :=
  SpecEntry.Impl.of (full_zero_tables2_step13_wp Γ)

theorem m6_hdr_dr_init_s13_impl (Γ : Env)
    (hEnsure : EnvSpec Γ "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    SpecEntry.Impl Γ fidStep13S3DrInitFn (fidStep13S3ReplRows[14]'(by decide)) :=
  SpecEntry.Impl.of (m6_hdr_dr_init_step13_wp Γ hEnsure)

theorem m6_hdr_dr_update_s13_impl (Γ : Env)
    (hDrInit : EnvSpec Γ "m6_hdr_dr_init" m6HdrDrMutSpec)
    (hFrom : EnvSpec Γ "f64u_from_u64" f64uPure1Spec)
    (hAdd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec) :
    SpecEntry.Impl Γ fidStep13S3DrUpdateFn (fidStep13S3ReplRows[15]'(by decide)) :=
  SpecEntry.Impl.of (m6_hdr_dr_update_step13_wp Γ hDrInit hFrom hAdd hSub hMul)

theorem m6_hdr_dr_allow_s13_impl (Γ : Env)
    (hEnsure : EnvSpec Γ "m6_ext_ensure_init" m6ExtEnsureInitSpec)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hDiv : EnvSpec Γ "f64u_div" f64uPure2Spec) :
    SpecEntry.Impl Γ fidStep13S3DrAllowFn (fidStep13S3ReplRows[16]'(by decide)) :=
  SpecEntry.Impl.of (m6_hdr_dr_allow_step13_wp Γ hEnsure hSub hDiv)

theorem full_rephase_s13_impl (Γ : Env)
    (hBT : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hWalk : EnvSpec Γ "full_walk" step13WarmupM6Spec)
    (hNlog : EnvSpec Γ "f64u_nlogpown" f64uPure2Spec)
    (hTo : EnvSpec Γ "f64u_to_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S3RephaseFn (fidStep13S3ReplRows[17]'(by decide)) :=
  SpecEntry.Impl.of (full_rephase_step13_wp Γ hBT hWalk hNlog hTo)

theorem full_restart_due_s13_impl (Γ : Env)
    (hSub : EnvSpec Γ "f64u_sub" f64uPure2Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hLog : EnvSpec Γ "f64u_log10_u64" f64uPure1Spec)
    (hTo : EnvSpec Γ "f64u_to_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S3RestartDueFn (fidStep13S3ReplRows[18]'(by decide)) :=
  SpecEntry.Impl.of (full_restart_due_step13_wp Γ hSub hMul hLog hTo)

theorem full_restart_s13_impl (Γ : Env)
    (hRandec : EnvSpec Γ "full_randec_var_lvl_fid" step13RandecVarLvlSpec)
    (hNDV : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hBT : EnvSpec Γ "full_backtrack" fullBacktrackSpec) :
    SpecEntry.Impl Γ fidStep13S3RestartFn (fidStep13S3ReplRows[19]'(by decide)) :=
  SpecEntry.Impl.of (full_restart_step13_wp Γ hRandec hNDV hBT)

theorem full_init_fresh_var_s13_impl (Γ : Env)
    (hHeapPush : EnvSpec Γ "full_heap_push" fullHeapPushSpec) :
    SpecEntry.Impl Γ fidStep13S3InitFreshVarFn (fidStep13S3ReplRows[20]'(by decide)) :=
  SpecEntry.Impl.of (full_init_fresh_var_step13_wp Γ hHeapPush)

theorem full_compact_mark_live_s13_impl (Γ : Env)
    (hnext : EnvSpec Γ "full_arena_next" fullArenaNextSpec) :
    SpecEntry.Impl Γ fidStep13S3CompactMarkLiveFn (fidStep13S3ReplRows[21]'(by decide)) :=
  SpecEntry.Impl.of (full_compact_mark_live_step13_wp Γ hnext)

theorem full_compact_vars_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S3CompactVarsFn (fidStep13S3ReplRows[22]'(by decide)) :=
  SpecEntry.Impl.of (full_compact_vars_step13_wp Γ)

theorem full_m7_state_init_s13_impl (Γ : Env)
    (hGet64 : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    SpecEntry.Impl Γ fidStep13S3M7StateInitFn (fidStep13S3ReplRows[23]'(by decide)) :=
  SpecEntry.Impl.of (full_m7_state_init_step13_wp Γ hGet64 hSet64)

theorem full_randec_var_m7_s13_impl (Γ : Env)
    (hLvl : EnvSpec Γ "full_randec_var_lvl_fid" step13RandecVarLvlSpec) :
    SpecEntry.Impl Γ fidStep13S3RandecVarM7Fn (fidStep13S3ReplRows[24]'(by decide)) :=
  SpecEntry.Impl.of (full_randec_var_m7_step13_wp Γ hLvl)

theorem full_ema_swap_m7_s13_impl (Γ : Env)
    (hInit : EnvSpec Γ "full_m7_state_init" step13M7StateInitSpec)
    (hGet64 : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    SpecEntry.Impl Γ fidStep13S3EmaSwapM7Fn (fidStep13S3ReplRows[25]'(by decide)) :=
  SpecEntry.Impl.of (full_ema_swap_m7_step13_wp Γ hInit hGet64 hSet64)

theorem full_switch_mode_m7_s13_impl (Γ : Env)
    (hWm4Get : EnvSpec Γ "m6_wm4_get" (m6HdrW2aSpec [] [i64]))
    (hWm4Set : EnvSpec Γ "m6_wm4_set" (m6HdrW2aSpec [i64] []))
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hHeapPush : EnvSpec Γ "full_heap_push" fullHeapPushSpec)
    (hNlog : EnvSpec Γ "f64u_nlogpown" f64uPure2Spec)
    (hTo : EnvSpec Γ "f64u_to_u64" f64uPure1Spec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" step13EmaSwapSpec)
    (hDrInit : EnvSpec Γ "m6_hdr_dr_init" m6HdrDrMutSpec)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hGet64 : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog : EnvSpec Γ "f64u_log10_u64" f64uPure1Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec) :
    SpecEntry.Impl Γ fidStep13S3SwitchModeM7Fn (fidStep13S3ReplRows[26]'(by decide)) :=
  SpecEntry.Impl.of (full_switch_mode_m7_step13_wp Γ hWm4Get hWm4Set hHeapUp hHeapDown
    hHeapPush hNlog hTo hEmaSwap hDrInit hIlog hGet64 hSet64 hLog hMul)

theorem full_search_m6_s13_impl (Γ : Env)
    (hLuckyLate : EnvSpec Γ "full_lucky_late_m7" step13LuckyLateM6Spec)
    (hClassify : EnvSpec Γ "full_update_classify_fid" (m6HdrW2aSpec [] []))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hProp : EnvSpec Γ "full_propagate" step13BcpM6Spec)
    (hAnalyze : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hReduce : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hSwitch : EnvSpec Γ "full_switch_mode_m7" step13SwitchModeM6Spec)
    (hRstDue : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hRst : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hReorder : EnvSpec Γ "full_reorder_m6" FullM4.m4ReorderSpec)
    (hRephase : EnvSpec Γ "full_rephase" step13RephaseM6Spec)
    (hSimplify : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hDecideFid : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec) :
    SpecEntry.Impl Γ fidStep13S3SearchM6Fn (fidStep13S3ReplRows[27]'(by decide)) :=
  SpecEntry.Impl.of (full_search_m6_step13_wp Γ hLuckyLate hClassify hSetWm hProp hAnalyze
    hReduce hSwitch hRstDue hRst hReorder hRephase hSimplify hDecideFid)

theorem kissat_solve_bytes_m6_s13_impl (Γ : Env)
    (hSeeded : EnvSpec Γ "kissat_solve_bytes_seeded" step13SolveBytesSeededSpec) :
    SpecEntry.Impl Γ fidStep13S3SolveBytesM6Fn (fidStep13S3ReplRows[28]'(by decide)) :=
  SpecEntry.Impl.of (kissat_solve_bytes_m6_step13_wp Γ hSeeded)

theorem kissat_solve_bytes_s13_impl (Γ : Env)
    (hSeeded : EnvSpec Γ "kissat_solve_bytes_seeded" step13SolveBytesSeededSpec) :
    SpecEntry.Impl Γ fidStep13S3SolveBytesFn (fidStep13S3ReplRows[29]'(by decide)) :=
  SpecEntry.Impl.of (kissat_solve_bytes_step13_wp Γ hSeeded)

theorem full_randec_var_lvl_fid_s13_impl (Γ : Env)
    (hInit : EnvSpec Γ "full_m7_state_init" step13M7StateInitSpec)
    (hGet64 : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog : EnvSpec Γ "f64u_log10_u64" f64uPure1Spec)
    (hMul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hTo : EnvSpec Γ "f64u_to_u64" f64uPure1Spec)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec) :
    SpecEntry.Impl Γ fidStep13S3RandecVarLvlFn (fidStep13S3BeforeRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_randec_var_lvl_fid_step13_wp Γ hInit hGet64 hSet64 hLog hMul hTo hLcg)

theorem kissat_solve_bytes_seeded_s13_impl (Γ : Env)
    (hMemInit : EnvSpec Γ "full_m6_mem_init" fullM6MemInitExactSpec)
    (hParse : EnvSpec Γ "full_parse_body" step13ParseBodyM6Spec)
    (hPre : EnvSpec Γ "full_preprocess_m6" fullM6PreprocessSpec)
    (hSearch : EnvSpec Γ "full_search_m6" fullM6SearchSpec)
    (hExt : EnvSpec Γ "full_extend" Full.fullExtendSpec)
    (hCheck : EnvSpec Γ "kissat_check_model" kissatCheckModelExactSpec) :
    SpecEntry.Impl Γ fidStep13S3SolveBytesSeededFn (fidStep13S3BeforeRows[1]'(by decide)) :=
  SpecEntry.Impl.of (kissat_solve_bytes_seeded_step13_wp Γ hMemInit hParse hPre hSearch hExt hCheck)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

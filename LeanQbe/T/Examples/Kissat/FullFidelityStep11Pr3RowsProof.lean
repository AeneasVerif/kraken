/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3Rows
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepEnvProof
public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof
public import LeanQbe.T.Examples.Kissat.FullFidelityVivFlagProof
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Logic.C0Step

/-!
# Kissat Step-11 PR 3 Specification Rows & `Impl` Barrel (`FullFidelityStep11Pr3RowsProof`)

Plain `public section` (`0` `@[expose]` on theorems/lemmas, `0` new `import all`, `std3`,
`XPost`-polymorphic) barrel exporting the `12` replacement rows (`fidStep11Pr3ReplRows`),
`1` inserted helper row (`fidStep11Pr3BeforeRows`), `Fn.checkCallsOk` witnesses, and
parametric `(Γ : Env)` `SpecEntry.Impl` theorems ready for 2-line plug-in into
`FullFidelityAssemblyStep11Proof.lean`:
- **S11-6a (`1` fn):** `full_m6_sweep_cone` (`FullM6Sweep.m6SweepConeSpec`)
- **S11-7 (`7 + 1` fns):** `full_save_target_best`, `full_backtrack` (consistent-state),
  `full_deduce_1uip_m6`, `full_deduce_1uip_m6_hdr`, `full_one_lit_confl`,
  `full_learn_clause`, `full_learn_clause_m6`, and helper `full_backtrack_ac_fid`
- **S11-8 (`4` fns):** `full_viv_collect_fid` (`fid11VivCollectSpec`), `full_viv_sort2_fid`,
  `full_viv_sort_fid`, `full_viv_clause_m6`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullFidelityStep10
open LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv
open LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. `fidStep11Pr3ReplRows`, `fidStep11Pr3BeforeRows`, Signatures & `noExit` -/

/-- The `12` Step-11 PR 3 replacement `SpecEntry` rows matching `fidStep11Pr3Repls`. -/
@[expose] def fidStep11Pr3ReplRows : List SpecEntry :=
  [ ⟨"full_m6_sweep_cone", [i64, i32], [i64], m6SweepConeSpec, true⟩
  , ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64], fullDeduce1uipSpec, true⟩
  , ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], m6Deduce1uipHdrSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  , ⟨"full_learn_clause_m6", [i64, i64], [i64], step10LearnClauseM6Spec, true⟩
  , ⟨"full_viv_collect_fid", [i64, i64], [i64], fid11VivCollectSpec, true⟩
  , ⟨"full_viv_sort2_fid", [i64, i64, i64], [], fullVivSort2FidSpec, true⟩
  , ⟨"full_viv_sort_fid", [i64, i64], [], fullVivSortFidSpec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩ ]

/-- The `1` Step-11 PR 3 inserted helper `SpecEntry` row matching `fidStep11Pr3Befores`. -/
@[expose] def fidStep11Pr3BeforeRows : List SpecEntry :=
  [ ⟨"full_backtrack_ac_fid", [i64, i64], [], fullBacktrackSpec, true⟩ ]

/-- Combined `13` Step-11 PR 3 `SpecEntry` rows (`12` repls + `1` inserted helper). -/
@[expose] def fidStep11Pr3Rows : List SpecEntry :=
  fidStep11Pr3ReplRows ++ fidStep11Pr3BeforeRows

/-- Names of all `13` PR 3 rows (`frontNames` helper). -/
@[expose] def fidStep11Pr3Names : List Sym :=
  [ "full_m6_sweep_cone", "full_save_target_best", "full_backtrack"
  , "full_deduce_1uip_m6", "full_deduce_1uip_m6_hdr", "full_one_lit_confl"
  , "full_learn_clause", "full_learn_clause_m6", "full_viv_collect_fid"
  , "full_viv_sort2_fid", "full_viv_sort_fid", "full_viv_clause_m6"
  , "full_backtrack_ac_fid" ]

theorem fidStep11Pr3Rows_map_name : fidStep11Pr3Rows.map SpecEntry.name = fidStep11Pr3Names :=
  rfl

theorem fidStep11Pr3Rows_nodup : (fidStep11Pr3Rows.map SpecEntry.name).Nodup := by
  rw [fidStep11Pr3Rows_map_name]
  decide

theorem fidStep11Pr3Rows_noExit : ∀ e ∈ fidStep11Pr3Rows, e.noExit = true := by
  intro e he
  have hall : fidStep11Pr3Rows.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem fidStep11Pr3ReplRows_sigs :
    fidStep11Pr3ReplRows.map (fun e => (e.name, e.as, e.rs)) =
      fidStep11Pr3Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep11Pr3BeforeRows_sigs :
    fidStep11Pr3BeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep11Pr3Befores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

/-! ## 2. Static `checkCallsOk` Witnesses (`13/13`) -/

theorem pr3_sweepCone_callsOk :
    fid11SweepConeFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_k6_init", [i64, i32], [])
      , ("full_k6_add_clause", [i64, i64, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem pr3_saveTargetBest_callsOk :
    fid11SaveTargetBestFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem pr3_backtrack_callsOk :
    fid11BacktrackFn.checkCallsOk
      [ ("full_save_target_best", [i64], [])
      , ("full_backtrack_raw_m5", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_backtrackAc_callsOk :
    fid11BacktrackAcFn.checkCallsOk
      [ ("full_save_target_best", [i64], [])
      , ("full_backtrack_raw_m5", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_deduce1uipM6_callsOk :
    fid11Deduce1uipM6Fn.checkCallsOk
      [ ("full_analyze_lit", [i64, i32, i32], [.bool])
      , ("full_analyze_rsn", [i64, i32, i32], [.bool])
      , ("full_clear_ana", [i64], [])
      , ("full_otfs_large", [i64, i32, i32], [.bool])
      , ("full_otfs_bin", [i64, i32, i32], [.bool])
      , ("full_otfs_subsume", [i64, i32, i64, i64, .bool], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_deduce1uipM6Hdr_callsOk :
    fid11Deduce1uipM6HdrFn.checkCallsOk
      [ ("full_analyze_lit", [i64, i32, i32], [.bool])
      , ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool])
      , ("full_clear_ana", [i64], [])
      , ("full_otfs_large", [i64, i32, i32], [.bool])
      , ("full_otfs_bin", [i64, i32, i32], [.bool])
      , ("full_otfs_subsume", [i64, i32, i64, i64, .bool], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_oneLitConfl_callsOk :
    fid11OneLitConflFn.checkCallsOk
      [ ("full_wstack_defrag", [i64], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_unwatch_large", [i64, i32, i32], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem pr3_learnClause_callsOk :
    fid11LearnClauseFn.checkCallsOk
      [ ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_wstack_defrag", [i64], [])
      , ("full_reduce", [i64, .bool], [i64])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64])
      , ("full_eager_subsume", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_learnClauseM6_callsOk :
    fid11LearnClauseM6Fn.checkCallsOk
      [ ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_wstack_defrag", [i64], [])
      , ("full_reduce_m6", [i64, .bool], [i64])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64])
      , ("full_eager_subsume", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_vivCollectFid_callsOk :
    fid11VivCollectFidFn.checkCallsOk
      [ ("full_arena_next", [i64, i32], [i32])
      , ("full_viv_tier_match_m6", [i64, i32, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem pr3_vivSort2Fid_callsOk :
    fid11VivSort2FidFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem pr3_vivSortFid_callsOk :
    fid11VivSortFidFn.checkCallsOk
      [ ("full_viv_sort2_fid", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem pr3_vivClauseM6_callsOk :
    fid11VivClauseM6Fn.checkCallsOk
      [ ("full_viv_l0_simp_m6", [i64, i32, i32], [i64])
      , ("full_viv_sort_counts_m6", [i64, i32], [])
      , ("full_viv_reuse_prefix_m6", [i64, i32, i32], [])
      , ("full_viv_best_implied_m6", [i64, i32], [i32])
      , ("full_assign", [i64, i32, i32], [])
      , ("full_propagate_ignore", [i64, i64], [i64])
      , ("full_backtrack", [i64, i64], [])
      , ("full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Theorems (`13/13`, `XPost`-Polymorphic) -/

theorem fid11_sweep_cone_impl (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hInit : M6EnvSpec Γ "full_k6_init" k6InitSpec)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec) :
    SpecEntry.Impl Γ fid11SweepConeFn fidStep11Pr3ReplRows[0] :=
  SpecEntry.Impl.of (fid11_sweep_cone_wp Γ hMaxV hInit hAddCl)

theorem fid11_save_target_best_impl (Γ : Env) :
    SpecEntry.Impl Γ fid11SaveTargetBestFn fidStep11Pr3ReplRows[1] :=
  SpecEntry.Impl.of (fid11_save_target_best_wp Γ)

theorem fid11_backtrack_impl (Γ : Env)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fid11BacktrackFn fidStep11Pr3ReplRows[2] :=
  SpecEntry.Impl.of (fid11_backtrack_cs_wp Γ hBtRaw hSave)

theorem fid11_deduce_1uip_m6_impl (Γ : Env)
    (hAlit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    SpecEntry.Impl Γ fid11Deduce1uipM6Fn fidStep11Pr3ReplRows[3] :=
  SpecEntry.Impl.of
    (fid11_deduce_1uip_m6_wp Γ hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub)

theorem fid11_deduce_1uip_m6_hdr_impl (Γ : Env)
    (hAlit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    SpecEntry.Impl Γ fid11Deduce1uipM6HdrFn fidStep11Pr3ReplRows[4] :=
  SpecEntry.Impl.of
    (fid11_deduce_1uip_m6_hdr_wp Γ hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub)

theorem fid11_one_lit_confl_impl (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hBtAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAss : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fid11OneLitConflFn fidStep11Pr3ReplRows[5] :=
  SpecEntry.Impl.of (fid11_one_lit_confl_wp Γ hDefrag hDet hBtAc hAss hUnw hPush)

theorem fid11_learn_clause_impl (Γ : Env)
    (hBtAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X →
      Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fid11LearnClauseFn fidStep11Pr3ReplRows[6] :=
  SpecEntry.Impl.of (fid11_learn_clause_wp Γ hBtAc hAsgn hDnl hDefrag hRed hAddCl hEsub)

theorem fid11_learn_clause_m6_impl (Γ : Env)
    (hBtAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fid11LearnClauseM6Fn fidStep11Pr3ReplRows[7] :=
  SpecEntry.Impl.of (fid11_learn_clause_m6_wp Γ hBtAc hAsgn hDnl hDefrag hRedM6 hAddCl hEsub)

theorem fid11_viv_collect_fid_impl (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Γ "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X) :
    SpecEntry.Impl Γ fid11VivCollectFidFn fidStep11Pr3ReplRows[8] :=
  SpecEntry.Impl.of (fid11_viv_collect_fid_wp Γ hNext hTierMatch)

theorem fid11_viv_sort2_fid_impl (Γ : Env) :
    SpecEntry.Impl Γ fid11VivSort2FidFn fidStep11Pr3ReplRows[9] :=
  SpecEntry.Impl.of (fid11_viv_sort2_fid_wp Γ)

theorem fid11_viv_sort_fid_impl (Γ : Env)
    (hSort2 : ∀ a m Q X, fullVivSort2FidSpec a m Q X →
      Γ "full_viv_sort2_fid" [i64, i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fid11VivSortFidFn fidStep11Pr3ReplRows[10] :=
  SpecEntry.Impl.of (fid11_viv_sort_fid_wp Γ hSort2)

theorem fid11_viv_clause_m6_impl (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
      Γ "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Γ "full_viv_sort_counts_m6" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Γ "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Γ "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    SpecEntry.Impl Γ fid11VivClauseM6Fn fidStep11Pr3ReplRows[11] :=
  SpecEntry.Impl.of (fid11_viv_clause_m6_wp Γ hL0Simp hSort hReuse hBestImpl hAssign hPropIgn
    hBacktrack hFinish)

theorem fid11_backtrack_ac_impl (Γ : Env)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fid11BacktrackAcFn fidStep11Pr3BeforeRows[0] :=
  SpecEntry.Impl.of (fid11_backtrack_ac_wp Γ hBtRaw hSave)

end LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3

end

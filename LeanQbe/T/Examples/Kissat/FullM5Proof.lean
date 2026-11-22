/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Proof1
import LeanQbe.T.Examples.Kissat.FullFastAdapters
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` Unified M5 `ModuleOk` Assembly & Top-Level Soundness (`FullM5Proof`, `270/270`)

1. Closed `270`-row specification table `m5SpecTable`, `mkM5Env`, `m5Env`, `m5UnsatEnv` aligned
   1-to-1 with `FullM5.m5Fns` (`0` exits, `0` externs).
2. `m5M4Unchanged_wp` (`153` unchanged M4 functions) + `m5Sweep22_wp` (`22` `FullM4Sweep` helpers) +
   `m5Fns_all_wp` (`270/270`).
3. Unconditional `mkM5Env_moduleOk`, `m5Env_moduleOk`, `m5UnsatEnv_moduleOk`,
   `m5_solve_bytes_correct`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `4096` B
   workspace, `fuel = 16`, `0` SAT proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_init_state_body full_init_state_wf
  full_reduce_body full_reduce_wf
  full_preprocess_body full_preprocess_wf
  full_search_body full_search_wf
  kissat_solve_bytes_body kissat_solve_bytes_full_wf
  full_add_bin_body full_add_bin_wf
open Kraken.Bedrock2.Test

/-! ## 1. Closed `270`-Row `m5SpecTable`, `mkM5Env`, `m5Env`, & `m5UnsatEnv` -/

/-- Closed `270`-row specification table aligned 1-to-1 with `FullM5.m5Fns` (`0` exits). -/
def m5SpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  [ ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  , ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  , ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  , ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  , ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  , ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , ⟨"full_wsort_sift", [i64, i64, i64, i64], [], fullWsortSiftSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  , ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  , ⟨"full_heap_pop", [i64], [i64], fullHeapPopSpec, true⟩
  , ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  , ⟨"full_queue_renumber", [i64], [], fullQueueRenumberSpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  , ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  , ⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  , ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  , ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  , ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  , ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.fullFastInitHdrSpec, true⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  , ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  , ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  , ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  , ⟨"full_assign_level", [i64, i32, i32], [i32], fullAssignLevelSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  , ⟨"full_red_less", [i64, i32, i32], [.bool], fullRedLessSpec, true⟩
  , ⟨"full_red_sift", [i64, i64, i64, i64], [], fullRedSiftSpec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  , ⟨"full_lit_rank", [i64, i64, i32], [i64], fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  , ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"full_reduce_m5", [i64, .bool], [i64], fullReduceSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  , ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  , ⟨"full_restore_bump_ana_m5", [i64], [], FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin_m5", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  , ⟨"full_min_mark", [i64, i32, i8], [], fullMinMarkSpec, true⟩
  , ⟨"full_min_lit", [i64, i32], [.bool], fullMinLitSpec, true⟩
  , ⟨"full_tmp_less", [i64, i64, i32, i32], [.bool], fullTmpLessSpec, true⟩
  , ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [], fullSortTmpSiftSpec, true⟩
  , ⟨"full_sort_tmp", [i64], [], fullSortTmpSpec, true⟩
  , ⟨"full_shrink_lower", [i64, i32, i32], [.bool], fullShrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk", [i64, i64, i64, i32, i64], [], fullShrinkBlkSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  , ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  , ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  , ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  , ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  , ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
  , ⟨"full_walk_collect", [i64], [i64], fullWalkCollectSpec, true⟩
  , ⟨"full_walk_cl_sat", [i64, i64, i64], [.bool], fullWalkClSatSpec, true⟩
  , ⟨"full_walk_pick_lit", [i64, i64, i64], [i32], fullWalkPickLitSpec, true⟩
  , ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  , ⟨"full_rephase", [i64], [], FullM5Sched.m5RephaseSpec, true⟩
  , ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  , ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  , ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩
  , ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], fullLuckyScanSpec, true⟩
  , ⟨"full_lucky_polar", [i64], [i64], fullLuckyPolarSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  , ⟨"full_hbr_dom", [i64, i32, i32], [i32], fullHbrDomSpec, true⟩
  , ⟨"full_probe_prop_lit", [i64, i32], [.bool], fullProbePropLitSpec, true⟩
  , ⟨"full_probe_prop", [i64], [i64], fullProbePropSpec, true⟩
  , ⟨"full_probe_flush_hbr", [i64, i64], [i64], fullProbeFlushHbrSpec, true⟩
  , ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  , ⟨"full_trans_lit_m5", [i64, i32], [.bool], fullTransLitSpec, true⟩
  , ⟨"full_transitive_m5", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_viv_simplify", [i64, i32], [i64], FullM4VivBce.fullVivSimplifyM4Spec, true⟩
  , ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
  , ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  , ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64],
      FullM4VivBce.fullVivCommitM4Spec, true⟩
  , ⟨"full_viv_sort_noccs_m4", [i64, i32], [], FullM4VivBce.fullVivSortNoccsM4Spec, true⟩
  , ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool], FullM4VivBce.fullVivHasL0M4Spec, true⟩
  , ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64], FullM4VivBce.fullVivL0SimpM4Spec, true⟩
  , ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [], FullM4VivBce.fullVivReusePrefixM4Spec, true⟩
  , ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64],
      FullM4VivBce.fullVivFinishM4Spec, true⟩
  , ⟨"full_viv_clause_m4", [i64, i32], [i64], FullM4VivBce.fullVivClauseM4Spec, true⟩
  , ⟨"full_viv_sort_sched_m4", [i64, i64], [], FullM4VivBce.fullVivSortSchedM4Spec, true⟩
  , ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool], FullM4VivBce.fullVivTierMatchM4Spec, true⟩
  , ⟨"full_viv_collect_m4", [i64, i64], [i64], FullM4VivBce.fullVivCollectM4Spec, true⟩
  , ⟨"full_viv_keys_m4", [i64, i64], [], FullM4VivBce.fullVivKeysM4Spec, true⟩
  , ⟨"full_viv_clear_tier_m4", [i64, i64], [], FullM4VivBce.fullVivClearTierM4Spec, true⟩
  , ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64], FullM5Orch.fullVivifyTierM5Spec, true⟩
  , ⟨"full_vivify_m5", [i64], [i64], FullM5Orch.m5VivifySpec, true⟩
  , ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  , ⟨"full_tarjan_scc", [i64], [i64], FullFastBveBudgets.fullTarjanSccFastSpec, true⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  , ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  , ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩
  , ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  , ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩
  , ⟨"full_kitten_mtf", [i64, i32], [], fullKittenMtfSpec, true⟩
  , ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩
  , ⟨"full_kitten_learn_unit0", [i64, i32, i32, .bool], [i32], fullKittenLearnUnit0Spec, true⟩
  , ⟨"full_kitten_propagate", [i64], [i32], fullKittenPropagateSpec, true⟩
  , ⟨"full_kitten_ana_clause", [i64, i32, i32], [], fullKittenAnaClauseSpec, true⟩
  , ⟨"full_kitten_analyze", [i64, i32], [.bool], fullKittenAnalyzeSpec, true⟩
  , ⟨"full_kitten_build_failing", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  , ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  , ⟨"full_kitten_core", [i64], [i32], fullKittenCoreSpec, true⟩
  , ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec, true⟩
  , ⟨"full_kitten_flip", [i64, i32], [.bool], fullKittenFlipSpec, true⟩
  , ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  , ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  , ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  , ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
      FullM5CongFix.m5CongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
      FullM5CongFix.m5CongEmitXorSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      FullM5CongFix.m5CongTryXorIteSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM5CongFix.m5CongExtractSpec, true⟩
  , ⟨"full_cong_mark_trail", [i64, i64, i32], [], FullM3CongBva.m3CongMarkTrailSpec, true⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], FullM3CongBva.m3CongUnitFoldSpec, true⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      FullM3CongBva.m3CongEquivFoldSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM5CongFix.m5CongAndMatchSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      FullM5CongFix.m5CongWorkStepSpec, true⟩
  , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], FullM5CongBins.m5CongEbMatchSpec, true⟩
  , ⟨"full_cong_extract_binaries", [i64], [i64],
      FullM5CongBins.m5CongExtractBinariesSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_k512_init", [i64, i32], [], FullM4Sweep.k5InitSpec, true⟩
  , ⟨"full_k512_watch", [i64, i32, i32, i32], [], FullM4Sweep.k5WatchSpec, true⟩
  , ⟨"full_k512_assign", [i64, i32, i32], [], FullM4Sweep.k5AssignSpec, true⟩
  , ⟨"full_k512_add_clause", [i64, i64, i32], [.bool], FullM4Sweep.k5AddClauseSpec, true⟩
  , ⟨"full_k512_mtf", [i64, i32], [], FullM4Sweep.k5MtfSpec, true⟩
  , ⟨"full_k512_backtrack", [i64, i32], [], FullM4Sweep.k5BacktrackSpec, true⟩
  , ⟨"full_k512_propagate", [i64], [i32], FullM4Sweep.k5PropagateSpec, true⟩
  , ⟨"full_k512_ana_clause", [i64, i32, i32], [], FullM4Sweep.k5AnaClauseSpec, true⟩
  , ⟨"full_k512_analyze", [i64, i32], [.bool], FullM4Sweep.k5AnalyzeSpec, true⟩
  , ⟨"full_k512_solve", [i64, i64], [i64], FullM4Sweep.k5SolveSpec, true⟩
  , ⟨"full_k512_flip", [i64, i32], [.bool], FullM4Sweep.k5FlipSpec, true⟩
  , ⟨"full_k512_add_live", [i64, i32, i32], [], FullM4Sweep.k5AddLiveSpec, true⟩
  , ⟨"full_m4_sweep_cone", [i64, i32], [i64], FullM4Sweep.m4SweepConeSpec, true⟩
  , ⟨"full_m4_sweep_refine_sig", [i64, i32, i32], [], FullM4Sweep.m4SweepRefineSigSpec, true⟩
  , ⟨"full_m4_sweep_rand_phases", [i64, i32], [], FullM4Sweep.m4SweepRandPhasesSpec, true⟩
  , ⟨"full_m4_sweep_flip_round", [i64, i32], [i32], FullM4Sweep.m4SweepFlipRoundSpec, true⟩
  , ⟨"full_m4_sweep_sim", [i64, i32, i64], [i32], FullM4Sweep.m4SweepSimSpec, true⟩
  , ⟨"full_m4_sweep_rearm", [i64, i32], [], FullM4Sweep.m4SweepRearmSpec, true⟩
  , ⟨"full_m4_sweep_build_pht", [i64, i32, i64], [], FullM4Sweep.m4SweepBuildPhtSpec, true⟩
  , ⟨"full_m4_sweep_units", [i64, i32, i32, i64], [i64], FullM4Sweep.m4SweepUnitsSpec, true⟩
  , ⟨"full_m4_sweep_classes", [i64, i32, i32, i64], [i64], FullM4Sweep.m4SweepClassesSpec, true⟩
  , ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], FullM4Sweep.m4SweepVarSpec, true⟩
  , ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  , ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool],
      FullDefSweep.fullBveMarkAndDefSpec, true⟩
  , ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  , ⟨"full_kitten_ana_clause_m5", [i64, i32, i32], [],
      FullM5KittenDefFix.fullKittenAnaClauseM5Spec, true⟩
  , ⟨"full_kitten_build_failing_m5", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  , ⟨"full_kitten_solve_m5", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  , ⟨"full_kitten_core_m5", [i64], [i32], fullKittenCoreSpec, true⟩
  , ⟨"full_find_definition", [i64, i32, i32, i32], [], FullDefSweep.fullFindDefinitionSpec, true⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], [], FullDefSweep.fullBveGatesDefSpec, true⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
      FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64],
      FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩
  , ⟨"full_bva_hop1", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop1Spec, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop2Spec, true⟩
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], FullM4Bva.m4BvaHop3Spec, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      FullBvaHeap.fullBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullBvaHeap.fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩
  , ⟨"full_compact_assign_map", [i64], [i64], FullM4Compact.fullCompactAssignMapSpec, true⟩
  , ⟨"full_compact_record_ext", [i64, i64, i64], [.bool],
      FullM4Compact.fullCompactRecordExtSpec, true⟩
  , ⟨"full_compact_bins", [i64, i64, i64], [], FullM4Compact.fullCompactBinsSpec, true⟩
  , ⟨"full_compact_arena", [i64, i64], [i64], FullM4Compact.fullCompactArenaSpec, true⟩
  , ⟨"full_compact_vars", [i64, i64, i64], [], FullM4Compact.fullCompactVarsSpec, true⟩
  , ⟨"full_compact_sift_q", [i64, i64, i64, i64], [], FullM4Compact.fullCompactSiftQSpec, true⟩
  , ⟨"full_compact_vmtf", [i64, i64], [], FullM4Compact.fullCompactVmtfSpec, true⟩
  , ⟨"full_compact_sift_h", [i64, i64, i64, i64, i64], [],
      FullM4Compact.fullCompactSiftHSpec, true⟩
  , ⟨"full_compact_heap", [i64, i64], [], FullM4Compact.fullCompactHeapSpec, true⟩
  , ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
  , ⟨"full_score_sift", [i64, i64, i64], [], FullM4Ternary.fullScoreSiftSpec, true⟩
  , ⟨"full_reorder_queue", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  , ⟨"full_reorder_m5", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4VivBce.fullBceSideM4Spec, true⟩
  , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.fullBcePairM4Spec, true⟩
  , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.fullBceVarM4Spec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  , ⟨"full_probe_dticks_m5", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  , ⟨"full_backbone_lit", [i64, i32], [i64], FullM3Backbone.fullBackboneLitSpec, true⟩
  , ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_probe_tail_m5", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  , ⟨"full_probe_m5", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  , ⟨"full_elim_dticks_m5", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  , ⟨"full_elim_collect_nbrs", [i64, i32], [i64], FullM3CongBva.m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m5", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], FullM4.m4PreprocessSpec, true⟩
  , ⟨"full_simplify_m5", [i64, .bool, .bool], [i64], FullM4.m4SimplifySpec, true⟩
  , ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩
  , ⟨"full_search", [i64], [i64], FullM4.m4SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

def mkM5Env (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m5SpecTable mainSpec)

/-- Headline `270`-function UNSAT-only environment for `FullM5.m5Module`. -/
def m5Env : Env := mkM5Env fullSolveBytesSpec

/-- Concrete `270`-function UNSAT non-vacuity environment (`fullUnsatWitnessSpec`, `20#64`). -/
def m5UnsatEnv : Env := mkM5Env fullUnsatWitnessSpec

theorem m5SpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m5SpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (m5SpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m5SpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m5SpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      m5Fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

theorem m5SpecTable_length (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m5SpecTable mainSpec).length = 270 := by
  have hs := congrArg List.length (m5SpecTable_sigs mainSpec)
  simpa only [List.length_map, m5Fns_length] using hs

theorem m5Fns_nodup : (m5Fns.map Fn.name).Nodup := by
  have hchk := m5_acyclic
  simp only [m5Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

theorem m5SpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m5SpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (m5SpecTable mainSpec).map SpecEntry.name = m5Fns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (m5SpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]; exact m5Fns_nodup

private theorem m5_ofTable_iff_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} :
    Env.ofTable tbl e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact Env.ofTable_cons_self _ _ _ _ _ _
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).trans (ih hmem hnd.2)

private theorem m5_ofTable_false_of_not_mem {tbl : List SpecEntry} {f : Sym}
    (hf : f ∉ tbl.map SpecEntry.name) {as bs : List Ty} (xs : Tup Val as) (m : Mem 64)
    (Q : Post bs) (X : XPost) : ¬ Env.ofTable tbl f as bs xs m Q X := by
  induction tbl with
  | nil => exact fun h => h
  | cons e es ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hf
    rw [Env.ofTable_cons_ne (Ne.symm hf.1)]
    exact ih hf.2

private theorem m5_ofTable_off_sig {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {as bs : List Ty}
    (hne : ¬ (e.as = as ∧ e.rs = bs))
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofTable tbl e.name as bs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · intro h
      rcases h with ⟨⟨_, ha, hb⟩, _⟩ | ⟨_, htail⟩
      · exact hne ⟨ha, hb⟩
      · exact absurd htail (m5_ofTable_false_of_not_mem hnd.1 xs m Q X)
    · have hne' : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      rw [Env.ofTable_cons_ne hne']
      exact ih hmem hnd.2

private theorem m5_ofTable_agree_of_mem_both {tbl1 tbl2 : List SpecEntry} {e : SpecEntry}
    (he1 : e ∈ tbl1) (hnd1 : (tbl1.map SpecEntry.name).Nodup)
    (he2 : e ∈ tbl2) (hnd2 : (tbl2.map SpecEntry.name).Nodup)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    Env.ofTable tbl1 e.name as bs xs m Q X ↔ Env.ofTable tbl2 e.name as bs xs m Q X := by
  by_cases hs : e.as = as ∧ e.rs = bs
  · rcases hs with ⟨rfl, rfl⟩
    exact (m5_ofTable_iff_of_mem he1 hnd1).trans (m5_ofTable_iff_of_mem he2 hnd2).symm
  · exact iff_of_false (m5_ofTable_off_sig he1 hnd1 hs xs m Q X)
      (m5_ofTable_off_sig he2 hnd2 hs xs m Q X)

private theorem mkM5Env_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m5SpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X :=
      by intro _ _ _ _ h; dsimp only [SpecEntry.eff]; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM5Env mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m5SpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem mkM5Env_row_elim {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m5SpecTable mainSpec)[i]? = some e := by rfl)
    (hno : e.noExit = true := by rfl) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} (hs : mkM5Env mainSpec e.name e.as e.rs xs m Q X) :
    e.spec xs m Q (fun _ _ _ _ => False) := by
  have heff := (m5_ofTable_iff_of_mem (List.mem_of_getElem? hi)
    (m5SpecTable_nodup mainSpec)).mp hs
  simpa only [SpecEntry.eff, hno, ↓reduceIte] using heff

theorem mkM5Env_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM5Env mainSpec f as bs xs m Q X → mkM5Env mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m5SpecTable_noExit mainSpec)

theorem m5Env_noExit :
    ∀ f as bs xs m Q X X', m5Env f as bs xs m Q X → m5Env f as bs xs m Q X' :=
  mkM5Env_noExit fullSolveBytesSpec

theorem m5UnsatEnv_noExit :
    ∀ f as bs xs m Q X X', m5UnsatEnv f as bs xs m Q X → m5UnsatEnv f as bs xs m Q X' :=
  mkM5Env_noExit fullUnsatWitnessSpec

/-! ## 2. Headline Source Soundness & Concrete `Mem 64` UNSAT Non-Vacuity -/

private theorem wp_noExit_lift {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : wp Γ Q (fun _ _ _ _ => False) e m) :
    wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

/-- Headline source-level UNSAT-only soundness of Unified M5 `kissat_solve_bytes` under
canonical `270`-function `m5Env` (`0` SAT/model proofs). -/
theorem m5_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5Env kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m5_solve_bytes_fwd_wp m5Env
    (mkM5Env_row_at (mainSpec := fullSolveBytesSpec) 268
      ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], fullSolveBytesSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under `270`-function `m5UnsatEnv`:
`kissat_solve_bytes_m5` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
with `4096`-byte workspace and `fuel = 16`. -/
theorem m5_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5UnsatEnv FullM5Orch.kissat_solve_bytes_m5_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  FullM5Orch.kissat_solve_bytes_m5_core_wp m5UnsatEnv
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 44
      ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 48
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 263
      ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩)
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 266
      ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩)
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 104
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) on exported `kissat_solve_bytes`
entry point under `270`-function `m5UnsatEnv`. -/
theorem m5_fwd_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5UnsatEnv kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_solve_bytes_fwd_wp m5UnsatEnv
    (mkM5Env_row_at (mainSpec := fullUnsatWitnessSpec) 268
      ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64],
        fullUnsatWitnessSpec, true⟩)
    _ _ _ _
    ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
      fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩

/-! ## 3. Unchanged M4 (`153`) & `FullM4Sweep` (`22`) Transport Helpers -/

section TransportHelpers

private def m5M4SegPairs : List (Nat × Nat × Nat) :=
  [ (0, 0, 14), (15, 15, 11), (29, 27, 2), (34, 31, 7), (43, 40, 1), (46, 42, 5)
  , (52, 47, 1), (56, 50, 7), (63, 58, 4), (69, 66, 1), (71, 68, 1), (77, 73, 9)
  , (91, 87, 2), (94, 90, 4), (101, 97, 5), (106, 103, 1), (108, 104, 6)
  , (116, 112, 4), (123, 119, 2), (139, 124, 3), (146, 131, 1), (148, 133, 15)
  , (165, 150, 1), (170, 155, 3), (201, 165, 1), (203, 167, 3)
  , (212, 171, 6), (219, 178, 8), (228, 187, 17), (245, 204, 2)
  , (252, 216, 2), (255, 219, 2), (260, 224, 2) ]

private theorem m5M4Segs_match (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ p ∈ m5M4SegPairs,
      ((m5SpecTable mainSpec).drop p.1).take p.2.2 =
        ((FullM4.m4SpecTable mainSpec).drop p.2.1).take p.2.2 := by
  intro p hp
  simp only [m5M4SegPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    t_kernel_rfl

private theorem m5M4Segs_fns :
    ∀ p ∈ m5M4SegPairs,
      (m5Fns.drop p.1).take p.2.2 = (FullM4.m4Fns.drop p.2.1).take p.2.2 := by
  intro p hp
  simp only [m5M4SegPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    t_kernel_rfl

private def m5M4SpecPairs : List (Nat × Nat × Nat) :=
  [ (0, 0, 26), (28, 26, 4), (33, 30, 8), (43, 40, 1), (45, 41, 6), (51, 57, 1)
  , (52, 47, 1), (54, 48, 9), (63, 58, 4), (69, 66, 4), (74, 70, 1), (76, 72, 22)
  , (99, 95, 7), (106, 103, 1), (107, 102, 1), (108, 104, 12), (123, 119, 2), (139, 124, 27)
  , (170, 155, 3), (177, 160, 1), (201, 165, 5), (211, 170, 36), (252, 216, 2)
  , (255, 219, 2), (260, 224, 2), (269, 230, 1) ]

private theorem m5M4SpecSegs_match (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ p ∈ m5M4SpecPairs,
      ((m5SpecTable mainSpec).drop p.1).take p.2.2 =
        ((FullM4.m4SpecTable mainSpec).drop p.2.1).take p.2.2 := by
  intro p hp
  simp only [m5M4SpecPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    t_kernel_rfl

private def m5M4AllowedEntries (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    List SpecEntry :=
  m5M4SpecPairs.flatMap fun (a, _, k) => ((m5SpecTable mainSpec).drop a).take k

private def m5M4AllowedSigs : List SigEntry :=
  m5M4SpecPairs.flatMap fun (a, _, k) => ((m5Fns.drop a).take k).map Fn.sig

private theorem m5M4AllowedSigs_eq (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    m5M4AllowedSigs =
      (m5M4AllowedEntries mainSpec).map (fun e => (e.name, e.as, e.rs)) := by
  unfold m5M4AllowedSigs m5M4AllowedEntries
  simp only [List.map_flatMap]
  congr 1; funext ⟨a, _, k⟩
  have h1 := congrArg (fun l => (l.drop a).take k) (m5SpecTable_sigs mainSpec)
  simp only [← List.map_drop, ← List.map_take] at h1
  exact h1.symm

private theorem mem_m5M4Allowed_both (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {e : SpecEntry} (he : e ∈ m5M4AllowedEntries mainSpec) :
    e ∈ m5SpecTable mainSpec ∧ e ∈ FullM4.m4SpecTable mainSpec := by
  simp only [m5M4AllowedEntries, List.mem_flatMap] at he
  obtain ⟨⟨a, b, k⟩, hp, hmem⟩ := he
  refine ⟨List.mem_of_mem_drop (List.mem_of_mem_take hmem), ?_⟩
  rw [m5M4SpecSegs_match mainSpec _ hp] at hmem
  exact List.mem_of_mem_drop (List.mem_of_mem_take hmem)

private theorem m5Env_agree_m4_entry (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {e : SpecEntry} (he : e ∈ m5M4AllowedEntries mainSpec)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    mkM5Env mainSpec e.name as bs xs m Q X ↔ FullM4.mkM4Env mainSpec e.name as bs xs m Q X := by
  obtain ⟨hm5, hm4⟩ := mem_m5M4Allowed_both mainSpec he
  exact m5_ofTable_agree_of_mem_both hm5 (m5SpecTable_nodup mainSpec) hm4
    (FullM4.m4SpecTable_nodup mainSpec) xs m Q X

private def m5M4UnchangedFns : List Fn :=
  m5M4SegPairs.flatMap fun (a, _, k) => (m5Fns.drop a).take k

private theorem m5M4Unchanged_callsOk :
    m5M4UnchangedFns.all (fun fn => fn.checkCallsOk m5M4AllowedSigs []) = true := by
  t_kernel_rfl

private theorem m5M4Unchanged_mem_m4 {fn : Fn} (hfn : fn ∈ m5M4UnchangedFns) :
    fn ∈ FullM4.m4Fns := by
  simp only [m5M4UnchangedFns, List.mem_flatMap] at hfn
  obtain ⟨p, hp, hmem⟩ := hfn
  rw [m5M4Segs_fns p hp] at hmem
  exact List.mem_of_mem_drop (List.mem_of_mem_take hmem)

private theorem m5M4_fn_agree_env (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {fn : Fn} (hfn : fn ∈ m5M4UnchangedFns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost} :
    mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X ↔
      FullM4.mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X := by
  simp only [m5M4UnchangedFns, List.mem_flatMap] at hfn
  obtain ⟨p, hp, hmem⟩ := hfn
  have hsig := congrArg (fun l => (l.drop p.1).take p.2.2) (m5SpecTable_sigs mainSpec)
  simp only [← List.map_drop, ← List.map_take] at hsig
  have hm_sig : (fn.name, fn.as, fn.rs) ∈
      (((m5SpecTable mainSpec).drop p.1).take p.2.2).map (fun e => (e.name, e.as, e.rs)) := by
    rw [hsig, List.mem_map]; exact ⟨fn, hmem, rfl⟩
  rw [List.mem_map] at hm_sig
  obtain ⟨e, he_seg, he_eq⟩ := hm_sig
  have hm5_e : e ∈ m5SpecTable mainSpec := List.mem_of_mem_drop (List.mem_of_mem_take he_seg)
  have hm4_e : e ∈ FullM4.m4SpecTable mainSpec := by
    have hsm := m5M4Segs_match mainSpec p hp
    rw [hsm] at he_seg
    exact List.mem_of_mem_drop (List.mem_of_mem_take he_seg)
  rcases e with ⟨ename, eas, ers, espec, eno⟩
  obtain ⟨rfl, rfl, rfl⟩ := he_eq
  exact m5_ofTable_agree_of_mem_both hm5_e (m5SpecTable_nodup mainSpec)
    hm4_e (FullM4.m4SpecTable_nodup mainSpec) xs m Q X

private theorem m5M4Unchanged_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ m5M4UnchangedFns, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  intro fn hfn xs m Q X hs
  have hm4 := m5M4Unchanged_mem_m4 hfn
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hm4
  have ⟨hwf, _, hwp0⟩ := hM4.fnsOk pre fn post hsplit
  have hcalls : fn.callsOk m5M4AllowedSigs [] :=
    Fn.callsOk_of_checkCallsOk (List.all_eq_true.mp m5M4Unchanged_callsOk fn hfn)
  have hs0 : FullM4.mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X :=
    (m5M4_fn_agree_env mainSpec hfn).mp hs
  refine wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    hcalls (fun g as bs hmem_g ys m' P E hG => ?_) m (hwp0 xs m Q X hs0)
  rw [m5M4AllowedSigs_eq mainSpec, List.mem_map] at hmem_g
  obtain ⟨e, he, hsig⟩ := hmem_g
  rcases e with ⟨ename, eas, ers, espec, eno⟩
  obtain ⟨rfl, rfl, rfl⟩ := hsig
  exact (m5Env_agree_m4_entry mainSpec he ys m' P E).mpr hG

private theorem m5_drop_take_m4_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) (a k : Nat)
    (hp : m5M4SegPairs.any (fun p => p.1 == a && p.2.2 == k) = true := by decide) :
    ∀ fn ∈ (m5Fns.drop a).take k, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  obtain ⟨⟨a', b, k'⟩, hmem, hpred⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨rfl, rfl⟩ := hpred
  exact fun fn hfn xs m Q X hs =>
    m5M4Unchanged_wp mainSpec hM4 fn
      (List.mem_flatMap.mpr ⟨(a', b, k'), hmem, hfn⟩) xs m Q X hs

private def m5SweepAllowedSigs : List SigEntry :=
  (FullM4Sweep.fullM4Sweep_fns.take 22).map Fn.sig ++
  [ ⟨"full_rng_next", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩ ]

private theorem m5Sweep22_callsOk :
    (FullM4Sweep.fullM4Sweep_fns.take 22).all
      (fun fn => fn.checkCallsOk m5SweepAllowedSigs []) = true := by
  t_kernel_rfl

private theorem m5Sweep_entries_match (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ FullM4Sweep.fullM4SweepSpecTable.take 22 ++
        (FullM4Sweep.fullM4SweepSpecTable.drop 24).filter
          (fun x => x.name != "full_enter_dense"),
      e ∈ m5SpecTable mainSpec := by
  intro e he
  have h1 : FullM4Sweep.fullM4SweepSpecTable.take 22 =
      ((m5SpecTable mainSpec).drop 178).take 22 := by
    t_kernel_rfl
  have h2 : (FullM4Sweep.fullM4SweepSpecTable.drop 24).filter
      (fun x => x.name != "full_enter_dense") =
      [ ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
      , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
      , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
      , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
      , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
      , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩ ] := by
    t_kernel_rfl
  rcases List.mem_append.mp he with hl | hr
  · rw [h1] at hl; exact List.mem_of_mem_drop (List.mem_of_mem_take hl)
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.mem_of_getElem? (show (m5SpecTable mainSpec)[10]? = some _ from rfl)
    · exact List.mem_of_getElem? (show (m5SpecTable mainSpec)[33]? = some _ from rfl)
    · exact List.mem_of_getElem? (show (m5SpecTable mainSpec)[56]? = some _ from rfl)
    · exact List.mem_of_getElem? (show (m5SpecTable mainSpec)[110]? = some _ from rfl)
    · exact List.mem_of_getElem? (show (m5SpecTable mainSpec)[107]? = some _ from rfl)
    · exact List.mem_of_getElem? (show (m5SpecTable mainSpec)[146]? = some _ from rfl)

private theorem m5Sweep22_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ FullM4Sweep.fullM4Sweep_fns.take 22, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  intro fn hfn xs m Q X hs
  have hsw_fn : fn ∈ FullM4Sweep.fullM4Sweep_fns := List.mem_of_mem_take hfn
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hsw_fn
  have ⟨hwf, _, hwp0⟩ := FullM4Sweep.fullM4SweepEnv_moduleOk.fnsOk pre fn post hsplit
  have hcalls : fn.callsOk m5SweepAllowedSigs [] :=
    Fn.callsOk_of_checkCallsOk (List.all_eq_true.mp m5Sweep22_callsOk fn hfn)
  let swAllowed := FullM4Sweep.fullM4SweepSpecTable.take 22 ++
    (FullM4Sweep.fullM4SweepSpecTable.drop 24).filter (fun x => x.name != "full_enter_dense")
  have hag : ∀ e ∈ swAllowed, ∀ {as bs} ys m' P E,
      mkM5Env mainSpec e.name as bs ys m' P E ↔
        FullM4Sweep.fullM4SweepEnv e.name as bs ys m' P E := by
    intro e he as bs ys m' P E
    have he_sw : e ∈ FullM4Sweep.fullM4SweepSpecTable := by
      rcases List.mem_append.mp he with hl | hr
      · exact List.mem_of_mem_take hl
      · exact List.mem_of_mem_drop (List.mem_filter.mp hr).1
    exact m5_ofTable_agree_of_mem_both (m5Sweep_entries_match mainSpec e he)
      (m5SpecTable_nodup mainSpec) he_sw FullM4Sweep.fullM4SweepSpecTable_nodup ys m' P E
  have hs0 : FullM4Sweep.fullM4SweepEnv fn.name fn.as fn.rs xs m Q X := by
    have hsig : ((FullM4Sweep.fullM4SweepSpecTable.take 22).map
        (fun e => (e.name, e.as, e.rs))) =
        (FullM4Sweep.fullM4Sweep_fns.take 22).map (fun f => (f.name, f.as, f.rs)) := by
      have h := congrArg (List.take 22) FullM4Sweep.fullM4SweepSpecTable_sigs
      simpa only [← List.map_take, List.take_take, show min 22 24 = 22 from rfl] using h
    have hm_e : (fn.name, fn.as, fn.rs) ∈
        (FullM4Sweep.fullM4SweepSpecTable.take 22).map (fun e => (e.name, e.as, e.rs)) := by
      rw [hsig, List.mem_map]; exact ⟨fn, hfn, rfl⟩
    rw [List.mem_map] at hm_e
    obtain ⟨e, he, he_eq⟩ := hm_e
    rcases e with ⟨ename, eas, ers, espec, eno⟩
    obtain ⟨rfl, rfl, rfl⟩ := he_eq
    exact (hag _ (List.mem_append_left _ he) xs m Q X).mp hs
  refine wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    hcalls (fun g as bs hmem_g ys m' P E hG => ?_) m (hwp0 xs m Q X hs0)
  have hsw_sig : m5SweepAllowedSigs = swAllowed.map (fun e => (e.name, e.as, e.rs)) := by
    simp only [m5SweepAllowedSigs, swAllowed, FullM4Sweep.fullM4SweepSpecTable,
      FullM4Sweep.fullM4Sweep_fns]; rfl
  rw [hsw_sig, List.mem_map] at hmem_g
  obtain ⟨e, he, he_eq⟩ := hmem_g
  rcases e with ⟨ename, eas, ers, espec, eno⟩
  obtain ⟨rfl, rfl, rfl⟩ := he_eq
  exact (hag _ he ys m' P E).mpr hG

private theorem m5_drop178_take22_eq :
    (m5Fns.drop 178).take 22 = FullM4Sweep.fullM4Sweep_fns.take 22 := by
  simp only [m5Fns, m5FnsPrefix, m5FnsSuffix, m5BvaFns, FullM4Sweep.fullM4Sweep_fns]; rfl

private theorem m5_sweep22_seg_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 178).take 22, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  rw [m5_drop178_take22_eq]
  exact m5Sweep22_wp mainSpec

end TransportHelpers

/-! ## 4. Unified `270/270` `m5Fns` Dispatch (`m5Fns_all_wp`) & `ModuleOk` -/

section AllFnsWp

private theorem forall_mem_drop_split {a k : Nat} {L : List Fn} {P : Fn → Prop}
    (ht : ∀ fn ∈ (L.drop a).take k, P fn) (hd : ∀ fn ∈ L.drop (a + k), P fn) :
    ∀ fn ∈ L.drop a, P fn := by
  have h : (L.drop a).take k ++ L.drop (a + k) = L.drop a := by
    rw [← List.drop_drop, List.take_append_drop]
  rw [← h]
  exact fun x hx => (List.mem_append.mp hx).elim (ht x) (hd x)

private theorem forall_mem_app {L1 L2 : List Fn} {P : Fn → Prop}
    (h1 : ∀ fn ∈ L1, P fn) (h2 : ∀ fn ∈ L2, P fn) : ∀ fn ∈ L1 ++ L2, P fn :=
  fun fn h => (List.mem_append.mp h).elim (h1 fn) (h2 fn)

private theorem m5_block14_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 14).take 1, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  have hseg : (m5Fns.drop 14).take 1 = [FullM4InprocHot.m4WstackDefragFn] := by t_kernel_rfl
  rw [hseg]
  intro fn hfn xs m Q X hs
  rcases List.mem_singleton.mp hfn with rfl
  exact wp_noExit_lift (FullM4InprocHot.full_wstack_defrag_m4_wp Γ xs m Q _
    (mkM5Env_row_elim 14 ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
      rfl rfl hs))

private theorem m5_block26to28_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 26).take 3, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h26 := mkM5Env_row_at (mainSpec := mainSpec) 26
    ⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩
  have hseg : (m5Fns.drop 26).take 3 =
      [ ⟨"full_log10_q16", [i64], [i64], FullM5Sched.full_log10_q16_body⟩
      , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullM5Sched.full_scale_delta_m5_body⟩
      , ⟨"full_ema_update", [i64, i64], [], FullM5Sched.full_ema_update_body⟩ ] := by
    t_kernel_rfl
  rw [hseg]
  intro fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl <;> intro xs m Q X hs
  · exact wp_noExit_lift (FullM5Sched.full_log10_q16_wp Γ xs m Q _
      (mkM5Env_row_elim 26 ⟨"full_log10_q16", [i64], [i64],
        FullM5Sched.m5Log10Q16Spec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5Sched.full_scale_delta_m5_wp Γ h26 xs m Q _
      (mkM5Env_row_elim 27 ⟨"full_scale_delta_m5", [i64, i64], [i64],
        FullFastSched.schedScaleDeltaSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5Sched.full_ema_update_wp Γ xs m Q _
      (mkM5Env_row_elim 28 ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
        rfl rfl hs))

private theorem m5_block31to33_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 31).take 3, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h18 := mkM5Env_row_at (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  let h31 := mkM5Env_row_at (mainSpec := mainSpec) 31
    ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  let h32 := mkM5Env_row_at (mainSpec := mainSpec) 32
    ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩
  have hseg : (m5Fns.drop 31).take 3 =
      [ FullM5HeurCore.m5SaveTargetBestFn, FullM5HeurCore.m5BacktrackRawFn
      , FullM5HeurCore.m5BacktrackFn ] := by
    t_kernel_rfl
  rw [hseg]
  intro fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl <;> intro xs m Q X hs
  · exact wp_noExit_lift (FullM5HeurCore.full_save_target_best_m5_wp Γ xs m Q _
      (mkM5Env_row_elim 31 ⟨"full_save_target_best", [i64], [],
        fullSaveTargetBestSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5HeurCore.full_backtrack_raw_m5_wp Γ h31 h18 xs m Q _
      (mkM5Env_row_elim 32 ⟨"full_backtrack_raw_m5", [i64, i64], [],
        FullM5HeurCore.fullBacktrackRawSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5HeurCore.full_backtrack_m5_wp Γ h32 h31 xs m Q _
      (mkM5Env_row_elim 33 ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
        rfl rfl hs))

private theorem m5_block41to42_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 41).take 2, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  have hseg : (m5Fns.drop 41).take 2 =
      [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.full_calc_ext_cap_m5_body⟩
      , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.full_calc_scr_cap_m5_body⟩ ] := by
    t_kernel_rfl
  rw [hseg]
  intro fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl <;> intro xs m Q X hs
  · exact wp_noExit_lift (FullM5Orch.full_calc_ext_cap_m5_wp Γ xs m Q _
      (mkM5Env_row_elim 41 ⟨"full_calc_ext_cap_m5", [i64], [i64],
        FullM5Orch.fullCalcExtCapM5Spec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5Orch.full_calc_scr_cap_m5_wp Γ xs m Q _
      (mkM5Env_row_elim 42 ⟨"full_calc_scr_cap_m5", [i64], [i64],
        FullM5Orch.fullCalcScrCapM5Spec, true⟩ rfl rfl hs))

private theorem m5_block44to45_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 44).take 2, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h5 := mkM5Env_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h35 := mkM5Env_row_at (mainSpec := mainSpec) 35
    ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  let h36 := mkM5Env_row_at (mainSpec := mainSpec) 36
    ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  let h37 := mkM5Env_row_at (mainSpec := mainSpec) 37
    ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  let h39 := mkM5Env_row_at (mainSpec := mainSpec) 39
    ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.fullFastInitHdrSpec, true⟩
  let h40 := mkM5Env_row_at (mainSpec := mainSpec) 40
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  let h41 := mkM5Env_row_at (mainSpec := mainSpec) 41
    ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
    (hno := FullM5Orch.fullCalcExtCapM5Spec_noExit)
  let h42 := mkM5Env_row_at (mainSpec := mainSpec) 42
    ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩
    (hno := FullM5Orch.fullCalcScrCapM5Spec_noExit)
  let h43 := mkM5Env_row_at (mainSpec := mainSpec) 43
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  let h44 := mkM5Env_row_at (mainSpec := mainSpec) 44
    ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  have hseg : (m5Fns.drop 44).take 2 =
      [ ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
          FullM5Orch.full_init_state_m5_body⟩
      , m5InitStateFwdFn ] := by
    t_kernel_rfl
  rw [hseg]
  intro fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl <;> intro xs m Q X hs
  · exact wp_noExit_lift (m5_init_state_m5_wp Γ h5 h37 h40 h41 h42 h43 h39 h35 h36 xs m Q _
      (mkM5Env_row_elim 44 ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
        fullInitStateSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (m5_init_state_fwd_wp Γ h44 xs m Q _
      (mkM5Env_row_elim 45 ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
        fullInitStateSpec, true⟩ rfl rfl hs))

private theorem m5_block51_53to55_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 51).take 5, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h14 := mkM5Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h51 := mkM5Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h52 := mkM5Env_row_at (mainSpec := mainSpec) 52
    ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  let h53 := mkM5Env_row_at (mainSpec := mainSpec) 53
    ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  have hseg : (m5Fns.drop 51).take 5 =
      [⟨"full_unwatch_large", [i64, i32, i32], [], FullM5Otfs.full_unwatch_large_body⟩] ++
      (((m5Fns.drop 52).take 1) ++
      [ ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], FullM5Otfs.full_prop_lit_chrono_body⟩
      , ⟨"full_prop_lit", [i64, i32, i64], [.bool], FullM5Otfs.full_prop_lit_body⟩
      , ⟨"full_propagate_ignore", [i64, i64], [i64], FullM5Otfs.full_propagate_ignore_body⟩ ]) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn xs m Q X hs => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 52 1) fun fn hfn => ?_)
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5Otfs.full_unwatch_large_wp Γ xs m Q _
      (mkM5Env_row_elim 51 ⟨"full_unwatch_large", [i64, i32, i32], [],
        fullUnwatchLargeSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Otfs.full_prop_lit_chrono_wp Γ h14 h51 h52 h15 xs m Q _
        (mkM5Env_row_elim 53 ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool],
          fullPropLitSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Otfs.full_prop_lit_wp Γ h53 h52 xs m Q _
        (mkM5Env_row_elim 54 ⟨"full_prop_lit", [i64, i32, i64], [.bool],
          fullPropLitSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Otfs.full_propagate_ignore_wp Γ h53 h52 xs m Q _
        (mkM5Env_row_elim 55 ⟨"full_propagate_ignore", [i64, i64], [i64],
          fullPropagateIgnoreSpec, true⟩ rfl rfl hs))

private theorem m5_block67to76_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 67).take 10, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h8 := mkM5Env_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  let h9 := mkM5Env_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h11 := mkM5Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkM5Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h21 := mkM5Env_row_at (mainSpec := mainSpec) 21
    ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  let h22 := mkM5Env_row_at (mainSpec := mainSpec) 22
    ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  let h24 := mkM5Env_row_at (mainSpec := mainSpec) 24
    ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  let h33 := mkM5Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h51 := mkM5Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h56 := mkM5Env_row_at (mainSpec := mainSpec) 56
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h57 := mkM5Env_row_at (mainSpec := mainSpec) 57
    ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  let h58 := mkM5Env_row_at (mainSpec := mainSpec) 58
    ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  let h61 := mkM5Env_row_at (mainSpec := mainSpec) 61
    ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  let h66 := mkM5Env_row_at (mainSpec := mainSpec) 66
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h67 := mkM5Env_row_at (mainSpec := mainSpec) 67
    ⟨"full_reduce_m5", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h69 := mkM5Env_row_at (mainSpec := mainSpec) 69
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  let h71 := mkM5Env_row_at (mainSpec := mainSpec) 71
    ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  let h72 := mkM5Env_row_at (mainSpec := mainSpec) 72
    ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  have hseg : (m5Fns.drop 67).take 10 =
      [ ⟨"full_reduce_m5", [i64, .bool], [i64], FullM5Orch.full_reduce_m5_body⟩
      , m5ReduceFwdFn ] ++
      (((m5Fns.drop 69).take 1) ++
      ([FullM5HeurCore.m5AnalyzeRsnFn] ++
      (((m5Fns.drop 71).take 1) ++
      [ FullM5HeurCore.m5BumpAnalyzedFn, FullM5HeurCore.m5RestoreBumpAnaFn
      , ⟨"full_otfs_large", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_large_body⟩
      , ⟨"full_otfs_bin_m5", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_bin_m5_body⟩
      , FullM5HeurCore.m5OtfsSubsumeFn ]))) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 69 1) (forall_mem_app (fun fn hfn xs m Q X hs => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 71 1) fun fn hfn => ?_)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Orch.full_reduce_m5_wp Γ h8 h9 h11 h57 h58 h61 h33 h56 h66
        xs m Q _ (mkM5Env_row_elim 67 ⟨"full_reduce_m5", [i64, .bool], [i64],
          fullReduceSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (m5_reduce_fwd_wp Γ h67 xs m Q _
        (mkM5Env_row_elim 68 ⟨"full_reduce", [i64, .bool], [i64],
          fullReduceSpec, true⟩ rfl rfl hs))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5HeurCore.full_analyze_rsn_m5_wp Γ h69 xs m Q _
      (mkM5Env_row_elim 70 ⟨"full_analyze_rsn", [i64, i32, i32], [.bool],
        fullAnalyzeRsnSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5HeurCore.full_bump_analyzed_m5_wp Γ h21 h24 h22 xs m Q _
        (mkM5Env_row_elim 72 ⟨"full_bump_analyzed", [i64], [],
          fullBumpAnalyzedSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5HeurCore.full_restore_bump_ana_m5_wp Γ h72 h71 xs m Q _
        (mkM5Env_row_elim 73 ⟨"full_restore_bump_ana_m5", [i64], [],
          FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Otfs.full_otfs_large_wp Γ h14 h51 h15 xs m Q _
        (mkM5Env_row_elim 74 ⟨"full_otfs_large", [i64, i32, i32], [.bool],
          fullOtfsLargeSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Otfs.full_otfs_bin_m5_wp Γ h11 h14 h51 h15 xs m Q _
        (mkM5Env_row_elim 75 ⟨"full_otfs_bin_m5", [i64, i32, i32], [.bool],
          fullOtfsBinSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5HeurCore.full_otfs_subsume_m5_wp Γ xs m Q _
        (mkM5Env_row_elim 76 ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [],
          fullOtfsSubsumeSpec, true⟩ rfl rfl hs))

private theorem m5_block86to93_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 86).take 8, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h14 := mkM5Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h25 := mkM5Env_row_at (mainSpec := mainSpec) 25
    ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  let h28 := mkM5Env_row_at (mainSpec := mainSpec) 28
    ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  let h29 := mkM5Env_row_at (mainSpec := mainSpec) 29
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h30 := mkM5Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h32 := mkM5Env_row_at (mainSpec := mainSpec) 32
    ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩
  let h33 := mkM5Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h34 := mkM5Env_row_at (mainSpec := mainSpec) 34
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h51 := mkM5Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h56 := mkM5Env_row_at (mainSpec := mainSpec) 56
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h68 := mkM5Env_row_at (mainSpec := mainSpec) 68
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h69 := mkM5Env_row_at (mainSpec := mainSpec) 69
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  let h70 := mkM5Env_row_at (mainSpec := mainSpec) 70
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  let h71 := mkM5Env_row_at (mainSpec := mainSpec) 71
    ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  let h73 := mkM5Env_row_at (mainSpec := mainSpec) 73
    ⟨"full_restore_bump_ana_m5", [i64], [], FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩
  let h74 := mkM5Env_row_at (mainSpec := mainSpec) 74
    ⟨"full_otfs_large", [i64, i32, i32], [.bool], fullOtfsLargeSpec, true⟩
  let h75 := mkM5Env_row_at (mainSpec := mainSpec) 75
    ⟨"full_otfs_bin_m5", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
  let h76 := mkM5Env_row_at (mainSpec := mainSpec) 76
    ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  let h84 := mkM5Env_row_at (mainSpec := mainSpec) 84
    ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  let h85 := mkM5Env_row_at (mainSpec := mainSpec) 85
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  let h86 := mkM5Env_row_at (mainSpec := mainSpec) 86
    ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  let h87 := mkM5Env_row_at (mainSpec := mainSpec) 87
    ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  let h88 := mkM5Env_row_at (mainSpec := mainSpec) 88
    ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  let h89 := mkM5Env_row_at (mainSpec := mainSpec) 89
    ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  let h91 := mkM5Env_row_at (mainSpec := mainSpec) 91
    ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  have hseg : (m5Fns.drop 86).take 8 =
      [ m5OneLitConflFn, m5Deduce1uipFn, FullM5HeurCore.m5EagerSubsumeFn
      , FullM5HeurCore.m5LearnClauseFn, FullM5HeurCore.m5AnalyzeFn ] ++
      (((m5Fns.drop 91).take 2) ++
      [FullM5HeurCore.m5WarmupFn]) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 91 2) fun fn hfn xs m Q X hs => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Otfs.full_one_lit_confl_m5_wp Γ h14 h85 h33 h29 h51 h15
        xs m Q _ (mkM5Env_row_elim 86 ⟨"full_one_lit_confl", [i64], [i64],
          fullOneLitConflSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Otfs.full_deduce_1uip_m5_wp Γ h69 h70 h71 h74 h75 h76
        xs m Q _ (mkM5Env_row_elim 87 ⟨"full_deduce_1uip", [i64], [i64],
          fullDeduce1uipSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5HeurCore.full_eager_subsume_m5_wp Γ xs m Q _
        (mkM5Env_row_elim 88 ⟨"full_eager_subsume", [i64, i64], [],
          fullEagerSubsumeSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5HeurCore.full_learn_clause_m5_wp Γ h33 h29 h85 h14 h68 h34 h88
        xs m Q _ (mkM5Env_row_elim 89 ⟨"full_learn_clause", [i64, i64], [i64],
          fullLearnClauseSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5HeurCore.full_analyze_m5_wp Γ h86 h87 h73 h84 h25 h28 h89
        xs m Q _ (mkM5Env_row_elim 90 ⟨"full_analyze", [i64], [i64],
          fullAnalyzeSpec, true⟩ rfl rfl hs))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5HeurCore.full_warmup_m5_wp Γ h91 h30 h56 h32 xs m Q _
      (mkM5Env_row_elim 93 ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩ rfl rfl hs))

private theorem m5_block98to115_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 98).take 18, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h9 := mkM5Env_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h17 := mkM5Env_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h26 := mkM5Env_row_at (mainSpec := mainSpec) 26
    ⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩
  let h29 := mkM5Env_row_at (mainSpec := mainSpec) 29
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h33 := mkM5Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h49 := mkM5Env_row_at (mainSpec := mainSpec) 49
    ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  let h97 := mkM5Env_row_at (mainSpec := mainSpec) 97
    ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  let h105 := mkM5Env_row_at (mainSpec := mainSpec) 105
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let h106 := mkM5Env_row_at (mainSpec := mainSpec) 106
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let h114 := mkM5Env_row_at (mainSpec := mainSpec) 114
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], fullHbrDomSpec, true⟩
  have hseg : (m5Fns.drop 98).take 18 =
      [ ⟨"full_rephase", [i64], [], FullM5Sched.full_rephase_body⟩
      , ⟨"full_switch_mode", [i64], [], FullM5Sched.full_switch_mode_body⟩
      , ⟨"full_restart_due", [i64], [i64], FullM5Sched.full_restart_due_body⟩ ] ++
      (((m5Fns.drop 101).take 5) ++ (((m5Fns.drop 106).take 1) ++
      ([m5AddBinFn] ++ (((m5Fns.drop 108).take 6) ++
      [m5HbrDomFn, m5ProbePropLitFn])))) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 101 5) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 106 1) (forall_mem_app (fun fn hfn xs m Q X hs => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 108 6) fun fn hfn => ?_))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Sched.full_rephase_wp Γ h33 h97 h26 xs m Q _
        (mkM5Env_row_elim 98 ⟨"full_rephase", [i64], [],
          FullM5Sched.m5RephaseSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Sched.full_switch_mode_wp Γ h17 h26 h9 xs m Q _
        (mkM5Env_row_elim 99 ⟨"full_switch_mode", [i64], [],
          fullSwitchModeSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Sched.full_restart_due_wp Γ h9 xs m Q _
        (mkM5Env_row_elim 100 ⟨"full_restart_due", [i64], [i64],
          fullRestartDueSpec, true⟩ rfl rfl hs))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (m5_add_bin_wp Γ h105 h29 h15 h106 xs m Q _
      (mkM5Env_row_elim 107 ⟨"full_add_bin", [i64, i32, i32], [i64],
        fullAddBinSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Hbr.full_hbr_dom_m5_wp Γ xs m Q _
        (mkM5Env_row_elim 114 ⟨"full_hbr_dom", [i64, i32, i32], [i32],
          fullHbrDomSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5ProbeProp.full_probe_prop_lit_m5_wp Γ h49 h15 h114 h29
        xs m Q _ (mkM5Env_row_elim 115 ⟨"full_probe_prop_lit", [i64, i32], [.bool],
          fullProbePropLitSpec, true⟩ rfl rfl hs))

private theorem m5_block120to138_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 120).take 19, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h11 := mkM5Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkM5Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h30 := mkM5Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h33 := mkM5Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h51 := mkM5Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h55 := mkM5Env_row_at (mainSpec := mainSpec) 55
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  let h56 := mkM5Env_row_at (mainSpec := mainSpec) 56
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h106 := mkM5Env_row_at (mainSpec := mainSpec) 106
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let h107 := mkM5Env_row_at (mainSpec := mainSpec) 107
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h110 := mkM5Env_row_at (mainSpec := mainSpec) 110
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h120 := mkM5Env_row_at (mainSpec := mainSpec) 120
    ⟨"full_trans_lit_m5", [i64, i32], [.bool], fullTransLitSpec, true⟩
  let h122 := mkM5Env_row_at (mainSpec := mainSpec) 122
    ⟨"full_viv_simplify", [i64, i32], [i64], FullM4VivBce.fullVivSimplifyM4Spec, true⟩
  let h124 := mkM5Env_row_at (mainSpec := mainSpec) 124
    ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  let h125 := mkM5Env_row_at (mainSpec := mainSpec) 125
    ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64],
      FullM4VivBce.fullVivCommitM4Spec, true⟩
  let h126 := mkM5Env_row_at (mainSpec := mainSpec) 126
    ⟨"full_viv_sort_noccs_m4", [i64, i32], [], FullM4VivBce.fullVivSortNoccsM4Spec, true⟩
  let h127 := mkM5Env_row_at (mainSpec := mainSpec) 127
    ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool], FullM4VivBce.fullVivHasL0M4Spec, true⟩
  let h128 := mkM5Env_row_at (mainSpec := mainSpec) 128
    ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64], FullM4VivBce.fullVivL0SimpM4Spec, true⟩
  let h129 := mkM5Env_row_at (mainSpec := mainSpec) 129
    ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [], FullM4VivBce.fullVivReusePrefixM4Spec, true⟩
  let h130 := mkM5Env_row_at (mainSpec := mainSpec) 130
    ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64],
      FullM4VivBce.fullVivFinishM4Spec, true⟩
  let h131 := mkM5Env_row_at (mainSpec := mainSpec) 131
    ⟨"full_viv_clause_m4", [i64, i32], [i64], FullM4VivBce.fullVivClauseM4Spec, true⟩
  let h132 := mkM5Env_row_at (mainSpec := mainSpec) 132
    ⟨"full_viv_sort_sched_m4", [i64, i64], [], FullM4VivBce.fullVivSortSchedM4Spec, true⟩
  let h133 := mkM5Env_row_at (mainSpec := mainSpec) 133
    ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool], FullM4VivBce.fullVivTierMatchM4Spec, true⟩
  let h134 := mkM5Env_row_at (mainSpec := mainSpec) 134
    ⟨"full_viv_collect_m4", [i64, i64], [i64], FullM4VivBce.fullVivCollectM4Spec, true⟩
  let h135 := mkM5Env_row_at (mainSpec := mainSpec) 135
    ⟨"full_viv_keys_m4", [i64, i64], [], FullM4VivBce.fullVivKeysM4Spec, true⟩
  let h136 := mkM5Env_row_at (mainSpec := mainSpec) 136
    ⟨"full_viv_clear_tier_m4", [i64, i64], [], FullM4VivBce.fullVivClearTierM4Spec, true⟩
  let h137 := mkM5Env_row_at (mainSpec := mainSpec) 137
    ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64], FullM5Orch.fullVivifyTierM5Spec, true⟩
    (hno := FullM5Orch.fullVivifyTierM5Spec_noExit)
  have hseg : (m5Fns.drop 120).take 19 =
      [ ⟨"full_trans_lit_m5", [i64, i32], [.bool], FullM5Orch.full_trans_lit_m5_body⟩
      , ⟨"full_transitive_m5", [i64, i64], [i64], FullM5Orch.full_transitive_m5_body⟩
      , ⟨"full_viv_simplify", [i64, i32], [i64], full_viv_simplify_body⟩ ] ++
      (((m5Fns.drop 123).take 2) ++
      [ ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], full_viv_commit_body⟩
      , ⟨"full_viv_sort_noccs_m4", [i64, i32], [], FullM4VivBce.full_viv_sort_noccs_m4_body⟩
      , ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool], FullM4VivBce.full_viv_has_l0_m4_body⟩
      , ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64], FullM4VivBce.full_viv_l0_simp_m4_body⟩
      , ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [],
          FullM4VivBce.full_viv_reuse_prefix_m4_body⟩
      , ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64],
          FullM4VivBce.full_viv_finish_m4_body⟩
      , ⟨"full_viv_clause_m4", [i64, i32], [i64], FullM4VivBce.full_viv_clause_m4_body⟩
      , ⟨"full_viv_sort_sched_m4", [i64, i64], [], FullM4VivBce.full_viv_sort_sched_m4_body⟩
      , ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool],
          FullM4VivBce.full_viv_tier_match_m4_body⟩
      , ⟨"full_viv_collect_m4", [i64, i64], [i64], FullM4VivBce.full_viv_collect_m4_body⟩
      , ⟨"full_viv_keys_m4", [i64, i64], [], FullM4VivBce.full_viv_keys_m4_body⟩
      , ⟨"full_viv_clear_tier_m4", [i64, i64], [], FullM4VivBce.full_viv_clear_tier_m4_body⟩
      , ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64], FullM5Orch.full_vivify_tier_m5_body⟩
      , ⟨"full_vivify_m5", [i64], [i64], FullM5Orch.full_vivify_m5_body⟩ ]) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 123 2) fun fn hfn => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Orch.full_trans_lit_m5_wp Γ h106 h110 xs m Q _
        (mkM5Env_row_elim 120 ⟨"full_trans_lit_m5", [i64, i32], [.bool],
          fullTransLitSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_transitive_m5_wp Γ h33 h120 h56 h14 xs m Q _
        (mkM5Env_row_elim 121 ⟨"full_transitive_m5", [i64, i64], [i64],
          FullFastBveBudgets.fullTransitiveFastSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_simplify_m4_wp Γ h51 h110 h107 h15 xs m Q _
        (mkM5Env_row_elim 122 ⟨"full_viv_simplify", [i64, i32], [i64],
          FullM4VivBce.fullVivSimplifyM4Spec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM4VivBce.full_viv_commit_m4_wp Γ h51 h110 h107 h15 xs m Q _
        (mkM5Env_row_elim 125 ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64],
          FullM4VivBce.fullVivCommitM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_sort_noccs_m4_wp Γ xs m Q _
        (mkM5Env_row_elim 126 ⟨"full_viv_sort_noccs_m4", [i64, i32], [],
          FullM4VivBce.fullVivSortNoccsM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_has_l0_m4_wp Γ xs m Q _
        (mkM5Env_row_elim 127 ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool],
          FullM4VivBce.fullVivHasL0M4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_l0_simp_m4_wp Γ h127 h33 h122 xs m Q _
        (mkM5Env_row_elim 128 ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64],
          FullM4VivBce.fullVivL0SimpM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_reuse_prefix_m4_wp Γ h33 xs m Q _
        (mkM5Env_row_elim 129 ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [],
          FullM4VivBce.fullVivReusePrefixM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_finish_m4_wp Γ h33 h124 h125 xs m Q _
        (mkM5Env_row_elim 130 ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64],
          FullM4VivBce.fullVivFinishM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_clause_m4_wp Γ h128 h126 h129 h30 h55 h33 h130
        xs m Q _ (mkM5Env_row_elim 131 ⟨"full_viv_clause_m4", [i64, i32], [i64],
          FullM4VivBce.fullVivClauseM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_sort_sched_m4_wp Γ xs m Q _
        (mkM5Env_row_elim 132 ⟨"full_viv_sort_sched_m4", [i64, i64], [],
          FullM4VivBce.fullVivSortSchedM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_tier_match_m4_wp Γ xs m Q _
        (mkM5Env_row_elim 133 ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool],
          FullM4VivBce.fullVivTierMatchM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_collect_m4_wp Γ h11 h133 xs m Q _
        (mkM5Env_row_elim 134 ⟨"full_viv_collect_m4", [i64, i64], [i64],
          FullM4VivBce.fullVivCollectM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_keys_m4_wp Γ xs m Q _
        (mkM5Env_row_elim 135 ⟨"full_viv_keys_m4", [i64, i64], [],
          FullM4VivBce.fullVivKeysM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_viv_clear_tier_m4_wp Γ h11 h133 xs m Q _
        (mkM5Env_row_elim 136 ⟨"full_viv_clear_tier_m4", [i64, i64], [],
          FullM4VivBce.fullVivClearTierM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_vivify_tier_m5_wp Γ h33 h134 h135 h132 h131 h56 h136
        xs m Q _ (mkM5Env_row_elim 137 ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64],
          FullM5Orch.fullVivifyTierM5Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_vivify_m5_wp Γ h33 h137 xs m Q _
        (mkM5Env_row_elim 138 ⟨"full_vivify_m5", [i64], [i64],
          FullM5Orch.m5VivifySpec, true⟩ rfl rfl hs))

private theorem m5_block142to145_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 142).take 4, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h11 := mkM5Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h33 := mkM5Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h56 := mkM5Env_row_at (mainSpec := mainSpec) 56
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h63 := mkM5Env_row_at (mainSpec := mainSpec) 63
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h66 := mkM5Env_row_at (mainSpec := mainSpec) 66
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h107 := mkM5Env_row_at (mainSpec := mainSpec) 107
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h110 := mkM5Env_row_at (mainSpec := mainSpec) 110
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h140_fast := mkM5Env_row_at (mainSpec := mainSpec) 140
    ⟨"full_tarjan_scc", [i64], [i64], FullFastBveBudgets.fullTarjanSccFastSpec, true⟩
  let h140 : ∀ a m Q X, fullTarjanSccSpec a m Q X →
      Γ "full_tarjan_scc" [i64] [i64] a m Q X :=
    fun a m Q X h => h140_fast a m Q X (FullFastBveBudgets.fullTarjanSccFastSpec_of_canon h)
  let h141 := mkM5Env_row_at (mainSpec := mainSpec) 141
    ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  let h142 := mkM5Env_row_at (mainSpec := mainSpec) 142
    ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  let h143 := mkM5Env_row_at (mainSpec := mainSpec) 143
    ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  have hseg : (m5Fns.drop 142).take 4 =
      [ FullM5DenseSafe.m5SubstRewriteBinsFn, FullM5DenseSafe.m5SubstRewriteArFn
      , FullM5DenseSafe.m5SubstituteFn, FullM5DenseSafe.m5EnterDenseFn ] := by
    t_kernel_rfl
  rw [hseg]
  intro fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl <;> intro xs m Q X hs
  · exact wp_noExit_lift (FullM5DenseSafe.full_subst_rewrite_bins_m5_wp Γ h110 h107 xs m Q _
      (mkM5Env_row_elim 142 ⟨"full_subst_rewrite_bins", [i64], [.bool],
        fullSubstRewriteBinsSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5DenseSafe.full_subst_rewrite_ar_m5_wp Γ h11 h110 h107 xs m Q _
      (mkM5Env_row_elim 143 ⟨"full_subst_rewrite_ar", [i64], [.bool],
        fullSubstRewriteArSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5DenseSafe.full_substitute_m5_wp Γ h33 h140 h141 h142 h143 h66 h56
      xs m Q _ (mkM5Env_row_elim 144 ⟨"full_substitute", [i64], [i64],
        fullSubstituteSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM5DenseSafe.full_enter_dense_m5_wp Γ h33 h56 h63 h15 h66 h11
      xs m Q _ (mkM5Env_row_elim 145 ⟨"full_enter_dense", [i64], [.bool],
        FullFastSched.schedEnterDenseSpec, true⟩ rfl rfl hs))

private theorem m5_block147_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ fn ∈ (m5Fns.drop 147).take 1, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  have hseg : (m5Fns.drop 147).take 1 = [FullM4InprocHot.m4KittenInitFn] := by t_kernel_rfl
  rw [hseg]
  intro fn hfn xs m Q X hs
  rcases List.mem_singleton.mp hfn with rfl
  exact wp_noExit_lift (FullM4InprocHot.full_kitten_init_m4_wp Γ xs m Q _
    (mkM5Env_row_elim 147 ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
      rfl rfl hs))

private theorem m5_block163to177_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 163).take 15, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h11 := mkM5Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h105 := mkM5Env_row_at (mainSpec := mainSpec) 105
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let h107 := mkM5Env_row_at (mainSpec := mainSpec) 107
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h162 := mkM5Env_row_at (mainSpec := mainSpec) 162
    ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  let h164 := mkM5Env_row_at (mainSpec := mainSpec) 164
    ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  let h165 := mkM5Env_row_at (mainSpec := mainSpec) 165
    ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  let h166 := mkM5Env_row_at (mainSpec := mainSpec) 166
    ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
      FullM5CongFix.m5CongExtractIteSpec, true⟩
  let h167 := mkM5Env_row_at (mainSpec := mainSpec) 167
    ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
      FullM5CongFix.m5CongEmitXorSpec, true⟩
  let h168 := mkM5Env_row_at (mainSpec := mainSpec) 168
    ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      FullM5CongFix.m5CongTryXorIteSpec, true⟩
  let h169 := mkM5Env_row_at (mainSpec := mainSpec) 169
    ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM5CongFix.m5CongExtractSpec, true⟩
  let h171 := mkM5Env_row_at (mainSpec := mainSpec) 171
    ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], FullM3CongBva.m3CongUnitFoldSpec, true⟩
  let h172 := mkM5Env_row_at (mainSpec := mainSpec) 172
    ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      FullM3CongBva.m3CongEquivFoldSpec, true⟩
  let h173 := mkM5Env_row_at (mainSpec := mainSpec) 173
    ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM5CongFix.m5CongAndMatchSpec, true⟩
  let h174 := mkM5Env_row_at (mainSpec := mainSpec) 174
    ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      FullM5CongFix.m5CongWorkStepSpec, true⟩
  let h175 := mkM5Env_row_at (mainSpec := mainSpec) 175
    ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
      FullM5CongBins.m5CongEbMatchSpec, true⟩
  let h176 := mkM5Env_row_at (mainSpec := mainSpec) 176
    ⟨"full_cong_extract_binaries", [i64], [i64],
      FullM5CongBins.m5CongExtractBinariesSpec, true⟩
  have hseg : (m5Fns.drop 163).take 15 =
      [ ⟨"full_cong_merge", [i64, i32, i32], [.bool], FullM5CongFix.full_cong_merge_body⟩
      , FullM4InprocHot.m4HasTernaryFn ] ++
      (((m5Fns.drop 165).take 1) ++
      ([ ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
          FullM5CongFix.full_cong_extract_ite_body⟩
      , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
          FullM5CongFix.full_cong_emit_xor_body⟩
      , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
          FullM5CongFix.full_cong_try_xor_ite_body⟩
      , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM5CongFix.full_cong_extract_body⟩ ] ++
      (((m5Fns.drop 170).take 3) ++
      [ ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM5CongFix.full_cong_and_match_body⟩
      , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM5CongFix.full_cong_work_step_body⟩
      , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
          FullM5CongBins.full_cong_eb_match_body⟩
      , ⟨"full_cong_extract_binaries", [i64], [i64],
          FullM5CongBins.full_cong_extract_binaries_body⟩
      , ⟨"full_congruence_dense", [i64, i64], [i64],
          FullM5CongBins.full_congruence_dense_body⟩ ]))) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 165 1) (forall_mem_app (fun fn hfn => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 170 3) fun fn hfn => ?_)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_merge_wp Γ h162 (m5_add_bin_cong_adapter h107)
        xs m Q _ (mkM5Env_row_elim 163 ⟨"full_cong_merge", [i64, i32, i32], [.bool],
          fullCongMergeSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4InprocHot.full_has_ternary_m4_wp Γ xs m Q _
        (mkM5Env_row_elim 164 ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool],
          fullHasTernarySpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_extract_ite_wp Γ h164 xs m Q _
        (mkM5Env_row_elim 166 ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
          FullM5CongFix.m5CongExtractIteSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_emit_xor_wp Γ xs m Q _
        (mkM5Env_row_elim 167 ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
          FullM5CongFix.m5CongEmitXorSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_try_xor_ite_wp Γ h164 h167 h166 xs m Q _
        (mkM5Env_row_elim 168 ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
          FullM5CongFix.m5CongTryXorIteSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_extract_wp Γ h11 h105 h168 xs m Q _
        (mkM5Env_row_elim 169 ⟨"full_cong_extract", [i64, i64, i64], [i64],
          FullM5CongFix.m5CongExtractSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_and_match_wp Γ h162 xs m Q _
        (mkM5Env_row_elim 173 ⟨"full_cong_and_match", [i64, i32, i32], [.bool],
          FullM5CongFix.m5CongAndMatchSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongFix.m5_cong_work_step_wp Γ h162 h165 h171 h172 h173 xs m Q _
        (mkM5Env_row_elim 174 ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM5CongFix.m5CongWorkStepSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongBins.full_cong_eb_match_wp Γ h105 xs m Q _
        (mkM5Env_row_elim 175 ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
          FullM5CongBins.m5CongEbMatchSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongBins.full_cong_extract_binaries_wp Γ h11 h105 h175 h107
        xs m Q _ (mkM5Env_row_elim 176 ⟨"full_cong_extract_binaries", [i64], [i64],
          FullM5CongBins.m5CongExtractBinariesSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5CongFix.m5_congruence_dense_fix_wp Γ h176 h169 h174 xs m Q _
        (mkM5Env_row_elim 177 ⟨"full_congruence_dense", [i64, i64], [i64],
          FullM3CongBva.m3CongruenceDenseSpec, true⟩ rfl rfl hs))

private theorem m5_block200to211_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 200).take 12, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h51 := mkM5Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h107 := mkM5Env_row_at (mainSpec := mainSpec) 107
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h110 := mkM5Env_row_at (mainSpec := mainSpec) 110
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h147 := mkM5Env_row_at (mainSpec := mainSpec) 147
    ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  let h148 := mkM5Env_row_at (mainSpec := mainSpec) 148
    ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩
  let h150 := mkM5Env_row_at (mainSpec := mainSpec) 150
    ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩
  let h152 := mkM5Env_row_at (mainSpec := mainSpec) 152
    ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩
  let h154 := mkM5Env_row_at (mainSpec := mainSpec) 154
    ⟨"full_kitten_propagate", [i64], [i32], fullKittenPropagateSpec, true⟩
  let h156 := mkM5Env_row_at (mainSpec := mainSpec) 156
    ⟨"full_kitten_analyze", [i64, i32], [.bool], fullKittenAnalyzeSpec, true⟩
  let h160 := mkM5Env_row_at (mainSpec := mainSpec) 160
    ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec, true⟩
  let h199 := mkM5Env_row_at (mainSpec := mainSpec) 199
    ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], FullM4Sweep.m4SweepVarSpec, true⟩
  let h206 := mkM5Env_row_at (mainSpec := mainSpec) 206
    ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  let h208 := mkM5Env_row_at (mainSpec := mainSpec) 208
    ⟨"full_kitten_build_failing_m5", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  let h209 := mkM5Env_row_at (mainSpec := mainSpec) 209
    ⟨"full_kitten_solve_m5", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  let h210 := mkM5Env_row_at (mainSpec := mainSpec) 210
    ⟨"full_kitten_core_m5", [i64], [i32], fullKittenCoreSpec, true⟩
  have hseg : (m5Fns.drop 200).take 12 =
      [⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullM5Orch.full_sweep_dense_m5_body⟩] ++
      (((m5Fns.drop 201).take 1) ++
      ([FullM5DenseSafe.m5FwdCheckClFn] ++
      (((m5Fns.drop 203).take 3) ++
      [ ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool],
          FullM5KittenDefFix.full_kitten_add_clause_m5_body⟩
      , ⟨"full_kitten_ana_clause_m5", [i64, i32, i32], [],
          FullM5KittenDefFix.full_kitten_ana_clause_m5_body⟩
      , ⟨"full_kitten_build_failing_m5", [i64, i32], [],
          FullM5KittenDefFix.full_kitten_build_failing_m5_body⟩
      , ⟨"full_kitten_solve_m5", [i64, i64], [i64], FullM5KittenDefFix.full_kitten_solve_m5_body⟩
      , ⟨"full_kitten_core_m5", [i64], [i32], FullM5KittenDefFix.full_kitten_core_m5_body⟩
      , m5FindDefinitionFn ]))) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn xs m Q X hs => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 201 1) (forall_mem_app (fun fn hfn xs m Q X hs => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 203 3) fun fn hfn => ?_)))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5Orch.full_sweep_dense_m5_wp Γ h199 xs m Q _
      (mkM5Env_row_elim 200 ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64],
        FullDefSweep.fullSweepDenseSpec, true⟩ rfl rfl hs))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5DenseSafe.full_fwd_check_cl_m5_wp Γ h51 h110 h107 xs m Q _
      (mkM5Env_row_elim 202 ⟨"full_fwd_check_cl", [i64, i32], [.bool],
        fullFwdCheckClSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5KittenDefFix.full_kitten_add_clause_m5_wp Γ h148 xs m Q _
        (mkM5Env_row_elim 206 ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool],
          fullKittenAddClauseSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5KittenDefFix.full_kitten_ana_clause_m5_wp Γ xs m Q _
        (mkM5Env_row_elim 207 ⟨"full_kitten_ana_clause_m5", [i64, i32, i32], [],
          FullM5KittenDefFix.fullKittenAnaClauseM5Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5KittenDefFix.full_kitten_build_failing_m5_wp Γ xs m Q _
        (mkM5Env_row_elim 208 ⟨"full_kitten_build_failing_m5", [i64, i32], [],
          fullKittenBuildFailingSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5KittenDefFix.full_kitten_solve_m5_wp Γ h152 h150 h154 h156 h208
        xs m Q _ (mkM5Env_row_elim 209 ⟨"full_kitten_solve_m5", [i64, i64], [i64],
          fullKittenSolveSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5KittenDefFix.full_kitten_core_m5_wp Γ xs m Q _
        (mkM5Env_row_elim 210 ⟨"full_kitten_core_m5", [i64], [i32],
          fullKittenCoreSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (m5_find_definition_wp Γ h147 h206 h209 h210 h160 xs m Q _
        (mkM5Env_row_elim 211 ⟨"full_find_definition", [i64, i32, i32, i32], [],
          FullDefSweep.fullFindDefinitionSpec, true⟩ rfl rfl hs))

private theorem m5_block218_227_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 218).take 10, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h12 := mkM5Env_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h14 := mkM5Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM5Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h51 := mkM5Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h102 := mkM5Env_row_at (mainSpec := mainSpec) 102
    ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩
  let h103 := mkM5Env_row_at (mainSpec := mainSpec) 103
    ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩
  let h107 := mkM5Env_row_at (mainSpec := mainSpec) 107
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h108 := mkM5Env_row_at (mainSpec := mainSpec) 108
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let h109 := mkM5Env_row_at (mainSpec := mainSpec) 109
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h204 := mkM5Env_row_at (mainSpec := mainSpec) 204
    ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  let h212 := mkM5Env_row_at (mainSpec := mainSpec) 212
    ⟨"full_bve_gates", [i64, i32, i32, i32], [], FullDefSweep.fullBveGatesDefSpec, true⟩
  let h213 := mkM5Env_row_at (mainSpec := mainSpec) 213
    ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  let h214 := mkM5Env_row_at (mainSpec := mainSpec) 214
    ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
      FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩
  let h215 := mkM5Env_row_at (mainSpec := mainSpec) 215
    ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  let h216 := mkM5Env_row_at (mainSpec := mainSpec) 216
    ⟨"full_bve_commit_res", [i64, i64, i64], [i64],
      FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩
  let h217 := mkM5Env_row_at (mainSpec := mainSpec) 217
    ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  let h219 := mkM5Env_row_at (mainSpec := mainSpec) 219
    ⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩
  have hseg : (m5Fns.drop 218).take 10 =
      [FullM5DenseSafe.m5BveVarFn] ++
      (((m5Fns.drop 219).take 8) ++ [FullM5DenseSafe.m5BvaCommitFn]) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn xs m Q X hs => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 219 8) fun fn hfn xs m Q X hs => ?_)
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5DenseSafe.full_bve_var_m5_def_wp Γ h14 h204 h217 h214 h109
      (FullFast.fast_bve_gates_def_adapter h212) h213 h216 h215 h102 h108 h103 xs m Q _
      (mkM5Env_row_elim 218 ⟨"full_bve_var", [i64, i32], [i64],
        FullFastBveBudgets.fullBveVarDefSpec, true⟩ rfl rfl hs))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5DenseSafe.full_bva_commit_m5_wp Γ h14 h219 h107 h12 h15 h108 h51
      xs m Q _ (mkM5Env_row_elim 227 ⟨"full_bva_commit", [i64, i32], [.bool],
        FullM4Bva.m4BvaCommitSpec, true⟩ rfl rfl hs))

private theorem m5_block247to269_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ (m5Fns.drop 247).take 23, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM5Env mainSpec
  let h7 := mkM5Env_row_at (mainSpec := mainSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let h9 := mkM5Env_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h27 := mkM5Env_row_at (mainSpec := mainSpec) 27
    ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  let h33 := mkM5Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h44 := mkM5Env_row_at (mainSpec := mainSpec) 44
    ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  let h48 := mkM5Env_row_at (mainSpec := mainSpec) 48
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  let h56 := mkM5Env_row_at (mainSpec := mainSpec) 56
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h66 := mkM5Env_row_at (mainSpec := mainSpec) 66
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h67 := mkM5Env_row_at (mainSpec := mainSpec) 67
    ⟨"full_reduce_m5", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h90 := mkM5Env_row_at (mainSpec := mainSpec) 90
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let h92 := mkM5Env_row_at (mainSpec := mainSpec) 92
    ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  let h98 := mkM5Env_row_at (mainSpec := mainSpec) 98
    ⟨"full_rephase", [i64], [], FullM5Sched.m5RephaseSpec, true⟩
  let h99 := mkM5Env_row_at (mainSpec := mainSpec) 99
    ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  let h100 := mkM5Env_row_at (mainSpec := mainSpec) 100
    ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  let h101 := mkM5Env_row_at (mainSpec := mainSpec) 101
    ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  let h102 := mkM5Env_row_at (mainSpec := mainSpec) 102
    ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩
  let h103 := mkM5Env_row_at (mainSpec := mainSpec) 103
    ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩
  let h104 := mkM5Env_row_at (mainSpec := mainSpec) 104
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  let h108 := mkM5Env_row_at (mainSpec := mainSpec) 108
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let h113 := mkM5Env_row_at (mainSpec := mainSpec) 113
    ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  let h119 := mkM5Env_row_at (mainSpec := mainSpec) 119
    ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  let h121 := mkM5Env_row_at (mainSpec := mainSpec) 121
    ⟨"full_transitive_m5", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  let h138 := mkM5Env_row_at (mainSpec := mainSpec) 138
    ⟨"full_vivify_m5", [i64], [i64], FullM5Orch.m5VivifySpec, true⟩
    (hno := FullM5Orch.m5VivifySpec_noExit)
  let h144 := mkM5Env_row_at (mainSpec := mainSpec) 144
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  let h145 := mkM5Env_row_at (mainSpec := mainSpec) 145
    ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  let h146 := mkM5Env_row_at (mainSpec := mainSpec) 146
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let h177 := mkM5Env_row_at (mainSpec := mainSpec) 177
    ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  let h200 := mkM5Env_row_at (mainSpec := mainSpec) 200
    ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  let h203 := mkM5Env_row_at (mainSpec := mainSpec) 203
    ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  let h204 := mkM5Env_row_at (mainSpec := mainSpec) 204
    ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  let h215 := mkM5Env_row_at (mainSpec := mainSpec) 215
    ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  let h231 := mkM5Env_row_at (mainSpec := mainSpec) 231
    ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  let h232 := mkM5Env_row_at (mainSpec := mainSpec) 232
    ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
  let h244 := mkM5Env_row_at (mainSpec := mainSpec) 244
    ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
  let h246 := mkM5Env_row_at (mainSpec := mainSpec) 246
    ⟨"full_reorder_queue", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  let h247 := mkM5Env_row_at (mainSpec := mainSpec) 247
    ⟨"full_reorder_m5", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  let h248 := mkM5Env_row_at (mainSpec := mainSpec) 248
    ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4VivBce.fullBceSideM4Spec, true⟩
  let h249 := mkM5Env_row_at (mainSpec := mainSpec) 249
    ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.fullBcePairM4Spec, true⟩
  let h250 := mkM5Env_row_at (mainSpec := mainSpec) 250
    ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.fullBceVarM4Spec, true⟩
  let h251 := mkM5Env_row_at (mainSpec := mainSpec) 251
    ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩
  let h252 := mkM5Env_row_at (mainSpec := mainSpec) 252
    ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  let h253 := mkM5Env_row_at (mainSpec := mainSpec) 253
    ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  let h254 := mkM5Env_row_at (mainSpec := mainSpec) 254
    ⟨"full_probe_dticks_m5", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  let h256 := mkM5Env_row_at (mainSpec := mainSpec) 256
    ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  let h257 := mkM5Env_row_at (mainSpec := mainSpec) 257
    ⟨"full_probe_tail_m5", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  let h258 := mkM5Env_row_at (mainSpec := mainSpec) 258
    ⟨"full_probe_m5", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  let h259 := mkM5Env_row_at (mainSpec := mainSpec) 259
    ⟨"full_elim_dticks_m5", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  let h261 := mkM5Env_row_at (mainSpec := mainSpec) 261
    ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  let h262 := mkM5Env_row_at (mainSpec := mainSpec) 262
    ⟨"full_eliminate_m5", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  let h263 := mkM5Env_row_at (mainSpec := mainSpec) 263
    ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩
  let h265 := mkM5Env_row_at (mainSpec := mainSpec) 265
    ⟨"full_simplify_m5", [i64, .bool, .bool], [i64], FullM4.m4SimplifySpec, true⟩
  let h266 := mkM5Env_row_at (mainSpec := mainSpec) 266
    ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩
  let mainEff : Spec [i64, i64, i64, i64, i64] [i64] :=
    fun xs m' Q' _ => mainSpec xs m' Q' (fun _ _ _ _ => False)
  let h268 : ∀ a m Q X, mainEff a m Q X →
      Γ "kissat_solve_bytes_m5" [i64, i64, i64, i64, i64] [i64] a m Q X :=
    fun a m Q X h =>
      Env.ofTable_of_mem
        (List.mem_of_getElem? (show (m5SpecTable mainSpec)[268]? = some
          ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ from rfl))
        (m5SpecTable_nodup mainSpec) h
  have hseg : (m5Fns.drop 247).take 23 =
      [ ⟨"full_reorder_m5", [i64, i64], [i64], FullM5Orch.full_reorder_m5_body⟩
      , ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
          FullM4VivBce.full_bce_side_m4_body⟩
      , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.full_bce_pair_m4_body⟩
      , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.full_bce_var_m4_body⟩
      , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.full_bce_m4_body⟩ ] ++
      (((m5Fns.drop 252).take 2) ++
      ([⟨"full_probe_dticks_m5", [i64, .bool], [i64], FullM5Orch.full_probe_dticks_m5_body⟩] ++
      (((m5Fns.drop 255).take 2) ++
      ([ ⟨"full_probe_tail_m5", [i64, i64], [i64], FullM5Orch.full_probe_tail_m5_body⟩
      , ⟨"full_probe_m5", [i64, .bool], [i64], FullM5Orch.full_probe_m5_body⟩
      , ⟨"full_elim_dticks_m5", [i64, .bool], [i64], FullM5Orch.full_elim_dticks_m5_body⟩ ] ++
      (((m5Fns.drop 260).take 2) ++
      [ ⟨"full_eliminate_m5", [i64, .bool], [i64], FullM5Orch.full_eliminate_m5_body⟩
      , ⟨"full_preprocess_m5", [i64], [i64], FullM5Orch.full_preprocess_m5_body⟩
      , m5PreprocessFwdFn
      , ⟨"full_simplify_m5", [i64, .bool, .bool], [i64], FullM5Orch.full_simplify_m5_body⟩
      , ⟨"full_search_m5", [i64], [i64], FullM5Orch.full_search_m5_body⟩
      , m5SearchFwdFn
      , ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64],
          FullM5Orch.kissat_solve_bytes_m5_body⟩
      , m5SolveBytesFwdFn ]))))) := by
    t_kernel_rfl
  rw [hseg]
  refine forall_mem_app (fun fn hfn => ?_) (forall_mem_app
    (m5_drop_take_m4_wp mainSpec hM4 252 2) (forall_mem_app (fun fn hfn xs m Q X hs => ?_)
    (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 255 2) (forall_mem_app
    (fun fn hfn => ?_) (forall_mem_app (m5_drop_take_m4_wp mainSpec hM4 260 2)
    fun fn hfn => ?_)))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Orch.full_reorder_m5_wp Γ h246 xs m Q _
        (mkM5Env_row_elim 247 ⟨"full_reorder_m5", [i64, i64], [i64],
          FullM4.m4ReorderSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_bce_side_m4_wp Γ h215
        (FullFast.fast_extend_push2_adapter h102) (m5_extend_push_cl_adapter h103) h108 xs m Q _
        (mkM5Env_row_elim 248 ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
          FullM4VivBce.fullBceSideM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_bce_pair_m4_wp Γ h248 xs m Q _
        (mkM5Env_row_elim 249 ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [],
          FullM4VivBce.fullBcePairM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM4VivBce.full_bce_var_m4_wp Γ h204 h249 xs m Q _
        (mkM5Env_row_elim 250 ⟨"full_bce_var_m4", [i64, i32], [],
          FullM4VivBce.fullBceVarM4Spec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (m5_bce_m4_wp Γ h145 h250 h146 h56 xs m Q _
        (mkM5Env_row_elim 251 ⟨"full_bce_m4", [i64, i64], [i64],
          FullM4VivBce.fullBceM4Spec, true⟩ rfl rfl hs))
  · rcases List.mem_singleton.mp hfn with rfl
    exact wp_noExit_lift (FullM5Orch.full_probe_dticks_m5_wp Γ h253 xs m Q _
      (mkM5Env_row_elim 254 ⟨"full_probe_dticks_m5", [i64, .bool], [i64],
        FullFastSched.schedProbeDticksSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Orch.full_probe_tail_m5_wp Γ h256 h121 h252 h119 h138 xs m Q _
        (mkM5Env_row_elim 257 ⟨"full_probe_tail_m5", [i64, i64], [i64],
          FullFastSched.schedProbeTailSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_probe_m5_wp Γ h254 h9 h27 h145 h177 h200 h146 h144
        h257 h256 h252 h231 xs m Q _ (mkM5Env_row_elim 258 ⟨"full_probe_m5", [i64, .bool], [i64],
          FullFastSched.schedProbeSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_elim_dticks_m5_wp Γ h253 xs m Q _
        (mkM5Env_row_elim 259 ⟨"full_elim_dticks_m5", [i64, .bool], [i64],
          FullFastSched.schedElimDticksSpec, true⟩ rfl rfl hs))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro xs m Q X hs
    · exact wp_noExit_lift (FullM5Orch.full_eliminate_m5_wp Γ h259 h9 h27 h145 h203 h252 h231
        h261 h146 h251 xs m Q _ (mkM5Env_row_elim 262 ⟨"full_eliminate_m5", [i64, .bool], [i64],
          FullFastSched.schedEliminateSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_preprocess_m5_wp Γ h56 h66 h113 h232 h244 h27 h258
        xs m Q _ (mkM5Env_row_elim 263 ⟨"full_preprocess_m5", [i64], [i64],
          FullM4.m4PreprocessSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (m5_preprocess_fwd_wp Γ h263 xs m Q _
        (mkM5Env_row_elim 264 ⟨"full_preprocess", [i64], [i64],
          FullM4.m4PreprocessSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.full_simplify_m5_wp Γ h33 h258 h262 h232 h244 xs m Q _
        (mkM5Env_row_elim 265 ⟨"full_simplify_m5", [i64, .bool, .bool], [i64],
          FullM4.m4SimplifySpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (m5_search_m5_wp Γ h56 h90 h67 h99 h100 h101 h247 h98 h265 h92 xs m Q _
        (mkM5Env_row_elim 266 ⟨"full_search_m5", [i64], [i64],
          FullM4.m4SearchSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (m5_search_fwd_wp Γ h266 xs m Q _
        (mkM5Env_row_elim 267 ⟨"full_search", [i64], [i64],
          FullM4.m4SearchSpec, true⟩ rfl rfl hs))
    · exact wp_noExit_lift (FullM5Orch.kissat_solve_bytes_m5_core_wp Γ h44 h48 h263 h266 h104 h7
        xs m Q _ (hweaken xs m Q _ (mkM5Env_row_elim 268
          ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
          rfl rfl hs)))
    · exact wp_noExit_lift (m5_solve_bytes_fwd_wp Γ (S := mainEff) h268 xs m Q _
        (mkM5Env_row_elim 269 ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
          mainSpec, true⟩ rfl rfl hs))

/-- Unconditional `270 / 270` `Func.wp` certification of every function in `FullM5.m5Fns`
against `mkM5Env mainSpec` (`153` unchanged M4, `2` `FullM4InprocHot` outside `m5_block163to177`,
`22` `FullM4Sweep`, and `93` M5-upgraded / wired functions). -/
theorem m5Fns_all_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hM4 : ModuleOk (FullM4.mkM4Env mainSpec) FullM4.m4Module) :
    ∀ fn ∈ m5Fns, ∀ xs m Q X,
      mkM5Env mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5Env mainSpec) fn.body xs m Q X := by
  rw [← @List.drop_zero _ m5Fns]
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 0 14) ?_
  refine forall_mem_drop_split (m5_block14_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 15 11) ?_
  refine forall_mem_drop_split (m5_block26to28_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 29 2) ?_
  refine forall_mem_drop_split (m5_block31to33_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 34 7) ?_
  refine forall_mem_drop_split (m5_block41to42_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 43 1) ?_
  refine forall_mem_drop_split (m5_block44to45_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 46 5) ?_
  refine forall_mem_drop_split (m5_block51_53to55_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 56 7) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 63 4) ?_
  refine forall_mem_drop_split (m5_block67to76_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 77 9) ?_
  refine forall_mem_drop_split (m5_block86to93_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 94 4) ?_
  refine forall_mem_drop_split (m5_block98to115_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 116 4) ?_
  refine forall_mem_drop_split (m5_block120to138_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 139 3) ?_
  refine forall_mem_drop_split (m5_block142to145_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 146 1) ?_
  refine forall_mem_drop_split (m5_block147_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 148 15) ?_
  refine forall_mem_drop_split (m5_block163to177_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_sweep22_seg_wp mainSpec) ?_
  refine forall_mem_drop_split (m5_block200to211_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 212 6) ?_
  refine forall_mem_drop_split (m5_block218_227_wp mainSpec hM4) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 228 17) ?_
  refine forall_mem_drop_split (m5_drop_take_m4_wp mainSpec hM4 245 2) ?_
  refine forall_mem_drop_split (m5_block247to269_wp mainSpec hweaken hM4) ?_
  have hnil : m5Fns.drop 270 = [] := by
    rw [List.drop_eq_nil_iff, m5Fns_length]; exact Nat.le_refl _
  rw [hnil]
  exact fun _ h => nomatch h

end AllFnsWp

/-! ## 5. Unconditional Closed `270/270` `ModuleOk` Assembly -/

/-- Unconditional `270`-function `ModuleOk` assembly for `mkM5Env mainSpec` on `m5Module`. -/
theorem mkM5Env_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkM5Env mainSpec) m5Module :=
  Module.moduleOk_of_checkAcyclic m5_acyclic m5Fns_wf
    (m5Fns_all_wp mainSpec hweaken (FullM4.mkM4Env_moduleOk mainSpec hweaken))

/-- Unconditional closed `ModuleOk m5Env m5Module` certifying all `270 / 270` functions of
Unified Kissat M5 against canonical UNSAT-only `m5Env` (`0` SAT/model proofs). -/
theorem m5Env_moduleOk : ModuleOk m5Env m5Module :=
  mkM5Env_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional closed `ModuleOk m5UnsatEnv m5Module` (`270 / 270`, concrete `Mem 64` UNSAT
non-vacuity environment). -/
theorem m5UnsatEnv_moduleOk : ModuleOk m5UnsatEnv m5Module :=
  mkM5Env_moduleOk fullUnsatWitnessSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

/-! ## 6. Public Prefix-Agreement & Row Accessors for Additive Tail-Respec / SAT-NV Modules -/

theorem m5Env_eq_mkM5Env : m5Env = mkM5Env fullSolveBytesSpec := by rfl

/-- All `268` prefix entries (`0..267`) agree between `mkM5Env s₁` and `mkM5Env s₂`. -/
theorem mkM5Env_agree_prefix (s₁ s₂ : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs, (f, as, bs) ∈ (m5Fns.take 268).map Fn.sig →
      ∀ xs m Q X, mkM5Env s₁ f as bs xs m Q X ↔ mkM5Env s₂ f as bs xs m Q X := by
  have htk : (m5SpecTable s₁).take 268 = (m5SpecTable s₂).take 268 := by t_kernel_rfl
  have hsigs : ((m5SpecTable s₁).take 268).map (fun e => (e.name, e.as, e.rs)) =
      (m5Fns.take 268).map Fn.sig := by
    rw [List.map_take, List.map_take]
    exact congrArg (List.take 268) (m5SpecTable_sigs s₁)
  intro f as bs hmem xs m Q X
  rw [← hsigs, List.mem_map] at hmem
  obtain ⟨e, he_tk, hsig⟩ := hmem
  rcases hsig with ⟨rfl, rfl, rfl⟩
  exact m5_ofTable_agree_of_mem_both (List.mem_of_mem_take he_tk) (m5SpecTable_nodup s₁)
    (List.mem_of_mem_take (htk ▸ he_tk)) (m5SpecTable_nodup s₂) xs m Q X

theorem mkM5Env_solve_bytes_m5_iff (s : Spec [i64, i64, i64, i64, i64] [i64])
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM5Env s "kissat_solve_bytes_m5" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      s xs m Q (fun _ _ _ _ => False) := by
  exact m5_ofTable_iff_of_mem
    (List.mem_of_getElem? (by t_kernel_rfl : (m5SpecTable s)[268]? =
      some ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], s, true⟩))
    (m5SpecTable_nodup s)

theorem mkM5Env_solve_bytes_iff (s : Spec [i64, i64, i64, i64, i64] [i64])
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM5Env s "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      s xs m Q (fun _ _ _ _ => False) := by
  exact m5_ofTable_iff_of_mem
    (List.mem_of_getElem? (by t_kernel_rfl : (m5SpecTable s)[269]? =
      some ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], s, true⟩))
    (m5SpecTable_nodup s)

theorem mkM5Env_skip_ws_comments (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      mkM5Env s "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩

theorem mkM5Env_parse_header (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      mkM5Env s "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩

theorem mkM5Env_next_lit (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, kissatNextLitSpec a m Q X →
      mkM5Env s "kissat_next_lit" [i64, i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩

theorem mkM5Env_check_model (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      mkM5Env s "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩

theorem mkM5Env_wstack_defrag (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X →
      mkM5Env s "full_wstack_defrag" [i64] [] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩

theorem mkM5Env_zero_tables1 (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullZeroTables1Spec a m Q X →
      mkM5Env s "full_zero_tables1" [i64] [] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 35
    ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩

theorem mkM5Env_fixed_bytes (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullFixedBytesSpec a m Q X →
      mkM5Env s "full_fixed_bytes" [i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 37
    ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩

theorem mkM5Env_calc_max_v (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullCalcMaxVSpec a m Q X →
      mkM5Env s "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 40
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩

theorem mkM5Env_calc_ext_cap_m5 (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, FullM5Orch.fullCalcExtCapM5Spec a m Q X →
      mkM5Env s "full_calc_ext_cap_m5" [i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 41
    ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
    (hno := FullM5Orch.fullCalcExtCapM5Spec_noExit)

theorem mkM5Env_calc_scr_cap_m5 (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, FullM5Orch.fullCalcScrCapM5Spec a m Q X →
      mkM5Env s "full_calc_scr_cap_m5" [i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 42
    ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩
    (hno := FullM5Orch.fullCalcScrCapM5Spec_noExit)

theorem mkM5Env_init_arenas (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullInitArenasSpec a m Q X →
      mkM5Env s "full_init_arenas" [i64, i64, i64, i64] [] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 43
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩

theorem mkM5Env_init_state_m5 (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullInitStateSpec a m Q X →
      mkM5Env s "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 44
    ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩

theorem mkM5Env_parse_body (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullParseBodySpec a m Q X →
      mkM5Env s "full_parse_body" [i64, i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 48
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩

theorem mkM5Env_extend (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, fullExtendSpec a m Q X →
      mkM5Env s "full_extend" [i64] [] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 104
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩

theorem mkM5Env_preprocess_m5 (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      mkM5Env s "full_preprocess_m5" [i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 263
    ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩

theorem mkM5Env_search_m5 (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, FullM4.m4SearchSpec a m Q X →
      mkM5Env s "full_search_m5" [i64] [i64] a m Q X := by
  exact mkM5Env_row_at (mainSpec := s) 266
    ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩

end LeanQbe.T.Examples.Kissat.FullM5

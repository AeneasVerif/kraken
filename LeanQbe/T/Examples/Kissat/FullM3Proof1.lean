module

public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
public import LeanQbe.T.Examples.Kissat.FullFastAdapters
public import LeanQbe.T.Examples.Kissat.FullFastTmkLemmas
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas
public import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Unified M3 Proof — Part 1 (`m3SpecTable`, Soundness, & Merged Orchestrators)

Defines:
1. Unified `204`-row specification table `m3SpecTable`, `mkM3Env`, `m3Env`, `m3UnsatEnv` aligned
   1-to-1 with `FullM3.m3Fns` (`m3SpecTable_sigs`, `m3SpecTable_noExit` via `t_kernel_rfl`).
2. Headline source-level UNSAT soundness `m3_solve_bytes_correct` and concrete `Mem 64` UNSAT
   non-vacuity `m3_unsat_nonvacuous` (`XPost := False`, `4096` B workspace, `fuel = 16`).
3. `Func.wp` proofs for both merged M3 orchestrators:
   - `m3_probe_tail_wp`: M3c `backbone` + `pbud` + M3a tier-3 `vivify(h, 3, v0)`
   - `m3_probe_wp`: M3b pure-3-CNF dense gate (`initial || num_binary * 3 >= num_irred`) +
     `m3CongruenceDenseSpec` + `fullSweepDenseSpec` + M3c `initial` branch vs `full_probe_tail`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Unified `204`-Row `m3SpecTable`, `mkM3Env`, Soundness & Non-Vacuity -/

/-- Unified `204`-row specification table aligned 1-to-1 with `FullM3.m3Fns` (flat list for
`O(1)` kernel indexing). -/
def m3SpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
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
  , ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  , ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  , ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  , ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.fullFastInitHdrSpec, true⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  , ⟨"full_calc_ext_cap", [i64], [i64], fullCalcExtCapSpec, true⟩
  , ⟨"full_calc_scr_cap", [i64], [i64], fullCalcScrCapSpec, true⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  , ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  , ⟨"full_assign_level", [i64, i32, i32], [i32], fullAssignLevelSpec, true⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  , ⟨"full_red_less", [i64, i32, i32], [.bool], fullRedLessSpec, true⟩
  , ⟨"full_red_sift", [i64, i64, i64, i64], [], fullRedSiftSpec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  , ⟨"full_lit_rank", [i64, i64, i32], [i64], fullLitRankSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  , ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  , ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
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
  , ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
  , ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  , ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  , ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩
  , ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
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
  , ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
  , ⟨"full_transitive", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifySpec, true⟩
  , ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
  , ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  , ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitSpec, true⟩
  , ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  , ⟨"full_vivify", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩
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
  , ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], fullCongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fullCongEmitXorSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], fullCongTryXorIteSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullDefSweep.fullCongExtractTickSpec, true⟩
  , ⟨"full_cong_mark_trail", [i64, i64, i32], [], FullM3CongBva.m3CongMarkTrailSpec, true⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], FullM3CongBva.m3CongUnitFoldSpec, true⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      FullM3CongBva.m3CongEquivFoldSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM3CongBva.m3CongAndMatchSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      FullM3CongBva.m3CongWorkStepSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_sweep_cone", [i64, i32], [i64],
      FullDefSweep.fullSweepConeKittenSpec FullFast.fastKInv, true⟩
  , ⟨"full_sweep_refine_kitten", [i64, i32, i32], [],
      FullDefSweep.fullSweepRefineKittenSpec, true⟩
  , ⟨"full_sweep_var", [i64, i32, i64], [i64], FullDefSweep.fullSweepVarKittenSpec, true⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  , ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool],
      FullDefSweep.fullBveMarkAndDefSpec, true⟩
  , ⟨"full_find_definition", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩
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
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop3Spec, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      FullBvaHeap.fullBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullBvaHeap.fullBvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullBvaHeap.fullBvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], FullBvaHeap.fullBvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullBvaHeap.fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  , ⟨"full_backbone_lit", [i64, i32], [i64], FullM3Backbone.fullBackboneLitSpec, true⟩
  , ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_probe_tail", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  , ⟨"full_elim_collect_nbrs", [i64, i32], [i64], FullM3CongBva.m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_eliminate", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  , ⟨"full_simplify", [i64, .bool, .bool], [i64], FullFastSched.schedSimplifySpec, true⟩
  , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

def mkM3Env (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m3SpecTable mainSpec)

/-- Headline `204`-function UNSAT-only environment for `FullM3.m3Module`. -/
def m3Env : Env := mkM3Env fullSolveBytesSpec

/-- Concrete `204`-function UNSAT non-vacuity environment (`fullUnsatWitnessSpec`, `20#64`). -/
def m3UnsatEnv : Env := mkM3Env fullUnsatWitnessSpec

theorem m3SpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m3SpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (m3SpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m3SpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3SpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      m3Fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

theorem m3SpecTable_length (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3SpecTable mainSpec).length = 204 := by
  have hs := congrArg List.length (m3SpecTable_sigs mainSpec)
  simpa only [List.length_map, m3Fns_length] using hs

private theorem m3Fns_nodup : (m3Fns.map Fn.name).Nodup := by
  have hchk := m3_acyclic
  simp only [m3Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem m3SpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m3SpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (m3SpecTable mainSpec).map SpecEntry.name = m3Fns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (m3SpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]; exact m3Fns_nodup

theorem mkM3Env_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m3SpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3Env mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m3SpecTable_nodup mainSpec) (hno xs m Q X h)

theorem mkM3Env_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM3Env mainSpec f as bs xs m Q X → mkM3Env mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m3SpecTable_noExit mainSpec)

theorem m3Env_noExit :
    ∀ f as bs xs m Q X X', m3Env f as bs xs m Q X → m3Env f as bs xs m Q X' :=
  mkM3Env_noExit fullSolveBytesSpec

theorem m3UnsatEnv_noExit :
    ∀ f as bs xs m Q X X', m3UnsatEnv f as bs xs m Q X → m3UnsatEnv f as bs xs m Q X' :=
  mkM3Env_noExit fullUnsatWitnessSpec

/-- Headline source-level UNSAT-only soundness of Unified M3 `kissat_solve_bytes` under
canonical `204`-function `m3Env` (`0` SAT/model proofs). -/
theorem m3_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m3Env Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  FullFastSched.sched_kissat_solve_bytes_wp m3Env
    (mkM3Env_row_at (mainSpec := fullSolveBytesSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullSolveBytesSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullSolveBytesSpec) 200
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullSolveBytesSpec) 202
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullSolveBytesSpec) 97
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullSolveBytesSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under `204`-function `m3UnsatEnv`:
`kissat_solve_bytes` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
with `4096`-byte workspace and `fuel = 16`. -/
theorem m3_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3UnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  FullFastSched.sched_kissat_solve_bytes_core_wp m3UnsatEnv
    (mkM3Env_row_at (mainSpec := fullUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullUnsatWitnessSpec) 200
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullUnsatWitnessSpec) 202
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullUnsatWitnessSpec) 97
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM3Env_row_at (mainSpec := fullUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

/-! ## 2. Merged M3 Orchestrator `Func.wp` Proofs (`full_probe_tail`, `full_probe`) -/

section MergedOrchestrators

open scoped FullArenaTactics

private theorem m3_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

/-- `Func.wp` proof for unified M3 `full_probe_tail(h, dticks)` combining M3c `full_backbone`,
M3c `pbud`, and M3a Tier-3 `full_vivify(h, 3ULL, v0)` (`backbone → transitive → probe_run →
vivify 1 → vivify 2 → vivify 3 → vivify 0`). -/
theorem m3_probe_tail_wp (Γ : Env)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Func.wp Γ full_probe_tail_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hMin; intro pbud _
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun s3 m3 => FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ s3 m3 ⟨hinv3, hcl3, hfu3, hm3⟩ => by
              c0_hsteps; c0_call hMin; intro v1 _
              c0_hsteps; c0_call hMin; intro v0 _
              c0_hsteps; c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
              intro r4 s4 m4 hinv4 hcl4 _ _ hfu4 _ hu4 hm4
              have hcl4' := hcl4 hcl3
              c0_hsteps
              · exact hQ 20#64 s4 m4 hinv4 hcl4' (by omega) (Or.inr rfl) (fun _ => hu4 hc) hm4
              c0_call hViv; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
              intro r5 s5 m5 hinv5 hcl5 _ _ hfu5 _ hu5 hm5
              have hcl5' := hcl5 hcl4'
              c0_hsteps
              · exact hQ 20#64 s5 m5 hinv5 hcl5' (by omega) (Or.inr rfl) (fun _ => hu5 hc) hm5
              c0_call hViv; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
              intro r6 s6 m6 hinv6 hcl6 _ _ hfu6 _ hu6 hm6
              have hcl6' := hcl6 hcl5'
              c0_hsteps
              · exact hQ 20#64 s6 m6 hinv6 hcl6' (by omega) (Or.inr rfl) (fun _ => hu6 hc) hm6
              c0_call hViv; refine ⟨c, F0, s6, R, rfl, hinv6, hm6, ?_⟩
              intro r7 s7 m7 hinv7 hcl7 _ _ hfu7 _ hu7 hm7
              have hcl7' := hcl7 hcl6'
              c0_hsteps
              · exact hQ 20#64 s7 m7 hinv7 hcl7' (by omega) (Or.inr rfl) (fun _ => hu7 hc) hm7
              exact hQ 1#64 s7 m7 hinv7 hcl7' (by omega) (Or.inl rfl) (fun h => by cases h) hm7)
            (fun J3 hJ3 => by
              c0_hsplit
              · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
                intro rp s3 m3 hinv3 hcl3 _ hfu3 _ hup3 _ hm3; c0_hsteps
                · exact hQ 20#64 s3 m3 hinv3 hcl3 (by omega) (Or.inr rfl) (fun _ => hup3 hc) hm3
                exact hJ3 s3 m3 ⟨hinv3, hcl3, by omega, hm3⟩
              · c0_hsteps; exact hJ3 s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rt s2 m2 hinv2 hcl2 _ _ hfu2 _ hut2 hm2
            have hcl2' := hcl2 hcl1
            c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 hcl2' (by omega) (Or.inr rfl) (fun _ => hut2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2', by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hBone; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rb s1 m1 hinv1 hcl1 _ hfu1 _ hub1 hm1; c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 hcl1 hfu1 (Or.inr rfl) (fun _ => hub1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for unified M3 `full_probe(h, initial)` combining M3b's pure-3-CNF dense gate
(`initial || num_binary * 3 >= num_irred`), `m3CongruenceDenseSpec`, `fullSweepDenseSpec`, and M3c's
`if (initial)` initial probing vs `full_probe_tail`. -/
theorem m3_probe_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedProbeDticksSpec a m Q X →
      Γ "full_probe_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hCongD : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X → Func.wp Γ full_probe_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩ => by
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
          s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
        (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ _ _ => by
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun s4 m4 => FullSparseInv c F0 s4 ∧ s4.core.cur_level = 0 ∧
                  s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s4 ⋆ R) m4)
                (fun _ s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩ => by
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FullState)
                    (fun s5 m5 => FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
                      s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s5 ⋆ R) m5)
                    (fun _ s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩ => by
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun s6 m6 => FullSparseInv c F0 s6 ∧ s6.core.cur_level = 0 ∧
                          s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s6 ⋆ R) m6)
                        (fun _ s6 m6 ⟨hinv6, hcl6, hfu6, hm6⟩ => by
                          c0_hsteps
                          let s7 : FullState :=
                            { s6 with scratch := { s6.scratch with
                              fwd_sub_cnt := s6.scratch.search_ticks } }
                          have hinv7 : FullSparseInv c F0 s7 :=
                            m3_sparseInv_with_scratch_keep hinv6 { hinv6.lengths.scratch_ok with }
                              rfl rfl
                          exact hQ 1#64 s7 _ hinv7.lengths hfu6 (Or.inl rfl) (fun h => by cases h)
                            (fun _ => ⟨hinv7, hcl6⟩) hm)
                        (fun J6 hJ6 => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_state0 (α := FullState)
                              (fun sa ma => FullSparseInv c F0 sa ∧ sa.core.cur_level = 0 ∧
                                sa.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sa ⋆ R) ma)
                              (fun _ sa ma ⟨hinva, hcla, hfua, hma⟩ => by
                                c0_hsteps_nogrp
                                refine wp_join_state0 (α := FullState)
                                  (fun sb mb => FullSparseInv c F0 sb ∧ sb.core.cur_level = 0 ∧
                                    sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                                  (fun _ sb mb ⟨hinvb, hclb, hfub, hmb⟩ => by
                                    c0_hsteps; c0_call hMin; intro pbud0 _
                                    c0_hsteps_nogrp; c0_hsplit
                                    · c0_hsteps; c0_call hPRun
                                      refine ⟨c, F0, sb, R, rfl, hinvb, hmb, ?_⟩
                                      intro rp sc mc hinvc hclc _ hfuc _ hupc _ hmc; c0_hsteps
                                      · exact hQ 20#64 sc mc hinvc.lengths (by omega) (Or.inr rfl)
                                          (fun _ => hupc hc) (fun h => by cases h) hmc
                                      exact hJ6 sc mc ⟨hinvc, hclc, by omega, hmc⟩
                                    · c0_hsteps; exact hJ6 sb mb ⟨hinvb, hclb, hfub, hmb⟩)
                                  (fun Jb hJb => by
                                    c0_hsplit
                                    · c0_hsteps; c0_call hTrans
                                      refine ⟨c, F0, sa, R, rfl, hinva, hma, ?_⟩
                                      intro rt sb mb hinvb hclb _ _ hfub _ hutb hmb
                                      have hclb' := hclb hcla
                                      c0_hsteps
                                      · exact hQ 20#64 sb mb hinvb.lengths (by omega) (Or.inr rfl)
                                          (fun _ => hutb hc) (fun h => by cases h) hmb
                                      exact hJb sb mb ⟨hinvb, hclb', by omega, hmb⟩
                                    · c0_hsteps; exact hJb sa ma ⟨hinva, hcla, hfua, hma⟩))
                              (fun Ja hJa => by
                                c0_hsplit
                                · c0_hsteps; c0_call hBone
                                  refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
                                  intro rb sa ma hinva hcla _ hfua _ huba hma; c0_hsteps
                                  · exact hQ 20#64 sa ma hinva.lengths (by omega) (Or.inr rfl)
                                      (fun _ => huba hc) (fun h => by cases h) hma
                                  exact hJa sa ma ⟨hinva, hcla, by omega, hma⟩
                                · c0_hsteps; exact hJa s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩)
                          · c0_hsteps; c0_call hTail
                            refine ⟨c, F0, s5, R, rfl, hinv5, hcl5, hm5, ?_⟩
                            intro rt s6 m6 hinv6 hcl6 hfu6 _ hut6 hm6; c0_hsteps
                            · exact hQ 20#64 s6 m6 hinv6.lengths (by omega) (Or.inr rfl)
                                (fun _ => hut6 hc) (fun h => by cases h) hm6
                            exact hJ6 s6 m6 ⟨hinv6, hcl6, by omega, hm6⟩))
                    (fun J5 hJ5 => by
                      c0_hsplit
                      · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
                        intro rs s5 m5 hinv5 hcl5 hfu5 _ hus5 hm5; c0_hsteps
                        · exact hQ 20#64 s5 m5 hinv5.lengths (by omega) (Or.inr rfl)
                            (fun _ => hus5 hc) (fun h => by cases h) hm5
                        exact hJ5 s5 m5 ⟨hinv5, hcl5, by omega, hm5⟩
                      · c0_hsteps; exact hJ5 s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩))
                (fun J4 hJ4 => by
                  c0_hsplit
                  · c0_hsteps; c0_call hEnter; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
                    intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
                    c0_hsplit
                    · have hden2 : FullDenseInv c F0 s2 := hok_d hc
                      c0_hsteps; c0_call hMin; intro sbud _
                      c0_hsteps; c0_call hCongD; refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
                      intro rc s3 m3 hden3 _ hfu3 _ huc3 hm3
                      have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hfu3]; exact Nat.le_trans hfu2 hfu1
                      c0_hsplit
                      · c0_hsteps; c0_call hReb; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro _ s3r m3r hsp3r _ hfu3r _ _ hm3r; c0_hsteps
                        exact hQ 20#64 s3r m3r hsp3r.lengths (by omega) (Or.inr rfl)
                          (fun _ => huc3 hc) (fun h => by cases h) hm3r
                      · c0_hsteps; c0_call hSweepD; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro rw4 s4 m4 hden4 _ hfu4 _ huw4 hm4
                        c0_hsplit
                        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro _ s4r m4r hsp4r _ hfu4r _ _ hm4r; c0_hsteps
                          exact hQ 20#64 s4r m4r hsp4r.lengths (by omega) (Or.inr rfl)
                            (fun _ => huw4 hc) (fun h => by cases h) hm4r
                        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro rrb s4r m4r hsp4r hcl4r hfu4r _ hurb hm4r; c0_hsteps
                          · exact hQ 20#64 s4r m4r hsp4r.lengths (by omega) (Or.inr rfl)
                              (fun _ => hurb hc) (fun h => by cases h) hm4r
                          exact hJ4 s4r m4r ⟨hsp4r, hcl4r, by omega, hm4r⟩
                    · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
                      c0_hsteps
                      · exact hQ 20#64 s2 m2 hsp2.lengths (by omega) (Or.inr rfl)
                          (fun _ => hsp2.inconsistent_unsat hc) (fun h => by cases h) hm2
                      exact hJ4 s2 m2 ⟨hsp2, hcl2, by omega, hm2⟩
                  · c0_hsteps; exact hJ4 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
            (fun Jd hJd => by c0_hsteps <;> exact hJd _ trivial))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
            intro rs1 s1 m1 hinv1 hcl1 hfu1 _ hus1 hm1; c0_hsteps
            · exact hQ 20#64 s1 m1 hinv1.lengths (by omega) (Or.inr rfl)
                (fun _ => hus1 hc) (fun h => by cases h) hm1
            exact hJ2 s1 m1 ⟨hinv1, hcl1, by omega, hm1⟩
          · c0_hsteps; exact hJ2 s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with probings := s.scratch.probings + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro logp _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        c0_hsteps
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with probe_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          m3_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

end MergedOrchestrators

end LeanQbe.T.Examples.Kissat.FullM3

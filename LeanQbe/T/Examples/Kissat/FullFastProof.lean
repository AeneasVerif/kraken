module

public import LeanQbe.T.Examples.Kissat.FullFast
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
public import LeanQbe.T.Examples.Kissat.FullFastAdapters
public import LeanQbe.T.Examples.Kissat.FullFastTmkLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 Unified Fast Proof (`FullFastProof`, UNSAT-Only, `196/196` Closed)

Assembles the unconditional `196`-function M2 `FullFast` proof (`0` SAT/model proofs):
1. `196`-row `fastSpecTable` / `mkFastEnv` / `fastEnv` / `fastUnsatEnv` aligned 1-to-1 with
   `FullFast.fastFns` (`fastSpecTable_sigs`, `fastSpecTable_noExit` via `t_kernel_rfl`).
2. Headline source-level UNSAT soundness (`fast_solve_bytes_correct`) and concrete `Mem 64`
   UNSAT non-vacuity (`fast_unsat_nonvacuous`, `4096` B work, `fuel = 16`, `XPost := False`).
3. `Func.wp` proofs for all `4` unified M2 orchestrators (`fast_probe_tail_wp`, `fast_probe_wp`,
   `fast_elim_bve_tmk_wp`, `fast_eliminate_wp` including pre-BVE `tarjan_mark` zeroing).
4. Unconditional `196`-row `TableImpl` & `ModuleOk` assembly (`mkFastEnv_tableImpl`,
   `mkFastEnv_moduleOk`, `fastEnv_moduleOk`, `fastUnsatEnv_moduleOk`) discharging all `196 / 196`
   functions (`134` unchanged `Full` + `3` `FastCore` + `13` `FullBvaHeap` + `15` `FullKitten` +
   `9` `FullDefSweep` + `7` `FastBveBudgets` + `12` `FullFastSched` + `3` `FullFast` orchestrators).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFast

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. M2 Cross-Slice Contracts & `196`-Row `fastSpecTable` -/

/-- `TmkZero`-carrying `full_elim_bve` contract wiring `full_eliminate`'s `tmk` zeroing loop into
`FullFastBveBudgets.fullBveVarDefSpec`. -/
def fastElimBveSpec : Spec [i64, i64] [i64] := fun (h, _bve_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ FullFastBveBudgets.TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → FullFastBveBudgets.TmkZero s' →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Unified `196`-row M2 specification table aligned 1-to-1 with `FullFast.fastFns` (flat list for
`O(1)` kernel indexing without nested `take`/`drop` reduction). -/
def fastSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
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
  , ⟨"full_probe_run", [i64, i64], [i64], FullFastBveBudgets.fullProbeRunFastSpec, true⟩
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
  , ⟨"full_cong_hash_step", [i64, i64, i64, i64], [.bool], fullCongHashStepSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullDefSweep.fullCongruenceDenseSpec, true⟩
  , ⟨"full_sweep_cone", [i64, i32], [i64], FullDefSweep.fullSweepConeKittenSpec fastKInv, true⟩
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
  , ⟨"full_probe_tail", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], fastElimBveSpec, true⟩
  , ⟨"full_eliminate", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  , ⟨"full_simplify", [i64, .bool, .bool], [i64], FullFastSched.schedSimplifySpec, true⟩
  , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

def mkFastEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (fastSpecTable mainSpec)

/-- Headline `196`-function UNSAT-only environment for `FullFast.fastModule`. -/
def fastEnv : Env := mkFastEnv fullSolveBytesSpec

/-- Concrete `196`-function UNSAT non-vacuity environment (`fullUnsatWitnessSpec`, `20#64`). -/
def fastUnsatEnv : Env := mkFastEnv fullUnsatWitnessSpec

theorem fastSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ fastSpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (fastSpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem fastSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (fastSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      fastFns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

private theorem fastFns_nodup : (fastFns.map Fn.name).Nodup := by
  have hchk := fast_acyclic
  simp only [fastModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fastSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fastSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fastSpecTable mainSpec).map SpecEntry.name = fastFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fastSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]; exact fastFns_nodup

private theorem mkFastEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fastSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFastEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fastSpecTable_nodup mainSpec) (hno xs m Q X h)

theorem mkFastEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkFastEnv mainSpec f as bs xs m Q X → mkFastEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (fastSpecTable_noExit mainSpec)

theorem fastEnv_noExit :
    ∀ f as bs xs m Q X X', fastEnv f as bs xs m Q X → fastEnv f as bs xs m Q X' :=
  mkFastEnv_noExit fullSolveBytesSpec

theorem fastUnsatEnv_noExit :
    ∀ f as bs xs m Q X X', fastUnsatEnv f as bs xs m Q X → fastUnsatEnv f as bs xs m Q X' :=
  mkFastEnv_noExit fullUnsatWitnessSpec

/-- Headline source-level UNSAT-only soundness of M2 `FullFast` `kissat_solve_bytes` under
canonical `196`-function `fastEnv` (`0` SAT/model proofs). -/
theorem fast_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fastEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  FullFastSched.sched_kissat_solve_bytes_wp fastEnv
    (mkFastEnv_row_at (mainSpec := fullSolveBytesSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullSolveBytesSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullSolveBytesSpec) 192
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullSolveBytesSpec) 194
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullSolveBytesSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullSolveBytesSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under `196`-function `fastUnsatEnv`:
`kissat_solve_bytes` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
with `4096`-byte workspace and `fuel = 16`. -/
theorem fast_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fastUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  FullFastSched.sched_kissat_solve_bytes_core_wp fastUnsatEnv
    (mkFastEnv_row_at (mainSpec := fullUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullUnsatWitnessSpec) 192
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullUnsatWitnessSpec) 194
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullUnsatWitnessSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkFastEnv_row_at (mainSpec := fullUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

/-! ## 2. Unified M2 Orchestrator `Func.wp` Proofs (`4` fns) -/

section FastOrchestrators

open scoped FullArenaTactics

private theorem fast_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem fast_denseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hll' : FullLastLearnedWf { s with scratch := sc' } := fun i hi => by
    change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s
    rw [hll]; exact h.2.2.2.1.1 i hi
  exact ⟨⟨h.lengths.with_scratch hok, F_cur, hw⟩,
    h.2.1, h.2.2.1, ⟨hll', hext ▸ h.2.2.2.1.2⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem fast_denseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hflen : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hlen' : ({ s with core := { s.core with flags := fl' } } : FullState).LengthsOk c :=
    ⟨{ h.lengths.core_ok with flags_len := hflen }, h.lengths.scratch_ok⟩
  exact ⟨⟨hlen', F_cur, { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem fast_max_vars_lt32 (c : FullCfg) : c.max_vars < 2 ^ 32 := by
  have h := c.hmaxv; unfold dimacsBound at h; omega

theorem fast_probe_tail_wp (Γ : Env)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, FullFastBveBudgets.fullProbeRunFastSpec a m Q X →
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
      c0_hsteps; c0_call hMin; intro pbud _
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hMin; intro v1 _
          c0_hsteps; c0_call hMin; intro v0 _
          c0_hsteps; c0_call hViv; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
          intro r3 s3 m3 hinv3 hcl3_imp _ _ hfu3 _ hu3 hm3
          have hcl3 := hcl3_imp hcl2; c0_hsteps
          · exact hQ 20#64 s3 m3 hinv3 hcl3 (by omega) (Or.inr rfl) (fun _ => hu3 hc) hm3
          c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
          intro r4 s4 m4 hinv4 hcl4_imp _ _ hfu4 _ hu4 hm4
          have hcl4 := hcl4_imp hcl3; c0_hsteps
          · exact hQ 20#64 s4 m4 hinv4 hcl4 (by omega) (Or.inr rfl) (fun _ => hu4 hc) hm4
          c0_call hViv; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
          intro r5 s5 m5 hinv5 hcl5_imp _ _ hfu5 _ hu5 hm5
          have hcl5 := hcl5_imp hcl4; c0_hsteps
          · exact hQ 20#64 s5 m5 hinv5 hcl5 (by omega) (Or.inr rfl) (fun _ => hu5 hc) hm5
          exact hQ 1#64 s5 m5 hinv5 hcl5 (by omega) (Or.inl rfl) (fun h => by cases h) hm5)
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rp s2 m2 hinv2 hcl2_imp _ _ hfu2 _ hup2 hm2
            have hcl2 := hcl2_imp hcl1; c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 hcl2 (by omega) (Or.inr rfl) (fun _ => hup2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2, by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rt s1 m1 hinv1 hcl1_imp _ _ hfu1 _ hut1 hm1
        have hcl1 := hcl1_imp hcl0; c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 hcl1 hfu1 (Or.inr rfl) (fun _ => hut1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

theorem fast_probe_wp (Γ : Env)
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
    (hCong : ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
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
                            fast_sparseInv_with_scratch_keep hinv6 { hinv6.lengths.scratch_ok with }
                              rfl rfl
                          exact hQ 1#64 s7 _ hinv7.lengths hfu6 (Or.inl rfl) (fun h => by cases h)
                            (fun _ => ⟨hinv7, hcl6⟩) hm)
                        (fun J6 hJ6 => by
                          c0_hsplit
                          · c0_hsteps; exact hJ6 s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩
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
                      c0_hsteps; c0_call hMin; intro sweep_bud _
                      c0_hsteps; c0_call hCong; refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
                      intro rc s3 m3 hden3 hfu3 _ huc3 hm3
                      c0_hsplit
                      · c0_hsteps; c0_call hReb; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro _ s3r m3r hsp3r _ hfu3r _ _ hm3r; c0_hsteps
                        exact hQ 20#64 s3r m3r hsp3r.lengths (by rw [hfu3] at hfu3r; omega)
                          (Or.inr rfl) (fun _ => huc3 hc) (fun h => by cases h) hm3r
                      · c0_hsteps; c0_call hSweep; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro rs s4 m4 hden4 _ hfu4 _ hus4 hm4
                        c0_hsplit
                        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro _ s4r m4r hsp4r _ hfu4r _ _ hm4r; c0_hsteps
                          exact hQ 20#64 s4r m4r hsp4r.lengths (by rw [hfu3] at hfu4; omega)
                            (Or.inr rfl) (fun _ => hus4 hc) (fun h => by cases h) hm4r
                        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro rr s5 m5 hsp5 hcl5 hfu5 _ hur5 hm5; c0_hsteps
                          · exact hQ 20#64 s5 m5 hsp5.lengths (by rw [hfu3] at hfu4; omega)
                              (Or.inr rfl) (fun _ => hur5 hc) (fun h => by cases h) hm5
                          · exact hJ4 s5 m5 ⟨hsp5, hcl5, by rw [hfu3] at hfu4; omega, hm5⟩
                    · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
                      c0_hsteps
                      · exact hQ 20#64 s2 m2 hsp2.lengths (by omega) (Or.inr rfl)
                          (fun _ => hsp2.inconsistent_unsat hc) (fun h => by cases h) hm2
                      · exact hJ4 s2 m2 ⟨hsp2, hcl2, by omega, hm2⟩
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
          fast_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

theorem fast_elim_bve_tmk_wp (Γ : Env)
    (hBve : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fastElimBveSpec a m Q X →
      Func.wp Γ FullFastSched.full_elim_bve_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hden0, htmk0, hm, hQ⟩
  let cv : Nat := s.core.cur_vars
  have hcv_le_max : cv ≤ c.max_vars := hden0.lengths.core_ok.cur_vars_le
  have hmax_lt32 : c.max_vars < 2 ^ 32 := fast_max_vars_lt32 c
  have hcv_lt64 : cv < 2 ^ 64 := by omega
  unfold Func.wp FullFastSched.full_elim_bve_body
  c0_hsteps_nogrp
  refine wp_while_break_state
    (α := BitVec 64 × BitVec 64 × FullState)
    (β := BitVec 64 × BitVec 64 × BitVec 64 × FullState)
    (fun p => (p.1, p.2.1, p.2.2.1, ()))
    (fun p mb => FullDenseInv c F0 p.2.2.2 ∧ FullFastBveBudgets.TmkZero p.2.2.2 ∧
      p.2.2.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (p.2.2.1 = 1#64 ∨ p.2.2.1 = 20#64) ∧ (p.2.2.1 = 20#64 → F0.Unsat) ∧
      (FullMem c p.2.2.2 ⋆ R) mb)
    (fun p => (p.1, p.2.1, ()))
    (fun p => cv - p.1.toNat)
    (fun p ml => p.1.toNat ≤ cv ∧ cv ≤ p.2.2.core.cur_vars ∧ FullDenseInv c F0 p.2.2 ∧
      FullFastBveBudgets.TmkZero p.2.2 ∧ p.2.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c p.2.2 ⋆ R) ml)
    ?_ ?_ ?_
  · rintro _ ⟨_, _, res, sb⟩ mb ⟨hdenb, htmkb, hfub, hrdom, hru, hmb⟩
    c0_hsteps; exact hQ res sb mb hdenb htmkb hfub hrdom hru hmb
  · rintro B L ⟨v_bv, tried, st⟩ ml hB hL ⟨hv_le, hcv_le, hden_t, htmk_t, hfu_t, hml⟩
    dsimp only at hv_le hcv_le hden_t htmk_t hfu_t hml
    c0_hsplit
    · have hv_lt_cv : v_bv.toNat < cv := by
        have : v_bv.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hcv_lt64] at this; exact this
      have hv_lt_fl : v_bv.toNat < st.core.flags.length := by
        rw [hden_t.lengths.core_ok.flags_len]; omega
      have h2v_lt_vals : (v_bv <<< (1 : Nat)).toNat < st.core.vals.length := by
        rw [hden_t.lengths.core_ok.vals_len, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hv_next_toNat : (v_bv + 1#64).toNat = v_bv.toNat + 1 := by bv_omega
      c0_hsplit
      · c0_hsplit
        · c0_hsplit
          · c0_hsteps
            · let st' : FullState :=
                { st with core :=
                  { st.core with
                    flags := st.core.flags.set v_bv.toNat
                      (st.core.flags[v_bv.toNat] &&& ~~~16#32) } }
              have hden_t' : FullDenseInv c F0 st' :=
                fast_denseInv_with_flags hden_t (by simp [hden_t.lengths.core_ok.flags_len])
              have htmk_t' : FullFastBveBudgets.TmkZero st' := htmk_t.congr rfl rfl
              have hfu_t' : st'.core.fuel = st.core.fuel := rfl
              have hcv_t' : st'.core.cur_vars = st.core.cur_vars := rfl
              have hv32 : (v_bv.setWidth 32).toNat < st'.core.cur_vars := by
                have : (v_bv.setWidth 32).toNat = v_bv.toNat := by bv_omega
                rw [hcv_t']; omega
              c0_call hBve; refine ⟨c, F0, st', R, rfl, hden_t', htmk_t', hv32, hm, ?_⟩
              intro br sb mb hden_b htmk_b hcv_b hfu_b _ hub hmb
              rw [hfu_t'] at hfu_b; rw [hcv_t'] at hcv_b
              c0_hsteps
              · exact hB (v_bv, tried + 1#64, 20#64, sb) mb
                  ⟨hden_b, htmk_b, by dsimp only; omega, Or.inr rfl, (fun _ => hub hc), hmb⟩
              · exact hB (v_bv, tried + 1#64, 1#64, sb) mb
                  ⟨hden_b, htmk_b, by dsimp only; omega, Or.inl rfl, (fun h => by cases h), hmb⟩
              · exact hL (v_bv + 1#64, tried + 1#64, sb) mb
                  (by dsimp only; rw [hv_next_toNat]; omega)
                  ⟨by dsimp only; rw [hv_next_toNat]; omega, Nat.le_trans hcv_le hcv_b,
                    hden_b, htmk_b, by dsimp only; omega, hmb⟩
            · exact hL (v_bv + 1#64, tried, st) ml (by dsimp only; rw [hv_next_toNat]; omega)
                ⟨by dsimp only; rw [hv_next_toNat]; omega, hcv_le, hden_t, htmk_t, hfu_t, hml⟩
            · exact hL (v_bv + 1#64, tried, st) ml (by dsimp only; rw [hv_next_toNat]; omega)
                ⟨by dsimp only; rw [hv_next_toNat]; omega, hcv_le, hden_t, htmk_t, hfu_t, hml⟩
          · c0_hsteps
            exact hB (v_bv, tried, 1#64, st) ml
              ⟨hden_t, htmk_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
        · c0_hsteps
          exact hB (v_bv, tried, 1#64, st) ml
            ⟨hden_t, htmk_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
      · c0_hsteps
        exact hB (v_bv, tried, 1#64, st) ml
          ⟨hden_t, htmk_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
    · c0_hsteps
      exact hB (v_bv, tried, 1#64, st) ml
        ⟨hden_t, htmk_t, hfu_t, Or.inl rfl, (fun h => by cases h), hml⟩
  · intro _ L _ hL; c0_hsteps
    exact hL (0#64, 0#64, s) m ⟨Nat.zero_le _, Nat.le_refl _, hden0, htmk0, Nat.le_refl _, hm⟩

theorem fast_eliminate_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, fastElimBveSpec a m Q X → Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  have hmax_lt32 : c.max_vars < 2 ^ 32 := fast_max_vars_lt32 c
  unfold Func.wp full_eliminate_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, _, hfu0, hm0⟩ => by
      c0_hsteps; c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro ok s1 m1 hcl1 hfu1 hok_d hfail_s hm1
      c0_hsplit
      · have hden1 : FullDenseInv c F0 s1 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps; c0_call hMin; intro fbud _
            c0_hsteps; c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hden1, hm1, ?_⟩
            intro fs s2 m2 hden2 _ hfu2 _ huf2 hm2
            let s2r : FullState :=
              { s2 with scratch := { s2.scratch with fwd_sub_cnt := s1.scratch.fwd_sub_cnt } }
            have hden2r : FullDenseInv c F0 s2r :=
              fast_denseInv_with_scratch_keep hden2 { hden2.lengths.scratch_ok with } rfl rfl
            have hfu2r : s2r.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change s2.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfu2]; omega
            c0_hsplit
            · c0_hsteps; c0_call hReb; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
              intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; c0_hsteps
              exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => huf2 hc) hm3
            · let cv : Nat := s2r.core.cur_vars
              have hcv_le_max : cv ≤ c.max_vars := hden2r.lengths.core_ok.cur_vars_le
              have hcv_lt64 : cv < 2 ^ 64 := by omega
              c0_hsteps_nogrp
              -- Zero `tmk[0 ..< cv)` to establish `TmkZero` for `full_elim_bve`
              refine wp_loop_inv (ts := [i64])
                (fun (ti, ()) mt =>
                  ti.toNat ≤ cv ∧
                  ∃ tmk' : List (BitVec 32), tmk'.length = 2 * c.max_vars ∧
                    (∀ j < ti.toNat, tmk'[j]?.getD 0#32 = 0#32) ∧
                    (FullMem c { s2r with scratch := { s2r.scratch with tarjan_mark := tmk' } } ⋆
                      R) mt)
                (fun (ti, ()) _ => cv - ti.toNat)
                (fun Jt hJt => by
                  c0_hsteps
                  exact hJt (0#64, ()) _ ⟨Nat.zero_le _, s2r.scratch.tarjan_mark,
                    hden2r.lengths.scratch_ok.tarjan_mark_len, fun _ h => by simp at h, hm⟩)
                (fun Jt ⟨ti, ⟨⟩⟩ mt ⟨hti_le, tmk', htmk_len, hzero, hmt⟩ ih => by
                  c0_hsplit
                  · have hti_lt : ti.toNat < cv := by
                      have : ti.toNat < s2r.core.cur_vars % 2 ^ 64 := by assumption
                      rw [Nat.mod_eq_of_lt hcv_lt64] at this; exact this
                    have hti_tmk : ti.toNat < tmk'.length := by rw [htmk_len]; omega
                    have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by bv_omega
                    c0_hsteps
                    refine ih (ti + 1#64, ()) _ (by dsimp only; rw [hti1]; omega)
                      ⟨by rw [hti1]; omega, tmk'.set ti.toNat 0#32, by simp [htmk_len],
                        fun j hj => ?_, hm⟩
                    rw [hti1] at hj
                    by_cases hji : j = ti.toNat
                    · subst hji; rw [List.getElem?_set_self hti_tmk, Option.getD_some]
                    · rw [List.getElem?_set_ne (Ne.symm hji)]; exact hzero j (by omega)
                  · have hti_eq : ti.toNat = cv := by
                      have : ¬ ti.toNat < s2r.core.cur_vars % 2 ^ 64 := by assumption
                      rw [Nat.mod_eq_of_lt hcv_lt64] at this; omega
                    let s2z : FullState :=
                      { s2r with scratch := { s2r.scratch with tarjan_mark := tmk' } }
                    have hden2z : FullDenseInv c F0 s2z :=
                      fast_denseInv_with_scratch_keep hden2r
                        { hden2r.lengths.scratch_ok with tarjan_mark_len := htmk_len } rfl rfl
                    have htmk2z : FullFastBveBudgets.TmkZero s2z :=
                      fun j hj => hzero j (hti_eq.symm ▸ hj)
                    c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                      (fun b => (b, ())) (fun _ => True)
                      (fun _ _ _ => by
                        c0_hsteps; c0_call hMin; intro bve_lim _
                        c0_hsteps; c0_call hBve
                        refine ⟨c, F0, s2z, R, rfl, hden2z, htmk2z, hmt, ?_⟩
                        intro res s3 m3 hden3 _ hfu3 hres_dom hres_u hm3
                        have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
                          change s3.core.fuel.toNat ≤ s2r.core.fuel.toNat at hfu3; omega
                        c0_hsteps_nogrp
                        refine wp_join_state0 (α := FullState)
                          (fun sf mf => FullDenseInv c F0 sf ∧
                            sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                          (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                            c0_hsteps; c0_call hReb; refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                            intro rr se me hspe hcle hfue _ hue hme
                            let se' : FullState :=
                              { se with scratch :=
                                { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                            have hspe' : FullSparseInv c F0 se' :=
                              fast_sparseInv_with_scratch_keep hspe
                                { hspe.lengths.scratch_ok with } rfl rfl
                            have hfue' : se'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              change se.core.fuel.toNat ≤ s.core.fuel.toNat; omega
                            c0_hsteps
                            · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                                (fun _ => hres_u hc) hm
                            · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                                (fun _ => hue hc) hm
                            · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                                (fun _ => hspe'.inconsistent_unsat hc) hm
                            · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                                (fun h => by cases h) hm)
                          (fun Jf hJf => by
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join_state0 (α := FullState)
                                (fun sg mg => FullDenseInv c F0 sg ∧
                                  sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                                (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                                  c0_hsteps_nogrp
                                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                    (fun b => (b, ())) (fun _ => True)
                                    (fun _ _ _ => by
                                      c0_hsteps; c0_call hMin; intro fact_bud _
                                      c0_hsteps; c0_call hFact
                                      refine ⟨c, F0, sg, R, rfl, hdeng, hmg, ?_⟩
                                      intro _ sf mf hdenf _ hfuf _ hmf; c0_hsteps
                                      exact hJf sf mf ⟨hdenf, by rw [hfuf]; omega, hmf⟩)
                                    (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial))
                                (fun Jdo hJdo => by
                                  c0_hsteps
                                  · exact hJdo s3 m3 ⟨hden3, hfu3', hm3⟩
                                  · exact hJdo s3 m3 ⟨hden3, hfu3', hm3⟩
                                  · exact hJf s3 m3 ⟨hden3, hfu3', hm3⟩)
                            · c0_hsteps; exact hJf s3 m3 ⟨hden3, hfu3', hm3⟩))
                      (fun Jb hJb => by c0_hsteps <;> exact hJb _ trivial)))
          (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial)
      · have hsp1 : FullSparseInv c F0 s1 := hfail_s hc
        let s1' : FullState :=
          { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
        have hsp1' : FullSparseInv c F0 s1' :=
          fast_sparseInv_with_scratch_keep hsp1 { hsp1.lengths.scratch_ok with } rfl rfl
        have hfu1' : s1'.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s1.core.fuel.toNat ≤ s.core.fuel.toNat; omega
        c0_hsteps
        · exact hQ 20#64 s1' _ hsp1' hcl1 hfu1' (Or.inr rfl)
            (fun _ => hsp1'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s1' _ hsp1' hcl1 hfu1' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with eliminations := s.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro loge _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          fast_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        let s0c : FullState :=
          { s0b with scratch :=
            { s0b.scratch with elim_bound := s0b.scratch.elim_bound + 2#64 } }
        have hinv0c : FullSparseInv c F0 s0c :=
          fast_sparseInv_with_scratch_keep hinv0b { hinv0b.lengths.scratch_ok with } rfl rfl
        c0_hsteps
        · exact hJ1 s0c _ ⟨hinv0c, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

end FastOrchestrators

/-! ## 3. Unconditional `196`-Row `TableImpl` & `ModuleOk` Assembly (`196/196` closed) -/

/-- Indices of the `3` `FastCore` BCP functions (`[47..49]`). -/
def fastCoreIndices : List Nat := [47, 48, 49]

/-- Indices of the `15` `FullKitten` mini-CDCL functions (`[128..142]`). -/
def fastKittenIndices : List Nat :=
  [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]

/-- Indices of the `9` `FullDefSweep` gate/congruence/sweep functions. -/
def fastDefSweepIndices : List Nat := [150, 152, 153, 154, 155, 156, 161, 162, 163]

/-- Indices of the `13` `FullBvaHeap` BVA/heap factoring functions (`[170..182]`). -/
def fastBvaHeapIndices : List Nat :=
  [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

private theorem fast_tableImpl_step {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    {i : Nat} {fn : Fn} {e : SpecEntry}
    (hf : fs[i]? = some fn) (he : tbl[i]? = some e)
    (himpl : SpecEntry.Impl Γ fn e)
    (hrest : TableImpl Γ (fs.drop (i + 1)) (tbl.drop (i + 1))) :
    TableImpl Γ (fs.drop i) (tbl.drop i) := by
  have hfi : i < fs.length := (List.getElem?_eq_some_iff.mp hf).1
  have hei : i < tbl.length := (List.getElem?_eq_some_iff.mp he).1
  rw [List.drop_eq_getElem_cons hfi, List.drop_eq_getElem_cons hei]
  have hfe : fs[i]'hfi = fn := Option.some.inj ((List.getElem?_eq_getElem hfi).symm.trans hf)
  have hee : tbl[i]'hei = e := Option.some.inj ((List.getElem?_eq_getElem hei).symm.trans he)
  rw [hfe, hee]
  exact ⟨himpl, hrest⟩

private theorem fast_tableImpl_nil (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    TableImpl (mkFastEnv mainSpec) (fastFns.drop 196) ((fastSpecTable mainSpec).drop 196) := by
  rw [List.drop_of_length_le (by rw [fastFns_length]; omega),
    List.drop_of_length_le (Nat.le_refl 196 : (fastSpecTable mainSpec).length ≤ 196)]
  trivial

/-! ### Fast `O(1)` `fastFns[i]?` slice lemmas (zero unfolding of `Full.fullFns`) -/

private theorem fullFns_len' : Full.fullFns.length = 166 := by t_kernel_rfl
private theorem fastCore_len' : FastCore.fastCore_fns.length = 3 := by t_kernel_rfl
private theorem bveBudgets_len' : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by
  t_kernel_rfl
private theorem sched_len' : FullFastSched.sched_fns.length = 15 := by t_kernel_rfl
private theorem kitten_len' : Full.fullKitten_fns.length = 15 := by t_kernel_rfl
private theorem defSweep_len' : FullDefSweep.full_def_sweep_fns.length = 9 := by t_kernel_rfl
private theorem bvaHeap_len' : FullBvaHeap.bvaHeap_fns.length = 13 := by t_kernel_rfl
private theorem fastOrch_len' : fastOrch_fns.length = 3 := by t_kernel_rfl

private theorem drop_append_l {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by subst h; simp

private theorem getElem?_of_take' {α : Type _} {xs src : List α} {len i : Nat}
    (htake : xs.take len = src.take len) (hi : i < len) : xs[i]? = src[i]? := by
  have h := congrArg (·[i]?) htake
  simpa only [List.getElem?_take, hi, ↓reduceIte] using h

private theorem getElem?_of_slice' {α : Type _} {xs src : List α} {k len d i : Nat}
    (hslice : (xs.drop k).take len = (src.drop d).take len) (h1 : k ≤ i) (h2 : i < k + len) :
    xs[i]? = src[d + (i - k)]? := by
  have h := congrArg (·[i - k]?) hslice
  simp only [List.getElem?_take, List.getElem?_drop, show i - k < len by omega, ↓reduceIte] at h
  rwa [show k + (i - k) = i by omega] at h

private theorem fastFns_drop_111_eq :
    fastFns.drop 111 =
      (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
      (Full.fullFns.drop 112).take 1 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
      (Full.fullFns.drop 114).take 5 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
      (Full.fullFns.drop 120).take 1 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
      (Full.fullFns.drop 122).take 3 ++
      (FullFastSched.sched_fns.drop 1).take 2 ++
      (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix := by
  have h111 : (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
      (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
      (Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1 ++
      (Full.fullFns.drop 58).take 53).length = 111 := by
    simp [fullFns_len', bveBudgets_len', fastCore_len', sched_len']
  have heq : fastFns =
      (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
        (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
        (Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1 ++
        (Full.fullFns.drop 58).take 53) ++
      ((FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
       (Full.fullFns.drop 112).take 1 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
       (Full.fullFns.drop 114).take 5 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
       (Full.fullFns.drop 120).take 1 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
       (Full.fullFns.drop 122).take 3 ++
       (FullFastSched.sched_fns.drop 1).take 2 ++
       (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  rw [heq, drop_append_l h111]

private theorem fastFns_drop_143_eq :
    fastFns.drop 143 =
      (Full.fullFns.drop 128).take 7 ++
      (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
      (Full.fullFns.drop 136).take 1 ++
      FullDefSweep.full_def_sweep_fns.drop 4 ++
      (Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
      (Full.fullFns.drop 148).take 1 ++
      FullDefSweep.full_def_sweep_fns.take 3 ++
      (Full.fullFns.drop 151).take 5 ++
      FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
      FullBvaHeap.bvaHeap_fns ++
      (FullFastSched.sched_fns.drop 3).take 4 ++
      fastOrch_fns.take 2 ++
      (FullFastSched.sched_fns.drop 9).take 2 ++
      fastOrch_fns.drop 2 ++
      FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165 := by
  have heq : fastFnsSuffix = Full.fullKitten_fns ++
      ((Full.fullFns.drop 128).take 7 ++
       (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
       (Full.fullFns.drop 136).take 1 ++ FullDefSweep.full_def_sweep_fns.drop 4 ++
       (Full.fullFns.drop 145).take 2 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
       (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
       (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
       FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
       fastOrch_fns.take 2 ++ (FullFastSched.sched_fns.drop 9).take 2 ++
       fastOrch_fns.drop 2 ++ FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165) := by
    simp only [fastFnsSuffix, List.append_assoc]
  rw [fastFns, show 143 = 128 + 15 from rfl, ← List.drop_drop,
    drop_append_l fastFnsPrefix_length, heq, drop_append_l kitten_len']

private theorem fastFns_drop_157_eq :
    fastFns.drop 157 =
      (Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
      (Full.fullFns.drop 148).take 1 ++
      FullDefSweep.full_def_sweep_fns.take 3 ++
      (Full.fullFns.drop 151).take 5 ++
      FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
      FullBvaHeap.bvaHeap_fns ++
      (FullFastSched.sched_fns.drop 3).take 4 ++
      fastOrch_fns.take 2 ++
      (FullFastSched.sched_fns.drop 9).take 2 ++
      fastOrch_fns.drop 2 ++
      FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165 := by
  have h14 : ((Full.fullFns.drop 128).take 7 ++
      (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
      (Full.fullFns.drop 136).take 1 ++
      FullDefSweep.full_def_sweep_fns.drop 4).length = 14 := by
    simp [fullFns_len', defSweep_len']
  rw [show 157 = 143 + 14 from rfl, ← List.drop_drop, fastFns_drop_143_eq]
  have heq :
      (Full.fullFns.drop 128).take 7 ++
      (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
      (Full.fullFns.drop 136).take 1 ++ FullDefSweep.full_def_sweep_fns.drop 4 ++
      (Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
      (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
      (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
      FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
      fastOrch_fns.take 2 ++ (FullFastSched.sched_fns.drop 9).take 2 ++
      fastOrch_fns.drop 2 ++ FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165 =
      ((Full.fullFns.drop 128).take 7 ++
        (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
        (Full.fullFns.drop 136).take 1 ++ FullDefSweep.full_def_sweep_fns.drop 4) ++
      ((Full.fullFns.drop 145).take 2 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
       (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
       (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
       FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
       fastOrch_fns.take 2 ++ (FullFastSched.sched_fns.drop 9).take 2 ++
       fastOrch_fns.drop 2 ++ FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165) := by
    simp only [List.append_assoc]
  rw [heq, drop_append_l h14]

private theorem fastFns_drop_183_eq :
    fastFns.drop 183 =
      (FullFastSched.sched_fns.drop 3).take 4 ++
      fastOrch_fns.take 2 ++
      (FullFastSched.sched_fns.drop 9).take 2 ++
      fastOrch_fns.drop 2 ++
      FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165 := by
  have h26 : ((Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
      (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
      (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
      FullBvaHeap.bvaHeap_fns).length = 26 := by
    simp [fullFns_len', bveBudgets_len', defSweep_len', bvaHeap_len']
  rw [show 183 = 157 + 26 from rfl, ← List.drop_drop, fastFns_drop_157_eq]
  have heq :
      (Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
      (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
      (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
      FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
      fastOrch_fns.take 2 ++ (FullFastSched.sched_fns.drop 9).take 2 ++
      fastOrch_fns.drop 2 ++ FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165 =
      ((Full.fullFns.drop 145).take 2 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
        (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
        (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
        FullBvaHeap.bvaHeap_fns) ++
      ((FullFastSched.sched_fns.drop 3).take 4 ++ fastOrch_fns.take 2 ++
       (FullFastSched.sched_fns.drop 9).take 2 ++ fastOrch_fns.drop 2 ++
       FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165) := by
    simp only [List.append_assoc]
  rw [heq, drop_append_l h26]

private theorem ff_0_36 {i : Nat} {fn : Fn} (hi : i < 36 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : fastFns[i]? = some fn :=
  (getElem?_of_take' fastFns_take_36 hi).trans h

private theorem ff_36 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[0]? = some fn := by rfl) :
    fastFns[36]? = some fn := by
  have h1 : fastFns[36]? = FullFastBveBudgets.fastBveBudgets_fns[0]? := by
    unfold fastFns fastFnsPrefix
    simp only [List.append_assoc, List.getElem?_append, List.length_take, fullFns_len',
      bveBudgets_len', show min 36 166 = 36 from rfl, show min 1 7 = 1 from rfl,
      show ¬(36 < 36) by omega, show 36 - 36 < 1 by omega, ↓reduceIte, List.getElem?_take]
  exact h1.trans h

private theorem ff_37_47 {i : Nat} {fn : Fn} (h1 : 37 ≤ i := by omega) (h2 : i < 47 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : fastFns[i]? = some fn := by
  have heq := getElem?_of_slice' fastFns_slice_37_47 h1 h2
  rw [show 37 + (i - 37) = i by omega] at heq
  exact heq.trans h

private theorem ff_47_50 {i : Nat} {fn : Fn} (h1 : 47 ≤ i := by omega) (h2 : i < 50 := by omega)
    (h : FastCore.fastCore_fns[i - 47]? = some fn := by rfl) : fastFns[i]? = some fn := by
  have h47 : (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
      (Full.fullFns.drop 37).take 10).length = 47 := by
    simp [fullFns_len', bveBudgets_len']
  have heq : fastFns =
      (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
        (Full.fullFns.drop 37).take 10) ++
      (FastCore.fastCore_fns ++
       ((Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1 ++
        (Full.fullFns.drop 58).take 53 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
        (Full.fullFns.drop 112).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
        (Full.fullFns.drop 114).take 5 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
        (Full.fullFns.drop 120).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
        (Full.fullFns.drop 122).take 3 ++
        (FullFastSched.sched_fns.drop 1).take 2 ++
        (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix)) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  have hd : (fastFns.drop 47)[i - 47]? = FastCore.fastCore_fns[i - 47]? := by
    rw [heq, drop_append_l h47, List.getElem?_append_left (by rw [fastCore_len']; omega)]
  simp only [List.getElem?_drop, show 47 + (i - 47) = i by omega] at hd
  exact hd.trans h

private theorem ff_50_57 {i : Nat} {fn : Fn} (h1 : 50 ≤ i := by omega) (h2 : i < 57 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : fastFns[i]? = some fn := by
  have heq := getElem?_of_slice' fastFns_slice_50_57 h1 h2
  rw [show 50 + (i - 50) = i by omega] at heq
  exact heq.trans h

private theorem ff_57 {fn : Fn}
    (h : FullFastSched.sched_fns[0]? = some fn := by rfl) : fastFns[57]? = some fn := by
  have h57 : (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
      (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
      (Full.fullFns.drop 50).take 7).length = 57 := by
    simp [fullFns_len', bveBudgets_len', fastCore_len']
  have heq : fastFns =
      (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
        (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
        (Full.fullFns.drop 50).take 7) ++
      (FullFastSched.sched_fns.take 1 ++
       ((Full.fullFns.drop 58).take 53 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
        (Full.fullFns.drop 112).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
        (Full.fullFns.drop 114).take 5 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
        (Full.fullFns.drop 120).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
        (Full.fullFns.drop 122).take 3 ++
        (FullFastSched.sched_fns.drop 1).take 2 ++
        (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix)) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  have hd : (fastFns.drop 57)[0]? = FullFastSched.sched_fns[0]? := by
    rw [heq, drop_append_l h57]
    simp only [List.getElem?_append, List.length_take, sched_len',
      show min 1 15 = 1 from rfl, show 0 < 1 by omega, ↓reduceIte, List.getElem?_take]
  simpa only [List.getElem?_drop, Nat.add_zero] using hd.trans h

private theorem ff_58_111 {i : Nat} {fn : Fn} (h1 : 58 ≤ i := by omega) (h2 : i < 111 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : fastFns[i]? = some fn := by
  have heq := getElem?_of_slice' fastFns_slice_58_111 h1 h2
  rw [show 58 + (i - 58) = i by omega] at heq
  exact heq.trans h

private theorem ff_d111 {k : Nat} {fn : Fn}
    (h : ((FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
      (Full.fullFns.drop 112).take 1 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
      (Full.fullFns.drop 114).take 5 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
      (Full.fullFns.drop 120).take 1 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
      (Full.fullFns.drop 122).take 3 ++
      (FullFastSched.sched_fns.drop 1).take 2 ++
      (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix)[k]? = some fn) :
    fastFns[111 + k]? = some fn := by
  have hd := congrArg (·[k]?) fastFns_drop_111_eq
  simpa only [List.getElem?_drop] using hd.trans h

private theorem ff_111 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[1]? = some fn := by rfl) :
    fastFns[111]? = some fn :=
  ff_d111 (k := 0) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', show min 1 (7 - 1) = 1 from rfl, show 0 < 1 by omega, ↓reduceIte,
      List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_112 {fn : Fn} (h : Full.fullFns[112]? = some fn := by rfl) :
    fastFns[112]? = some fn :=
  ff_d111 (k := 1) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
      show min 1 (166 - 112) = 1 from rfl, show ¬(1 < 1) by omega, show 1 - 1 < 1 by omega,
      ↓reduceIte, List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_113 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[2]? = some fn := by rfl) :
    fastFns[113]? = some fn :=
  ff_d111 (k := 2) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
      show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
      show ¬(2 < 1) by omega, show ¬(2 - 1 < 1) by omega, show 2 - 1 - 1 < 1 by omega,
      ↓reduceIte, List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_114_119 {i : Nat} {fn : Fn} (h1 : 114 ≤ i := by omega)
    (h2 : i < 119 := by omega) (h : Full.fullFns[i]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  rw [show i = 111 + (i - 111) by omega]
  refine ff_d111 (k := i - 111) ?_
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
    show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl,
    show ¬(i - 111 < 1) by omega, show ¬(i - 111 - 1 < 1) by omega,
    show ¬(i - 111 - 1 - 1 < 1) by omega, show i - 111 - 1 - 1 - 1 < 5 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 114 + (i - 111 - 1 - 1 - 1) = i by omega]; exact h

private theorem ff_119 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[3]? = some fn := by rfl) :
    fastFns[119]? = some fn :=
  ff_d111 (k := 8) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
      show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
      show min 5 (166 - 114) = 5 from rfl, show min 1 (7 - 3) = 1 from rfl,
      show ¬(8 < 1) by omega, show ¬(8 - 1 < 1) by omega, show ¬(8 - 1 - 1 < 1) by omega,
      show ¬(8 - 1 - 1 - 1 < 5) by omega, show 8 - 1 - 1 - 1 - 5 < 1 by omega,
      ↓reduceIte, List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_120 {fn : Fn} (h : Full.fullFns[120]? = some fn := by rfl) :
    fastFns[120]? = some fn :=
  ff_d111 (k := 9) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
      show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
      show min 5 (166 - 114) = 5 from rfl, show min 1 (7 - 3) = 1 from rfl,
      show min 1 (166 - 120) = 1 from rfl,
      show ¬(9 < 1) by omega, show ¬(9 - 1 < 1) by omega, show ¬(9 - 1 - 1 < 1) by omega,
      show ¬(9 - 1 - 1 - 1 < 5) by omega, show ¬(9 - 1 - 1 - 1 - 5 < 1) by omega,
      show 9 - 1 - 1 - 1 - 5 - 1 < 1 by omega,
      ↓reduceIte, List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_121 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[4]? = some fn := by rfl) :
    fastFns[121]? = some fn :=
  ff_d111 (k := 10) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
      show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
      show min 5 (166 - 114) = 5 from rfl, show min 1 (7 - 3) = 1 from rfl,
      show min 1 (166 - 120) = 1 from rfl, show min 1 (7 - 4) = 1 from rfl,
      show ¬(10 < 1) by omega, show ¬(10 - 1 < 1) by omega, show ¬(10 - 1 - 1 < 1) by omega,
      show ¬(10 - 1 - 1 - 1 < 5) by omega, show ¬(10 - 1 - 1 - 1 - 5 < 1) by omega,
      show ¬(10 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
      show 10 - 1 - 1 - 1 - 5 - 1 - 1 < 1 by omega,
      ↓reduceIte, List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_122_125 {i : Nat} {fn : Fn} (h1 : 122 ≤ i := by omega)
    (h2 : i < 125 := by omega) (h : Full.fullFns[i]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  rw [show i = 111 + (i - 111) by omega]
  refine ff_d111 (k := i - 111) ?_
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    bveBudgets_len', fullFns_len', show min 1 (7 - 1) = 1 from rfl,
    show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (7 - 3) = 1 from rfl,
    show min 1 (166 - 120) = 1 from rfl, show min 1 (7 - 4) = 1 from rfl,
    show min 3 (166 - 122) = 3 from rfl,
    show ¬(i - 111 < 1) by omega, show ¬(i - 111 - 1 < 1) by omega,
    show ¬(i - 111 - 1 - 1 < 1) by omega, show ¬(i - 111 - 1 - 1 - 1 < 5) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 < 1) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 - 1 - 1 < 1) by omega,
    show i - 111 - 1 - 1 - 1 - 5 - 1 - 1 - 1 < 3 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 122 + (i - 111 - 1 - 1 - 1 - 5 - 1 - 1 - 1) = i by omega]; exact h

private theorem ff_125_127 {i : Nat} {fn : Fn} (h1 : 125 ≤ i := by omega)
    (h2 : i < 127 := by omega)
    (h : FullFastSched.sched_fns[1 + (i - 125)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  rw [show i = 111 + (i - 111) by omega]
  refine ff_d111 (k := i - 111) ?_
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    bveBudgets_len', fullFns_len', sched_len', show min 1 (7 - 1) = 1 from rfl,
    show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (7 - 3) = 1 from rfl,
    show min 1 (166 - 120) = 1 from rfl, show min 1 (7 - 4) = 1 from rfl,
    show min 3 (166 - 122) = 3 from rfl, show min 2 (15 - 1) = 2 from rfl,
    show ¬(i - 111 < 1) by omega, show ¬(i - 111 - 1 < 1) by omega,
    show ¬(i - 111 - 1 - 1 < 1) by omega, show ¬(i - 111 - 1 - 1 - 1 < 5) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 < 1) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 - 1 - 1 < 1) by omega,
    show ¬(i - 111 - 1 - 1 - 1 - 5 - 1 - 1 - 1 < 3) by omega,
    show i - 111 - 1 - 1 - 1 - 5 - 1 - 1 - 1 - 3 < 2 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 1 + (i - 111 - 1 - 1 - 1 - 5 - 1 - 1 - 1 - 3) = 1 + (i - 125) by omega]; exact h

private theorem ff_127 {fn : Fn} (h : Full.fullFns[127]? = some fn := by rfl) :
    fastFns[127]? = some fn :=
  ff_d111 (k := 16) (by
    simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
      bveBudgets_len', fullFns_len', sched_len', show min 1 (7 - 1) = 1 from rfl,
      show min 1 (166 - 112) = 1 from rfl, show min 1 (7 - 2) = 1 from rfl,
      show min 5 (166 - 114) = 5 from rfl, show min 1 (7 - 3) = 1 from rfl,
      show min 1 (166 - 120) = 1 from rfl, show min 1 (7 - 4) = 1 from rfl,
      show min 3 (166 - 122) = 3 from rfl, show min 2 (15 - 1) = 2 from rfl,
      show min 1 (166 - 127) = 1 from rfl,
      show ¬(16 < 1) by omega, show ¬(16 - 1 < 1) by omega, show ¬(16 - 1 - 1 < 1) by omega,
      show ¬(16 - 1 - 1 - 1 < 5) by omega, show ¬(16 - 1 - 1 - 1 - 5 < 1) by omega,
      show ¬(16 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
      show ¬(16 - 1 - 1 - 1 - 5 - 1 - 1 < 1) by omega,
      show ¬(16 - 1 - 1 - 1 - 5 - 1 - 1 - 1 < 3) by omega,
      show ¬(16 - 1 - 1 - 1 - 5 - 1 - 1 - 1 - 3 < 2) by omega,
      show 16 - 1 - 1 - 1 - 5 - 1 - 1 - 1 - 3 - 2 < 1 by omega,
      ↓reduceIte, List.getElem?_take, List.getElem?_drop]; exact h)

private theorem ff_128_143 {i : Nat} {fn : Fn} (h1 : 128 ≤ i := by omega)
    (h2 : i < 143 := by omega) (h : Full.fullKitten_fns[i - 128]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd : (fastFns.drop 128)[i - 128]? = Full.fullKitten_fns[i - 128]? := by
    rw [fastFns, drop_append_l fastFnsPrefix_length]
    unfold fastFnsSuffix
    simp only [List.append_assoc]
    exact List.getElem?_append_left (by rw [kitten_len']; omega)
  simp only [List.getElem?_drop, show 128 + (i - 128) = i by omega] at hd
  exact hd.trans h

private theorem ff_143_150 {i : Nat} {fn : Fn} (h1 : 143 ≤ i := by omega)
    (h2 : i < 150 := by omega) (h : Full.fullFns[128 + (i - 143)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 143]?) fastFns_drop_143_eq
  simp only [List.getElem?_drop, show 143 + (i - 143) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', show min 7 (166 - 128) = 7 from rfl, show i - 143 < 7 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_150 {fn : Fn} (h : FullDefSweep.full_def_sweep_fns[3]? = some fn := by rfl) :
    fastFns[150]? = some fn := by
  have hd := congrArg (·[7]?) fastFns_drop_143_eq
  simp only [List.getElem?_drop] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', defSweep_len', show min 7 (166 - 128) = 7 from rfl,
    show min 1 (9 - 3) = 1 from rfl, show ¬(7 < 7) by omega, show 7 - 7 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_151 {fn : Fn} (h : Full.fullFns[136]? = some fn := by rfl) :
    fastFns[151]? = some fn := by
  have hd := congrArg (·[8]?) fastFns_drop_143_eq
  simp only [List.getElem?_drop] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', defSweep_len', show min 7 (166 - 128) = 7 from rfl,
    show min 1 (9 - 3) = 1 from rfl, show min 1 (166 - 136) = 1 from rfl,
    show ¬(8 < 7) by omega, show ¬(8 - 7 < 1) by omega, show 8 - 7 - 1 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_152_157 {i : Nat} {fn : Fn} (h1 : 152 ≤ i := by omega)
    (h2 : i < 157 := by omega)
    (h : FullDefSweep.full_def_sweep_fns[4 + (i - 152)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 143]?) fastFns_drop_143_eq
  simp only [List.getElem?_drop, show 143 + (i - 143) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', defSweep_len', show min 7 (166 - 128) = 7 from rfl,
    show min 1 (9 - 3) = 1 from rfl, show min 1 (166 - 136) = 1 from rfl,
    show ¬(i - 143 < 7) by omega, show ¬(i - 143 - 7 < 1) by omega,
    show ¬(i - 143 - 7 - 1 < 1) by omega, show i - 143 - 7 - 1 - 1 < 9 - 4 by omega,
    ↓reduceIte, List.getElem?_drop]
  rw [show 4 + (i - 143 - 7 - 1 - 1) = 4 + (i - 152) by omega]; exact h

private theorem ff_157_159 {i : Nat} {fn : Fn} (h1 : 157 ≤ i := by omega)
    (h2 : i < 159 := by omega) (h : Full.fullFns[145 + (i - 157)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 157]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop, show 157 + (i - 157) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', show min 2 (166 - 145) = 2 from rfl, show i - 157 < 2 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_159 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[5]? = some fn := by rfl) :
    fastFns[159]? = some fn := by
  have hd := congrArg (·[2]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', bveBudgets_len', show min 2 (166 - 145) = 2 from rfl,
    show min 1 (7 - 5) = 1 from rfl, show ¬(2 < 2) by omega, show 2 - 2 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_160 {fn : Fn} (h : Full.fullFns[148]? = some fn := by rfl) :
    fastFns[160]? = some fn := by
  have hd := congrArg (·[3]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', bveBudgets_len', show min 2 (166 - 145) = 2 from rfl,
    show min 1 (7 - 5) = 1 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show ¬(3 < 2) by omega, show ¬(3 - 2 < 1) by omega, show 3 - 2 - 1 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_161_164 {i : Nat} {fn : Fn} (h1 : 161 ≤ i := by omega)
    (h2 : i < 164 := by omega)
    (h : FullDefSweep.full_def_sweep_fns[i - 161]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 157]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop, show 157 + (i - 157) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', bveBudgets_len', defSweep_len', show min 2 (166 - 145) = 2 from rfl,
    show min 1 (7 - 5) = 1 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 3 9 = 3 from rfl,
    show ¬(i - 157 < 2) by omega, show ¬(i - 157 - 2 < 1) by omega,
    show ¬(i - 157 - 2 - 1 < 1) by omega, show i - 157 - 2 - 1 - 1 < 3 by omega,
    ↓reduceIte, List.getElem?_take]
  rw [show i - 157 - 2 - 1 - 1 = i - 161 by omega]; exact h

private theorem ff_164_169 {i : Nat} {fn : Fn} (h1 : 164 ≤ i := by omega)
    (h2 : i < 169 := by omega) (h : Full.fullFns[151 + (i - 164)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 157]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop, show 157 + (i - 157) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', bveBudgets_len', defSweep_len', show min 2 (166 - 145) = 2 from rfl,
    show min 1 (7 - 5) = 1 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 3 9 = 3 from rfl, show min 5 (166 - 151) = 5 from rfl,
    show ¬(i - 157 < 2) by omega, show ¬(i - 157 - 2 < 1) by omega,
    show ¬(i - 157 - 2 - 1 < 1) by omega, show ¬(i - 157 - 2 - 1 - 1 < 3) by omega,
    show i - 157 - 2 - 1 - 1 - 3 < 5 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 151 + (i - 157 - 2 - 1 - 1 - 3) = 151 + (i - 164) by omega]; exact h

private theorem ff_169 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[6]? = some fn := by rfl) :
    fastFns[169]? = some fn := by
  have hd := congrArg (·[12]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', bveBudgets_len', defSweep_len', show min 2 (166 - 145) = 2 from rfl,
    show min 1 (7 - 5) = 1 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 3 9 = 3 from rfl, show min 5 (166 - 151) = 5 from rfl,
    show ¬(12 < 2) by omega, show ¬(12 - 2 < 1) by omega, show ¬(12 - 2 - 1 < 1) by omega,
    show ¬(12 - 2 - 1 - 1 < 3) by omega, show ¬(12 - 2 - 1 - 1 - 3 < 5) by omega,
    show 12 - 2 - 1 - 1 - 3 - 5 < 7 - 6 by omega,
    ↓reduceIte, List.getElem?_drop]
  exact h

private theorem ff_170_183 {i : Nat} {fn : Fn} (h1 : 170 ≤ i := by omega)
    (h2 : i < 183 := by omega) (h : FullBvaHeap.bvaHeap_fns[i - 170]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 157]?) fastFns_drop_157_eq
  simp only [List.getElem?_drop, show 157 + (i - 157) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', bveBudgets_len', defSweep_len', bvaHeap_len',
    show min 2 (166 - 145) = 2 from rfl, show min 1 (7 - 5) = 1 from rfl,
    show min 1 (166 - 148) = 1 from rfl, show min 3 9 = 3 from rfl,
    show min 5 (166 - 151) = 5 from rfl,
    show ¬(i - 157 < 2) by omega, show ¬(i - 157 - 2 < 1) by omega,
    show ¬(i - 157 - 2 - 1 < 1) by omega, show ¬(i - 157 - 2 - 1 - 1 < 3) by omega,
    show ¬(i - 157 - 2 - 1 - 1 - 3 < 5) by omega,
    show ¬(i - 157 - 2 - 1 - 1 - 3 - 5 < 7 - 6) by omega,
    show i - 157 - 2 - 1 - 1 - 3 - 5 - (7 - 6) < 13 by omega, ↓reduceIte]
  rw [show i - 157 - 2 - 1 - 1 - 3 - 5 - (7 - 6) = i - 170 by omega]; exact h

private theorem ff_183_187 {i : Nat} {fn : Fn} (h1 : 183 ≤ i := by omega)
    (h2 : i < 187 := by omega)
    (h : FullFastSched.sched_fns[3 + (i - 183)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 183]?) fastFns_drop_183_eq
  simp only [List.getElem?_drop, show 183 + (i - 183) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    sched_len', show min 4 (15 - 3) = 4 from rfl, show i - 183 < 4 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  exact h

private theorem ff_187_189 {i : Nat} {fn : Fn} (h1 : 187 ≤ i := by omega)
    (h2 : i < 189 := by omega) (h : fastOrch_fns[i - 187]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 183]?) fastFns_drop_183_eq
  simp only [List.getElem?_drop, show 183 + (i - 183) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    sched_len', fastOrch_len', show min 4 (15 - 3) = 4 from rfl, show min 2 3 = 2 from rfl,
    show ¬(i - 183 < 4) by omega, show i - 183 - 4 < 2 by omega, ↓reduceIte, List.getElem?_take]
  rw [show i - 183 - 4 = i - 187 by omega]; exact h

private theorem ff_189_191 {i : Nat} {fn : Fn} (h1 : 189 ≤ i := by omega)
    (h2 : i < 191 := by omega)
    (h : FullFastSched.sched_fns[9 + (i - 189)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 183]?) fastFns_drop_183_eq
  simp only [List.getElem?_drop, show 183 + (i - 183) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    sched_len', fastOrch_len', show min 4 (15 - 3) = 4 from rfl, show min 2 3 = 2 from rfl,
    show min 2 (15 - 9) = 2 from rfl, show ¬(i - 183 < 4) by omega,
    show ¬(i - 183 - 4 < 2) by omega, show i - 183 - 4 - 2 < 2 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 9 + (i - 183 - 4 - 2) = 9 + (i - 189) by omega]; exact h

private theorem ff_191 {fn : Fn} (h : fastOrch_fns[2]? = some fn := by rfl) :
    fastFns[191]? = some fn := by
  have hd := congrArg (·[8]?) fastFns_drop_183_eq
  simp only [List.getElem?_drop] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    sched_len', fastOrch_len', show min 4 (15 - 3) = 4 from rfl, show min 2 3 = 2 from rfl,
    show min 2 (15 - 9) = 2 from rfl, show ¬(8 < 4) by omega, show ¬(8 - 4 < 2) by omega,
    show ¬(8 - 4 - 2 < 2) by omega, show 8 - 4 - 2 - 2 < 3 - 2 by omega, ↓reduceIte,
    List.getElem?_drop]
  exact h

private theorem ff_192_195 {i : Nat} {fn : Fn} (h1 : 192 ≤ i := by omega)
    (h2 : i < 195 := by omega)
    (h : FullFastSched.sched_fns[12 + (i - 192)]? = some fn := by rfl) :
    fastFns[i]? = some fn := by
  have hd := congrArg (·[i - 183]?) fastFns_drop_183_eq
  simp only [List.getElem?_drop, show 183 + (i - 183) = i by omega] at hd
  rw [hd]
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    sched_len', fastOrch_len', show min 4 (15 - 3) = 4 from rfl, show min 2 3 = 2 from rfl,
    show min 2 (15 - 9) = 2 from rfl, show ¬(i - 183 < 4) by omega,
    show ¬(i - 183 - 4 < 2) by omega, show ¬(i - 183 - 4 - 2 < 2) by omega,
    show ¬(i - 183 - 4 - 2 - 2 < 3 - 2) by omega,
    show i - 183 - 4 - 2 - 2 - (3 - 2) < 15 - 12 by omega, ↓reduceIte, List.getElem?_drop]
  rw [show 12 + (i - 183 - 4 - 2 - 2 - (3 - 2)) = 12 + (i - 192) by omega]; exact h

private theorem ff_195 {fn : Fn} (h : Full.fullFns[165]? = some fn := by rfl) :
    fastFns[195]? = some fn := by
  have hd := congrArg (·[0]?) fastFns_drop_195
  simpa only [List.getElem?_drop, Nat.add_zero] using hd.trans h

private theorem fast_table_drop_157
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFastEnv mainSpec) (fastFns.drop 157) ((fastSpecTable mainSpec).drop 157) := by
  let Γ := mkFastEnv mainSpec
  let h7 := mkFastEnv_row_at (mainSpec := mainSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let h9 := mkFastEnv_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h11 := mkFastEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h12 := mkFastEnv_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h14 := mkFastEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkFastEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h30 := mkFastEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h41 := mkFastEnv_row_at (mainSpec := mainSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  let h44 := mkFastEnv_row_at (mainSpec := mainSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  let h49 := mkFastEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h56 := mkFastEnv_row_at (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h60 := mkFastEnv_row_at (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h61 := mkFastEnv_row_at (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h82 := mkFastEnv_row_at (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let h84 := mkFastEnv_row_at (mainSpec := mainSpec) 84
    ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  let h85 := mkFastEnv_row_at (mainSpec := mainSpec) 85
    ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
  let h90 := mkFastEnv_row_at (mainSpec := mainSpec) 90
    ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
  let h91 := mkFastEnv_row_at (mainSpec := mainSpec) 91
    ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  let h92 := mkFastEnv_row_at (mainSpec := mainSpec) 92
    ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  let h93 := mkFastEnv_row_at (mainSpec := mainSpec) 93
    ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  let h94 := mkFastEnv_row_at (mainSpec := mainSpec) 94
    ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩
  let h95 := mkFastEnv_row_at (mainSpec := mainSpec) 95
    ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩
  let h96 := mkFastEnv_row_at (mainSpec := mainSpec) 96
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  let h98 := mkFastEnv_row_at (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h100 := mkFastEnv_row_at (mainSpec := mainSpec) 100
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let h101 := mkFastEnv_row_at (mainSpec := mainSpec) 101
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h102 := mkFastEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h105 := mkFastEnv_row_at (mainSpec := mainSpec) 105
    ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  let h111 := mkFastEnv_row_at (mainSpec := mainSpec) 111
    ⟨"full_probe_run", [i64, i64], [i64], FullFastBveBudgets.fullProbeRunFastSpec, true⟩
  let h113 := mkFastEnv_row_at (mainSpec := mainSpec) 113
    ⟨"full_transitive", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  let h119 := mkFastEnv_row_at (mainSpec := mainSpec) 119
    ⟨"full_vivify", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩
  let h125 := mkFastEnv_row_at (mainSpec := mainSpec) 125
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  let h126 := mkFastEnv_row_at (mainSpec := mainSpec) 126
    ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  let h127 := mkFastEnv_row_at (mainSpec := mainSpec) 127
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let h128 := mkFastEnv_row_at (mainSpec := mainSpec) 128
    ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  let h130 := mkFastEnv_row_at (mainSpec := mainSpec) 130
    ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  let h139 := mkFastEnv_row_at (mainSpec := mainSpec) 139
    ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  let h140 := mkFastEnv_row_at (mainSpec := mainSpec) 140
    ⟨"full_kitten_core", [i64], [i32], fullKittenCoreSpec, true⟩
  let h141 := mkFastEnv_row_at (mainSpec := mainSpec) 141
    ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec, true⟩
  let h152 := mkFastEnv_row_at (mainSpec := mainSpec) 152
    ⟨"full_congruence_dense", [i64, i64], [i64], FullDefSweep.fullCongruenceDenseSpec, true⟩
  let h156 := mkFastEnv_row_at (mainSpec := mainSpec) 156
    ⟨"full_sweep_dense", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  let h157 := mkFastEnv_row_at (mainSpec := mainSpec) 157
    ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  let h158 := mkFastEnv_row_at (mainSpec := mainSpec) 158
    ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  let h159 := mkFastEnv_row_at (mainSpec := mainSpec) 159
    ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  let h160 := mkFastEnv_row_at (mainSpec := mainSpec) 160
    ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  let h161 := mkFastEnv_row_at (mainSpec := mainSpec) 161
    ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool],
      FullDefSweep.fullBveMarkAndDefSpec, true⟩
  let h162 := mkFastEnv_row_at (mainSpec := mainSpec) 162
    ⟨"full_find_definition", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩
  let h163_def := mkFastEnv_row_at (mainSpec := mainSpec) 163
    ⟨"full_bve_gates", [i64, i32, i32, i32], [], FullDefSweep.fullBveGatesDefSpec, true⟩
  let h163 := fast_bve_gates_def_adapter h163_def
  let h164 := mkFastEnv_row_at (mainSpec := mainSpec) 164
    ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  let h165 := mkFastEnv_row_at (mainSpec := mainSpec) 165
    ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
      FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩
  let h166 := mkFastEnv_row_at (mainSpec := mainSpec) 166
    ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  let h167 := mkFastEnv_row_at (mainSpec := mainSpec) 167
    ⟨"full_bve_commit_res", [i64, i64, i64], [i64],
      FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩
  let h168 := mkFastEnv_row_at (mainSpec := mainSpec) 168
    ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  let h169 := mkFastEnv_row_at (mainSpec := mainSpec) 169
    ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  let h170 := mkFastEnv_row_at (mainSpec := mainSpec) 170
    ⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩
  let h171 := mkFastEnv_row_at (mainSpec := mainSpec) 171
    ⟨"full_bva_hop1", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop1Spec, true⟩
  let h172 := mkFastEnv_row_at (mainSpec := mainSpec) 172
    ⟨"full_bva_hop2", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop2Spec, true⟩
  let h173 := mkFastEnv_row_at (mainSpec := mainSpec) 173
    ⟨"full_bva_hop3", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop3Spec, true⟩
  let h174 := mkFastEnv_row_at (mainSpec := mainSpec) 174
    ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      FullBvaHeap.fullBvaMatchLargeSpec, true⟩
  let h175 := mkFastEnv_row_at (mainSpec := mainSpec) 175
    ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullBvaHeap.fullBvaScanCandsSpec, true⟩
  let h176 := mkFastEnv_row_at (mainSpec := mainSpec) 176
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩
  let h177 := mkFastEnv_row_at (mainSpec := mainSpec) 177
    ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullBvaHeap.fullBvaFilterRowSpec, true⟩
  let h178 := mkFastEnv_row_at (mainSpec := mainSpec) 178
    ⟨"full_bva_commit", [i64, i32], [.bool], FullBvaHeap.fullBvaCommitSpec, true⟩
  let h179 := mkFastEnv_row_at (mainSpec := mainSpec) 179
    ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullBvaHeap.fullBvaTryLitHeapSpec, true⟩
  let h180 := mkFastEnv_row_at (mainSpec := mainSpec) 180
    ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  let h181 := mkFastEnv_row_at (mainSpec := mainSpec) 181
    ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩
  let h182 := mkFastEnv_row_at (mainSpec := mainSpec) 182
    ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  let h183 := mkFastEnv_row_at (mainSpec := mainSpec) 183
    ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  let h184 := mkFastEnv_row_at (mainSpec := mainSpec) 184
    ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  let h185 := mkFastEnv_row_at (mainSpec := mainSpec) 185
    ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  let h186 := mkFastEnv_row_at (mainSpec := mainSpec) 186
    ⟨"full_probe_dticks", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  let h187 := mkFastEnv_row_at (mainSpec := mainSpec) 187
    ⟨"full_probe_tail", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  let h188 := mkFastEnv_row_at (mainSpec := mainSpec) 188
    ⟨"full_probe", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  let h189 := mkFastEnv_row_at (mainSpec := mainSpec) 189
    ⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  let h190 := mkFastEnv_row_at (mainSpec := mainSpec) 190
    ⟨"full_elim_bve", [i64, i64], [i64], fastElimBveSpec, true⟩
  let h191 := mkFastEnv_row_at (mainSpec := mainSpec) 191
    ⟨"full_eliminate", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  let h192 := mkFastEnv_row_at (mainSpec := mainSpec) 192
    ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  let h193 := mkFastEnv_row_at (mainSpec := mainSpec) 193
    ⟨"full_simplify", [i64, .bool, .bool], [i64], FullFastSched.schedSimplifySpec, true⟩
  let h194 := mkFastEnv_row_at (mainSpec := mainSpec) 194
    ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  refine fast_tableImpl_step ff_157_159 rfl (.of (full_fwd_dedup_bins_bridge_wp Γ h102)) ?_
  refine fast_tableImpl_step ff_157_159 rfl (.of (full_fwd_check_cl_bridge_wp Γ h56 h102 h98)) ?_
  refine fast_tableImpl_step ff_159 rfl
    (.of (FullFastBveBudgets.fast_forward_sub_wp Γ h157 h11 h158)) ?_
  refine fast_tableImpl_step ff_160 rfl (.of (full_bve_collect_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_161_164 rfl (.of (FullDefSweep.full_bve_mark_and_wp Γ)) ?_
  refine fast_tableImpl_step ff_161_164 rfl
    (.of (FullDefSweep.full_find_definition_wp Γ fastKInv_laws
      (fast_kitten_init_adapter h128) (fast_kitten_add_clause_adapter h130)
      (fast_kitten_solve_adapter h139) (fast_kitten_core_adapter h140)
      (fast_kitten_shrink_adapter h141))) ?_
  refine fast_tableImpl_step ff_161_164 rfl
    (.of (FullDefSweep.full_bve_gates_wp Γ h161 h162)) ?_
  refine fast_tableImpl_step ff_164_169 rfl (.of (full_bve_resolve_pair_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_164_169 rfl (.of (fast_bve_weaken_tmk_wp Γ h94 h100 h95)) ?_
  refine fast_tableImpl_step ff_164_169 rfl (.of (full_bve_try_bce_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_164_169 rfl (.of (fast_bve_commit_res_tmk_wp Γ h12 h15 h98 h102)) ?_
  refine fast_tableImpl_step ff_164_169 rfl (.of (full_bve_ext_need_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_169 rfl
    (.of (FullFastBveBudgets.fast_bve_var_def_wp Γ h160 h168 h165 h101 h163 h164 h167 h166
      h94 h100 h95)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_init_fresh_var_heap_wp Γ)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_hop1_wp Γ)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_hop2_wp Γ h171)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_hop3_wp Γ h172)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_match_large_wp Γ)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_scan_cands_wp Γ)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_pick_cand_wp Γ h173)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_bva_filter_row_wp Γ h174)) ?_
  refine fast_tableImpl_step ff_170_183 rfl
    (.of (FullBvaHeap.full_bva_commit_wp Γ h14 h170 h98 h12 h15 h100 h56)) ?_
  refine fast_tableImpl_step ff_170_183 rfl
    (.of (FullBvaHeap.full_bva_try_lit_wp Γ h175 h176 h177 h178)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_fheap_up_wp Γ)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_fheap_down_wp Γ)) ?_
  refine fast_tableImpl_step ff_170_183 rfl (.of (FullBvaHeap.full_factor_wp Γ h180 h181 h179)) ?_
  refine fast_tableImpl_step ff_183_187 rfl (.of (FullFastSched.sched_scale_delta_wp Γ h9)) ?_
  refine fast_tableImpl_step ff_183_187 rfl (.of (FullFastSched.sched_min_u64_wp Γ)) ?_
  refine fast_tableImpl_step ff_183_187 rfl (.of (FullFastSched.sched_max_u64_wp Γ)) ?_
  refine fast_tableImpl_step ff_183_187 rfl (.of (FullFastSched.sched_probe_dticks_wp Γ h185)) ?_
  refine fast_tableImpl_step ff_187_189 rfl (.of (fast_probe_tail_wp Γ h113 h184 h111 h119)) ?_
  refine fast_tableImpl_step ff_187_189 rfl
    (.of (fast_probe_wp Γ h186 h9 h183 h125 h126 h184 h152 h156 h127 h187)) ?_
  refine fast_tableImpl_step ff_189_191 rfl (.of (FullFastSched.sched_elim_dticks_wp Γ)) ?_
  refine fast_tableImpl_step ff_189_191 rfl (.of (fast_elim_bve_tmk_wp Γ h169)) ?_
  refine fast_tableImpl_step ff_191 rfl
    (.of (fast_eliminate_wp Γ h189 h9 h183 h126 h184 h159 h190 h182 h127)) ?_
  refine fast_tableImpl_step ff_192_195 rfl
    (.of (FullFastSched.sched_preprocess_wp Γ h49 h60 h183 h188 h191)) ?_
  refine fast_tableImpl_step ff_192_195 rfl
    (.of (FullFastSched.sched_simplify_wp Γ h30 h61 h188 h191)) ?_
  refine fast_tableImpl_step ff_192_195 rfl
    (.of (FullFastSched.sched_search_wp Γ h105 h85 h49 h82 h91 h90 h61 h193 h92 h93 h84)) ?_
  refine fast_tableImpl_step ff_195 rfl
    (.of (fun a m Q X h => FullFastSched.sched_kissat_solve_bytes_core_wp Γ
      h41 h44 h192 h194 h96 h7 a m Q X (hweaken a m Q X h))) ?_
  exact fast_tableImpl_nil mainSpec

private theorem fast_table_drop_97
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFastEnv mainSpec) (fastFns.drop 97) ((fastSpecTable mainSpec).drop 97) := by
  let Γ := mkFastEnv mainSpec
  let h11 := mkFastEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkFastEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkFastEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h27 := mkFastEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h28 := mkFastEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h30 := mkFastEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h45 := mkFastEnv_row_at (mainSpec := mainSpec) 45
    ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  let h48 := mkFastEnv_row_at (mainSpec := mainSpec) 48
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  let h49 := mkFastEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h56 := mkFastEnv_row_at (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h57 := mkFastEnv_row_at (mainSpec := mainSpec) 57
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h60 := mkFastEnv_row_at (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h82 := mkFastEnv_row_at (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let h94 := fast_extend_push2_adapter (mkFastEnv_row_at (mainSpec := mainSpec) 94
    ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩)
  let h97 := mkFastEnv_row_at (mainSpec := mainSpec) 97
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let h98 := mkFastEnv_row_at (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h99 := mkFastEnv_row_at (mainSpec := mainSpec) 99
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let h101 := mkFastEnv_row_at (mainSpec := mainSpec) 101
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h102 := mkFastEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h103 := mkFastEnv_row_at (mainSpec := mainSpec) 103
    ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], fullLuckyScanSpec, true⟩
  let h104 := mkFastEnv_row_at (mainSpec := mainSpec) 104
    ⟨"full_lucky_polar", [i64], [i64], fullLuckyPolarSpec, true⟩
  let h106 := mkFastEnv_row_at (mainSpec := mainSpec) 106
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], fullHbrDomSpec, true⟩
  let h107 := mkFastEnv_row_at (mainSpec := mainSpec) 107
    ⟨"full_probe_prop_lit", [i64, i32], [.bool], fullProbePropLitSpec, true⟩
  let h108 := mkFastEnv_row_at (mainSpec := mainSpec) 108
    ⟨"full_probe_prop", [i64], [i64], fullProbePropSpec, true⟩
  let h109 := mkFastEnv_row_at (mainSpec := mainSpec) 109
    ⟨"full_probe_flush_hbr", [i64, i64], [i64], fullProbeFlushHbrSpec, true⟩
  let h110 := mkFastEnv_row_at (mainSpec := mainSpec) 110
    ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  let h112 := mkFastEnv_row_at (mainSpec := mainSpec) 112
    ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
  let h114 := mkFastEnv_row_at (mainSpec := mainSpec) 114
    ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifySpec, true⟩
  let h115 := mkFastEnv_row_at (mainSpec := mainSpec) 115
    ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
  let h116 := mkFastEnv_row_at (mainSpec := mainSpec) 116
    ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  let h117 := mkFastEnv_row_at (mainSpec := mainSpec) 117
    ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitSpec, true⟩
  let h118 := mkFastEnv_row_at (mainSpec := mainSpec) 118
    ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  let h120 := mkFastEnv_row_at (mainSpec := mainSpec) 120
    ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  let h121_fast := mkFastEnv_row_at (mainSpec := mainSpec) 121
    ⟨"full_tarjan_scc", [i64], [i64], FullFastBveBudgets.fullTarjanSccFastSpec, true⟩
  let h121 : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X :=
    fun a m Q X h => h121_fast a m Q X (FullFastBveBudgets.fullTarjanSccFastSpec_of_canon h)
  let h122 := mkFastEnv_row_at (mainSpec := mainSpec) 122
    ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  let h123 := mkFastEnv_row_at (mainSpec := mainSpec) 123
    ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  let h124 := mkFastEnv_row_at (mainSpec := mainSpec) 124
    ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  let h128 := mkFastEnv_row_at (mainSpec := mainSpec) 128
    ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  let h129 := mkFastEnv_row_at (mainSpec := mainSpec) 129
    ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩
  let h130 := mkFastEnv_row_at (mainSpec := mainSpec) 130
    ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  let h131 := mkFastEnv_row_at (mainSpec := mainSpec) 131
    ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩
  let h132 := mkFastEnv_row_at (mainSpec := mainSpec) 132
    ⟨"full_kitten_mtf", [i64, i32], [], fullKittenMtfSpec, true⟩
  let h133 := mkFastEnv_row_at (mainSpec := mainSpec) 133
    ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩
  let h134 := mkFastEnv_row_at (mainSpec := mainSpec) 134
    ⟨"full_kitten_learn_unit0", [i64, i32, i32, .bool], [i32], fullKittenLearnUnit0Spec, true⟩
  let h135 := mkFastEnv_row_at (mainSpec := mainSpec) 135
    ⟨"full_kitten_propagate", [i64], [i32], fullKittenPropagateSpec, true⟩
  let h136 := mkFastEnv_row_at (mainSpec := mainSpec) 136
    ⟨"full_kitten_ana_clause", [i64, i32, i32], [], fullKittenAnaClauseSpec, true⟩
  let h137 := mkFastEnv_row_at (mainSpec := mainSpec) 137
    ⟨"full_kitten_analyze", [i64, i32], [.bool], fullKittenAnalyzeSpec, true⟩
  let h138 := mkFastEnv_row_at (mainSpec := mainSpec) 138
    ⟨"full_kitten_build_failing", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  let h139 := mkFastEnv_row_at (mainSpec := mainSpec) 139
    ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  let h142 := mkFastEnv_row_at (mainSpec := mainSpec) 142
    ⟨"full_kitten_flip", [i64, i32], [.bool], fullKittenFlipSpec, true⟩
  let h143 := mkFastEnv_row_at (mainSpec := mainSpec) 143
    ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  let h144 := mkFastEnv_row_at (mainSpec := mainSpec) 144
    ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  let h145 := mkFastEnv_row_at (mainSpec := mainSpec) 145
    ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  let h146 := mkFastEnv_row_at (mainSpec := mainSpec) 146
    ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  let h147 := mkFastEnv_row_at (mainSpec := mainSpec) 147
    ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], fullCongExtractIteSpec, true⟩
  let h148 := mkFastEnv_row_at (mainSpec := mainSpec) 148
    ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fullCongEmitXorSpec, true⟩
  let h149 := mkFastEnv_row_at (mainSpec := mainSpec) 149
    ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      fullCongTryXorIteSpec, true⟩
  let h150 := mkFastEnv_row_at (mainSpec := mainSpec) 150
    ⟨"full_cong_extract", [i64, i64, i64], [i64], FullDefSweep.fullCongExtractTickSpec, true⟩
  let h151 := mkFastEnv_row_at (mainSpec := mainSpec) 151
    ⟨"full_cong_hash_step", [i64, i64, i64, i64], [.bool], fullCongHashStepSpec, true⟩
  let h153 := mkFastEnv_row_at (mainSpec := mainSpec) 153
    ⟨"full_sweep_cone", [i64, i32], [i64], FullDefSweep.fullSweepConeKittenSpec fastKInv, true⟩
  let h154 := mkFastEnv_row_at (mainSpec := mainSpec) 154
    ⟨"full_sweep_refine_kitten", [i64, i32, i32], [],
      FullDefSweep.fullSweepRefineKittenSpec, true⟩
  let h155 := mkFastEnv_row_at (mainSpec := mainSpec) 155
    ⟨"full_sweep_var", [i64, i32, i64], [i64], FullDefSweep.fullSweepVarKittenSpec, true⟩
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_has_bin_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_add_bin_bridge_wp Γ h97 h27 h15)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_delete_bin_side_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_delete_binary_bridge_wp Γ h99)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_set_inactive_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_add_unit_bridge_wp Γ h30 h27)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_lucky_scan_bridge_wp Γ h28 h30 h49 h82)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_lucky_polar_bridge_wp Γ h11)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_lucky_bridge_wp Γ h104 h103 h28 h30 h49)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_hbr_dom_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl
    (.of (full_probe_prop_lit_bridge_wp Γ h45 h15 h106 h27)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_probe_prop_bridge_wp Γ h107)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_probe_flush_hbr_bridge_wp Γ h98 h49)) ?_
  refine fast_tableImpl_step ff_58_111 rfl
    (.of (full_probe_assume_pair_bridge_wp Γ h28 h108 h30 h82 h49 h109 h102)) ?_
  refine fast_tableImpl_step ff_111 rfl (.of (FullFastBveBudgets.fast_probe_run_wp Γ h30 h110)) ?_
  refine fast_tableImpl_step ff_112 rfl (.of (full_trans_lit_bridge_wp Γ h99 h102)) ?_
  refine fast_tableImpl_step ff_113 rfl
    (.of (FullFastBveBudgets.fast_transitive_wp Γ h30 h112 h49 h14)) ?_
  refine fast_tableImpl_step ff_114_119 rfl
    (.of (full_viv_simplify_bridge_wp Γ h56 h102 h98 h15)) ?_
  refine fast_tableImpl_step ff_114_119 rfl (.of (full_viv_sort_lits_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_114_119 rfl (.of (full_viv_deduce_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_114_119 rfl (.of (full_viv_commit_bridge_wp Γ h56 h102 h98 h15)) ?_
  refine fast_tableImpl_step ff_114_119 rfl
    (.of (full_viv_clause_bridge_wp Γ h114 h115 h28 h48 h30 h116 h117)) ?_
  refine fast_tableImpl_step ff_119 rfl
    (.of (FullFastBveBudgets.fast_vivify_wp Γ h30 h11 h118 h49)) ?_
  refine fast_tableImpl_step ff_120 rfl (.of (full_tarjan_pop_scc_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_121 rfl (.of (FullFastBveBudgets.fast_tarjan_scc_wp Γ h120)) ?_
  refine fast_tableImpl_step ff_122_125 rfl
    (.of (full_subst_elim_vars_bridge_wp Γ h102 h49 h94 h101)) ?_
  refine fast_tableImpl_step ff_122_125 rfl (.of (full_subst_rewrite_bins_bridge_wp Γ h102 h98)) ?_
  refine fast_tableImpl_step ff_122_125 rfl
    (.of (full_subst_rewrite_ar_bridge_wp Γ h11 h102 h98)) ?_
  refine fast_tableImpl_step ff_125_127 rfl
    (.of (FullFastSched.sched_substitute_wp Γ h30 h121 h122 h123 h124 h60 h49)) ?_
  refine fast_tableImpl_step ff_125_127 rfl
    (.of (FullFastSched.sched_enter_dense_wp Γ h30 h49 h57 h15 h60 h11)) ?_
  refine fast_tableImpl_step ff_127 rfl (.of (full_rebuild_watches_bridge_wp Γ h60 h49)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_init_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_watch_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_add_clause_wp Γ h129)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_assign_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_mtf_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_backtrack_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_learn_unit0_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_propagate_wp Γ h131 h134)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_ana_clause_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl
    (.of (full_kitten_analyze_wp Γ h136 h133 h132 h134 h131 h129)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_build_failing_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl
    (.of (full_kitten_solve_wp Γ h133 h131 h135 h137 h138)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_core_wp Γ)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_shrink_wp Γ h129)) ?_
  refine fast_tableImpl_step ff_128_143 rfl (.of (full_kitten_flip_wp Γ)) ?_
  refine fast_tableImpl_step ff_143_150 rfl (.of (full_cong_find_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_143_150 rfl (.of (full_cong_merge_bridge_wp Γ h143 h98)) ?_
  refine fast_tableImpl_step ff_143_150 rfl (.of (full_has_ternary_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_143_150 rfl (.of (full_sort_u32_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_143_150 rfl (.of (full_cong_extract_ite_bridge_wp Γ h145)) ?_
  refine fast_tableImpl_step ff_143_150 rfl (.of (full_cong_emit_xor_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_143_150 rfl
    (.of (full_cong_try_xor_ite_bridge_wp Γ h145 h148 h147)) ?_
  refine fast_tableImpl_step ff_150 rfl
    (.of (FullDefSweep.full_cong_extract_wp Γ h11 h97
      (fast_cong_try_xor_ite_adapter h149))) ?_
  refine fast_tableImpl_step ff_151 rfl
    (.of (full_cong_hash_step_bridge_wp Γ h143 h146 h144 h102)) ?_
  refine fast_tableImpl_step ff_152_157 rfl
    (.of (FullDefSweep.full_congruence_dense_wp Γ h150
      (fast_cong_hash_step_adapter h151))) ?_
  refine fast_tableImpl_step ff_152_157 rfl
    (.of (FullDefSweep.full_sweep_cone_wp Γ fastKInv_laws
      (fast_kitten_init_adapter h128) (fast_kitten_add_clause_adapter h130))) ?_
  refine fast_tableImpl_step ff_152_157 rfl
    (.of (FullDefSweep.full_sweep_refine_kitten_wp Γ)) ?_
  refine fast_tableImpl_step ff_152_157 rfl
    (.of (FullDefSweep.full_sweep_var_wp Γ fastKInv_laws h153
      (fast_kitten_solve_adapter h139) h154 (fast_kitten_flip_adapter h142)
      (fast_sweep_add_unit_adapter h102) h98)) ?_
  refine fast_tableImpl_step ff_152_157 rfl
    (.of (FullDefSweep.full_sweep_dense_wp Γ h155)) ?_
  exact fast_table_drop_157 mainSpec hweaken

private theorem fast_table_drop_50
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFastEnv mainSpec) (fastFns.drop 50) ((fastSpecTable mainSpec).drop 50) := by
  let Γ := mkFastEnv mainSpec
  let h8 := mkFastEnv_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  let h9 := mkFastEnv_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h10 := mkFastEnv_row_at (mainSpec := mainSpec) 10
    ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  let h11 := mkFastEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkFastEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkFastEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h17 := mkFastEnv_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h19 := mkFastEnv_row_at (mainSpec := mainSpec) 19
    ⟨"full_heap_pop", [i64], [i64], fullHeapPopSpec, true⟩
  let h21 := mkFastEnv_row_at (mainSpec := mainSpec) 21
    ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  let h22 := mkFastEnv_row_at (mainSpec := mainSpec) 22
    ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  let h24 := mkFastEnv_row_at (mainSpec := mainSpec) 24
    ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  let h25 := mkFastEnv_row_at (mainSpec := mainSpec) 25
    ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  let h26 := mkFastEnv_row_at (mainSpec := mainSpec) 26
    ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  let h27 := mkFastEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h28 := mkFastEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h30 := mkFastEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h31 := mkFastEnv_row_at (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h49 := mkFastEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h50 := mkFastEnv_row_at (mainSpec := mainSpec) 50
    ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  let h51 := mkFastEnv_row_at (mainSpec := mainSpec) 51
    ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  let h52 := mkFastEnv_row_at (mainSpec := mainSpec) 52
    ⟨"full_red_less", [i64, i32, i32], [.bool], fullRedLessSpec, true⟩
  let h53 := mkFastEnv_row_at (mainSpec := mainSpec) 53
    ⟨"full_red_sift", [i64, i64, i64, i64], [], fullRedSiftSpec, true⟩
  let h54 := mkFastEnv_row_at (mainSpec := mainSpec) 54
    ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  let h55 := mkFastEnv_row_at (mainSpec := mainSpec) 55
    ⟨"full_lit_rank", [i64, i64, i32], [i64], fullLitRankSpec, true⟩
  let h56 := mkFastEnv_row_at (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h57 := mkFastEnv_row_at (mainSpec := mainSpec) 57
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h58 := mkFastEnv_row_at (mainSpec := mainSpec) 58
    ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  let h59 := mkFastEnv_row_at (mainSpec := mainSpec) 59
    ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  let h60 := mkFastEnv_row_at (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h61 := mkFastEnv_row_at (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h62 := mkFastEnv_row_at (mainSpec := mainSpec) 62
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  let h63 := mkFastEnv_row_at (mainSpec := mainSpec) 63
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  let h64 := mkFastEnv_row_at (mainSpec := mainSpec) 64
    ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  let h65 := mkFastEnv_row_at (mainSpec := mainSpec) 65
    ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  let h66 := mkFastEnv_row_at (mainSpec := mainSpec) 66
    ⟨"full_otfs_large", [i64, i32, i32], [.bool], fullOtfsLargeSpec, true⟩
  let h67 := mkFastEnv_row_at (mainSpec := mainSpec) 67
    ⟨"full_otfs_bin", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
  let h68 := mkFastEnv_row_at (mainSpec := mainSpec) 68
    ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  let h69 := mkFastEnv_row_at (mainSpec := mainSpec) 69
    ⟨"full_min_mark", [i64, i32, i8], [], fullMinMarkSpec, true⟩
  let h70 := mkFastEnv_row_at (mainSpec := mainSpec) 70
    ⟨"full_min_lit", [i64, i32], [.bool], fullMinLitSpec, true⟩
  let h71 := mkFastEnv_row_at (mainSpec := mainSpec) 71
    ⟨"full_tmp_less", [i64, i64, i32, i32], [.bool], fullTmpLessSpec, true⟩
  let h72 := mkFastEnv_row_at (mainSpec := mainSpec) 72
    ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [], fullSortTmpSiftSpec, true⟩
  let h73 := mkFastEnv_row_at (mainSpec := mainSpec) 73
    ⟨"full_sort_tmp", [i64], [], fullSortTmpSpec, true⟩
  let h74 := mkFastEnv_row_at (mainSpec := mainSpec) 74
    ⟨"full_shrink_lower", [i64, i32, i32], [.bool], fullShrinkLowerSpec, true⟩
  let h75 := mkFastEnv_row_at (mainSpec := mainSpec) 75
    ⟨"full_shrink_blk", [i64, i64, i64, i32, i64], [], fullShrinkBlkSpec, true⟩
  let h76 := mkFastEnv_row_at (mainSpec := mainSpec) 76
    ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  let h77 := mkFastEnv_row_at (mainSpec := mainSpec) 77
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  let h78 := mkFastEnv_row_at (mainSpec := mainSpec) 78
    ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  let h79 := mkFastEnv_row_at (mainSpec := mainSpec) 79
    ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  let h80 := mkFastEnv_row_at (mainSpec := mainSpec) 80
    ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  let h81 := mkFastEnv_row_at (mainSpec := mainSpec) 81
    ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  let h83 := mkFastEnv_row_at (mainSpec := mainSpec) 83
    ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  let h86 := mkFastEnv_row_at (mainSpec := mainSpec) 86
    ⟨"full_walk_collect", [i64], [i64], fullWalkCollectSpec, true⟩
  let h87 := mkFastEnv_row_at (mainSpec := mainSpec) 87
    ⟨"full_walk_cl_sat", [i64, i64, i64], [.bool], fullWalkClSatSpec, true⟩
  let h88 := mkFastEnv_row_at (mainSpec := mainSpec) 88
    ⟨"full_walk_pick_lit", [i64, i64, i64], [i32], fullWalkPickLitSpec, true⟩
  let h89 := mkFastEnv_row_at (mainSpec := mainSpec) 89
    ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_recompute_tiers_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_mark_reasons_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_red_less_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_red_sift_bridge_wp Γ h52)) ?_
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_sort_reds_bridge_wp Γ h53)) ?_
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_lit_rank_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_50_57 rfl (.of (full_unwatch_large_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_57 rfl (.of (FullFastSched.sched_sweep_bins_wp Γ h14)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_sweep_copy_bridge_wp Γ h27 h15)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_rewatch_arena_bridge_wp Γ h55 h15)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_arena_sweep_bridge_wp Γ h57 h11 h58 h59)) ?_
  refine fast_tableImpl_step ff_58_111 rfl
    (.of (full_reduce_bridge_wp Γ h8 h9 h11 h50 h51 h54 h30 h49 h60)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_analyze_lit_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_analyze_rsn_bridge_wp Γ h62)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_clear_ana_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_bump_analyzed_bridge_wp Γ h21 h24 h22)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_otfs_large_bridge_wp Γ h56 h15)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_otfs_bin_bridge_wp Γ h56 h15)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_otfs_subsume_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_min_mark_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_min_lit_bridge_wp Γ h69)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_tmp_less_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_sort_tmp_sift_bridge_wp Γ h71)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_sort_tmp_bridge_wp Γ h72)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_shrink_lower_bridge_wp Γ h69 h70)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_shrink_blk_bridge_wp Γ h74 h69)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_min_shrink_bridge_wp Γ h73 h69 h70 h75)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_det_new_level_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_one_lit_confl_wp Γ h77 h30 h27 h56 h15)) ?_
  refine fast_tableImpl_step ff_58_111 rfl
    (.of (full_deduce_1uip_wp Γ h62 h63 h64 h65 h66 h67 h68)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_eager_subsume_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl
    (.of (full_learn_clause_bridge_wp Γ h30 h27 h77 h14 h61 h31 h80)) ?_
  refine fast_tableImpl_step ff_58_111 rfl
    (.of (full_analyze_bridge_wp Γ h78 h79 h76 h25 h26 h81)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_next_dec_var_bridge_wp Γ h19)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_decide_bridge_wp Γ h83 h28)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_warmup_bridge_wp Γ h83 h28 h49 h30)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_walk_collect_bridge_wp Γ h11)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_walk_cl_sat_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_walk_pick_lit_bridge_wp Γ h10)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_walk_bridge_wp Γ h86 h87 h10 h88)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_rephase_bridge_wp Γ h30 h89 h9)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_switch_mode_bridge_wp Γ h17 h9)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_restart_due_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_restart_bridge_wp Γ h83 h30)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (fast_extend_push2_tmk_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (fast_extend_push_cl_tmk_wp Γ)) ?_
  refine fast_tableImpl_step ff_58_111 rfl (.of (full_extend_bridge_wp Γ)) ?_
  exact fast_table_drop_97 mainSpec hweaken

private theorem fast_table_drop_8
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFastEnv mainSpec) (fastFns.drop 8) ((fastSpecTable mainSpec).drop 8) := by
  let Γ := mkFastEnv mainSpec
  let h2 := mkFastEnv_row_at (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let h5 := mkFastEnv_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h6 := mkFastEnv_row_at (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  let h12 := mkFastEnv_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h13 := mkFastEnv_row_at (mainSpec := mainSpec) 13
    ⟨"full_wsort_sift", [i64, i64, i64, i64], [], fullWsortSiftSpec, true⟩
  let h14 := mkFastEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkFastEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h16 := mkFastEnv_row_at (mainSpec := mainSpec) 16
    ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  let h17 := mkFastEnv_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h18 := mkFastEnv_row_at (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  let h20 := mkFastEnv_row_at (mainSpec := mainSpec) 20
    ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
  let h23 := mkFastEnv_row_at (mainSpec := mainSpec) 23
    ⟨"full_queue_renumber", [i64], [], fullQueueRenumberSpec, true⟩
  let h27 := mkFastEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h29 := mkFastEnv_row_at (mainSpec := mainSpec) 29
    ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  let h31 := mkFastEnv_row_at (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h32 := mkFastEnv_row_at (mainSpec := mainSpec) 32
    ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  let h33 := mkFastEnv_row_at (mainSpec := mainSpec) 33
    ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  let h34 := mkFastEnv_row_at (mainSpec := mainSpec) 34
    ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  let h35 := mkFastEnv_row_at (mainSpec := mainSpec) 35
    ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  let h36_fast := mkFastEnv_row_at (mainSpec := mainSpec) 36
    ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.fullFastInitHdrSpec, true⟩
  let h36 : ∀ a m Q X, fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X :=
    fun a m Q X h => h36_fast a m Q X (FullFastBveBudgets.fullFastInitHdrSpec_of_canon h)
  let h37 := mkFastEnv_row_at (mainSpec := mainSpec) 37
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  let h38 := mkFastEnv_row_at (mainSpec := mainSpec) 38
    ⟨"full_calc_ext_cap", [i64], [i64], fullCalcExtCapSpec, true⟩
  let h39 := mkFastEnv_row_at (mainSpec := mainSpec) 39
    ⟨"full_calc_scr_cap", [i64], [i64], fullCalcScrCapSpec, true⟩
  let h40 := mkFastEnv_row_at (mainSpec := mainSpec) 40
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  let h42 := mkFastEnv_row_at (mainSpec := mainSpec) 42
    ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  let h43 := mkFastEnv_row_at (mainSpec := mainSpec) 43
    ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  let h47 := mkFastEnv_row_at (mainSpec := mainSpec) 47
    ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  let h48 := mkFastEnv_row_at (mainSpec := mainSpec) 48
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_isqrt_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_ilog10_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_rng_next_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_arena_next_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_alloc_cl_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_wsort_sift_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_wstack_defrag_bridge_wp Γ h13)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_watch_push_bridge_wp Γ h14)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_heap_up_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_heap_down_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_heap_push_bridge_wp Γ h16)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_heap_pop_bridge_wp Γ h17)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_rescale_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_bump_var_bridge_wp Γ h16 h20)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_bump_decay_bridge_wp Γ h20)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_queue_renumber_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_queue_mtf_bridge_wp Γ h23)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_tick_rel_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_ema_update_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_assign_lvl_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_assign_bridge_wp Γ h27)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_save_target_best_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_backtrack_bridge_wp Γ h29 h18)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_add_clause_bridge_wp Γ h12 h15)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_zero_tables1_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_zero_tables2_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_fixed_bytes_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (full_init_ptrs_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_36 rfl (.of (FullFastBveBudgets.fast_init_hdr_wp Γ)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_calc_max_v_bridge_wp Γ h34)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_calc_ext_cap_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_calc_scr_cap_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_init_arenas_bridge_wp Γ h35)) ?_
  refine fast_tableImpl_step ff_37_47 rfl
    (.of (full_init_state_bridge_wp Γ h5 h34 h37 h38 h39 h40 h36 h32 h33)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_skip_cl_bridge_wp Γ h6)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_ingest_cl_bridge_wp Γ h6 h27 h31)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_parse_body_bridge_wp Γ h42 h43 h2)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_find_repl_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_37_47 rfl (.of (full_assign_level_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_47_50 rfl (.of (FastCore.full_prop_lit_wp Γ h15)) ?_
  refine fast_tableImpl_step ff_47_50 rfl (.of (FastCore.full_propagate_ignore_wp Γ h47)) ?_
  refine fast_tableImpl_step ff_47_50 rfl (.of (FastCore.full_propagate_wp Γ h48)) ?_
  exact fast_table_drop_50 mainSpec hweaken

/-- Unconditional row-by-row `TableImpl` discharging all `196 / 196` functions of `fastFns`
against `fastSpecTable mainSpec`. -/
theorem mkFastEnv_tableImpl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFastEnv mainSpec) fastFns (fastSpecTable mainSpec) := by
  let Γ := mkFastEnv mainSpec
  let h0 := mkFastEnv_row_at (mainSpec := mainSpec) 0
    ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  let h1 := mkFastEnv_row_at (mainSpec := mainSpec) 1
    ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  let h2 := mkFastEnv_row_at (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let h3 := mkFastEnv_row_at (mainSpec := mainSpec) 3
    ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  let h4 := mkFastEnv_row_at (mainSpec := mainSpec) 4
    ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  let h5 := mkFastEnv_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h6 := mkFastEnv_row_at (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  change TableImpl Γ (fastFns.drop 0) ((fastSpecTable mainSpec).drop 0)
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_is_ws_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_is_digit_bridge_wp Γ)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_skip_ws_comments_bridge_wp Γ h0)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_skip_ws1_bridge_wp Γ h0)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_read_nat_bridge_wp Γ h1 h0)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_parse_header_bridge_wp Γ h2 h3 h4)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_next_lit_bridge_wp Γ h2 h4)) ?_
  refine fast_tableImpl_step ff_0_36 rfl (.of (kissat_check_model_bridge_wp Γ h5 h6 h2)) ?_
  exact fast_table_drop_8 mainSpec hweaken

/-- Unconditional `ModuleOk` assembly for `mkFastEnv mainSpec` on `fastModule` (`196/196`). -/
theorem mkFastEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkFastEnv mainSpec) fastModule :=
  Env.ofTable_moduleOk fast_acyclic (allFns_of_forall fastFns_wf)
    (mkFastEnv_tableImpl mainSpec hweaken)

/-- Unconditional `ModuleOk fastEnv fastModule` certifying all `196 / 196` functions of Kissat M2
`FullFast` against the canonical UNSAT-only specification `fastEnv` (`0` SAT proofs). -/
theorem fastEnv_moduleOk : ModuleOk fastEnv fastModule :=
  mkFastEnv_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional `ModuleOk fastUnsatEnv fastModule` (`196/196`, concrete UNSAT witness). -/
theorem fastUnsatEnv_moduleOk : ModuleOk fastUnsatEnv fastModule :=
  mkFastEnv_moduleOk fullUnsatWitnessSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

end LeanQbe.T.Examples.Kissat.FullFast

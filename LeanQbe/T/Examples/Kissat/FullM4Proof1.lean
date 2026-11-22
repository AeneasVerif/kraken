module

public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.Examples.Kissat.FullM3Proof1
public import LeanQbe.T.Examples.Kissat.FullM4ReduceLemmas
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Unified M4 Proof — Part 1 (`m4SpecTable`, Orchestrators, & Non-Vacuity)

Defines:
1. Upgraded M4 specs (`m4ReorderSpec`, `m4PreprocessSpec`, `m4SimplifySpec`, `m4SearchSpec`)
   threading `FullM4Compact.FullCfgCompat c c'` across dead-variable compaction and level-0/fuel
   preservation across `full_reorder`.
2. Unified `231`-row specification table `m4SpecTable`, `mkM4Env`, `m4Env`, `m4UnsatEnv` aligned
   1-to-1 with `FullM4.m4Fns` (`m4SpecTable_sigs`, `m4SpecTable_length`, `m4SpecTable_noExit`).
3. Parametric `(Γ : Env)` `Func.wp` proofs for all unified M4 orchestrators:
   `m4_reorder_wp`, `m4_extend_wp`, `m4_probe_wp`, `m4_eliminate_wp`, `m4_preprocess_wp`,
   `m4_simplify_wp`, `m4_search_wp`, and `m4_kissat_solve_bytes_core_wp`.
4. Headline source-level UNSAT soundness `m4_solve_bytes_correct` and concrete `Mem 64` UNSAT
   non-vacuity `m4_unsat_nonvacuous` (`XPost := False`, `4096` B workspace, `fuel = 16`, `0` SAT
   proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Upgraded M4 Contracts & `231`-Row `m4SpecTable` -/

/-- Strengthened `full_reorder` contract exposing `cur_level` and `fuel` preservation for
`full_simplify`. -/
def m4ReorderSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_level = s.core.cur_level → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Upgraded M4 `full_preprocess` contract threading `FullCfgCompat c c'` across compaction. -/
def m4PreprocessSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r c' s' m',
      FullM4Compact.FullCfgCompat c c' →
      s'.LengthsOk c' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c' F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullMem c' s' ⋆ R) m' → Q (r, ()) m'

/-- Upgraded M4 `full_simplify` contract threading `FullCfgCompat c c'` across compaction. -/
def m4SimplifySpec : Spec [i64, .bool, .bool] [i64] := fun (h, _dp, _de, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r c' s' m',
      FullM4Compact.FullCfgCompat c c' →
      s'.LengthsOk c' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c' F0 s' ∧ s'.core.cur_level = 0) →
      (FullMem c' s' ⋆ R) m' → Q (r, ()) m'

/-- Upgraded M4 `full_search` contract threading `FullCfgCompat c c'` across compaction. -/
def m4SearchSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r c' s' m',
      FullM4Compact.FullCfgCompat c c' →
      s'.LengthsOk c' → (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullMem c' s' ⋆ R) m' → Q (r, ()) m'

/-- Unified `231`-row specification table aligned 1-to-1 with `FullM4.m4Fns`. -/
def m4SpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
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
  , ⟨"full_compute_lbd", [i64, i32], [i32], FullM4Ternary.fullComputeLbdSpec, true⟩
  , ⟨"full_promote_clause", [i64, i32], [.bool], FullM4Ternary.fullPromoteClauseSpec, true⟩
  , ⟨"full_promote_reasons", [i64], [i64], FullM4Ternary.fullPromoteReasonsSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], m4ReduceSpec, true⟩
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
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], FullM4Bva.m4BvaHop3Spec, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      FullBvaHeap.fullBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullM4Bva.m4BvaScanCandsSpec, true⟩
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
  , ⟨"full_compact_record_ext", [i64, i64, i64], [], FullM4Compact.fullCompactRecordExtSpec, true⟩
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
  , ⟨"full_reorder_heap", [i64], [i64], FullM4Ternary.fullReorderHeapSpec, true⟩
  , ⟨"full_tumble_clause", [i64, i32], [.bool], FullM4Ternary.fullTumbleClauseSpec, true⟩
  , ⟨"full_tumble_clauses", [i64, i64], [i64], FullM4Ternary.fullTumbleClausesSpec, true⟩
  , ⟨"full_reorder", [i64, i64], [i64], m4ReorderSpec, true⟩
  , ⟨"full_ternary_match_bin", [i32, i32, i32, i32, i32, i32], [.bool],
      FullM4Ternary.fullTernaryMatchBinSpec, true⟩
  , ⟨"full_ternary_collect", [i64, i64], [i64], FullM4Ternary.fullTernaryCollectSpec, true⟩
  , ⟨"full_ternary_resolve_bin", [i64, i32, i32], [i64],
      FullM4Ternary.fullTernaryResolveBinSpec, true⟩
  , ⟨"full_ternary_round", [i64, i64, i64], [i64], FullM4Ternary.fullTernaryRoundSpec, true⟩
  , ⟨"full_ternary", [i64, i64, i64], [i64], FullM4Ternary.fullTernarySpec, true⟩
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
  , ⟨"full_preprocess", [i64], [i64], m4PreprocessSpec, true⟩
  , ⟨"full_simplify", [i64, .bool, .bool], [i64], m4SimplifySpec, true⟩
  , ⟨"full_search", [i64], [i64], m4SearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

def mkM4Env (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m4SpecTable mainSpec)

/-- Headline `231`-function UNSAT-only environment for `FullM4.m4Module`. -/
def m4Env : Env := mkM4Env fullSolveBytesSpec

/-- Concrete `231`-function UNSAT non-vacuity environment (`fullUnsatWitnessSpec`, `20#64`). -/
def m4UnsatEnv : Env := mkM4Env fullUnsatWitnessSpec

theorem m4SpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m4SpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (m4SpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m4SpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m4SpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      m4Fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

theorem m4SpecTable_length (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m4SpecTable mainSpec).length = 231 := by
  have hs := congrArg List.length (m4SpecTable_sigs mainSpec)
  simpa only [List.length_map, m4Fns_length] using hs

theorem m4Fns_nodup : (m4Fns.map Fn.name).Nodup := by
  have hchk := m4_acyclic
  simp only [m4Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

theorem m4SpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m4SpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (m4SpecTable mainSpec).map SpecEntry.name = m4Fns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (m4SpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]; exact m4Fns_nodup

theorem mkM4Env_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m4SpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM4Env mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m4SpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem m4_ofTable_iff_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
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

theorem mkM4Env_row_elim {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m4SpecTable mainSpec)[i]? = some e := by rfl)
    (hno : e.noExit = true := by rfl) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hs : mkM4Env mainSpec e.name e.as e.rs xs m Q X) :
    e.spec xs m Q (fun _ _ _ _ => False) := by
  have heff := (m4_ofTable_iff_of_mem (List.mem_of_getElem? hi)
    (m4SpecTable_nodup mainSpec)).mp hs
  simpa only [SpecEntry.eff, hno, ↓reduceIte] using heff

theorem mkM4Env_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM4Env mainSpec f as bs xs m Q X → mkM4Env mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m4SpecTable_noExit mainSpec)

theorem m4Env_noExit :
    ∀ f as bs xs m Q X X', m4Env f as bs xs m Q X → m4Env f as bs xs m Q X' :=
  mkM4Env_noExit fullSolveBytesSpec

theorem m4UnsatEnv_noExit :
    ∀ f as bs xs m Q X X', m4UnsatEnv f as bs xs m Q X → m4UnsatEnv f as bs xs m Q X' :=
  mkM4Env_noExit fullUnsatWitnessSpec

/-! ## 2. Pure Invariant Helpers & Upgraded M4 Orchestrator Proofs -/

section M4Orchestrators

open scoped FullArenaTactics

private theorem m4_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m4_denseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m4_tmkZero_of_init_loop {s : FullState}
    {tmki : List (BitVec 32)} (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    FullFastBveBudgets.TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

private theorem m4_sparseInv_of_perm_core {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem m4_sparseInv_of_same_arena {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · intro ref href hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact hsp.2.2.1 ref href hng
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem m4_sparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem m4_sparseInv_after_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hpres : FullExtScratchPres s s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro ref href hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact hsp.2.2.2.1 ref href hng
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem m4_bv64_shl1_or1 {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
  have hs : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_or, hs, show (1#64 : BitVec 64).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    simp [Nat.testBit_succ, show (2 * v.toNat + 1) / 2 = v.toNat by omega,
      show (2 * v.toNat) / 2 = v.toNat by omega]

private theorem m4_bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat / 2 < n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  have h1 : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl
  rw [h1]; exact litNeg_lt_two_mul (by omega)

private theorem m4_bv32_and_mask_lt {x : BitVec 32} :
    (x &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-- `Func.wp` proof for `full_reorder` against strengthened `m4ReorderSpec` exposing `cur_level`
and `fuel` preservation. -/
theorem m4_reorder_wp (Γ : Env)
    (hQueue : FullM4Ternary.EnvSpec Γ "full_reorder_queue" FullM4Ternary.fullReorderQueueSpec)
    (hHeap : FullM4Ternary.EnvSpec Γ "full_reorder_heap" FullM4Ternary.fullReorderHeapSpec)
    (hTumble : FullM4Ternary.EnvSpec Γ "full_tumble_clauses" FullM4Ternary.fullTumbleClausesSpec) :
    ∀ a m Q X, m4ReorderSpec a m Q X →
      Func.wp Γ FullM4Ternary.full_reorder_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold Func.wp FullM4Ternary.full_reorder_body
  c0_hsteps_nogrp; c0_call hQueue
  refine ⟨c, s, R, rfl, hsp.lengths, hm, ?_⟩
  rintro ⟨_, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1
  change (FullMem c s1 ⋆ R) m1 at hm1
  have hsp1 := hsp.of_safetySlice hlen1 hcore1 hpres1
  have hce1 : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
  c0_hsteps_nogrp; c0_call hHeap
  refine ⟨c, s1, R, rfl, hlen1, hm1, ?_⟩
  rintro ⟨_, ⟨⟩⟩ s2 m2 hcore2 hlen2 hpres2 hm2
  change (FullMem c s2 ⋆ R) m2 at hm2
  have hsp2 := hsp1.of_safetySlice hlen2 hcore2 hpres2
  have hce2 : s2.core = s.core := (fullCoreState_agrees_with_scratch hcore2).trans hce1
  obtain ⟨F_cur, hspW2⟩ := hsp2.exists_witness
  c0_hsteps_nogrp; c0_call hTumble
  refine ⟨c, F0, F_cur, s2, R, rfl, hspW2, hm2, ?_⟩
  rintro r ar' rng' m3 s3 hspW3 hperm3 hm3
  c0_hsteps
  exact hQ r s3 m3 hspW3.toSparse (by simpa only [hce2] using hperm3)
    (by simp [s3, hce2]) (by simp [s3, hce2]) hm3

/-- `Func.wp` proof for M4 `full_extend(h)` (handling both `EXT_COMPACT_FLAG` variable-remap
frames across `[0..max_vars)` and pairwise/clause witness frames) against `Full.fullExtendSpec`. -/
theorem m4_extend_wp (Γ : Env) :
    ∀ a m Q X, fullExtendSpec a m Q X → Func.wp Γ full_extend_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hext : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hmax hext
  obtain hvl := hlen.core_ok.vals_len
  obtain hfll := hlen.core_ok.flags_len
  obtain hesl := hlen.scratch_ok.extend_stk_len
  unfold Func.wp full_extend_body
  c0_hsteps_nogrp
  -- Loop 1: `while (v < mx)` setting `FL_ELIM`/`FL_SUBST`/unassigned in `[0..max_vars)`
  refine wp_while_state
    (fun (p : BitVec 64 × FullState) => (p.1, ()))
    (fun p => c.max_vars - p.1.toNat)
    (fun p ml =>
      p.1.toNat ≤ c.max_vars ∧ PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
      p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) ml)
    (fun J hJ => by c0_hsteps; exact hJ (0#64, s) m ⟨Nat.zero_le _, rfl, hlen, hm⟩)
    (fun J ⟨v, s1⟩ m1 ⟨hvle, hcore1, hs1, hm1⟩ ih1 => ?_)
  dsimp only at hvle hcore1 hs1 hm1 ih1 ⊢
  c0_hsplit
  · have hv_lt : v.toNat < c.max_vars := by
      have h1 : v.toNat < c.max_vars % 2 ^ 64 := by assumption
      omega
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by simp only [bv_c0]; omega
    have hfl_v : v.toNat < s1.core.flags.length := by
      rw [hs1.core_ok.flags_len]; exact hv_lt
    have hv_shl : (v <<< (1 : Nat)).toNat < s1.core.vals.length := by
      rw [hs1.core_ok.vals_len, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
    c0_hsteps_nogrp
    refine wp_join_state0 (α := FullState)
      (fun s2 m2 => PreservesCoreSlice (fullExtendSlice c).coreProj s1 s2 ∧ s2.LengthsOk c ∧
        (FullMem c s2 ⋆ R) m2)
      (fun J2 s2 m2 ⟨hcore2, hs2, hm2⟩ => by
        c0_hsteps
        exact ih1 (v + 1#64, s2) m2 (by dsimp only; rw [hv1]; omega)
          ⟨by rw [hv1]; omega, hcore1.trans hcore2, hs2, hm2⟩)
      (fun J2 hJ2 => by
        have hvl1 := hs1.core_ok.vals_len
        have hv_or : ((v <<< (1 : Nat)) ||| 1#64).toNat <
            (s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).length := by
          rw [List.length_set, hvl1, m4_bv64_shl1_or1 (by omega)]; omega
        c0_hsteps
        · exact hJ2 { s1 with core := { s1.core with vals :=
            ((s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).set
              ((v <<< (1 : Nat)) ||| 1#64).toNat (BitVec.setWidth 8 (-1))) } } _
            ⟨rfl, ⟨{ hs1.core_ok with vals_len := by simp [hvl1] }, hs1.scratch_ok⟩, hm⟩
        · exact hJ2 { s1 with core := { s1.core with vals :=
            ((s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).set
              ((v <<< (1 : Nat)) ||| 1#64).toNat (BitVec.setWidth 8 (-1))) } } _
            ⟨rfl, ⟨{ hs1.core_ok with vals_len := by simp [hvl1] }, hs1.scratch_ok⟩, hm⟩
        · exact hJ2 s1 m1 ⟨rfl, hs1, hm1⟩)
  · clear hm hlen
    obtain ⟨hsc1, _, _, _, _, _⟩ := fullExtend_preserves_nonVals hcore1
    c0_hsteps
    -- Outer Loop 2: `while (end > 0ULL)`
    refine wp_while_state
      (fun (p : BitVec 64 × FullState) => (p.1, ()))
      (fun p => p.1.toNat)
      (fun p ml =>
        p.1.toNat ≤ c.extend_cap ∧ PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
        p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) ml)
      (fun Je hJe => by
        c0_hsteps
        exact hJe (BitVec.ofNat 64 s1.scratch.extend_len, s1) m1
          ⟨by rw [hsc1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hel,
           hcore1, hs1, hm1⟩)
      (fun Je ⟨end_v, s2⟩ m2 ⟨hend_le, hcore2, hs2, hm2⟩ ihe => ?_)
    dsimp only at hend_le hcore2 hs2 hm2 ihe ⊢
    c0_hsplit
    · have hend_pos : 0 < end_v.toNat := by c0_bound
      have hesl2 : s2.scratch.extend_stk.length = c.extend_cap := hs2.scratch_ok.extend_stk_len
      c0_hsteps_nogrp
      -- Backward scan loop: `while (start > 0ULL) { ... if (ext[start] & BLK) break; }`
      refine wp_while_break_state (α := BitVec 64) (β := BitVec 64)
        (fun sv => (sv, ()))
        (fun sv ml => sv.toNat < end_v.toNat ∧ ml = m2)
        (fun sv => (sv, ()))
        BitVec.toNat
        (fun sv ml => sv.toNat ≤ end_v.toNat ∧ ml = m2)
        (fun B start_v mb ⟨hstart_lt, hm_eq⟩ => ?_)
        (fun B L start_v ml hB hL ⟨hstart_le, hm_eq⟩ => ?_)
        (fun _ _ _ hL => by c0_hsteps; exact hL end_v m2 ⟨Nat.le_refl _, rfl⟩)
      · -- After break from backward scan (`start_v < end_v`)
        dsimp only at hstart_lt hm_eq ⊢; subst mb
        have hstart_ext : start_v.toNat < s2.scratch.extend_stk.length := by omega
        c0_hsteps_nogrp
        refine wp_join_state0 (α := FullState)
          (fun s3 m3 => PreservesCoreSlice (fullExtendSlice c).coreProj s2 s3 ∧ s3.LengthsOk c ∧
            (FullMem c s3 ⋆ R) m3)
          (fun Jext s3 m3 ⟨hcore3, hs3, hm3⟩ => by
            c0_hsteps
            exact ihe (start_v, s3) m3 (by dsimp only; exact hstart_lt)
              ⟨by dsimp only; omega, hcore2.trans hcore3, hs3, hm3⟩)
          (fun Jext hJext => by
            c0_hsplit
            · -- `EXT_COMPACT_FLAG` branch
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun s3 m3 => PreservesCoreSlice (fullExtendSlice c).coreProj s2 s3 ∧
                  s3.LengthsOk c ∧ (FullMem c s3 ⋆ R) m3)
                (fun Jcm s3 m3 h => by c0_hsteps; exact hJext s3 m3 h)
                (fun Jcm hJcm => by
                  c0_hsplit
                  · c0_hsplit
                    · let ncv := (s2.scratch.extend_stk[start_v.toNat]'hstart_ext &&&
                        0x3FFFFFFF#32).setWidth 64
                      have hncv_eq : ncv.toNat =
                          (s2.scratch.extend_stk[start_v.toNat]'hstart_ext &&&
                            0x3FFFFFFF#32).toNat := by
                        dsimp only [ncv]; exact zext_toNat _ (by decide)
                      have hncv_lt : ncv.toNat < 2 ^ 30 := by
                        rw [hncv_eq, BitVec.toNat_and,
                          show (0x3FFFFFFF#32 : BitVec 32).toNat = 2 ^ 30 - 1 from rfl,
                          Nat.and_two_pow_sub_one_eq_mod]
                        exact Nat.mod_lt _ (by decide)
                      have hs1ncv_le : start_v.toNat + 1 + ncv.toNat ≤ end_v.toNat := by
                        have h64 : start_v.toNat + 1 + ncv.toNat < 2 ^ 64 := by omega
                        have h1 : (start_v.toNat + BitVec.toNat (1#64) + ncv.toNat) % 2 ^ 64 ≤
                            end_v.toNat := by rw [hncv_eq]; assumption
                        rw [show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h64] at h1
                        exact h1
                      have hncv_mx : ncv.toNat ≤ c.max_vars := by
                        have h1 : ncv.toNat ≤ c.max_vars % 2 ^ 64 := by
                          rw [hncv_eq]; assumption
                        omega
                      -- Loop 2a: backward unmap `while (k > 0ULL)`
                      c0_hsteps_nogrp
                      refine wp_while_state
                        (fun (p : BitVec 64 × FullState) => (p.1, ()))
                        (fun p => p.1.toNat)
                        (fun p mk =>
                          p.1.toNat ≤ ncv.toNat ∧
                          PreservesCoreSlice (fullExtendSlice c).coreProj s2 p.2 ∧
                          p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) mk)
                        (fun Jk hJk => by
                          c0_hsteps; exact hJk (ncv, s2) m2 ⟨Nat.le_refl _, rfl, hs2, hm2⟩)
                        (fun Jk ⟨kv, sk⟩ mk ⟨hk_le, hcorek, hsk, hmk⟩ ihk => ?_)
                      dsimp only at hk_le hcorek hsk hmk ihk ⊢
                      c0_hsplit
                      · have hk_pos : 0 < kv.toNat := by c0_bound
                        have hk1 : (kv - 1#64).toNat = kv.toNat - 1 := by bv_omega
                        obtain ⟨_, _, _, _, _, _⟩ := fullExtend_preserves_nonVals hcorek
                        have hesk : sk.scratch.extend_stk = s2.scratch.extend_stk :=
                          (fullExtend_preserves_nonVals hcorek).1 ▸ rfl
                        have hk_add64 : start_v.toNat + 1 + (kv.toNat - 1) < 2 ^ 64 := by omega
                        have hext_k_eq : (start_v + 1#64 + (kv - 1#64)).toNat =
                            start_v.toNat + 1 + (kv.toNat - 1) := by
                          rw [BitVec.toNat_add, BitVec.toNat_add, hk1,
                            show (1#64 : BitVec 64).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : start_v.toNat + 1 < 2 ^ 64),
                            Nat.mod_eq_of_lt hk_add64]
                        have hext_k : (start_v + 1#64 + (kv - 1#64)).toNat <
                            sk.scratch.extend_stk.length := by
                          rw [hesk, hesl2, hext_k_eq]; omega
                        c0_hsteps_nogrp
                        refine wp_join_state0 (α := FullState)
                          (fun sk' mk' => PreservesCoreSlice (fullExtendSlice c).coreProj sk sk' ∧
                            sk'.LengthsOk c ∧ (FullMem c sk' ⋆ R) mk')
                          (fun _ sk' mk' ⟨hck', hsk', hmk'⟩ => by
                            c0_hsteps
                            exact ihk (kv - 1#64, sk') mk' (by dsimp only; omega)
                              ⟨by dsimp only; omega, hcorek.trans hck', hsk', hmk'⟩)
                          (fun Jk2 hJk2 => by
                            c0_hsplit
                            · have hext_c0 : (start_v + 1#64 + (kv - 1#64)).toNat =
                                  (start_v.toNat + BitVec.toNat (1 : BitVec 64) +
                                    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + kv.toNat)) %
                                    2 ^ 64 := by
                                rw [hext_k_eq]
                                change start_v.toNat + 1 + (kv.toNat - 1) =
                                  (start_v.toNat + 1 + (2 ^ 64 - 1 + kv.toNat)) % 2 ^ 64
                                omega
                              have hov_32 : (sk.scratch.extend_stk[(start_v + 1#64 +
                                    (kv - 1#64)).toNat]'hext_k).toNat < c.max_vars % 2 ^ 64 := by
                                simpa only [hext_c0] using hc
                              let ov64 := (sk.scratch.extend_stk[(start_v + 1#64 +
                                (kv - 1#64)).toNat]'hext_k).setWidth 64
                              have hov_lt : ov64.toNat < c.max_vars := by
                                dsimp only [ov64]; rw [zext_toNat _ (by decide)]; omega
                              have hvlk := hsk.core_ok.vals_len
                              have hk_shl0 : ((kv - 1#64) <<< (1 : Nat)).toNat <
                                  sk.core.vals.length := by
                                rw [hvlk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                  show (2 : Nat) ^ 1 = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                                omega
                              have hk_shl1 : (((kv - 1#64) <<< (1 : Nat)) ||| 1#64).toNat <
                                  sk.core.vals.length := by
                                rw [hvlk, m4_bv64_shl1_or1 (by omega)]; omega
                              have hov_shl0 : (ov64 <<< (1 : Nat)).toNat < sk.core.vals.length := by
                                rw [hvlk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                  show (2 : Nat) ^ 1 = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                                omega
                              have hov_shl1 : ((ov64 <<< (1 : Nat)) ||| 1#64).toNat <
                                  (sk.core.vals.set (ov64 <<< (1 : Nat)).toNat
                                    (sk.core.vals[((kv - 1#64) <<< (1 : Nat)).toNat]'hk_shl0)
                                  ).length := by
                                rw [List.length_set, hvlk, m4_bv64_shl1_or1 (by omega)]; omega
                              c0_hsteps
                              let sk' : FullState := { sk with core := { sk.core with vals :=
                                ((sk.core.vals.set (ov64 <<< (1 : Nat)).toNat
                                  (sk.core.vals[((kv - 1#64) <<< (1 : Nat)).toNat]'hk_shl0)).set
                                  ((ov64 <<< (1 : Nat)) ||| 1#64).toNat
                                  (sk.core.vals[(((kv - 1#64) <<< (1 : Nat)) |||
                                    1#64).toNat]'hk_shl1)) } }
                              exact hJk2 sk' _
                                ⟨rfl, ⟨{ hsk.core_ok with
                                    vals_len := by dsimp only [sk']; simp [hvlk] },
                                  hsk.scratch_ok⟩, hm⟩
                            · c0_hsteps; exact hJk2 sk mk ⟨rfl, hsk, hmk⟩)
                      · -- Loop 2b: `while (g < mx)` zeroing/defaulting gaps `[0..max_vars)`
                        c0_hsteps_nogrp
                        refine wp_while_state
                          (fun (p : BitVec 64 × BitVec 64 × FullState) => (p.1, p.2.1, ()))
                          (fun p => c.max_vars - p.2.1.toNat)
                          (fun p mg =>
                            p.1.toNat ≤ ncv.toNat ∧ p.2.1.toNat ≤ c.max_vars ∧
                            PreservesCoreSlice (fullExtendSlice c).coreProj s2 p.2.2 ∧
                            p.2.2.LengthsOk c ∧ (FullMem c p.2.2 ⋆ R) mg)
                          (fun Jg hJg => by
                            c0_hsteps
                            exact hJg (0#64, 0#64, sk) mk
                              ⟨Nat.zero_le _, Nat.zero_le _, hcorek, hsk, hmk⟩)
                          (fun Jg ⟨jv, gv, sg⟩ mg ⟨hj_le, hg_le, hcoreg, hsg, hmg⟩ ihg => ?_)
                        dsimp only at hj_le hg_le hcoreg hsg hmg ihg ⊢
                        c0_hsplit
                        · have hg_lt : gv.toNat < c.max_vars := by
                            have h1 : gv.toNat < c.max_vars % 2 ^ 64 := by assumption
                            omega
                          have hg1 : (gv + 1#64).toNat = gv.toNat + 1 := by
                            simp only [bv_c0]; omega
                          have hesg : sg.scratch.extend_stk = s2.scratch.extend_stk :=
                            (fullExtend_preserves_nonVals hcoreg).1 ▸ rfl
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun b => (b, ()))
                            (fun nxt => jv.toNat < ncv.toNat ∨ nxt.toNat = c.max_vars)
                            (fun _ nxt hnxt => by
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i64])
                                (fun (p : BitVec 64 × FullState) => (p.1, ()))
                                (fun p mg' =>
                                  p.1.toNat ≤ ncv.toNat ∧
                                  PreservesCoreSlice (fullExtendSlice c).coreProj sg p.2 ∧
                                  p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) mg')
                                (fun _ ⟨j', sg'⟩ mg' ⟨hj', hcg', hsg', hmg'⟩ => by
                                  dsimp only at hj' hcg' hsg' hmg' ⊢
                                  c0_hsteps
                                  exact ihg (j', gv + 1#64, sg') mg'
                                    (by dsimp only; rw [hg1]; omega)
                                    ⟨hj', by rw [hg1]; omega, hcoreg.trans hcg', hsg', hmg'⟩)
                                (fun _ hJj => by
                                  c0_hsplit
                                  · have hj_lt : jv.toNat < ncv.toNat := by
                                      rcases hnxt with h | h
                                      · exact h
                                      · exfalso; have hgv : gv.toNat = nxt.toNat :=
                                          congrArg BitVec.toNat (by assumption)
                                        omega
                                    have hj1 : (jv + 1#64).toNat = jv.toNat + 1 := by
                                      simp only [bv_c0]; omega
                                    c0_hsteps
                                    exact hJj (jv + 1#64, sg) mg
                                      ⟨by rw [hj1]; omega, rfl, hsg, hmg⟩
                                  · have hvlg := hsg.core_ok.vals_len
                                    have hg_shl0 : (gv <<< (1 : Nat)).toNat <
                                        sg.core.vals.length := by
                                      rw [hvlg, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                        show (2 : Nat) ^ 1 = 2 from rfl,
                                        Nat.mod_eq_of_lt (by omega)]
                                      omega
                                    have hg_shl1 : ((gv <<< (1 : Nat)) ||| 1#64).toNat <
                                        (sg.core.vals.set (gv <<< (1 : Nat)).toNat 1#8).length := by
                                      rw [List.length_set, hvlg, m4_bv64_shl1_or1 (by omega)]; omega
                                    c0_hsteps
                                    let sg' : FullState := { sg with core := { sg.core with vals :=
                                      ((sg.core.vals.set (gv <<< (1 : Nat)).toNat 1#8).set
                                        ((gv <<< (1 : Nat)) ||| 1#64).toNat
                                        (BitVec.setWidth 8 (-1#32))) } }
                                    exact hJj (jv, sg') _ ⟨hj_le, rfl,
                                      ⟨{ hsg.core_ok with
                                          vals_len := by dsimp only [sg']; simp [hvlg] },
                                        hsg.scratch_ok⟩, hm⟩))
                            (fun _ hJn => by
                              c0_hsplit
                              · have hj_lt : jv.toNat < ncv.toNat := by c0_bound
                                have hj_add64 : start_v.toNat + 1 + jv.toNat < 2 ^ 64 := by omega
                                have hext_j_eq : (start_v + 1#64 + jv).toNat =
                                    start_v.toNat + 1 + jv.toNat := by
                                  rw [BitVec.toNat_add, BitVec.toNat_add,
                                    show (1#64 : BitVec 64).toNat = 1 from rfl,
                                    Nat.mod_eq_of_lt (by omega : start_v.toNat + 1 < 2 ^ 64),
                                    Nat.mod_eq_of_lt hj_add64]
                                have hext_j : (start_v + 1#64 + jv).toNat <
                                    sg.scratch.extend_stk.length := by
                                  rw [hesg, hesl2, hext_j_eq]; omega
                                c0_hsteps; exact hJn _ (Or.inl hj_lt)
                              · c0_hsteps
                                exact hJn (BitVec.ofNat 64 c.max_vars)
                                  (Or.inr (bv64_ofNat_toNat (by omega))))
                        · c0_hsteps; exact hJcm sg mg ⟨hcoreg, hsg, hmg⟩
                    · c0_hsteps; exact hJcm s2 m2 ⟨rfl, hs2, hm2⟩
                  · c0_hsteps; exact hJcm s2 m2 ⟨rfl, hs2, hm2⟩)
            · -- Normal witness branch (`(head &&& 0x40000000) == 0`)
              c0_hsteps_nogrp
              refine wp_while_break_state (α := BitVec 64) (β := Bool × BitVec 64)
                (fun p => (p.1, p.2, ()))
                (fun _ ml => ml = m2)
                (fun pv => (pv, ()))
                (fun pv => end_v.toNat - pv.toNat)
                (fun pv ml => start_v.toNat ≤ pv.toNat ∧ pv.toNat ≤ end_v.toNat ∧ ml = m2)
                (fun _ ⟨sat, pv_end⟩ mb hm_eq => ?_)
                (fun B L pv ml hB hL ⟨hps, hpe, hm_eq⟩ => ?_)
                (fun _ _ _ hL => by
                  c0_hsteps; exact hL start_v m2 ⟨Nat.le_refl _, by omega, rfl⟩)
              · -- After `sat` scan loop
                dsimp only at hm_eq ⊢; subst mb
                let head := s2.scratch.extend_stk[start_v.toNat]'hstart_ext
                let blk := head &&& 0x7FFFFFFF#32
                have hblk_v_lt : blk.toNat < 2 ^ 31 := m4_bv32_and_mask_lt
                refine wp_join_state0 (α := FullState)
                  (fun s3 m3 => PreservesCoreSlice (fullExtendSlice c).coreProj s2 s3 ∧
                    s3.LengthsOk c ∧ (FullMem c s3 ⋆ R) m3)
                  (fun _ s3 m3 ⟨hcore3, hs3, hm3⟩ => by
                    c0_hsteps; exact hJext s3 m3 ⟨hcore3, hs3, hm3⟩)
                  (fun _ hJif => by
                    c0_hsplit
                    · c0_hsteps; exact hJif s2 m2 ⟨rfl, hs2, hm2⟩
                    · c0_hsplit
                      · have hblk_v : blk.toNat / 2 < c.max_vars := by
                          have h1 : blk.toNat / 2 < c.max_vars % 2 ^ 64 := by
                            change blk.toNat / 2 < c.max_vars % 2 ^ 64 at hc; exact hc
                          omega
                        have hvl2 := hs2.core_ok.vals_len
                        have hblk0 : (blk.setWidth 64).toNat < s2.core.vals.length := by
                          rw [hvl2, zext_toNat _ (by decide)]; omega
                        have hblk_xor : ((blk ^^^ 1#32).setWidth 64).toNat <
                            (s2.core.vals.set (blk.setWidth 64).toNat 1#8).length := by
                          rw [List.length_set, hvl2, zext_toNat _ (by decide)]
                          exact m4_bv32_xor1_lt hblk_v
                        c0_hsteps
                        let s2' : FullState := { s2 with core := { s2.core with vals :=
                          ((s2.core.vals.set (blk.setWidth 64).toNat 1#8).set
                            ((blk ^^^ 1#32).setWidth 64).toNat
                            (BitVec.setWidth 8 (-1#32))) } }
                        exact hJif s2' _
                          ⟨rfl, ⟨{ hs2.core_ok with
                              vals_len := by dsimp only [s2']; simp [hvl2] },
                            hs2.scratch_ok⟩, hm⟩
                      · c0_hsteps; exact hJif s2 m2 ⟨rfl, hs2, hm2⟩)
              · -- Body of `while (p < end)` witness satisfaction check
                dsimp only at hps hpe hm_eq ⊢; subst ml
                c0_hsplit
                · have hp_lt : pv.toNat < end_v.toNat := by c0_bound
                  have hp1 : (pv + 1#64).toNat = pv.toNat + 1 := by simp only [bv_c0]; omega
                  have hp_ext : pv.toNat < s2.scratch.extend_stk.length := by omega
                  let lit := s2.scratch.extend_stk[pv.toNat]'hp_ext &&& 0x7FFFFFFF#32
                  have hlit_lt31 : lit.toNat < 2 ^ 31 := m4_bv32_and_mask_lt
                  c0_hsteps_nogrp
                  refine wp_join0 (fun m' => m' = m2)
                    (fun _ _ hm_eq => by
                      dsimp only at hm_eq ⊢; rw [hm_eq]; c0_hsteps
                      exact hL (pv + 1#64) m2 (by rw [hp1]; omega)
                        ⟨by rw [hp1]; omega, by rw [hp1]; omega, rfl⟩)
                    (fun _ hJnx => by
                      c0_hsplit
                      · have hlit_v : lit.toNat / 2 < c.max_vars := by
                          have h1 : lit.toNat / 2 < c.max_vars % 2 ^ 64 := by
                            change lit.toNat / 2 < c.max_vars % 2 ^ 64 at hc; exact hc
                          omega
                        have hlit_vals : (lit.setWidth 64).toNat < s2.core.vals.length := by
                          rw [hs2.core_ok.vals_len, zext_toNat _ (by decide)]; omega
                        c0_hsplit
                        · c0_hsteps; exact hB (true, pv) m2 rfl
                        · c0_hsteps; exact hJnx m2 rfl
                      · c0_hsteps; exact hJnx m2 rfl)
                · c0_hsteps; exact hB (false, pv) m2 rfl)
      · -- Body of backward scan loop `while (start > 0ULL)`
        dsimp only at hstart_le hm_eq ⊢; subst ml
        c0_hsplit
        · have hs_pos : 0 < start_v.toNat := by c0_bound
          have hsm1 : (start_v - 1#64).toNat < start_v.toNat := by bv_omega
          have hsm1_ext : (start_v - 1#64).toNat < s2.scratch.extend_stk.length := by omega
          c0_hsteps_nogrp; c0_hsplit
          · c0_hsteps; exact hB (start_v - 1#64) m2 ⟨by omega, rfl⟩
          · c0_hsteps; exact hL (start_v - 1#64) m2 hsm1 ⟨by omega, rfl⟩
        · c0_hsteps; exact hB start_v m2 ⟨by omega, rfl⟩
    · c0_hsteps; exact hQ () s2 m2 hcore2 hs2 trivial hm2

/-- `Func.wp` proof for unified M4 `full_probe(h, initial)` combining M3c/M3b/M3a probing with
M4c hyper-ternary resolution (`full_ternary(h, 2, 4096)`), against `schedProbeSpec`. -/
theorem m4_probe_wp (Γ : Env)
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
    (hTern : ∀ a m Q X, FullM4Ternary.fullTernarySpec a m Q X →
      Γ "full_ternary" [i64, i64, i64] [i64] a m Q X)
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
                        (fun s5t m5t => FullSparseInv c F0 s5t ∧ s5t.core.cur_level = 0 ∧
                          s5t.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s5t ⋆ R) m5t)
                        (fun _ s5t m5t ⟨hinv5t, hcl5t, hfu5t, hm5t⟩ => by
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
                                m4_sparseInv_with_scratch_keep hinv6
                                  { hinv6.lengths.scratch_ok with } rfl rfl
                              exact hQ 1#64 s7 _ hinv7.lengths hfu6 (Or.inl rfl)
                                (fun h => by cases h) (fun _ => ⟨hinv7, hcl6⟩) hm)
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
                                        sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                        (FullMem c sb ⋆ R) mb)
                                      (fun _ sb mb ⟨hinvb, hclb, hfub, hmb⟩ => by
                                        c0_hsteps; c0_call hMin; intro pbud0 _
                                        c0_hsteps_nogrp; c0_hsplit
                                        · c0_hsteps; c0_call hPRun
                                          refine ⟨c, F0, sb, R, rfl, hinvb, hmb, ?_⟩
                                          intro rp sc mc hinvc hclc _ hfuc _ hupc _ hmc
                                          c0_hsteps
                                          · exact hQ 20#64 sc mc hinvc.lengths (by omega)
                                              (Or.inr rfl) (fun _ => hupc hc)
                                              (fun h => by cases h) hmc
                                          exact hJ6 sc mc ⟨hinvc, hclc, by omega, hmc⟩
                                        · c0_hsteps; exact hJ6 sb mb ⟨hinvb, hclb, hfub, hmb⟩)
                                      (fun Jb hJb => by
                                        c0_hsplit
                                        · c0_hsteps; c0_call hTrans
                                          refine ⟨c, F0, sa, R, rfl, hinva, hma, ?_⟩
                                          intro rt sb mb hinvb hclb _ _ hfub _ hutb hmb
                                          have hclb' := hclb hcla
                                          c0_hsteps
                                          · exact hQ 20#64 sb mb hinvb.lengths (by omega)
                                              (Or.inr rfl) (fun _ => hutb hc) (fun h => by cases h)
                                              hmb
                                          exact hJb sb mb ⟨hinvb, hclb', by omega, hmb⟩
                                        · c0_hsteps; exact hJb sa ma ⟨hinva, hcla, hfua, hma⟩))
                                  (fun Ja hJa => by
                                    c0_hsplit
                                    · c0_hsteps; c0_call hBone
                                      refine ⟨c, F0, s5t, R, rfl, hinv5t, hm5t, ?_⟩
                                      intro rb sa ma hinva hcla _ hfua _ huba hma; c0_hsteps
                                      · exact hQ 20#64 sa ma hinva.lengths (by omega) (Or.inr rfl)
                                          (fun _ => huba hc) (fun h => by cases h) hma
                                      exact hJa sa ma ⟨hinva, hcla, by omega, hma⟩
                                    · c0_hsteps; exact hJa s5t m5t ⟨hinv5t, hcl5t, hfu5t, hm5t⟩)
                              · c0_hsteps; c0_call hTail
                                refine ⟨c, F0, s5t, R, rfl, hinv5t, hcl5t, hm5t, ?_⟩
                                intro rt s6 m6 hinv6 hcl6 hfu6 _ hut6 hm6; c0_hsteps
                                · exact hQ 20#64 s6 m6 hinv6.lengths (by omega) (Or.inr rfl)
                                    (fun _ => hut6 hc) (fun h => by cases h) hm6
                                exact hJ6 s6 m6 ⟨hinv6, hcl6, by omega, hm6⟩))
                        (fun J5t hJ5t => by
                          c0_hsplit
                          · c0_hsteps; c0_call hTern; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
                            intro rt s5t m5t hinv5t hfu5t hdomt hut hclt hm5t; c0_hsteps
                            · exact hQ 20#64 s5t m5t hinv5t.lengths (by omega) (Or.inr rfl)
                                (fun _ => hut hc) (fun h => by cases h) hm5t
                            exact hJ5t s5t m5t
                              ⟨hinv5t, hclt (hdomt.resolve_right hc), by omega, hm5t⟩
                          · c0_hsteps; exact hJ5t s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩))
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
          m4_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for unified M4 `full_eliminate(h, initial)` (pre-BVE `full_factor`, skipping
redundant post-BVE `full_factor` per Tier-1 ablation) against `schedEliminateSpec`. -/
theorem m4_eliminate_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
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
          (fun _ fbud _ => by
            c0_hsteps; c0_call hMin; intro _ _
            c0_hsteps; c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hden1, hm1, ?_⟩
            intro fs s2 m2 hden2 _ hfu2 _ huf2 hm2
            let s2r : FullState :=
              { s2 with scratch := { s2.scratch with fwd_sub_cnt := s1.scratch.fwd_sub_cnt } }
            have hden2r : FullDenseInv c F0 s2r :=
              m4_denseInv_with_scratch_keep hden2 { hden2.lengths.scratch_ok with } rfl rfl
            have hfu2r : s2r.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change s2.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfu2]; omega
            c0_hsplit
            · c0_hsteps; c0_call hReb; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
              intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; c0_hsteps
              exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => huf2 hc) hm3
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                (fun b => (b, ())) (fun _ => True)
                (fun _ _ _ => by
                  c0_hsteps; c0_call hMin; intro fact_bud _
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FullState)
                    (fun s2f m2f => FullDenseInv c F0 s2f ∧
                      s2f.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2f ⋆ R) m2f)
                    (fun _ s2f m2f ⟨hden2f, hfu2f, hm2f⟩ => by
                      let cv2 := s2f.core.cur_vars
                      have hcv2_le : cv2 ≤ c.max_vars := hden2f.lengths.core_ok.cur_vars_le
                      have hmx := c.hmaxv; unfold dimacsBound at hmx
                      have hcv2_64 : cv2 < 2 ^ 64 := by omega
                      have htl2 := hden2f.lengths.scratch_ok.tarjan_mark_len
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (ti, ()) mt => ∃ tmki : List (BitVec 32),
                          tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv2 ∧
                          (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                          (FullMem c { s2f with scratch :=
                            { s2f.scratch with tarjan_mark := tmki } } ⋆ R) mt)
                        (fun (ti, ()) _ => cv2 - ti.toNat)
                        (fun Jt hJt => by
                          c0_hsteps; exact hJt (0#64, ()) m2f
                            ⟨s2f.scratch.tarjan_mark, htl2, Nat.zero_le _,
                             fun _ h => by simp at h, hm2f⟩)
                        (fun Jt (ti, ()) mt ⟨tmki, htli, hti_le, hinit, hmt⟩ iht => ?_)
                      c0_hsplit
                      · have hti_lt : ti.toNat < cv2 := by
                          have hlt : ti.toNat < (BitVec.ofNat 64 cv2).toNat := by assumption
                          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hlt
                        have hti_arr : ti.toNat < tmki.length := by omega
                        have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by simp only [bv_c0]; omega
                        c0_hsteps
                        exact iht (ti + 1#64, ()) m (by dsimp only; omega)
                          ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega,
                           fun k hk => by
                             rw [hti1] at hk
                             by_cases hkt : k = ti.toNat
                             · subst hkt; rw [List.getElem?_set_self (by omega), Option.getD_some]
                             · rw [List.getElem?_set_ne (Ne.symm hkt)]; exact hinit k (by omega),
                           hm⟩
                      · have hti_eq : ti.toNat = cv2 := by
                          have hnot : ¬ ti.toNat < (BitVec.ofNat 64 cv2).toNat := by assumption
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hnot
                          omega
                        rw [hti_eq] at hinit
                        let s2t : FullState :=
                          { s2f with scratch := { s2f.scratch with tarjan_mark := tmki } }
                        have hden2t : FullDenseInv c F0 s2t :=
                          m4_denseInv_with_scratch_keep hden2f
                            { hden2f.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                        have htmk2 := m4_tmkZero_of_init_loop hinit
                        have hfu2t : s2t.core.fuel.toNat ≤ s.core.fuel.toNat := hfu2f
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                          (fun b => (b, ())) (fun _ => True)
                          (fun _ bve_lim _ => by
                            c0_hsteps; c0_call hBve
                            refine ⟨c, F0, s2t, R, rfl, hden2t, htmk2, hmt, ?_⟩
                            intro res s3 m3 hden3 _ hfu3 _ hres_u hm3
                            c0_hsteps; c0_call hReb
                            refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                            intro rr se me hspe hcle hfue _ hue hme
                            let se' : FullState :=
                              { se with scratch :=
                                { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                            have hspe' : FullSparseInv c F0 se' :=
                              m4_sparseInv_with_scratch_keep hspe
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
                          (fun Jb hJb => by
                            c0_hsteps
                            · exact hJb _ trivial
                            · c0_call hMin; intro b _; exact hJb b trivial))
                    (fun Jf1 hJf1 => by
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun sg mg => FullDenseInv c F0 sg ∧
                          sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                        (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                          c0_hsteps; c0_call hFact
                          refine ⟨c, F0, sg, R, rfl, hdeng, hmg, ?_⟩
                          intro _ sf mf hdenf _ hfuf _ hmf
                          exact hJf1 sf mf ⟨hdenf, by rw [hfuf]; exact hfug, hmf⟩)
                        (fun Jdo1 hJdo1 => by
                          c0_hsteps
                          · exact hJdo1 s2r m ⟨hden2r, hfu2r, hm⟩
                          · exact hJdo1 s2r m ⟨hden2r, hfu2r, hm⟩
                          · exact hJf1 s2r m ⟨hden2r, hfu2r, hm⟩)))
                (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial))
          (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial)
      · have hsp1 : FullSparseInv c F0 s1 := hfail_s hc
        let s1' : FullState :=
          { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
        have hsp1' : FullSparseInv c F0 s1' :=
          m4_sparseInv_with_scratch_keep hsp1 { hsp1.lengths.scratch_ok with } rfl rfl
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
        intro d_scale
        c0_hsteps; c0_call hIsqrt; intro sq _ _ _
        c0_hsteps; c0_call hMin; intro delta _
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          m4_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        let s0c : FullState :=
          { s0b with scratch :=
            { s0b.scratch with elim_bound := s0b.scratch.elim_bound + 2#64 } }
        have hinv0c : FullSparseInv c F0 s0c :=
          m4_sparseInv_with_scratch_keep hinv0b { hinv0b.lengths.scratch_ok with } rfl rfl
        c0_hsteps
        · exact hJ1 s0c _ ⟨hinv0c, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for unified M4 `full_preprocess(h)` (adding `full_compact` + `FullCfgCompat`)
against `m4PreprocessSpec`. -/
theorem m4_preprocess_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X →
      Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X)
    (hCNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hComp : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, m4PreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hinv.exists_witness
  unfold Func.wp full_preprocess_body
  c0_hsteps; c0_call hProp
  refine ⟨c, F0, F_cur, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hm, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
    hlen1 hw1 _ hperm1 hfu1 _ _ hpr1 _ _ hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    ⟨hlen1, hw1, ⟨fun v hv => hspW.2.2.1.1 v hv, fun l hl => hspW.2.2.1.2 l hl⟩,
     fun ref href hng => by
       have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm1.2.1 ▸ href
       obtain ⟨_, hgb, hp⟩ := hperm1.2.2 ref href0
       exact (hp.map (· / 2)).nodup_iff.mpr (hspW.2.2.2.1 ref href0 (hgb.symm.trans hng)),
     hspW.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun ref href => by
       change ref ∈ fullArenaClauseRefsCore s1.core; rw [hperm1.2.1]; exact href,
     hspW.2.2.2.2.2⟩
  have hcl1 : s1.core.cur_level = 0 := hcl0
  c0_hsplit
  · c0_hsteps
    exact hQ 20#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1
      (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => level0_unsat_of_conflict_okW (s := s1) hw1 hcl1 (hpr1 hc).2.2)
      (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 (Or.inl rfl) hfu1
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 (Or.inl rfl) hfu1
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
      c0_hsplit
      · c0_hsteps
        exact hQ 10#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths
          (Or.inr (Or.inr (Or.inl rfl))) hfu2
          (fun h => by cases h) (fun h => by cases h) (fun _ => hinv2.2.2.2.1.2) hm2
      c0_hsteps; c0_call hScale; refine ⟨c, s2, R, rfl, hinv2.lengths, hm2, ?_⟩
      intro plim
      c0_hsteps
      let s2a : FullState := { s2 with scratch := { s2.scratch with probe_limit := plim } }
      have hinv2a : FullSparseInv c F0 s2a :=
        m4_sparseInv_with_scratch_keep hinv2 { hinv2.lengths.scratch_ok with } rfl rfl
      c0_call hScale; refine ⟨c, s2a, R, rfl, hinv2a.lengths, hm, ?_⟩
      intro elim_raw
      c0_hsteps; c0_call hMin; intro elim _
      c0_hsteps
      let s2b : FullState := { s2a with scratch := { s2a.scratch with elim_limit := elim } }
      have hinv2b : FullSparseInv c F0 s2b :=
        m4_sparseInv_with_scratch_keep hinv2a { hinv2a.lengths.scratch_ok with } rfl rfl
      c0_call hProbe; refine ⟨c, F0, s2b, R, rfl, hinv2b, hcl2, hm, ?_⟩
      intro rp s3 m3 hlen3 hfu3 hrp_dom hup3 hsp3 hm3
      dsimp only [s2b, s2a] at hfu3
      have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps
      · exact hQ 20#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3
          (Or.inr (Or.inr (Or.inr rfl))) hfu3'
          (fun _ => hup3 hc) (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 (Or.inl rfl) hfu3'
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 (Or.inl rfl) hfu3'
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm3
      obtain ⟨hinv3, hcl3⟩ := hsp3 (hrp_dom.resolve_right (by assumption))
      c0_call hElim; refine ⟨c, F0, s3, R, rfl, hinv3, hcl3, hm3, ?_⟩
      intro re s4 m4 hinv4 hcl4 hfu4 _ hue4 hm4
      have hfu4' : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps_nogrp
      · exact hQ 20#64 c s4 m4 (FullM4Compact.FullCfgCompat.refl c) hinv4.lengths
          (Or.inr (Or.inr (Or.inr rfl))) hfu4'
          (fun _ => hue4 hc) (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 20#64 c s4 m4 (FullM4Compact.FullCfgCompat.refl c) hinv4.lengths
          (Or.inr (Or.inr (Or.inr rfl))) hfu4'
          (fun _ => hinv4.inconsistent_unsat hc) (fun h => by cases h)
          (fun h => by cases h) hm4
      · exact hQ 0#64 c s4 m4 (FullM4Compact.FullCfgCompat.refl c) hinv4.lengths (Or.inl rfl)
          hfu4' (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm4
      refine wp_join_state0 (α := FullCfg × FullState)
        (fun ⟨c5, s5⟩ m5 =>
          FullM4Compact.FullCfgCompat c c5 ∧ FullSparseInv c5 F0 s5 ∧
          s5.core.cur_level = 0 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullMem c5 s5 ⋆ R) m5)
        (fun _ ⟨c5, s5⟩ m5 ⟨hcomp5, hinv5, hcl5, hfu5, hm5⟩ => by
          have hch5 : c5.hdr = c.hdr := hcomp5.hdr
          rw [← hch5]
          c0_hsteps
          · exact hQ 20#64 c5 s5 m5 hcomp5 hinv5.lengths (Or.inr (Or.inr (Or.inr rfl))) hfu5
              (fun _ => hinv5.inconsistent_unsat hc) (fun h => by cases h)
              (fun h => by cases h) hm5
          · exact hQ 0#64 c5 s5 m5 hcomp5 hinv5.lengths (Or.inl rfl) hfu5
              (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm5
          · exact hQ 10#64 c5 s5 m5 hcomp5 hinv5.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu5
              (fun h => by cases h) (fun h => by cases h) (fun _ => hinv5.2.2.2.1.2) hm5
          · c0_call hScale; refine ⟨c5, s5, R, rfl, hinv5.lengths, hm5, ?_⟩
            intro plim2
            c0_hsteps
            let s5a : FullState :=
              { s5 with scratch := { s5.scratch with probe_limit := plim2 } }
            have hinv5a : FullSparseInv c5 F0 s5a :=
              m4_sparseInv_with_scratch_keep hinv5 { hinv5.lengths.scratch_ok with } rfl rfl
            c0_call hScale; refine ⟨c5, s5a, R, rfl, hinv5a.lengths, hm, ?_⟩
            intro elim2_raw
            c0_hsteps; c0_call hMin; intro elim2 _
            c0_hsteps
            let s5b : FullState :=
              { s5a with scratch := { s5a.scratch with elim_limit := elim2 } }
            have hinv5b : FullSparseInv c5 F0 s5b :=
              m4_sparseInv_with_scratch_keep hinv5a { hinv5a.lengths.scratch_ok with } rfl rfl
            exact hQ 1#64 c5 s5b _ hcomp5 hinv5b.lengths (Or.inr (Or.inl rfl)) hfu5
              (fun h => by cases h) (fun _ => ⟨hinv5b, hcl5⟩) (fun h => by cases h) hm)
        (fun Jc hJc => by
          c0_call hCNeed
          refine ⟨c, s4, R, rfl, hinv4.lengths, by omega, hm4, ?_⟩
          intro need _
          c0_hsplit
          · c0_hsteps; c0_call hComp; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
            intro cr c5 s5 m5 hcomp5 hinv5 hcr_dom _ hfu5 hu5 hcl5 hm5
            c0_hsteps
            · exact hQ 20#64 c5 s5 m5 hcomp5 hinv5.lengths (Or.inr (Or.inr (Or.inr rfl)))
                (by omega) (fun _ => hu5 hc) (fun h => by cases h) (fun h => by cases h) hm5
            · exact hQ 0#64 c5 s5 m5 hcomp5 hinv5.lengths (Or.inl rfl) (by omega)
                (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm5
            · exact hJc (c5, s5) m5 ⟨hcomp5, hinv5, hcl5 hc, by omega, hm5⟩
          · c0_hsteps
            exact hJc (c, s4) m4 ⟨FullM4Compact.FullCfgCompat.refl c, hinv4, hcl4, hfu4', hm4⟩))
    (fun Ju hJu => by
      c0_hsplit
      · c0_hsteps; c0_call hSweep
        refine ⟨c, F0, F_cur, s1, R, rfl, hspW1.1, hspW1.2.1, hspW1.2.2.2.1, hspW1.2.2.2.2.2,
          fun hpos => by omega, hm1, ?_⟩
        intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc1a m1a s1a
          hlen1a _ hext1a _ hll1a hw1a hnd1a _ _ _ hsr2 _ hm1a
        have hspW1a : FullSparseInvW c F0 F_cur s1a :=
          ⟨hlen1a, hw1a, hspW1.2.2.1, hnd1a,
           ⟨hll1a, hext1a.symm ▸ hspW1.2.2.2.2.1.2⟩, hspW1.2.2.2.2.2⟩
        have hcl1a : s1a.core.cur_level = 0 := hcl1
        c0_hsteps
        · exact hQ 20#64 c s1a m1a (FullM4Compact.FullCfgCompat.refl c) hlen1a
            (Or.inr (Or.inr (Or.inr rfl))) hfu1
            (fun _ => (hsr2 hc).2) (fun h => by cases h) (fun h => by cases h) hm1a
        c0_call hProp
        refine ⟨c, F0, F_cur, s1a, R, rfl, hspW1a.1, hspW1a.2.1, hspW1a.2.2.2.2.2, hm1a, ?_⟩
        intro pr1b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1b _ _ _ _ _ _ _ _ m1b s1b
          hlen1b hw1b _ hperm1b hfl1b _ _ hpr1b_1 _ _ hm1b
        have hspW1b : FullSparseInvW c F0 F_cur s1b :=
          ⟨hlen1b, hw1b, hspW1a.2.2.1,
           fun ref href hng => by
             have href0 : ref ∈ fullArenaClauseRefsCore s1a.core := hperm1b.2.1 ▸ href
             obtain ⟨_, hgb, hp⟩ := hperm1b.2.2 ref href0
             exact (hp.map (· / 2)).nodup_iff.mpr (hspW1a.2.2.2.1 ref href0 (hgb.symm.trans hng)),
           hspW1a.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun ref href => by
             change ref ∈ fullArenaClauseRefsCore s1b.core; rw [hperm1b.2.1]; exact href,
           hspW1a.2.2.2.2.2⟩
        have hfu1b : s1b.core.fuel.toNat ≤ s.core.fuel.toNat := by
          have h1 : s1a.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
          dsimp only [s1b]; omega
        c0_hsteps
        · exact hQ 20#64 c s1b m1b (FullM4Compact.FullCfgCompat.refl c) hlen1b
            (Or.inr (Or.inr (Or.inr rfl))) hfu1b
            (fun _ => level0_unsat_of_conflict_okW (s := s1b) hw1b hcl1a (hpr1b_1 hc).2.2)
            (fun h => by cases h) (fun h => by cases h) hm1b
        have hspW1c : FullSparseInvW c F0 F_cur
            { s1b with core := { s1b.core with unflushed := 0#64 } } :=
          ⟨⟨{ hspW1b.1.core_ok with }, hspW1b.1.scratch_ok⟩,
           { hspW1b.2.1 with
             arena := { hspW1b.2.1.arena with len_ok := hspW1b.2.1.arena.len_ok }
             watches := hspW1b.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
           hspW1b.2.2.1, hspW1b.2.2.2.1, hspW1b.2.2.2.2.1, hspW1b.2.2.2.2.2⟩
        exact hJu _ _ ⟨hspW1c.toSparse, hcl1a, hfu1b, hm⟩
      · c0_hsteps; exact hJu s1 m1 ⟨hspW1.toSparse, hcl1, hfu1, hm1⟩)

/-- `Func.wp` proof for unified M4 `full_simplify(h, do_probe, do_elim)` (lazy `full_reduce(h,
false)` + `full_compact` + `full_reorder(h, 256)`) against `m4SimplifySpec`. -/
theorem m4_simplify_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hRed : ∀ a m Q X, m4ReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X →
      Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X)
    (hCNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hComp : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hReord : ∀ a m Q X, m4ReorderSpec a m Q X →
      Γ "full_reorder" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m4SimplifySpec a m Q X → Func.wp Γ full_simplify_body a m Q X := by
  rintro ⟨h, do_probe, do_elim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain ⟨F_cur0, hw0⟩ := hinv.exists_witness
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
    have := hinv.lengths.core_ok.cur_vars_le; have := fullInv_max_vars_lt32 c; omega
  unfold Func.wp full_simplify_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0, hfu0, hm0⟩ => by
      c0_hsteps; c0_call hRed; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro r1 s1 m1 hinv1 _ hcl1_le hfu1 hur1 _ hm1
      have hcl1 : s1.core.cur_level = 0 := by omega
      have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.lengths hfu1'
          (Or.inr (Or.inr rfl)) (fun _ => hur1 hc) (fun h => by cases h) hm1
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths hfu2
              (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm2
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths hfu2
              (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm2
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun s3 m3 => FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ s3 m3 ⟨hinv3, hcl3, hfu3, hm3⟩ => by
              c0_hsteps_nogrp
              · exact hQ 20#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hinv3.lengths hfu3
                  (Or.inr (Or.inr rfl)) (fun _ => hinv3.inconsistent_unsat hc)
                  (fun h => by cases h) hm3
              · exact hQ 0#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hinv3.lengths hfu3
                  (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm3
              refine wp_join_state0 (α := FullCfg × FullState)
                (fun ⟨c4, s4⟩ m4 =>
                  FullM4Compact.FullCfgCompat c c4 ∧ FullSparseInv c4 F0 s4 ∧
                  s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c4 s4 ⋆ R) m4)
                (fun _ ⟨c4, s4⟩ m4 ⟨hcomp4, hinv4, hcl4, hfu4, hm4⟩ => by
                  have hch4 : c4.hdr = c.hdr := hcomp4.hdr
                  rw [← hch4]
                  c0_hsteps_nogrp
                  · exact hQ 20#64 c4 s4 m4 hcomp4 hinv4.lengths hfu4 (Or.inr (Or.inr rfl))
                      (fun _ => hinv4.inconsistent_unsat hc) (fun h => by cases h) hm4
                  · exact hQ 0#64 c4 s4 m4 hcomp4 hinv4.lengths hfu4 (Or.inl rfl)
                      (fun h => by cases h) (fun h => by cases h) hm4
                  refine wp_join_state0 (α := FullState)
                    (fun s5 m5 =>
                      FullSparseInv c4 F0 s5 ∧ s5.core.cur_level = 0 ∧
                      s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c4 s5 ⋆ R) m5)
                    (fun _ s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩ => by
                      c0_hsteps
                      exact hQ 1#64 c4 s5 m5 hcomp4 hinv5.lengths hfu5 (Or.inr (Or.inl rfl))
                        (fun h => by cases h) (fun _ => ⟨hinv5, hcl5⟩) hm5)
                    (fun Jr hJr => by
                      c0_hsplit
                      · c0_hsteps; c0_call hReord
                        refine ⟨c4, F0, s4, R, rfl, hinv4, hm4, ?_⟩
                        intro _ s5 m5 hinv5 _ hcl5 hfu5 hm5
                        exact hJr s5 m5
                          ⟨hinv5, hcl5.trans hcl4, by rw [hfu5]; exact hfu4, hm5⟩
                      · c0_hsteps; exact hJr s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩))
                (fun Jc hJc => by
                  c0_call hCNeed
                  refine ⟨c, s3, R, rfl, hinv3.lengths, by omega, hm3, ?_⟩
                  intro need _
                  c0_hsplit
                  · c0_hsteps; c0_call hComp; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
                    intro cr c4 s4 m4 hcomp4 hinv4 hcr_dom _ hfu4 hu4 hcl4 hm4
                    c0_hsteps
                    · exact hQ 20#64 c4 s4 m4 hcomp4 hinv4.lengths (Nat.le_trans hfu4 hfu3)
                        (Or.inr (Or.inr rfl)) (fun _ => hu4 hc) (fun h => by cases h) hm4
                    · exact hQ 0#64 c4 s4 m4 hcomp4 hinv4.lengths (Nat.le_trans hfu4 hfu3)
                        (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm4
                    · exact hJc (c4, s4) m4 ⟨hcomp4, hinv4, hcl4 hc, by omega, hm4⟩
                  · c0_hsteps
                    exact hJc (c, s3) m3
                      ⟨FullM4Compact.FullCfgCompat.refl c, hinv3, hcl3, hfu3, hm3⟩))
            (fun Je hJe => by
              c0_hsplit
              · c0_hsteps; c0_call hElim; refine ⟨c, F0, s2, R, rfl, hinv2, hcl2, hm2, ?_⟩
                intro re s3 m3 hinv3 hcl3 hfu3 _ hue3 hm3; c0_hsteps
                · exact hQ 20#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hinv3.lengths
                    (by omega) (Or.inr (Or.inr rfl)) (fun _ => hue3 hc)
                    (fun h => by cases h) hm3
                exact hJe s3 m3 ⟨hinv3, hcl3, by omega, hm3⟩
              · c0_hsteps; exact hJe s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩))
        (fun Jp hJp => by
          c0_hsplit
          · c0_hsteps; c0_call hProbe; refine ⟨c, F0, s1, R, rfl, hinv1, hcl1, hm1, ?_⟩
            intro rp s2 m2 hlen2 hfu2 hrp_dom hup2 hsp2 hm2; c0_hsteps
            · exact hQ 20#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hlen2 (by omega)
                (Or.inr (Or.inr rfl)) (fun _ => hup2 hc) (fun h => by cases h) hm2
            obtain ⟨hinv2, hcl2⟩ := hsp2 (hrp_dom.resolve_right hc)
            exact hJp s2 m2 ⟨hinv2, hcl2, by omega, hm2⟩
          · c0_hsteps; exact hJp s1 m1 ⟨hinv1, hcl1, hfu1', hm1⟩))
    (fun Jbt hJbt => by
      c0_hsplit
      · c0_hsteps; c0_call hBt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, fun _ => by
          have := hw0.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
          have := hinv.lengths.core_ok.cur_vars_le; omega,
          hw0.2.1.trail_lits_lt, hm, ?_⟩
        intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
        have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
        have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
        have hsp1 := m4_sparseInv_after_backtrack0 hw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
        c0_hsteps; exact hJbt s1 m1 ⟨hsp1.toSparse, hl01, Nat.le_refl _, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          have : ¬ 0 < s.core.cur_level % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt hcl_lt64] at this; omega
        c0_hsteps; exact hJbt s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

private def m4SearchVariant (st : FullState) : Nat :=
  2 * st.core.fuel.toNat + if st.core.propagated = st.core.trail_end then 1 else 0

/-- `Func.wp` proof for unified M4 `full_search` (`FullFastSched.full_search_body`) threading
`FullM4Compact.FullCfgCompat c c'` and using `m4ReduceSpec` + `m4SimplifySpec` against
`m4SearchSpec`. -/
theorem m4_search_wp (Γ : Env)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hWarm : ∀ a m Q X, fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hReph : ∀ a m Q X, fullRephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, m4ReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hSimp : ∀ a m Q X, m4SimplifySpec a m Q X →
      Γ "full_simplify" [i64, .bool, .bool] [i64] a m Q X)
    (hRdue : ∀ a m Q X, fullRestartDueSpec a m Q X → Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hDec : ∀ a m Q X, fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ a m Q X, m4SearchSpec a m Q X →
      Func.wp Γ FullFastSched.full_search_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp FullFastSched.full_search_body
  c0_hsteps; c0_call hLucky; refine ⟨c, F0, s, R, rfl, hinv, hcl0, hm, ?_⟩
  intro lk s1 m1 hlen1 hlk_dom _ _ hulk hsp1 hext1 hm1; c0_hsteps
  · rw [hc]; exact hQ 20#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1
      (Or.inr (Or.inr rfl)) (fun _ => hulk hc) (fun h => by cases h) hm1
  · rw [hc]; exact hQ 10#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1
      (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => hext1 hc) hm1
  have hlk02 : lk = 0#64 ∨ lk = 2#64 := by
    rcases hlk_dom with h0 | h2 | h10 | h20
    · exact Or.inl h0
    · exact Or.inr h2
    · exact absurd h10 hc
    · exact absurd h20 (by assumption)
  have hinv1 : FullSparseInv c F0 s1 := (hsp1 hlk02).1
  c0_call hWarm; refine ⟨c, F0, s1, R, rfl, hinv1.1, hinv1.2.2.2.2, hm1, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 s2
    hcore2 hperm2 _ hpres2 _ hm2
  have hinv2 : FullSparseInv c F0 s2 :=
    m4_sparseInv_of_perm_core hinv1 hcore2 hperm2 rfl rfl rfl hpres2
  c0_hsteps_nogrp
  refine wp_while_state0 (α := FullCfg × FullState)
    (fun p => m4SearchVariant p.2)
    (fun ⟨cc, st⟩ ml =>
      FullM4Compact.FullCfgCompat c cc ∧ FullSparseInv cc F0 st ∧ (FullMem cc st ⋆ R) ml)
    (fun _ hL => by c0_hsteps; exact hL (c, s2) m2 ⟨FullM4Compact.FullCfgCompat.refl c, hinv2, hm2⟩)
    (fun _ ⟨cc, st⟩ ml ⟨hcc, hst, hml⟩ ih => ?_)
  have hch_cc : cc.hdr = c.hdr := hcc.hdr
  rw [← hch_cc]
  c0_hsplit
  rotate_left; · cases hc
  c0_hsteps
  · exact hQ 0#64 cc st ml hcc hst.lengths (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hml
  · exact hQ 0#64 cc st ml hcc hst.lengths (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hml
  obtain ⟨F_cur, hspW⟩ := hst.exists_witness
  c0_call hProp; refine ⟨cc, F0, F_cur, st, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hml, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s3
    hlen3 hw3 _ hperm3 hfu3 hpr_dom hpr0 hpr1 _ _ hm3
  have hspW3 : FullSparseInvW cc F0 F_cur s3 :=
    m4_sparseInvW_of_perm hspW hlen3 hw3 hperm3 rfl rfl rfl ⟨rfl, rfl⟩
  c0_hsteps
  · exact hQ 0#64 cc s3 m3 hcc hlen3 (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm3
  · obtain ⟨hfu3_lt, _, hconf3⟩ := hpr1 hc
    c0_call hAna; refine ⟨cc, F0, F_cur, s3, R, rfl, hspW3, hconf3, hm3, ?_⟩
    intro ast s4 m4 hlen4 _ _ hfu4 _ hua4 _ hsp4 hm4; c0_hsteps
    · exact hQ 20#64 cc s4 m4 hcc hlen4 (Or.inr (Or.inr rfl))
        (fun _ => hua4 hc) (fun h => by cases h) hm4
    · exact hQ 0#64 cc s4 m4 hcc hlen4 (Or.inl rfl)
        (fun h => by cases h) (fun h => by cases h) hm4
    have hinv4 : FullSparseInv cc F0 s4 := (hsp4 hc).1.toSparse
    c0_call hSw; refine ⟨cc, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
    intro ⟨⟩ s5 m5 hcore5 hlen5 hpres5 hm5
    dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm5
    have hinv5 : FullSparseInv cc F0 s5 := hinv4.of_safetySlice hlen5 hcore5 hpres5.1
    have hfu5 : s5.core.fuel.toNat < st.core.fuel.toNat := by
      have heq : s5.core = s4.core := fullCoreState_agrees_with_scratch hcore5
      rw [heq]; change s4.core.fuel.toNat < st.core.fuel.toNat; dsimp only [s3] at hfu4; omega
    c0_hsteps_nogrp
    refine wp_join_state0 (α := FullState)
      (fun s6 m6 => FullSparseInv cc F0 s6 ∧ s6.core.fuel.toNat < st.core.fuel.toNat ∧
        (FullMem cc s6 ⋆ R) m6)
      (fun _ s6 m6 ⟨hinv6, hfu6, hm6⟩ => by
        c0_hsteps_nogrp
        refine wp_join_state0 (α := FullState)
          (fun s7 m7 => FullSparseInv cc F0 s7 ∧ s7.core.fuel.toNat < st.core.fuel.toNat ∧
            (FullMem cc s7 ⋆ R) m7)
          (fun _ s7 m7 ⟨hinv7, hfu7, hm7⟩ => by
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullCfg × FullState)
              (fun ⟨c8, s8⟩ m8 => FullM4Compact.FullCfgCompat c c8 ∧ FullSparseInv c8 F0 s8 ∧
                s8.core.fuel.toNat < st.core.fuel.toNat ∧ (FullMem c8 s8 ⋆ R) m8)
              (fun _ ⟨c8, s8⟩ m8 ⟨hc8, hinv8, hfu8, hm8⟩ => by
                c0_hsteps
                have hv_lt : m4SearchVariant s8 < m4SearchVariant st := by
                  unfold m4SearchVariant; split <;> split <;> omega
                exact ih (c8, s8) m8 hv_lt ⟨hc8, hinv8, hm8⟩)
              (fun Jsr hJsr => by
                c0_hsteps_nogrp
                refine wp_join_group (fun () ms => ms = m7)
                  (fun _ ⟨⟩ ms hms => by
                    subst hms; c0_hsteps
                    c0_call hSimp; refine ⟨cc, F0, s7, R, rfl, hinv7, hm7, ?_⟩
                    intro sr c8 s8 m8 hcomp8 hlen8 hfu8 _ hus8 hsp8 hm8
                    have hc8 := hcc.trans hcomp8
                    c0_hsteps
                    · exact hQ 20#64 c8 s8 m8 hc8 hlen8 (Or.inr (Or.inr rfl))
                        (fun _ => hus8 hc) (fun h => by cases h) hm8
                    · exact hQ 0#64 c8 s8 m8 hc8 hlen8 (Or.inl rfl)
                        (fun h => by cases h) (fun h => by cases h) hm8
                    exact hJsr (c8, s8) m8 ⟨hc8, (hsp8 hc).1, by omega, hm8⟩)
                  (fun Jsimp hJsimp => by
                    c0_hsteps
                    · exact hJsimp () m7 rfl
                    · exact hJsimp () m7 rfl
                    · c0_call hRdue; refine ⟨cc, s7, R, rfl, hinv7.lengths, hm7, ?_⟩
                      intro ⟨rd, ⟨⟩⟩ s7' m7' hcore7' hlen7' ⟨_, hpres7'⟩ hm7'
                      dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm7'
                      have hinv7' : FullSparseInv cc F0 s7' :=
                        hinv7.of_safetySlice hlen7' hcore7' hpres7'
                      have hfu7' : s7'.core.fuel.toNat < st.core.fuel.toNat := by
                        have heq : s7'.core = s7.core :=
                          fullCoreState_agrees_with_scratch hcore7'
                        rw [heq]; exact hfu7
                      c0_hsteps
                      · c0_call hRst; refine ⟨cc, F0, s7', R, rfl, hinv7'.1, hm7', ?_⟩
                        intro _ _ _ _ _ _ _ _ _ _ m8 s8 hcore8 _ hpres8 hm8
                        have hinv8 : FullSparseInv cc F0 s8 :=
                          m4_sparseInv_of_same_arena hinv7' hcore8 rfl rfl rfl rfl rfl hpres8
                        c0_hsteps; exact hJsr (cc, s8) m8 ⟨hcc, hinv8, hfu7', hm8⟩
                      · exact hJsr (cc, s7') m7' ⟨hcc, hinv7', hfu7', hm7'⟩)))
          (fun Jrd hJrd => by
            c0_hsteps
            · c0_call hRed; refine ⟨cc, F0, s6, R, rfl, hinv6, hm6, ?_⟩
              intro rr s7 m7 hinv7 _ _ hfu7 hur7 _ hm7; c0_hsteps
              · exact hQ 20#64 cc s7 m7 hcc hinv7.lengths (Or.inr (Or.inr rfl))
                  (fun _ => hur7 hc) (fun h => by cases h) hm7
              · exact hQ 0#64 cc s7 m7 hcc hinv7.lengths (Or.inl rfl)
                  (fun h => by cases h) (fun h => by cases h) hm7
              exact hJrd s7 m7 ⟨hinv7, by omega, hm7⟩
            · exact hJrd s6 m6 ⟨hinv6, hfu6, hm6⟩))
      (fun Jrp hJrp => by
        c0_hsteps
        · c0_call hReph; refine ⟨cc, F0, s5, R, rfl, hinv5.1, hm5, ?_⟩
          intro _ _ _ _ _ _ _ _ _ _ m6 s6 hcore6 hfu6 hpres6 hm6
          have hinv6 : FullSparseInv cc F0 s6 :=
            m4_sparseInv_of_same_arena hinv5 hcore6 rfl rfl rfl rfl rfl hpres6
          c0_hsteps; exact hJrp s6 m6 ⟨hinv6, by dsimp only [s6]; omega, hm6⟩
        · exact hJrp s5 m5 ⟨hinv5, hfu5, hm5⟩)
  · exact hQ 10#64 cc s3 m3 hcc hlen3 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hspW3.2.2.2.2.1.2) hm3
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_dom with h0 | h1 | h2
      · exact h0
      · exact absurd h1 (by assumption)
      · exact absurd h2 (by assumption)
    obtain ⟨hprop3, _, hfu3_lt_if⟩ := hpr0 hpr_eq0
    have hinv3 : FullSparseInv cc F0 s3 := hspW3.toSparse
    c0_call hDec; refine ⟨cc, F0, s3, R, rfl, hinv3.1, hm3, ?_⟩
    intro dr _ _ _ _ _ _ _ _ _ _ _ _ _ m4 s4 hcore4 hpres4 hdr_dom _ hd1 hm4
    have hinv4 : FullSparseInv cc F0 s4 :=
      m4_sparseInv_of_same_arena hinv3 hcore4 rfl rfl rfl rfl rfl hpres4
    c0_hsteps
    · exact hQ 10#64 cc s4 m4 hcc hinv4.lengths (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hinv4.2.2.2.1.2) hm4
    · exact hQ 0#64 cc s4 m4 hcc hinv4.lengths (Or.inl rfl) (fun h => by cases h)
        (fun h => by cases h) hm4
    · have hdr1 : dr = 1#64 := hdr_dom.resolve_left hc
      have hte4 : s4.core.trail_end = s3.core.trail_end + 1 := (hd1 hdr1).2
      have hv_lt : m4SearchVariant s4 < m4SearchVariant st := by
        have hfu3' : s3.core.fuel.toNat ≤ st.core.fuel.toNat := hfu3
        have hprop3' : s3.core.propagated = s3.core.trail_end := hprop3
        have hne4 : s4.core.propagated ≠ s4.core.trail_end := by
          change s3.core.propagated ≠ s4.core.trail_end; omega
        have hle_st := hst.lengths.core_ok.propagated_le
        have hfu4 : s4.core.fuel = s3.core.fuel := rfl
        unfold m4SearchVariant
        simp only [hne4, ↓reduceIte, Nat.add_zero, hfu4]
        by_cases heq_st : st.core.propagated = st.core.trail_end
        · simp only [heq_st, ↓reduceIte]; omega
        · simp only [heq_st, ↓reduceIte, Nat.add_zero]
          have hlt_f : s3.core.fuel.toNat < st.core.fuel.toNat := hfu3_lt_if (by omega)
          omega
      exact ih (cc, s4) m4 hv_lt ⟨hcc, hinv4, hm4⟩

end M4Orchestrators

/-! ## 3. Top-Level `kissat_solve_bytes`, Headline Soundness, & Concrete UNSAT Non-Vacuity -/

section TopAndNonVacuity

open scoped FullArenaTactics

private theorem m4_parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil => rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact m4_parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem m4_parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact m4_parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem m4_bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem m4_alignPad_bv_eq (p : BitVec 64) :
    (8 - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem m4_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr ≤ wlen) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
  have h2 : (region work_ptr (fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
    sep_mono (fun _ f => pad_region_merge (by omega) f) h1
  rw [show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by omega] at h2
  exact sep_ac h2

private theorem m4_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : FullCfg} {st : FullState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply m4_merge_reg hwfit hw_ge
  have h1 : (FullMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
      (wlen - fullAlignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact FullArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

private def M4CheckRest (c : FullCfg) (s : FullState) (bva_bv : BitVec 64) : Mem 64 → Prop :=
  array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

private theorem m4_arr8 {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hn : xs.length = n) (hbd : n ≤ 2 ^ 64) (f : Mem 64) (hf : array (t := i8) a xs f) :
    region a n f := by
  simpa [Ty.bytes, Ty.size, i8, hn] using
    array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf

private theorem m4_arr32 (m : Nat) {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : xs.length = n) (hm : 4 * n = m) (hbd : m ≤ 2 ^ 64) (f : Mem 64)
    (hf : array (t := i32) a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i32, hn, hm] using
    array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf

private theorem m4_arr64 (m : Nat) {a : BitVec 64} {xs : List (BitVec 64)} {n : Nat}
    (hn : xs.length = n) (hm : 8 * n = m) (hbd : m ≤ 2 ^ 64) (f : Mem 64)
    (hf : array64 a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i64, hn, hm] using
    array_to_region (t := i64) (xs := xs) (by simp [Ty.bytes, Ty.size, i64, hn]; omega)
      ((array64_eq_array a xs) ▸ hf)

private theorem m4_checkModel_post_to_region {c : FullCfg} {s : FullState}
    {bva_bv mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ (M4CheckRest c s bva_bv ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap
  have hd := c.hdel; have hred := c.hred; have hext := c.hext; have hscr := c.hscr
  have hmd := fullMinDepthOf_le c.max_vars
  unfold dimacsBound at *
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  have h1 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆
          array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) ⋆
        ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
            array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
            array (t := i8) c.pLitMark s.core.lit_mark) ⋆
          (array (t := i8) c.pMark s.core.mrk ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
            array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
            array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
            array (t := i8) c.pWalkBest s.scratch.walk_best)) ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆
        (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
          array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
          array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆
        (array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          array (t := i32) c.pFrameDec s.core.frame_dec) ⋆
        (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
          array (t := i32) c.pWsort s.scratch.wsort ⋆
          array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
          array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
          array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
          array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
          array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig) ⋆
        (array (t := i32) c.pMinStk s.core.min_stk ⋆
          array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
          array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
          array (t := i32) c.pDelayed s.scratch.delayed ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆
        c.pad)) m := by
    unfold M4CheckRest FullCoreU32A FullCoreU32B FullCoreDynArrs FullScratchArrays
      FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs FullScrDynArrs at hm
    exact sep_ac hm
  have hHead : ∀ k,
      (dimacsState c.hdr mv' nc' cur' val' ⋆
        array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) k →
      (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) k :=
    sep_mono2 (fun _ hb => dimacsState_to_region hb)
      (m4_arr64 1120 (by rw [List.length_set, Full.hdrTailWords_length])
        (by decide) (by decide))
  have hB : ∀ k,
      ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
          array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
          array (t := i8) c.pLitMark s.core.lit_mark) ⋆
        (array (t := i8) c.pMark s.core.mrk ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
          array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
          array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          array (t := i8) c.pWalkBest s.scratch.walk_best)) k →
      ((region c.pVals (2 * c.max_vars) ⋆ region c.pWalkVals (2 * c.max_vars) ⋆
          region c.pLitMark (2 * c.max_vars)) ⋆
        (region c.pMark c.max_vars ⋆ region c.pPhases c.max_vars ⋆
          region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
          region c.pWalkBest c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (fun x (hb : bytes c.pVals (s.core.vals.map UInt8.ofBitVec) x) => by
            have hb' := bytes_to_region hb; simpa [hc.vals_len] using hb')
          (m4_arr8 hs.walk_vals_len (by omega)))
        (m4_arr8 hc.lit_mark_len (by omega)))
      (sep_mono2
        (sep_mono2
          (sep_mono2 (sep_mono2 (m4_arr8 hc.mrk_len (by omega))
              (m4_arr8 hs.phases_len (by omega)))
            (m4_arr8 hs.phases_target_len (by omega)))
          (m4_arr8 hs.phases_best_len (by omega)))
        (m4_arr8 hs.walk_best_len (by omega)))
  have hU1 : ∀ k,
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) k →
      (region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
        region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
        region c.pTrailPos (4 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (m4_arr32 (4 * c.max_vars) hc.flags_len rfl (by omega))
            (m4_arr32 (4 * c.max_vars) hc.lvl_len rfl (by omega)))
          (m4_arr32 (4 * c.max_vars) hc.rsns_len rfl (by omega)))
        (m4_arr32 (4 * c.max_vars) hc.trl_len rfl (by omega)))
      (m4_arr32 (4 * c.max_vars) hc.trail_pos_len rfl (by omega))
  have hU2 : ∀ k,
      (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) k →
      (region c.pTmp (4 * c.max_vars) ⋆ region c.pHeap (4 * c.max_vars) ⋆
        region c.pPos (4 * c.max_vars) ⋆ region c.pMinClr (4 * c.max_vars) ⋆
        region c.pShrinkStk (4 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (m4_arr32 (4 * c.max_vars) hc.tmp_len_arr rfl (by omega))
            (m4_arr32 (4 * c.max_vars) hs.heap_len_arr rfl (by omega)))
          (m4_arr32 (4 * c.max_vars) hs.pos_len rfl (by omega)))
        (m4_arr32 (4 * c.max_vars) hc.min_clr_len_arr rfl (by omega)))
      (m4_arr32 (4 * c.max_vars) hs.shrink_stk_len rfl (by omega))
  have hU3 : ∀ k,
      (array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec) k →
      (region c.pQPrev (4 * c.max_vars) ⋆ region c.pQNext (4 * c.max_vars) ⋆
        region c.pQStamp (4 * c.max_vars) ⋆ region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
        region c.pFrameDec (4 * (c.max_vars + 1))) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (m4_arr32 (4 * c.max_vars) hs.q_prev_len rfl (by omega))
            (m4_arr32 (4 * c.max_vars) hs.q_next_len rfl (by omega)))
          (m4_arr32 (4 * c.max_vars) hs.q_stamp_len rfl (by omega)))
        (m4_arr32 (4 * (c.max_vars + 1)) hc.frame_trail_len rfl (by omega)))
      (m4_arr32 (4 * (c.max_vars + 1)) hc.frame_dec_len rfl (by omega))
  have hT1 : ∀ k,
      (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
        array (t := i32) c.pWsort s.scratch.wsort ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig) k →
      (region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
        region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2
                  (sep_mono2 (m4_arr32 (16 * c.max_vars) hc.wvec_len (by omega) (by omega))
                    (m4_arr32 (8 * c.max_vars) hc.repr_len (by omega) (by omega)))
                  (m4_arr32 (8 * c.max_vars) hs.wsort_len (by omega) (by omega)))
                (m4_arr32 (8 * c.max_vars) hs.work_stk1_len (by omega) (by omega)))
              (m4_arr32 (8 * c.max_vars) hs.work_stk2_len (by omega) (by omega)))
            (m4_arr32 (8 * c.max_vars) hs.tarjan_mark_len (by omega) (by omega)))
          (m4_arr32 (8 * c.max_vars) hs.tarjan_reach_len (by omega) (by omega)))
        (m4_arr64 (8 * c.max_vars) hs.score_len rfl (by omega)))
      (m4_arr64 (8 * c.max_vars) hs.sim_sig_len rfl (by omega))
  have hT2 : ∀ k,
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
        array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
        array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
        array (t := i32) c.pDelayed s.scratch.delayed ⋆
        array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
        array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf) k →
      (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
        region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
        region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
        region c.pScratchBuf (4 * c.scratch_cap)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2
                  (sep_mono2
                    (m4_arr32 (8 * c.minDepth) hc.min_stk_len
                      (by unfold FullCfg.minDepth; omega) (by unfold FullCfg.minDepth; omega))
                    (m4_arr32 256 hs.glue_used_len (by decide) (by decide)))
                  (m4_arr32 64 hs.last_learned_len (by decide) (by decide)))
                (m4_arr32 (4 * c.arena_cap) hc.arena_len_arr rfl (by omega)))
              (m4_arr32 (4 * c.wcap) hc.wstk_len_arr rfl (by omega)))
            (m4_arr32 (12 * c.delayed_cap) hs.delayed_len_arr (by omega) (by omega)))
          (m4_arr32 (4 * c.red_cap) hs.red_refs_len rfl (by omega)))
        (m4_arr32 (4 * c.extend_cap) hs.extend_stk_len rfl (by omega)))
      (m4_arr32 (4 * c.scratch_cap) hs.scratch_buf_len rfl (by omega))
  have h2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ region c.hdr c.avail) m :=
    sep_mono_r (fun _ h => c.regions_to_avail h)
      (sep_mono_r
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2 (sep_mono2 (sep_mono2 hHead hB) hU1) hU2)
                hU3)
              hT1)
            hT2)
          (fun _ hb => hb))
        h1)
  exact sep_ac h2

private theorem m4_solve_bytes_extend_check {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c0 c2 : FullCfg} {s3 : FullState} {cnf_ptr work_ptr hdr_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hcompat : FullM4Compact.FullCfgCompat c0 c2)
    (hch_ptr : c0.hdr = hdr_ptr)
    (hch : c0.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c0.avail = wlen - fullAlignPad work_ptr)
    (hlen3 : s3.LengthsOk c2) (hext3 : s3.scratch.extend_len ≤ c2.extend_cap)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ FullMem c2 s3 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3)
    (hRet : ∀ r m', (r = 0#64 ∨ r = 10#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_extend" (Arg.var hdr_ptr, ()) fun _ =>
      Expr.store (t := i64) (Arg.var (BitVec.ofNat 64 c0.mv)) (Arg.var hdr_ptr)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 768, ())⟩
        fun p_mx => Expr.load i64 (Arg.var p_mx.fst) fun ld_mx =>
        Expr.let_ ⟨OpCode.sub i64, (Arg.var ld_mx, Arg.var (BitVec.ofNat 64 c0.mv), ())⟩
          fun p_bva => Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 784, ())⟩
            fun p_bva_addr => Expr.store (t := i64) (Arg.var p_bva.fst) (Arg.var p_bva_addr.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 64, ())⟩
                fun p1 => Expr.load i64 (Arg.var p1.fst) fun ld_v =>
                Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
                  (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var hdr_ptr, Arg.var ld_v,
                   Arg.var (BitVec.ofNat 64 c0.mv), ())
                fun p2 => Expr.group (sig := [[i64]])
                  (fun _ => Blocks.cons (fun p3 => Expr.ret (Arg.var p3.fst, ())) Blocks.nil)
                  fun Jr => Expr.let_
                    ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p2.fst, Arg.imm 1, ())⟩
                    fun p3 => Expr.jnz (Arg.var p3.fst)
                      (Expr.jump Jr.fst (Arg.imm 10, ()))
                      (Expr.jump Jr.fst (Arg.imm 0, ()))))) m3 := by
  dsimp only
  have hch2 : c2.hdr = hdr_ptr := hcompat.hdr.trans hch_ptr
  rw [← hch2]
  c0_call hExt
  refine ⟨c2, s3, bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext3⟩, hlen3,
    by dsimp only [fullExtendSlice, SafetySlice.ofMask]; exact sep_ac hm3, ?_⟩
  intro ⟨⟩ s4 m4 _ hlen4 _ hm4
  dsimp only [fullExtendSlice, SafetySlice.ofMask] at hm4
  have hm4_f : (FullMem c2 s4 ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
  refine wp_store_sep (FullM4Compact.full_store_mv_mid (BitVec.ofNat 64 c0.mv) hm4_f) ?_
  intro m4_1 hm4_1
  c0_step
  refine wp_load_of (FullM4Compact.full_load_max_vars_mid hm4_1) ?_
  c0_step
  let bva_bv : BitVec 64 := BitVec.ofNat 64 c2.max_vars - BitVec.ofNat 64 c0.mv
  have hmid_arr : (array64 (c2.hdr + 32) (Full.hdrTailWords c2 s4) ⋆
      (dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
          s4.core.d_cur s4.core.d_val ⋆
        FullCoreArrays c2 s4.core ⋆ FullScratchArrays c2 s4.scratch ⋆ c2.pad ⋆
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R))) m4_1 := by
    unfold FullM4Compact.FullMemShrinkMid at hm4_1; exact sep_ac hm4_1
  obtain ⟨hst_bva_ok, hm4_bva⟩ := store_array64 (i := 94) bva_bv
    (by rw [Full.hdrTailWords_length]; decide) hmid_arr
  have hptr784 : c2.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c2.hdr + 784 := by
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
  rw [hptr784] at hst_bva_ok hm4_bva
  refine wp_store_sep ⟨hst_bva_ok, hm4_bva⟩ ?_
  intro m4_2 hm4_2
  c0_step
  have hget4 := loadVal_array64 (i := 4)
    (by rw [List.length_set, Full.hdrTailWords_length]; decide) hm4_2
  rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) = 64 by decide,
    List.getElem_set_ne (by decide)] at hget4
  have hpv4 : (Full.hdrTailWords c2 s4)[4]'(by rw [Full.hdrTailWords_length]; decide) =
      c2.pVals := rfl
  rw [hpv4] at hget4
  refine wp_load_of hget4 ?_
  have hmv0_bd := c0.hmv; have hmx0_bd := c0.hmaxv; have hbva0 := c0.hbva
  unfold dimacsBound at hmv0_bd hmx0_bd
  have hm4_2_b : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
        s4.core.d_cur s4.core.d_val ⋆
      bytes c2.pVals (s4.core.vals.map UInt8.ofBitVec) ⋆
      (M4CheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m4_2 := by
    have ha1 : (array (t := i8) c2.pVals s4.core.vals ⋆
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
            s4.core.d_cur s4.core.d_val ⋆
          (M4CheckRest c2 s4 bva_bv ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)))) m4_2 := by
      unfold M4CheckRest FullCoreArrays FullCoreByteArrs at *; exact sep_ac hm4_2
    have hm2x : c2.max_vars < 2 * dimacsBound := c2.hmaxv
    unfold dimacsBound at hm2x
    have ha2 : (bytes c2.pVals (s4.core.vals.map UInt8.ofBitVec) ⋆
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
            s4.core.d_cur s4.core.d_val ⋆
          (M4CheckRest c2 s4 bva_bv ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)))) m4_2 := by
      refine sep_mono (fun _ hf => ?_) ha1
      have hbytes := array_eq_bytesOf (t := i8) c2.pVals s4.core.vals
        (by simp [Ty.bytes, Ty.size, i8, hlen4.core_ok.vals_len]; omega) hf
      rw [bytesOf_i8_eq_map] at hbytes; exact hbytes.symm
    exact sep_ac ha2
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c0.mv, BitVec.ofNat 64 c2.nc, s4.core.d_cur, s4.core.d_val,
    cnfBytes, s4.core.vals.map UInt8.ofBitVec, c0.mv,
    M4CheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega,
    by have := hcompat.max_vars; simp [hlen4.core_ok.vals_len]; omega,
    by have := c2.hmaxv; unfold dimacsBound at this; simp [hlen4.core_ok.vals_len]; omega,
    by simpa [sep_assoc] using hm4_2_b, ?_⟩
  intro ok mv' nc' cur' val' m5 _ hm5
  have hm5_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m5 :=
    m4_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca, ← hcompat.hdr, ← hcompat.avail]
      exact m4_checkModel_post_to_region hlen4 (by simpa [sep_assoc] using hm5))
  refine wp_join_group (ts := [i64])
    (fun (res_v, ()) m6 => (res_v = 0#64 ∨ res_v = 10#64) ∧ m6 = m5)
    (fun _ ⟨res_v, ⟨⟩⟩ m6 ⟨hres_v, hm6⟩ => by
      rw [hm6]; c0_hsteps; exact hRet res_v m5 hres_v hm5_reg)
    (fun Jr hJr => by
      c0_hsteps
      · exact hJr (10#64, ()) m5 ⟨Or.inr rfl, rfl⟩
      · exact hJr (0#64, ()) m5 ⟨Or.inl rfl, rfl⟩)

/-- `Func.wp` proof for Unified M4 `kissat_solve_bytes` against `fullSolveBytesCoreSpec`. -/
theorem m4_kissat_solve_bytes_core_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, m4PreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, m4SearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesCoreSpec a m Q X →
      Func.wp Γ kissat_solve_bytes_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_body; wp_unfold
  refine ⟨fun hf0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ _ hf => by rw [hf0] at hf; simp at hf) hm
  refine ⟨fun hcp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ hcp => absurd hcp0 hcp) hm
  refine ⟨fun hwp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ hwp => absurd hwp0 hwp) hm
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, m4_bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [m4_bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [m4_alignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hw_small => ?_, fun hw_ge_not => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun mv nc _ _ _ _ hsz _ _ _ => by unfold fullFixedBytes at hsz; omega) hm
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := m4_alignPad_bv_eq work_ptr
  have hhdr_bv : work_ptr + ((8 - (work_ptr &&& 7)) &&& 7) = hdr_addr := by rw [hpad_bv]
  have hav_bv :
      BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7) = BitVec.ofNat 64 availNat := by
    rw [hpad_bv]; exact bv_sub_ofNat (by omega) (by omega)
  have hav_toNat : (BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7)).toNat = availNat := by
    rw [hav_bv, bv64_ofNat_toNat (by omega)]
  have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
    rw [bv_add_ofNat_toNat (by omega)]; omega
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
    have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
    have h2 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m :=
      sep_mono (fun _ f => region_work_to_hdr (by omega) (by omega) f) h1
    exact sep_ac h2
  c0_call hInit
  refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
    by rw [hhdr_bv, hav_toNat]; exact hhdr_fit,
    by rw [hav_toNat]; omega,
    by rw [hhdr_bv, hav_toNat]; exact hsplit, ?_, ?_⟩
  · intro m' hm' hfail; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      m4_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h)
      (fun mv nc i0 _ _ _ hsz _ hhdr _ => by
        have hlt := hfail mv nc (cnfBytes.drop i0) hhdr; rw [hav_toNat] at hlt; omega) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hcv0 hdcur0
      hal0 _ hte0 hpr0 hcl0 _ _ hprob0 _ _ hoom0 hinc0 hvals0 hwvec0 _ _ _ hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    have hvals_take : s0.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
      have hbva := c.hbva; rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hcv0, hdcur0, hcl0, hte0, hpr0, hal0,
      hoom0, hprob0, hinc0, hvals0, hwvec0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom _ _ _ hpb20 hpb1 huns_tr hm1; c0_hsteps
    · rcases hpb_dom with rfl | h1 | rfl
      · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) ?_
          (m4_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut); cases h20
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (m4_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hcnf_pos : CnfVarsPos cnf := m4_parseDimacs_vars_pos hparse
      have hnot_ut : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc → False := by
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        rw [hc] at h20; cases h20
      have hm1_load :
          (FullMem c s1 ⋆ (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m1 := sep_ac hm1
      have hload_mv : loadVal m1 i64 (work_ptr + ((8 - (work_ptr &&& 7)) &&& 7)) =
          some (BitVec.ofNat 64 c.mv) := by
        rw [hhdr_bv, ← hch]
        exact FullArenaTactics.load_full_mv hm1_load
      refine wp_load_of hload_mv ?_
      -- Load `orig_mv := h->d.mv`
      c0_call hPre; refine ⟨c, shiftDownCnf cnf, s1,
        bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp c2 s2 m2 hcomp2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      have hch2 : c2.hdr = hdr_addr := hcomp2.hdr.trans hch
      have hca2 : c2.avail = availNat := hcomp2.avail.trans hca
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 m2 (Or.inr (Or.inr rfl))
          (fun _ => ⟨cnf, hparse, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (m4_merge_arena hwfit (by omega) hch2 hca2 hlen2 (sep_ac hm2))
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
        (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
          p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
          (p.1 = 20#64 → cnf.Unsat) ∧ (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, cr, sr⟩ mr ⟨hcompr, hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          have hchr : cr.hdr = hdr_addr := hcompr.hdr.trans hch
          have hcar : cr.avail = availNat := hcompr.avail.trans hca
          c0_hsteps
          · exact m4_solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hcompr
              hch_ptr (by rw [← hpad_bv]; exact hch_ptr) hca hlen_r (hrv_ext hc) hmr
              fun res m_end hres hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 =>
                    (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
                  hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
              (m4_merge_arena hwfit (by omega) hchr hcar hlen_r hmr))
        (fun Jr hJr => by
          c0_hsplit
          · c0_hsteps
            exact hJr (10#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inr (Or.inl rfl), (fun h => by cases h),
              (fun _ => hpp10 hc), sep_ac hm2⟩
          · c0_hsteps_nogrp
            refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
              (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
                p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
                (p.1 = 20#64 → cnf.Unsat) ∧
                (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ p mr hp => by c0_hsteps; exact hJr p mr hp)
              (fun Jr2 hJr2 => by
                c0_hsplit
                · c0_hsteps
                  exact hJr2 (0#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inl rfl,
                    (fun h => by cases h), (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_hsteps; rw [hhdr_bv, ← hch2]; c0_call hSearch
                  refine ⟨c2, shiftDownCnf cnf, s2,
                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    rfl, hinv2, hcl2, hm2, ?_⟩
                  intro r3 c3 s3 m3 hcomp3 hlen3 hr3_dom hur3 hext3 hm3; c0_hsteps
                  exact hJr2 (r3, c3, s3) m3 ⟨hcomp2.trans hcomp3, hlen3, hr3_dom,
                    fun h20 => shiftDownCnf_unsat hcnf_pos (hur3 h20), hext3, sep_ac hm3⟩))

theorem m4_kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, m4PreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, m4SearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesSpec a m Q X → Func.wp Γ kissat_solve_bytes_body a m Q X :=
  fun _ _ _ _ h => m4_kissat_solve_bytes_core_wp Γ hInit hParse hPre hSearch hExt hCheck
    _ _ _ _ (fullSolveBytesCoreSpec_of_spec h)

/-- Headline source-level UNSAT-only soundness of Unified M4 `kissat_solve_bytes` under
canonical `231`-function `m4Env` (`0` SAT/model proofs). -/
theorem m4_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4Env kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m4_kissat_solve_bytes_wp m4Env
    (mkM4Env_row_at (mainSpec := fullSolveBytesSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullSolveBytesSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullSolveBytesSpec) 227
      ⟨"full_preprocess", [i64], [i64], m4PreprocessSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullSolveBytesSpec) 229
      ⟨"full_search", [i64], [i64], m4SearchSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullSolveBytesSpec) 100
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullSolveBytesSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under `231`-function `m4UnsatEnv`:
`kissat_solve_bytes` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
with `4096`-byte workspace and `fuel = 16`. -/
theorem m4_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m4UnsatEnv kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m4_kissat_solve_bytes_core_wp m4UnsatEnv
    (mkM4Env_row_at (mainSpec := fullUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullUnsatWitnessSpec) 227
      ⟨"full_preprocess", [i64], [i64], m4PreprocessSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullUnsatWitnessSpec) 229
      ⟨"full_search", [i64], [i64], m4SearchSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullUnsatWitnessSpec) 100
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM4Env_row_at (mainSpec := fullUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

end TopAndNonVacuity

end LeanQbe.T.Examples.Kissat.FullM4

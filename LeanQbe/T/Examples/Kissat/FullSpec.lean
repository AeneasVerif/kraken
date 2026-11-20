module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.DimacsLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Top-Level UNSAT-Only `Spec` & 166-Row `fullSpecTable` (`Stage 4`)

Defines the headline Stage-4 UNSAT-only contracts for `kissat_solve_bytes` (zero SAT/model
reconstruction proofs):
- `fullSolveBytesCoreSpec`: memory safety (`0 | 10 | 20`), UNSAT soundness (`r = 20#64 → ∃ cnf,
  parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`), restored workspace framing, and deterministic
  level-0 unit-contradiction non-vacuity (`UnitUnsatTrace → r = 20#64`).
- `fullSolveBytesSpec` & `fullSolveBytesCoreSpec_of_spec`.
- 166-row `fullSpecTable`, `mkFullEnv`, `fullEnv`, `fullSpecTable_noExit`, and kernel-`rfl`
  signature-alignment theorem `fullSpecTable_sigs`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-- Core UNSAT-only `kissat_solve_bytes` contract carrying general UNSAT soundness (`0 | 10 | 20`)
and deterministic level-0 unit-contradiction non-vacuity (`UnitUnsatTrace → r = 20#64`). -/
def fullSolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Headline UNSAT-only soundness specification of `kissat_solve_bytes` (`D-Full`). -/
def fullSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

theorem fullSolveBytesCoreSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullSolveBytesSpec args m Q X) : fullSolveBytesCoreSpec args m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' hdom hu _ hm' => hQ r m' hdom hu hm'⟩

/-- Specification table matching `fullFns` (`dimacs_fns ++ full1_fns ++ full2_fns ++ full3_fns
++ full4_fns`) row-by-row (`166` functions). -/
def fullSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
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
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullInitHdrSpec, true⟩
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
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩
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
  , ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunSpec, true⟩
  , ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
  , ⟨"full_transitive", [i64], [i64], fullTransitiveSpec, true⟩
  , ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifySpec, true⟩
  , ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
  , ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  , ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitSpec, true⟩
  , ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  , ⟨"full_vivify", [i64, i64], [i64], fullVivifySpec, true⟩
  , ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  , ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccSpec, true⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  , ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], fullEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  , ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  , ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  , ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], fullCongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fullCongEmitXorSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], fullCongTryXorIteSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64], [i64], fullCongExtractSpec, true⟩
  , ⟨"full_cong_hash_step", [i64, i64, i64, i64], [.bool], fullCongHashStepSpec, true⟩
  , ⟨"full_congruence", [i64], [i64], fullCongruenceSpec, true⟩
  , ⟨"full_sweep_add_cl", [i64, i64, i32, i32], [i64], fullSweepAddClSpec, true⟩
  , ⟨"full_sweep_cone", [i64, i32], [i64], fullSweepConeSpec, true⟩
  , ⟨"full_sweep_dpll", [i64, i32, i32, i32, i32], [i64], fullSweepDpllSpec, true⟩
  , ⟨"full_sweep_refine", [i64, i32, i32], [], fullSweepRefineSpec, true⟩
  , ⟨"full_sweep_seed_sim", [i64, i32, i32], [i32], fullSweepSeedSimSpec, true⟩
  , ⟨"full_sweep_var", [i64, i32], [i64], fullSweepVarSpec, true⟩
  , ⟨"full_sweep_sat", [i64], [i64], fullSweepSatSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  , ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  , ⟨"full_forward_sub", [i64], [i64], fullForwardSubSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool], fullBveMarkAndSpec, true⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesSpec, true⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResSpec, true⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], fullBveVarSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32], [.bool], fullBvaTryLitSpec, true⟩
  , ⟨"full_factor", [i64], [i64], fullFactorSpec, true⟩
  , ⟨"full_probe", [i64], [i64], fullProbeSpec, true⟩
  , ⟨"full_eliminate", [i64], [i64], fullEliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  , ⟨"full_simplify", [i64], [i64], fullSimplifySpec, true⟩
  , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  ]

/-- Parameterized specification environment covering all `166` functions in `fullFns`. -/
def mkFullEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (fullSpecTable mainSpec)

/-- Headline 166-function UNSAT-only specification environment for `fullModule`. -/
def fullEnv : Env := mkFullEnv fullSolveBytesSpec

theorem fullSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ fullSpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (fullSpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem fullSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (fullSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      fullFns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full

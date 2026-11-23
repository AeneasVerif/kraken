/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.WPLemmas

/-!
# Kissat `D-Full` M6 Orchestration Top-Level Proof (`FullM6OrchProof`, `29/29` Fns & Soundness/NV)

Completes standalone certification of `FullM6Orch.m6OrchModule` (`29` owned fns + `65` externs):
1. `24`-row prefix `m6OrchPfxSpecTable` (`m6Orch_fns.take 24`), `sigs` (`m6OrchPfxSpecTable_sigs`),
   `length = 24`, `nodup`, `noExit`, `noTail`, and parametric `m6OrchPfx_tableImpl` (compatible
   with both standalone `m6OrchSpecTable` and unified `FullM6Proof.mkM6Env`).
2. Complete `94`-row `m6OrchSpecTable solveSpec` (`24` prefix + `5` tail + `65` externs),
   `mkM6OrchEnv`, `m6OrchEnv`, `m6OrchCoreEnv`, `mkM6OrchEnv_moduleOk`, `m6Orch_moduleOk`, and
   `m6OrchCore_moduleOk`.
3. Top-level SAT + UNSAT soundness (`m6Orch_solve_bytes_sound`, `m6Orch_solve_bytes_m6_sound`,
   `m6Orch_solve_bytes_host_sound`) and concrete Tier-3b UNSAT + SAT non-vacuity
   (`m6Orch_unsat_nv`, `m6Orch_sat_nv` with `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. `24`-Row Prefix `m6OrchPfxSpecTable` & Metadata -/

/-- `24`-row specification table aligned 1-to-1 with `m6Orch_fns.take 24` (all `noExit`). -/
abbrev m6OrchPfxSpecTable : List SpecEntry :=
  [ ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_lit_rank", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], Full.fullSweepBinsSpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], m6AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], Full.fullMinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], m6Deduce1uipHdrSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], FullM6Hdr.m6HdrAnalyzeSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_ema_swap_m6", [i64, i64, i64], [], m6EmaSwapSpec, true⟩
  , ⟨"full_switch_mode_m6", [i64], [], m6SwitchModeSpec, true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩ ]

theorem m6OrchPfxSpecTable_sigs :
    m6OrchPfxSpecTable.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig := by
  t_kernel_rfl

theorem m6OrchPfxSpecTable_length : m6OrchPfxSpecTable.length = 24 := by rfl

theorem m6OrchPfxSpecTable_noExit : m6OrchPfxSpecTable.all SpecEntry.noExit = true := by rfl

theorem m6OrchPfxSpecTable_nodup : (m6OrchPfxSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m6OrchPfxSpecTable_noTail :
    ∀ e ∈ m6OrchPfxSpecTable, e.name ∉
      ["full_search_m6", "kissat_solve_bytes_m6", "full_preprocess",
       "full_search", "kissat_solve_bytes"] := by
  intro e he
  have hall : m6OrchPfxSpecTable.all (fun x => decide (x.name ∉
      ["full_search_m6", "kissat_solve_bytes_m6", "full_preprocess",
       "full_search", "kissat_solve_bytes"])) = true := by
    rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall e he)

theorem m6OrchPfxSpecTable_row_at (i : Nat) (e : SpecEntry)
    (h : m6OrchPfxSpecTable[i]? = some e := by rfl) : e ∈ m6OrchPfxSpecTable :=
  List.mem_of_getElem? h

/-! ## 2. Parametric Prefix `TableImpl` (`m6OrchPfx_tableImpl`) -/

/-- External callee lookups required by `m6Orch_fns.take 24`. -/
structure M6OrchPfxExtCallees (Γ : Env) : Prop where
  wstackDefragM6 : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
    Γ "full_wstack_defrag_m6" [i64] [] a m Q X
  watchPushM6 : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
    Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X
  rescaleM6 : ∀ a m Q X, Full.fullRescaleSpec a m Q X → Γ "full_rescale_m6" [i64] [] a m Q X
  parseBodyM6 : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
    Γ "full_parse_body_m6" [i64, i64] [i64] a m Q X
  litRankM6 : ∀ a m Q X, Full.fullLitRankSpec a m Q X →
    Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X
  sweepBinsM6cf : ∀ a m Q X, Full.fullSweepBinsSpec a m Q X →
    Γ "full_sweep_bins_m6cf" [i64] [] a m Q X
  rewatchArenaM6 : ∀ a m Q X, Full.fullRewatchArenaSpec a m Q X →
    Γ "full_rewatch_arena_m6" [i64, i64] [.bool] a m Q X
  arenaSweepM6 : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
    Γ "full_arena_sweep_m6" [i64] [i64] a m Q X
  markReasonsM6 : ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
    Γ "full_mark_reasons_m6" [i64, .bool] [] a m Q X
  minShrinkM6 : ∀ a m Q X, Full.fullMinShrinkSpec a m Q X →
    Γ "full_min_shrink_m6" [i64] [] a m Q X
  deduce1uipM6 : ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
    Γ "full_deduce_1uip_m6" [i64] [i64] a m Q X
  walkM6 : ∀ a m Q X, Full.fullWarmupSpec a m Q X → Γ "full_walk_m6" [i64] [] a m Q X
  sweepDenseM5 : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
    Γ "full_sweep_dense_m5" [i64, i64, i64] [i64] a m Q X
  isqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X
  backtrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
    Γ "full_backtrack" [i64, i64] [] a m Q X
  propagate : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
    Γ "full_propagate" [i64] [i64] a m Q X
  recomputeTiers : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [] [] a m Q X →
    Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X
  arenaNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
    Γ "full_arena_next" [i64, i32] [i32] a m Q X
  sortReds : ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
    Γ "full_sort_reds" [i64, i64] [] a m Q X
  ilog10 : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X
  setWm : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64, i64] [] a m Q X →
    Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X
  analyzeLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
    Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X
  recordUsed : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
    Γ "m6_hdr_record_used" [i64, i64] [] a m Q X
  clearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X
  otfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
    Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X
  otfsSubsume : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
    Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X
  otfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
    Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X
  oneLitConfl : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
    Γ "full_one_lit_confl" [i64] [i64] a m Q X
  anaFailedLit : ∀ a m Q X, FullM6OrchAdapters.m6aAnaFailedLitSpec a m Q X →
    Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X
  restoreBumpAna : ∀ a m Q X, FullM6OrchAdapters.m6aRestoreBumpAnaSpec a m Q X →
    Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X
  tickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X
  emaUpdate : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
    Γ "full_ema_update" [i64, i64] [] a m Q X
  learnClause : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
    Γ "full_learn_clause" [i64, i64] [i64] a m Q X
  extReady : ∀ a m Q X, FullM6Hdr.m6HdrExtReadySpec a m Q X →
    Γ "m6_hdr_ext_ready" [i64] [.bool] a m Q X
  getWm : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X →
    Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X
  heapDown : ∀ a m Q X, Full.fullHeapDownSpec a m Q X →
    Γ "full_heap_down" [i64, i32] [] a m Q X
  log10Q16 : ∀ a m Q X, FullM5Sched.m5Log10Q16Spec a m Q X →
    Γ "full_log10_q16" [i64] [i64] a m Q X
  reorderQueueM7 : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
    Γ "full_reorder_queue_m7" [i64] [i64] a m Q X
  backboneM6 : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
    Γ "full_backbone_m6" [i64, i64] [i64] a m Q X
  transitiveM6 : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
    Γ "full_transitive_m6" [i64, i64] [i64] a m Q X
  minU64 : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
    Γ "full_min_u64" [i64, i64] [i64] a m Q X
  probeRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
    Γ "full_probe_run" [i64, i64] [i64] a m Q X
  vivifyM6Hdr : ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
    Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X
  probeDticks : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
    Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X
  scaleDeltaM5 : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
    Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X
  enterDense : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
    Γ "full_enter_dense" [i64] [.bool] a m Q X
  delaying : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [.bool] a m Q X →
    Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X
  congruenceDense : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
    Γ "full_congruence_dense" [i64, i64] [i64] a m Q X
  rebuildWatches : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
    Γ "full_rebuild_watches" [i64] [i64] a m Q X
  reduceDelay : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
    Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X
  bumpDelay : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
    Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X
  substitute : ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
    Γ "full_substitute" [i64] [i64] a m Q X
  factor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
    Γ "full_factor" [i64, i64] [i64] a m Q X
  lucky : ∀ a m Q X, Full.fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X
  compactNeeded : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
    Γ "full_compact_needed" [i64] [.bool] a m Q X
  compact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
    Γ "full_compact" [i64] [i64] a m Q X
  eliminateM6 : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
    Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X

/-- Internal prefix callee lookups used within `m6Orch_fns.take 24`. -/
structure M6OrchPfxSelfCallees (Γ : Env) : Prop where
  arenaSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
    Γ "full_arena_sweep" [i64] [i64] a m Q X
  markReasons : ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
    Γ "full_mark_reasons" [i64, .bool] [] a m Q X
  analyzeRsnM6 : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
    Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X
  deduce1uipM6 : ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
    Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X
  emaSwapM6 : ∀ a m Q X, m6EmaSwapSpec a m Q X → Γ "full_ema_swap_m6" [i64, i64, i64] [] a m Q X
  sweepDenseM6 : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
    Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X
  probeTailM6 : ∀ a m Q X, m6ProbeTailSpec a m Q X →
    Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X
  probeM6 : ∀ a m Q X, m6ProbeSpec a m Q X → Γ "full_probe_m6" [i64, .bool] [i64] a m Q X

private theorem m6o_env_of_mem {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (nm : String) (as bs : List Ty) (sp : Spec as bs)
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ tbl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → Env.ofTable tbl nm as bs xs m Q X :=
  fun xs m Q X hs => Env.ofTable_of_mem hmem hnd (by
    dsimp only [SpecEntry.eff]; simp only [ite_true]; exact hno xs m Q X hs)

private theorem m6o_pfxSelf_of_sub {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (htPfx : ∀ e ∈ m6OrchPfxSpecTable, e ∈ tbl) :
    M6OrchPfxSelfCallees (Env.ofTable tbl) :=
  ⟨ m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 7 _))
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 8 _))
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 10 _))
      (fun _ _ _ _ h => m6AnalyzeRsnHdrSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 13 _))
      (fun _ _ _ _ h => m6Deduce1uipHdrSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 16 _))
      (fun _ _ _ _ h => m6EmaSwapSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 18 _))
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 20 _))
      (fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (htPfx _ (m6OrchPfxSpecTable_row_at 21 _))
      (fun _ _ _ _ h => m6ProbeSpec_monoX h) ⟩

/-- Environment-parametric `TableImpl` for `m6Orch_fns.take 24` against
`m6OrchPfxSpecTable`. -/
theorem m6OrchPfx_env_tableImpl (Γ : Env)
    (hExt : M6OrchPfxExtCallees Γ) (hSelf : M6OrchPfxSelfCallees Γ) :
    TableImpl Γ (m6Orch_fns.take 24) m6OrchPfxSpecTable := by
  have htake : m6Orch_fns.take 24 =
      [ m6oWstackDefragFn, m6oWatchPushFn, m6oRescaleFn, m6oParseBodyFn, m6oLitRankFn
      , m6oSweepBinsFn, m6oRewatchArenaFn, m6oArenaSweepFn, m6oMarkReasonsFn, m6oReduceM6Fn
      , m6oAnalyzeRsnM6HdrFn, m6oMinShrinkFn, m6oDeduce1uipFn, m6oDeduce1uipM6HdrFn
      , m6oAnalyzeCoreM6Fn, m6oWalkFn, m6oEmaSwapM6Fn, m6oSwitchModeM6Fn, m6oSweepDenseM6Fn
      , m6oReorderM6Fn, m6oProbeTailM6Fn, m6oProbeM6Fn, m6oPreprocessM6Fn
      , m6oSimplifyM6Fn ] := by rfl
  rw [htake]; unfold m6OrchPfxSpecTable
  exact
    ⟨ SpecEntry.Impl.of (full_wstack_defrag_wp Γ hExt.wstackDefragM6)
    , SpecEntry.Impl.of (full_watch_push_wp Γ hExt.watchPushM6)
    , SpecEntry.Impl.of (full_rescale_wp Γ hExt.rescaleM6)
    , SpecEntry.Impl.of (full_parse_body_wp Γ hExt.parseBodyM6)
    , SpecEntry.Impl.of (full_lit_rank_wp Γ hExt.litRankM6)
    , SpecEntry.Impl.of (full_sweep_bins_wp Γ hExt.sweepBinsM6cf)
    , SpecEntry.Impl.of (full_rewatch_arena_wp Γ hExt.rewatchArenaM6)
    , SpecEntry.Impl.of (full_arena_sweep_wp Γ hExt.arenaSweepM6)
    , SpecEntry.Impl.of (full_mark_reasons_wp Γ hExt.markReasonsM6)
    , SpecEntry.Impl.of (full_reduce_m6_wp Γ hExt.isqrt hExt.ilog10 hExt.arenaNext
        hExt.recomputeTiers hExt.setWm hSelf.markReasons hExt.sortReds hExt.backtrack
        hExt.propagate hSelf.arenaSweep)
    , SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_wp Γ hExt.analyzeLit hExt.recordUsed)
    , SpecEntry.Impl.of (full_min_shrink_wp Γ hExt.minShrinkM6)
    , SpecEntry.Impl.of (full_deduce_1uip_wp Γ hExt.deduce1uipM6)
    , SpecEntry.Impl.of (full_deduce_1uip_m6_hdr_wp Γ hExt.analyzeLit hSelf.analyzeRsnM6
        hExt.clearAna hExt.otfsLarge hExt.otfsBin hExt.otfsSubsume)
    , SpecEntry.Impl.of (full_analyze_core_m6_wp Γ hExt.oneLitConfl hExt.anaFailedLit
        hSelf.deduce1uipM6 hExt.restoreBumpAna hExt.minShrinkM6 hExt.tickRel hExt.emaUpdate
        hExt.learnClause)
    , SpecEntry.Impl.of (full_walk_wp Γ hExt.walkM6)
    , SpecEntry.Impl.of (full_ema_swap_m6_wp Γ)
    , SpecEntry.Impl.of (full_switch_mode_m6_wp Γ hExt.extReady hExt.getWm hExt.setWm
        hExt.heapDown hExt.log10Q16 hSelf.emaSwapM6 hExt.ilog10)
    , SpecEntry.Impl.of (full_sweep_dense_m6_wp Γ hExt.sweepDenseM5)
    , SpecEntry.Impl.of (full_reorder_m6_wp Γ hExt.reorderQueueM7)
    , SpecEntry.Impl.of (full_probe_tail_m6_wp Γ hExt.backboneM6 hExt.transitiveM6 hExt.minU64
        hExt.probeRun hExt.vivifyM6Hdr)
    , SpecEntry.Impl.of (full_probe_m6_wp Γ hExt.probeDticks hExt.ilog10 hExt.scaleDeltaM5
        hExt.enterDense hExt.delaying hExt.congruenceDense hExt.rebuildWatches hExt.setWm
        hExt.reduceDelay hExt.bumpDelay hSelf.sweepDenseM6 hExt.substitute hSelf.probeTailM6
        hExt.backboneM6 hExt.minU64 hExt.factor)
    , SpecEntry.Impl.of (full_preprocess_m6_wp Γ hExt.propagate hSelf.arenaSweep hExt.lucky
        hExt.compactNeeded hExt.compact hExt.scaleDeltaM5 hSelf.probeM6)
    , SpecEntry.Impl.of (full_simplify_m6_wp Γ hExt.backtrack hSelf.probeM6 hExt.eliminateM6
        hExt.compactNeeded hExt.compact)
    , trivial ⟩

/-- `Env.ofTable`-parametric `TableImpl` for `m6Orch_fns.take 24` against `m6OrchPfxSpecTable`.
Directly instantiates both standalone `m6OrchSpecTable` and unified `FullM6Proof.mkM6Env`. -/
theorem m6OrchPfx_tableImpl {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (htPfx : ∀ e ∈ m6OrchPfxSpecTable, e ∈ tbl)
    (hExt : M6OrchPfxExtCallees (Env.ofTable tbl)) :
    TableImpl (Env.ofTable tbl) (m6Orch_fns.take 24) m6OrchPfxSpecTable :=
  m6OrchPfx_env_tableImpl (Env.ofTable tbl) hExt (m6o_pfxSelf_of_sub hnd htPfx)

/-! ## 3. Closed `94`-Row `m6OrchSpecTable`, `mkM6OrchEnv`, & `ModuleOk` -/

/-- All `65` external specification rows aligned 1-to-1 with `m6OrchExterns`. -/
def m6OrchExtRows : List SpecEntry :=
  [ ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_rescale_m6", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins_m6cf", [i64], [], Full.fullSweepBinsSpec, true⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], Full.fullMinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_walk_m6", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩
  , ⟨"m6_hdr_record_used", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], FullM6OrchAdapters.m6aAnaFailedLitSpec, true⟩
  , ⟨"full_restore_bump_ana_m6_hdr", [i64], [], FullM6OrchAdapters.m6aRestoreBumpAnaSpec, true⟩
  , ⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩
  , ⟨"m6_hdr_ext_ready", [i64], [.bool], FullM6Hdr.m6HdrExtReadySpec, true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], FullM6Hdr.m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], FullM6OrchAdapters.m6aVivifySpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64],
      FullM6Hdr.m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], FullM6Hdr.m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullM3CongBva.fullFactorHeapSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], Full.fullLuckySpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM6CompactFlush.fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_analyze_m6_hdr", [i64], [i64], FullM6Hdr.m6HdrAnalyzeSpec, true⟩
  , ⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩
  , ⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩
  , ⟨"full_rephase_m6_hdr", [i64], [], m6aRephaseSpec, true⟩
  , ⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitExactSpec, true⟩
  , ⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩ ]

theorem m6OrchExtRows_row_at (i : Nat) (e : SpecEntry)
    (h : m6OrchExtRows[i]? = some e := by rfl) : e ∈ m6OrchExtRows :=
  List.mem_of_getElem? h

/-- Construct `M6OrchPfxExtCallees (Env.ofTable tbl)` from membership of `m6OrchExtRows.take 57`. -/
theorem m6OrchPfxExtCallees_of_mem {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hmem : ∀ e ∈ m6OrchExtRows, e ∈ tbl) :
    M6OrchPfxExtCallees (Env.ofTable tbl) :=
  ⟨ m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 0 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 1 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 2 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 3 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 4 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 5 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 6 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 7 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 8 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 9 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 10 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 11 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 12 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 13 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 14 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 15 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 16 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 17 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 18 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 19 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 20 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 21 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 22 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 23 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 24 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 25 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 26 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 27 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 28 _))
      (fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 29 _))
      (fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 30 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 31 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 32 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 33 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrExtReadySpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 34 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 35 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 36 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 37 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 38 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 39 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 40 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 41 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 42 _))
      (fun _ _ _ _ h => FullM6OrchAdapters.m6aVivifySpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 43 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 44 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 45 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 46 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 47 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 48 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 49 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 50 _))
      (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 51 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 52 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 53 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 54 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 55 _))
  , m6o_env_of_mem hnd _ _ _ _ (hmem _ (m6OrchExtRows_row_at 56 _)) ⟩

/-- Transparent `5`-row tail specification table aligned 1-to-1 with `m6Orch_fns.drop 24`. -/
def m6OrchTailRows
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  [ ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_search", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩ ]

theorem m6OrchTailRows_sigs (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchTailRows solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      (m6Orch_fns.drop 24).map Fn.sig := by
  t_kernel_rfl

theorem m6OrchTailRows_noExit (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchTailRows solveSpec).all SpecEntry.noExit = true := by rfl

/-- Closed `94`-row specification table aligned 1-to-1 with `m6OrchModule.sigs`. -/
def m6OrchSpecTable
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  m6OrchPfxSpecTable ++ m6OrchTailRows solveSpec ++ m6OrchExtRows

def mkM6OrchEnv (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m6OrchSpecTable solveSpec)

/-- Closed SAT + UNSAT verification environment for `m6OrchModule`. -/
def m6OrchEnv : Env := mkM6OrchEnv fullM6SolveBytesSpec

/-- Closed deterministic core-model environment (for Tier-3b UNSAT non-vacuity). -/
def m6OrchCoreEnv : Env := mkM6OrchEnv fullM6SolveBytesCoreModelSpec

theorem m6OrchSpecTable_sigs (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchSpecTable solveSpec).map (fun e => (e.name, e.as, e.rs)) = m6OrchModule.sigs := by
  have hext : m6OrchExtRows.map (fun e => (e.name, e.as, e.rs)) =
      m6OrchExterns.map Extern.sig := by
    t_kernel_rfl
  have hfns : m6OrchModule.sigs =
      ((m6Orch_fns.take 24).map Fn.sig ++ (m6Orch_fns.drop 24).map Fn.sig) ++
        m6OrchExterns.map Extern.sig := by
    dsimp only [m6OrchModule, Module.sigs]
    rw [← List.map_append, List.take_append_drop]
  rw [hfns, m6OrchSpecTable, List.map_append, List.map_append,
    m6OrchPfxSpecTable_sigs, m6OrchTailRows_sigs solveSpec, hext]

theorem m6OrchSpecTable_length (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchSpecTable solveSpec).length = 94 := by
  have hs := congrArg List.length (m6OrchSpecTable_sigs solveSpec)
  have hl : m6OrchModule.sigs.length = 94 := by t_kernel_rfl
  simpa only [List.length_map, hl] using hs

theorem m6OrchSpecTable_nodup (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m6OrchSpecTable solveSpec).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (m6OrchSpecTable_sigs solveSpec)
  have heq : (m6OrchSpecTable solveSpec).map SpecEntry.name = m6OrchModule.names := by
    dsimp only [Module.names]
    simp only [List.map_map, Function.comp_def, Module.sigs, List.map_append, Fn.sig,
      Extern.sig] at hm ⊢
    exact hm
  have hchk := m6Orch_acyclic
  simp only [m6OrchModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  rw [heq]; exact Module.namesNodup_of_checkNamesNodup hchk.1

theorem m6OrchSpecTable_noExit (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchSpecTable solveSpec).all SpecEntry.noExit = true := by
  have hext : m6OrchExtRows.all SpecEntry.noExit = true := by rfl
  simp only [m6OrchSpecTable, List.all_append, m6OrchPfxSpecTable_noExit,
    m6OrchTailRows_noExit solveSpec, hext, Bool.and_self]

theorem mkM6OrchEnv_noExit (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM6OrchEnv solveSpec f as bs xs m Q X → mkM6OrchEnv solveSpec f as bs xs m Q X' :=
  env_ofTable_noExit_all (m6OrchSpecTable_noExit solveSpec)

theorem mkM6OrchEnv_solve_bytes_iff
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM6OrchEnv solveSpec "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have htail : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6OrchTailRows solveSpec :=
    List.mem_of_getElem? (i := 4) rfl
  have hmem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6OrchSpecTable solveSpec :=
    List.mem_append_left _ (List.mem_append_right _ htail)
  have hnd := m6OrchSpecTable_nodup solveSpec
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

theorem mkM6OrchEnv_solve_bytes_m6_iff
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM6OrchEnv solveSpec "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have htail : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6OrchTailRows solveSpec :=
    List.mem_of_getElem? (i := 1) rfl
  have hmem : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6OrchSpecTable solveSpec :=
    List.mem_append_left _ (List.mem_append_right _ htail)
  have hnd := m6OrchSpecTable_nodup solveSpec
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

private theorem m6o_tableImpl_append_right {Γ : Env} :
    ∀ {fs : List Fn} {t ext : List SpecEntry},
      TableImpl Γ fs t → TableImpl Γ fs (t ++ ext)
  | [], _, _, _ => trivial
  | _ :: _, [], _, h => False.elim h
  | _ :: _, _ :: _, _, ⟨h1, h2⟩ => ⟨h1, m6o_tableImpl_append_right h2⟩

/-- Parameterized `29/29` `ModuleOk` for `FullM6Orch.m6OrchModule` under `mkM6OrchEnv`. -/
theorem m6OrchClosedEnv_moduleOk
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X') :
    ModuleOk (mkM6OrchEnv solveSpec) m6OrchModule := by
  let tbl := m6OrchSpecTable solveSpec
  have hnd := m6OrchSpecTable_nodup solveSpec
  have hPfxSub : ∀ e ∈ m6OrchPfxSpecTable, e ∈ tbl :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have hTailSub : ∀ e ∈ m6OrchTailRows solveSpec, e ∈ tbl :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have hExtSub : ∀ e ∈ m6OrchExtRows, e ∈ tbl :=
    fun _ h => List.mem_append_right _ h
  have hPfxOk : TableImpl (Env.ofTable tbl) (m6Orch_fns.take 24) m6OrchPfxSpecTable :=
    m6OrchPfx_tableImpl hnd hPfxSub (m6OrchPfxExtCallees_of_mem hnd hExtSub)
  have hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Env.ofTable tbl "full_search_m6" [i64] [i64] a m Q X :=
    m6o_env_of_mem hnd _ _ _ _ (hTailSub _ (List.mem_of_getElem? (i := 0) rfl))
      (fun _ _ _ _ h => fullM6SearchSpec_monoX h)
  have hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Env.ofTable tbl "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X :=
    fun a m Q X hs => Env.ofTable_of_mem (hTailSub _ (List.mem_of_getElem? (i := 1) rfl)) hnd
      (hSolveMonoX a m Q X _ hs)
  have hPreM6 : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Env.ofTable tbl "full_preprocess_m6" [i64] [i64] a m Q X :=
    m6o_env_of_mem hnd _ _ _ _ (hPfxSub _ (m6OrchPfxSpecTable_row_at 22 _))
      (fun _ _ _ _ h => fullM6PreprocessSpec_monoX h)
  have hTailOk : TableImpl (Env.ofTable tbl) (m6Orch_fns.drop 24) (m6OrchTailRows solveSpec) := by
    have hdrop : m6Orch_fns.drop 24 =
        [ m6oSearchM6Fn, m6oSolveBytesM6Fn, m6oPreprocessFn
        , m6oSearchFn, m6oSolveBytesFn ] := by rfl
    rw [hdrop]; unfold m6OrchTailRows
    exact
      ⟨ SpecEntry.Impl.of (full_search_m6_wp (Env.ofTable tbl)
          (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 15 _)))
          (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 57 _))
            (fun _ _ _ _ h => FullM6Hdr.m6HdrAnalyzeSpec_monoX h))
          (m6o_env_of_mem hnd _ _ _ _ (hPfxSub _ (m6OrchPfxSpecTable_row_at 9 _))
            (fun _ _ _ _ h => m6ReduceSpec_monoX h))
          (m6o_env_of_mem hnd _ _ _ _ (hPfxSub _ (m6OrchPfxSpecTable_row_at 17 _))
            (fun _ _ _ _ h => m6SwitchModeSpec_monoX h))
          (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 58 _)))
          (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 59 _)))
          (m6o_env_of_mem hnd _ _ _ _ (hPfxSub _ (m6OrchPfxSpecTable_row_at 19 _)))
          (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 60 _))
            (fun _ _ _ _ h => m6aRephaseSpec_monoX h))
          (m6o_env_of_mem hnd _ _ _ _ (hPfxSub _ (m6OrchPfxSpecTable_row_at 23 _))
            (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
          (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 61 _))
            (fun _ _ _ _ h => FullM6Hdr.m6HdrDecideSpec_monoX h)))
      , ⟨ ⟨rfl, rfl, rfl⟩
        , fun xs m Q _ hs => wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
            (kissat_solve_bytes_m6_core_wp (Env.ofTable tbl)
              (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 62 _))
                (fun _ _ _ _ h => fullM6MemInitExactSpec_monoX h))
              (m6o_env_of_mem hnd _ _ _ _ (hPfxSub _ (m6OrchPfxSpecTable_row_at 3 _)))
              hPreM6 hSearchM6
              (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 63 _)))
              (m6o_env_of_mem hnd _ _ _ _ (hExtSub _ (m6OrchExtRows_row_at 64 _)))
              xs m Q _ (hWeaken xs m Q _ hs)) ⟩
      , SpecEntry.Impl.of (full_preprocess_wp (Env.ofTable tbl) hPreM6)
      , SpecEntry.Impl.of (full_search_wp (Env.ofTable tbl) hSearchM6)
      , SpecEntry.Impl.of (kissat_solve_bytes_core_wp (Env.ofTable tbl) solveSpec hSolveM6)
      , trivial ⟩
  have hfns : m6OrchModule.fns = m6Orch_fns.take 24 ++ m6Orch_fns.drop 24 :=
    (List.take_append_drop 24 m6Orch_fns).symm
  have hlen1 : (m6Orch_fns.take 24).length = m6OrchPfxSpecTable.length := by rfl
  have hOk : TableImpl (Env.ofTable tbl) m6OrchModule.fns tbl := by
    rw [hfns]; change TableImpl (Env.ofTable tbl) _
      (m6OrchPfxSpecTable ++ (m6OrchTailRows solveSpec ++ m6OrchExtRows))
    exact tableImpl_append hlen1 hPfxOk (m6o_tableImpl_append_right hTailOk)
  exact Env.ofTable_moduleOk m6Orch_acyclic (allFns_of_mem m6Orch_fns_wf) hOk

/-- Closed `ModuleOk` for `m6OrchModule` under `m6OrchEnv` (`fullM6SolveBytesSpec`). -/
theorem m6Orch_moduleOk : ModuleOk m6OrchEnv m6OrchModule :=
  m6OrchClosedEnv_moduleOk fullM6SolveBytesSpec
    (fun _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_of_spec hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesSpec_monoX hs)

/-- Closed `ModuleOk` for `m6OrchModule` under `m6OrchCoreEnv` (`fullM6SolveBytesCoreModelSpec`). -/
theorem m6OrchCore_moduleOk : ModuleOk m6OrchCoreEnv m6OrchModule :=
  m6OrchClosedEnv_moduleOk fullM6SolveBytesCoreModelSpec
    (fun _ _ _ _ hs => hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_monoX hs)

/-! ## 4. Top-Level SAT + UNSAT Soundness & Concrete Tier-3b Non-Vacuity -/

private theorem m6oSolveBytesM6Fn_mem : m6oSolveBytesM6Fn ∈ m6OrchModule.fns :=
  List.mem_of_getElem? (i := 25) rfl

private theorem m6oSolveBytesFn_mem : m6oSolveBytesFn ∈ m6OrchModule.fns :=
  List.mem_of_getElem? (i := 28) rfl

/-- Standalone top-level `kissat_solve_bytes` SAT + UNSAT soundness on `m6OrchModule`. -/
theorem m6Orch_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m6OrchEnv kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_moduleOk_combinator m6OrchEnv m6OrchModule
    "kissat_solve_bytes" kissat_solve_bytes_body
    m6Orch_moduleOk m6oSolveBytesFn_mem
    (fun _ _ _ _ hs =>
      (mkM6OrchEnv_solve_bytes_iff fullM6SolveBytesSpec).mpr (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Standalone top-level `kissat_solve_bytes_m6` SAT + UNSAT soundness on `m6OrchModule`. -/
theorem m6Orch_solve_bytes_m6_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m6OrchEnv kissat_solve_bytes_m6_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_moduleOk_combinator m6OrchEnv m6OrchModule
    "kissat_solve_bytes_m6" kissat_solve_bytes_m6_body
    m6Orch_moduleOk m6oSolveBytesM6Fn_mem
    (fun _ _ _ _ hs =>
      (mkM6OrchEnv_solve_bytes_m6_iff fullM6SolveBytesSpec).mpr (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Host-framed machine-memory lift for `m6OrchModule`. -/
theorem m6Orch_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      cnf.Sat (readModelFromWorkM6 st_dmem work_ptr)) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  fullM6_host_sound_lift hq hdmem

/-- Concrete Tier-3b UNSAT non-vacuity (`(x1) ∧ (~x1)`, `XPost := False`) on `m6OrchModule`. -/
theorem m6Orch_unsat_nv :
    Func.wp m6OrchCoreEnv kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m6oSolveBytesFn_mem
  have hfn := (m6OrchCore_moduleOk.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv m6OrchCoreEnv kissat_solve_bytes_body fun a m0 Q X hs => hfn a m0 Q X ?_
  exact (mkM6OrchEnv_solve_bytes_iff fullM6SolveBytesCoreModelSpec).mpr
    (fullM6SolveBytesCoreModelSpec_monoX hs)

/-- Concrete Tier-3b SAT non-vacuity (`(x1 ∨ x2)`, `XPost := False`) on `m6OrchModule`. -/
theorem m6Orch_sat_nv :
    Func.wp m6OrchEnv kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64) ∧ r ≠ 20#64 ∧
          (r = 10#64 →
            ¬ nvM6SatCnf.Unsat ∧
            (∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr))) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m6oSolveBytesFn_mem
  have hfn := (m6Orch_moduleOk.fnsOk pre _ post hsplit).2.2
  refine fullM6_sat_nv m6OrchEnv kissat_solve_bytes_body fun a m0 Q X hs => hfn a m0 Q X ?_
  exact (mkM6OrchEnv_solve_bytes_iff fullM6SolveBytesSpec).mpr (fullM6SolveBytesSpec_monoX hs)

end LeanQbe.T.Examples.Kissat.FullM6Orch

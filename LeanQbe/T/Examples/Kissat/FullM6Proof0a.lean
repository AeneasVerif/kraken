/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.FullM6Transport0
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof3
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof
public import LeanQbe.T.Examples.Kissat.FullM6S15Bridge
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas2
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` Unified `M6.0` Part 1 (`0..111`, `FullM6Proof0a`)

Assembles `m6RowsPart1 tPfx` aligned 1-to-1 with `FullM6.m6FnsPart1`, proves `sigs`/`noExit`
metadata, defines the shared `M6OrchPfxTblSpecs` and `M6Part1Callees` contracts, and certifies all
`112` functions of Part 1 (`Dimacs` through `full_reduce_m6`) in `Env.ofTable tbl`, with zero
`expose` attributes and plain `public section`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6S15Bridge
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. Shared Prefix / Callee Contracts & Helpers -/

/-- Exact `SpecEntry` rows required on `tPfx` (`m6Orch_fns.take 24` excluding unused rows and
`full_walk` which is parameterized separately). -/
structure M6OrchPfxTblSpecs (tPfx : List SpecEntry) : Prop where
  wstackDefrag :
    (⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈ tPfx
  watchPush :
    (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tPfx
  rescale :
    (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈ tPfx
  parseBody :
    (⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩ : SpecEntry) ∈ tPfx
  litRank :
    (⟨"full_lit_rank", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩ : SpecEntry) ∈ tPfx
  sweepBins :
    (⟨"full_sweep_bins", [i64], [], Full.fullSweepBinsSpec, true⟩ : SpecEntry) ∈ tPfx
  rewatchArena :
    (⟨"full_rewatch_arena", [i64, i64], [.bool],
      Full.fullRewatchArenaSpec, true⟩ : SpecEntry) ∈ tPfx
  arenaSweep :
    (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈ tPfx
  markReasons :
    (⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ : SpecEntry) ∈ tPfx
  reduceM6 :
    (⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩ : SpecEntry) ∈ tPfx
  minShrink :
    (⟨"full_min_shrink", [i64], [], Full.fullMinShrinkSpec, true⟩ : SpecEntry) ∈ tPfx
  deduce1uip :
    (⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ : SpecEntry) ∈ tPfx
  analyzeCoreM6 :
    (⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩ : SpecEntry) ∈ tPfx
  switchModeM6 :
    (⟨"full_switch_mode_m6", [i64], [], m6SwitchModeSpec, true⟩ : SpecEntry) ∈ tPfx
  reorderM6 :
    (⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩ : SpecEntry) ∈ tPfx
  preprocessM6 :
    (⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩ : SpecEntry) ∈ tPfx
  simplifyM6 :
    (⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩ : SpecEntry) ∈ tPfx

/-- Cross-part Part 1 row memberships required by Part 2, Part 3, and the `5`-fn tail. -/
structure M6Part1Callees (tbl : List SpecEntry) : Prop where
  isqrt : (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈ tbl
  ilog10 : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl
  rngNext : (⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩ : SpecEntry) ∈ tbl
  arenaNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
    tbl
  allocCl : (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩ :
    SpecEntry) ∈ tbl
  heapPop : (⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩ : SpecEntry) ∈ tbl
  bumpVar : (⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ : SpecEntry) ∈ tbl
  bumpDecay : (⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩ : SpecEntry) ∈ tbl
  queueMtf : (⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩ : SpecEntry) ∈ tbl
  tickRel : (⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩ : SpecEntry) ∈ tbl
  log10Q16 : (⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩ : SpecEntry) ∈
    tbl
  scaleDeltaM5 : (⟨"full_scale_delta_m5", [i64, i64], [i64],
    FullFastSched.schedScaleDeltaSpec, true⟩ : SpecEntry) ∈ tbl
  emaUpdate : (⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩ : SpecEntry) ∈
    tbl
  assignLvl : (⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ :
    SpecEntry) ∈ tbl
  assign : (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl
  backtrackRaw : (⟨"full_backtrack_raw_m5", [i64, i64], [],
    FullM5HeurCore.fullBacktrackRawSpec, true⟩ : SpecEntry) ∈ tbl
  backtrack : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl
  addClause : (⟨"full_add_clause", [i64, i32, i32, .bool], [i64],
    Full.fullAddClauseSpec, true⟩ : SpecEntry) ∈ tbl
  hdrSyncLegacy : (⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩ :
    SpecEntry) ∈ tbl
  hdrUpdateTier : (⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩ :
    SpecEntry) ∈ tbl
  hdrGetWm : (⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩ :
    SpecEntry) ∈ tbl
  hdrSetWm : (⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩ :
    SpecEntry) ∈ tbl
  hdrDrInit : (⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩ : SpecEntry) ∈ tbl
  hdrDrUpdate : (⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩ : SpecEntry) ∈ tbl
  hdrDrAllow : (⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩ : SpecEntry) ∈ tbl
  findRepl : (⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩ : SpecEntry) ∈
    tbl
  unwatchLarge : (⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ :
    SpecEntry) ∈ tbl
  propLitRawS15 : (⟨"full_prop_lit_raw_s15", [i64, i32, i64], [.bool],
    fullPropLitS15Spec, true⟩ : SpecEntry) ∈ tbl
  propagateIgnS15 : (⟨"full_propagate_ignore_s15", [i64, i64], [i64],
    fullPropagateIgnoreS15Spec, true⟩ : SpecEntry) ∈ tbl
  bcpS15 : (⟨"full_bcp_s15", [i64], [i64], fullBcpS15Spec, true⟩ : SpecEntry) ∈ tbl
  scaleDelta : (⟨"full_scale_delta", [i64, i64], [i64],
    FullFastSched.schedScaleDeltaSpec, true⟩ : SpecEntry) ∈ tbl
  propagateIgn : (⟨"full_propagate_ignore", [i64, i64], [i64],
    fullPropagateIgnoreS15Spec, true⟩ : SpecEntry) ∈ tbl
  propagate : (⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩ : SpecEntry) ∈ tbl
  flushTrail : (⟨"full_flush_trail", [i64], [i64],
    FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈ tbl
  reduce : (⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩ : SpecEntry) ∈ tbl

theorem pfxSlice_sigs {tPfx : List SpecEntry}
    (hsig : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (off n : Nat) :
    ((tPfx.drop off).take n).map (fun e => (e.name, e.as, e.rs)) =
      (((m6Orch_fns.take 24).drop off).take n).map Fn.sig := by
  simp only [List.map_take, List.map_drop, hsig]

theorem pfxSlice_noExit {tPfx : List SpecEntry}
    (hno : tPfx.all SpecEntry.noExit = true) (off n : Nat) :
    ((tPfx.drop off).take n).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_drop (List.mem_of_mem_take he))

theorem m6_bool_all_append {α : Type _} {p : α → Bool} {l1 l2 : List α}
    (h1 : l1.all p = true) (h2 : l2.all p = true) : (l1 ++ l2).all p = true := by
  simp only [List.all_append, h1, h2, Bool.and_self]

theorem m6_list_len_of_map {α β : Type _} {f : α → β} {l1 : List α} {l2 : List β}
    (h : l1.map f = l2) : l1.length = l2.length := by
  have h1 := congrArg List.length h
  simpa only [List.length_map] using h1

theorem m6_oneImpl {tbl : List SpecEntry} {fs : List Fn} {rs : List SpecEntry}
    {nm : Sym} {as bs : List Ty} {body : Func as bs} {sp : Spec as bs}
    (hfn : fs = [⟨nm, as, bs, body⟩]) (hrs : rs = [⟨nm, as, bs, sp, true⟩])
    (hwp : ∀ xs m Q X, sp xs m Q X → Func.wp (Env.ofTable tbl) body xs m Q X) :
    TableImpl (Env.ofTable tbl) fs rs := by
  subst hfn hrs
  exact ⟨SpecEntry.Impl.of hwp, trivial⟩

theorem m6_mem1 {α : Type _} {a : α} {l : List α} (h : a ∈ l) : ∀ e ∈ [a], e ∈ l :=
  fun _ he => by cases List.mem_singleton.mp he; exact h

theorem m6_memC {α : Type _} {a : α} {xs l : List α} (h : a ∈ l)
    (hs : ∀ e ∈ xs, e ∈ l) : ∀ e ∈ a :: xs, e ∈ l :=
  fun _ he => by rcases List.mem_cons.mp he with rfl | hx; exact h; exact hs _ hx

/-! ## 2. Part 1 Segment Rows (`112` Entries) -/

private def p1DimacsRows : List SpecEntry := fullBaseTable.take 8
private def p1Full1CoreRows : List SpecEntry := (fullBaseTable.drop 8).take 6
private def p1WatchGc0Rows : List SpecEntry :=
  [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
      FullM6WatchGc.fullWstackRadixSortSpec, true⟩
  , ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩ ]
private def p1HeapRows : List SpecEntry := (fullBaseTable.drop 16).take 4
private def p1RescaleM6Rows : List SpecEntry :=
  [⟨"full_rescale_m6", [i64], [], Full.fullRescaleSpec, true⟩]
private def p1BumpSchedRows : List SpecEntry :=
  [⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩] ++
  ((fullBaseTable.drop 22).take 3 ++
  ([⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩] ++
  FullM5Sched.m5SchedSpecTable.take 3))
private def p1Adp0Rows : List SpecEntry :=
  [⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩]
private def p1InitAssignRows : List SpecEntry :=
  (fullBaseTable.drop 27).take 2 ++
  ([ ⟨"full_save_target_best", [i64], [], Full.fullSaveTargetBestSpec, true⟩
   , ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩
   , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ] ++
  ((fullBaseTable.drop 31).take 5 ++
  ([⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩] ++
  ((fullBaseTable.drop 37).take 1 ++
  ([ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
   , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩ ] ++
  ((fullBaseTable.drop 40).take 1 ++
  [ ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩ ]))))))
private def p1Hdr0ExactRows : List SpecEntry :=
  [ ⟨"full_m6_hdr_sizeof", [], [i64], m6HdrSizeofSpec, true⟩
  , ⟨"full_m6_ext_sizeof", [], [i64], m6ExtSizeofSpec, true⟩
  , ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_hdr_reset", [i64], [], m6HdrResetSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"m6_hdr_ext_ready", [i64], [.bool], m6HdrExtReadySpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitExactSpec, true⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reset_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_add_ticks", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩ ]
private def p1ParseHelpersRows : List SpecEntry := (fullBaseTable.drop 42).take 2
private def p1PropHelpersRows : List SpecEntry :=
  (fullBaseTable.drop 45).take 2 ++
  [⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩]
private def p1BcpS15Rows : List SpecEntry := FullM6BcpS15.m6BcpS15SpecTable.take 4
private def p1Adp13Rows : List SpecEntry :=
  [ ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitS15Spec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩ ]
private def p1ParseBodyM6Rows : List SpecEntry :=
  [⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩]
private def p1RecomputeTiersRows : List SpecEntry := (fullBaseTable.drop 50).take 1
private def p1WatchGc1Rows : List SpecEntry :=
  [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins_range_m6", [i64, i64], [], FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ ]
private def p1WatchGc2Rows : List SpecEntry :=
  [ ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool], FullM6WatchGc.fullRewatchRangeSpec, true⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩ ]
private def p1SweepBinsM6cfRows : List SpecEntry :=
  [⟨"full_sweep_bins_m6cf", [i64], [], Full.fullSweepBinsSpec, true⟩]
private def p1SweepCopyRows : List SpecEntry := (fullBaseTable.drop 58).take 1
private def p1WatchGc3Rows : List SpecEntry :=
  [ ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedPass2Spec, true⟩
  , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedEndBufSpec, true⟩
  , ⟨"full_move_red_end_m6", [i64, i64, i64], [], FullM6WatchGc.fullMoveRedEndSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ ]
private def p1FlushTrailRows : List SpecEntry :=
  [⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.fullFlushTrailSpec, true⟩]
private def p1RedsRows : List SpecEntry := (fullBaseTable.drop 52).take 3
private def p1ReduceRows : List SpecEntry :=
  [⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩]

/-- Part 1 rows (`0..111`, `112` entries) aligned 1-to-1 with `FullM6.m6FnsPart1`. -/
def m6RowsPart1 (tPfx : List SpecEntry) : List SpecEntry :=
  p1DimacsRows ++ (p1Full1CoreRows ++ (p1WatchGc0Rows ++ ((tPfx.drop 0).take 2 ++
  (p1HeapRows ++ (p1RescaleM6Rows ++ ((tPfx.drop 2).take 1 ++ (p1BumpSchedRows ++
  (p1Adp0Rows ++ (p1InitAssignRows ++ (p1Hdr0ExactRows ++ (p1ParseHelpersRows ++
  (p1PropHelpersRows ++ (p1BcpS15Rows ++ (p1Adp13Rows ++ (p1ParseBodyM6Rows ++
  ((tPfx.drop 3).take 1 ++ (p1RecomputeTiersRows ++ (p1WatchGc1Rows ++ (p1WatchGc2Rows ++
  ((tPfx.drop 4).take 1 ++ (p1SweepBinsM6cfRows ++ ((tPfx.drop 5).take 1 ++ (p1SweepCopyRows ++
  ((tPfx.drop 6).take 1 ++ (p1WatchGc3Rows ++ ((tPfx.drop 7).take 2 ++ (p1FlushTrailRows ++
  (p1RedsRows ++ (p1ReduceRows ++ (tPfx.drop 9).take 1)))))))))))))))))))))))))))))

/-! ## 3. Part 1 Function Decomposition & Metadata -/

private def p1DimacsFns : List Fn := Full.fullFns.take 8
private def p1Full1CoreFns : List Fn := (Full.fullFns.drop 8).take 6
private def p1WatchGc0Fns : List Fn := FullM6WatchGc.m6WatchGc_fns.take 3
private def p1HeapFns : List Fn := (Full.fullFns.drop 16).take 4
private def p1RescaleM6Fns : List Fn := FullM6WalkParse.m6WalkParse_fns.take 1
private def p1BumpSchedFns : List Fn :=
  [FullM4Bump.m4BumpVarFn] ++ ((Full.fullFns.drop 22).take 3 ++
  ([FullM3VivChrono.m3TickRelFn] ++ FullM5Sched.m5Sched_fns.take 3))
private def p1Adp0Fns : List Fn := [m6aScaleDeltaFn]
private def p1InitAssignFns : List Fn :=
  (Full.fullFns.drop 27).take 2 ++
  ([ FullM5HeurCore.m5SaveTargetBestFn
   , FullM5HeurCore.m5BacktrackRawFn
   , FullM5HeurCore.m5BacktrackFn ] ++
  ((Full.fullFns.drop 31).take 5 ++
  (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  ((Full.fullFns.drop 37).take 1 ++
  (FullM5Orch.m5Orch_fns.take 2 ++
  ((Full.fullFns.drop 40).take 1 ++
  ((FullM5Orch.m5Orch_fns.drop 2).take 1 ++
  [FullM5.m5InitStateFwdFn])))))))
private def p1Hdr0Fns : List Fn := FullM6Hdr.m6HdrModule.fns.take 24
private def p1ParseHelpersFns : List Fn := (Full.fullFns.drop 42).take 2
private def p1PropHelpersFns : List Fn :=
  (Full.fullFns.drop 45).take 2 ++ FullM5Otfs.m5Otfs_fns.take 1
private def p1BcpS15Fns : List Fn := FullM6BcpS15.m6BcpS15_fns
private def p1Adp13Fns : List Fn := [m6aPropLitRawFn, m6aPropagateIgnoreFn, m6aPropagateFn]
private def p1ParseBodyM6Fns : List Fn := (FullM6WalkParse.m6WalkParse_fns.drop 1).take 1
private def p1RecomputeTiersFns : List Fn := (Full.fullFns.drop 50).take 1
private def p1WatchGc1Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 3).take 2
private def p1WatchGc2Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 6).take 2
private def p1SweepBinsM6cfFns : List Fn := (FullM6CompactFlush.m6CompactFlush_fns.drop 1).take 1
private def p1SweepCopyFns : List Fn := (Full.fullFns.drop 58).take 1
private def p1WatchGc3Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 8).take 5
private def p1FlushTrailFns : List Fn := [FullM6CompactFlush.m6cfFlushTrailFn]
private def p1RedsFns : List Fn := (Full.fullFns.drop 52).take 3
private def p1ReduceFns : List Fn := [m6CanonicalReduceFn]

private def p1FnsSeg : List Fn :=
  p1DimacsFns ++ (p1Full1CoreFns ++ (p1WatchGc0Fns ++ (((m6Orch_fns.take 24).drop 0).take 2 ++
  (p1HeapFns ++ (p1RescaleM6Fns ++ (((m6Orch_fns.take 24).drop 2).take 1 ++ (p1BumpSchedFns ++
  (p1Adp0Fns ++ (p1InitAssignFns ++ (p1Hdr0Fns ++ (p1ParseHelpersFns ++
  (p1PropHelpersFns ++ (p1BcpS15Fns ++ (p1Adp13Fns ++ (p1ParseBodyM6Fns ++
  (((m6Orch_fns.take 24).drop 3).take 1 ++ (p1RecomputeTiersFns ++ (p1WatchGc1Fns ++
  (p1WatchGc2Fns ++ (((m6Orch_fns.take 24).drop 4).take 1 ++ (p1SweepBinsM6cfFns ++
  (((m6Orch_fns.take 24).drop 5).take 1 ++ (p1SweepCopyFns ++
  (((m6Orch_fns.take 24).drop 6).take 1 ++ (p1WatchGc3Fns ++
  (((m6Orch_fns.take 24).drop 7).take 2 ++ (p1FlushTrailFns ++
  (p1RedsFns ++ (p1ReduceFns ++ ((m6Orch_fns.take 24).drop 9).take 1)))))))))))))))))))))))))))))

private theorem p1Fns_eq : m6FnsPart1 = p1FnsSeg := by t_kernel_rfl

theorem m6RowsPart1_sigs {tPfx : List SpecEntry}
    (hsig : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    (m6RowsPart1 tPfx).map (fun e => (e.name, e.as, e.rs)) = m6FnsPart1.map Fn.sig := by
  have h01 : p1DimacsRows.map (fun e => (e.name, e.as, e.rs)) = p1DimacsFns.map Fn.sig := by
    t_kernel_rfl
  have h02 : p1Full1CoreRows.map (fun e => (e.name, e.as, e.rs)) = p1Full1CoreFns.map Fn.sig := by
    t_kernel_rfl
  have h03 : p1WatchGc0Rows.map (fun e => (e.name, e.as, e.rs)) = p1WatchGc0Fns.map Fn.sig := by
    t_kernel_rfl
  have h04 : p1HeapRows.map (fun e => (e.name, e.as, e.rs)) = p1HeapFns.map Fn.sig := by
    t_kernel_rfl
  have h05 : p1RescaleM6Rows.map (fun e => (e.name, e.as, e.rs)) = p1RescaleM6Fns.map Fn.sig := by
    t_kernel_rfl
  have h06 : p1BumpSchedRows.map (fun e => (e.name, e.as, e.rs)) = p1BumpSchedFns.map Fn.sig := by
    t_kernel_rfl
  have h07 : p1Adp0Rows.map (fun e => (e.name, e.as, e.rs)) = p1Adp0Fns.map Fn.sig := by
    t_kernel_rfl
  have h08 : p1InitAssignRows.map (fun e => (e.name, e.as, e.rs)) =
      p1InitAssignFns.map Fn.sig := by t_kernel_rfl
  have h09 : p1Hdr0ExactRows.map (fun e => (e.name, e.as, e.rs)) = p1Hdr0Fns.map Fn.sig := by
    t_kernel_rfl
  have h10 : p1ParseHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      p1ParseHelpersFns.map Fn.sig := by t_kernel_rfl
  have h11 : p1PropHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      p1PropHelpersFns.map Fn.sig := by t_kernel_rfl
  have h12 : p1BcpS15Rows.map (fun e => (e.name, e.as, e.rs)) = p1BcpS15Fns.map Fn.sig := by
    t_kernel_rfl
  have h13 : p1Adp13Rows.map (fun e => (e.name, e.as, e.rs)) = p1Adp13Fns.map Fn.sig := by
    t_kernel_rfl
  have h14 : p1ParseBodyM6Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1ParseBodyM6Fns.map Fn.sig := by t_kernel_rfl
  have h15 : p1RecomputeTiersRows.map (fun e => (e.name, e.as, e.rs)) =
      p1RecomputeTiersFns.map Fn.sig := by t_kernel_rfl
  have h16 : p1WatchGc1Rows.map (fun e => (e.name, e.as, e.rs)) = p1WatchGc1Fns.map Fn.sig := by
    t_kernel_rfl
  have h17 : p1WatchGc2Rows.map (fun e => (e.name, e.as, e.rs)) = p1WatchGc2Fns.map Fn.sig := by
    t_kernel_rfl
  have h18 : p1SweepBinsM6cfRows.map (fun e => (e.name, e.as, e.rs)) =
      p1SweepBinsM6cfFns.map Fn.sig := by t_kernel_rfl
  have h19 : p1SweepCopyRows.map (fun e => (e.name, e.as, e.rs)) = p1SweepCopyFns.map Fn.sig := by
    t_kernel_rfl
  have h20 : p1WatchGc3Rows.map (fun e => (e.name, e.as, e.rs)) = p1WatchGc3Fns.map Fn.sig := by
    t_kernel_rfl
  have h21 : p1FlushTrailRows.map (fun e => (e.name, e.as, e.rs)) =
      p1FlushTrailFns.map Fn.sig := by t_kernel_rfl
  have h22 : p1RedsRows.map (fun e => (e.name, e.as, e.rs)) = p1RedsFns.map Fn.sig := by
    t_kernel_rfl
  have h23 : p1ReduceRows.map (fun e => (e.name, e.as, e.rs)) = p1ReduceFns.map Fn.sig := by
    t_kernel_rfl
  rw [p1Fns_eq]
  unfold m6RowsPart1 p1FnsSeg
  simp only [List.map_append]
  rw [h01, h02, h03, pfxSlice_sigs hsig 0 2, h04, h05, pfxSlice_sigs hsig 2 1, h06, h07, h08,
    h09, h10, h11, h12, h13, h14, pfxSlice_sigs hsig 3 1, h15, h16, h17,
    pfxSlice_sigs hsig 4 1, h18, pfxSlice_sigs hsig 5 1, h19, pfxSlice_sigs hsig 6 1, h20,
    pfxSlice_sigs hsig 7 2, h21, h22, h23, pfxSlice_sigs hsig 9 1]

theorem m6RowsPart1_noExit {tPfx : List SpecEntry}
    (hno : tPfx.all SpecEntry.noExit = true) :
    (m6RowsPart1 tPfx).all SpecEntry.noExit = true := by
  have n01 : p1DimacsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n02 : p1Full1CoreRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n03 : p1WatchGc0Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n04 : p1HeapRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n05 : p1RescaleM6Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n06 : p1BumpSchedRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n07 : p1Adp0Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n08 : p1InitAssignRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n09 : p1Hdr0ExactRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n10 : p1ParseHelpersRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n11 : p1PropHelpersRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n12 : p1BcpS15Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n13 : p1Adp13Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n14 : p1ParseBodyM6Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n15 : p1RecomputeTiersRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n16 : p1WatchGc1Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n17 : p1WatchGc2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n18 : p1SweepBinsM6cfRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n19 : p1SweepCopyRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n20 : p1WatchGc3Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n21 : p1FlushTrailRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n22 : p1RedsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n23 : p1ReduceRows.all SpecEntry.noExit = true := by t_kernel_rfl
  simp only [m6RowsPart1, List.all_append, n01, n02, n03, n04, n05, n06, n07, n08, n09, n10, n11,
    n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, pfxSlice_noExit hno,
    Bool.and_self]

theorem m6Part1Callees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m6RowsPart1 tPfx, e ∈ tbl) : M6Part1Callees tbl := by
  have sub_f1c : ∀ e ∈ p1Full1CoreRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; apply List.mem_append_right; exact List.mem_append_left _ h)
  have sub_heap : ∀ e ∈ p1HeapRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 4 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_bump : ∀ e ∈ p1BumpSchedRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 7 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_adp0 : ∀ e ∈ p1Adp0Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 8 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_init : ∀ e ∈ p1InitAssignRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 9 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_hdr0 : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 10 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_prph : ∀ e ∈ p1PropHelpersRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 12 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_bcp : ∀ e ∈ p1BcpS15Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 13 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_adp13 : ∀ e ∈ p1Adp13Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 14 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_flsh : ∀ e ∈ p1FlushTrailRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 27 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_red : ∀ e ∈ p1ReduceRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 29 apply List.mem_append_right
    exact List.mem_append_left _ h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sub_f1c _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_f1c _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_f1c _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_f1c _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_f1c _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_heap _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 5) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 6) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 7) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 5) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 7) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 10) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 18) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 19) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 21) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 22) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 23) rfl)
  · exact sub_prph _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_prph _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_adp0 _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_adp13 _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_adp13 _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_flsh _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_red _ (List.mem_of_getElem? (i := 0) rfl)

/-! ## 4. Part 1 Segment `TableImpl` Proofs -/

private theorem m3_tick_zip_p :
    ∀ p ∈ List.zip [FullM3VivChrono.m3TickRelFn]
        [⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩],
      p.1 ∈ FullM3VivChrono.m3Module.fns ∧
      p.2 ∈ FullM3VivChrono.m3SpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
  subst hp
  exact ⟨List.mem_of_getElem? (i := 0) rfl, List.mem_of_getElem? (i := 0) rfl, rfl, rfl, rfl⟩

private theorem m5Sched3_zip_p :
    ∀ p ∈ List.zip (FullM5Sched.m5Sched_fns.take 3) (FullM5Sched.m5SchedSpecTable.take 3),
      p.1 ∈ FullM5Sched.m5SchedModule.fns ∧ p.2 ∈ FullM5Sched.m5SchedSpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  have hz := modSub_drop_take (M1 := FullM5Sched.m5SchedModule)
    (t1 := FullM5Sched.m5SchedSpecTable.take 6) rfl (off := 0) (n := 3)
  have hdt : (FullM5Sched.m5SchedModule.fns.drop 0).take 3 =
      FullM5Sched.m5Sched_fns.take 3 := rfl
  have hst : ((FullM5Sched.m5SchedSpecTable.take 6).drop 0).take 3 =
      FullM5Sched.m5SchedSpecTable.take 3 := by
    rw [List.drop_zero, List.take_take]; rfl
  intro p hp
  rw [← hdt, ← hst] at hp
  obtain ⟨h1, h2, hn, ha, hrs⟩ := hz.2 p hp
  exact ⟨h1, List.mem_of_mem_take h2, hn, ha, hrs⟩

private theorem m5SchedSpecTable_nodup :
    (FullM5Sched.m5SchedSpecTable.map SpecEntry.name).Nodup := by
  decide

private theorem m6BcpS15SpecTable_nodup :
    (FullM6BcpS15.m6BcpS15SpecTable.map SpecEntry.name).Nodup := by
  decide

private theorem p1BumpSched_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1BumpSchedRows, e ∈ tbl)
    (hUp : (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRes : (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1BumpSchedFns p1BumpSchedRows := by
  have h1 : SpecEntry.Impl (Env.ofTable tbl) FullM4Bump.m4BumpVarFn
      ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ :=
    SpecEntry.Impl.of (FullM4Bump.full_bump_var_m4_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hUp) (envRow_mem hnd _ _ _ _ hRes))
  have h2 := (fullSliceTransport 22 3 [⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩]
    (by t_kernel_rfl) (fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact fullRow_at 20 _)
    hnd (fun _ h => hown _ (by
      unfold p1BumpSchedRows; apply List.mem_append_right; exact List.mem_append_left _ h))
    (m6_mem1 hRes)).2
  have h3 := (modSubTransport FullM3VivChrono.m3_moduleOk FullM3VivChrono.m3SpecTable_nodup
    (fs := [FullM3VivChrono.m3TickRelFn])
    (sub_tbl := [⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩]) (extRows := [])
    rfl m3_tick_zip_p (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact hown _ (by unfold p1BumpSchedRows; iterate 2 apply List.mem_append_right
                       exact List.mem_append_left _ List.mem_cons_self))
    (fun _ h => nomatch h)).2
  have h4 := (modSubTransport FullM5Sched.m5Sched_moduleOk m5SchedSpecTable_nodup
    (extRows := []) rfl m5Sched3_zip_p
    (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (by
      unfold p1BumpSchedRows
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))))
    (fun _ h => nomatch h)).2
  exact tableImpl_append rfl ⟨h1, trivial⟩
    (tableImpl_append rfl h2 (tableImpl_append rfl h3 h4))

private theorem p1InitAssign_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1InitAssignRows, e ∈ tbl)
    (hHdr : (⟨"kissat_parse_header", [i64, i64, i64], [.bool],
      kissatParseHeaderSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAlloc : (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64],
      Full.fullAllocClSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl)
    (hHeapPush : (⟨"full_heap_push", [i64, i32], [], Full.fullHeapPushSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p1InitAssignFns p1InitAssignRows := by
  have hm : ∀ (i : Nat) (e : SpecEntry), p1InitAssignRows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hs0 := (fullSliceTransport 27 2 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (by unfold p1InitAssignRows; exact List.mem_append_left _ h))
    (fun _ h => nomatch h)).2
  have hSave : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5SaveTargetBestFn
      ⟨"full_save_target_best", [i64], [], Full.fullSaveTargetBestSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_save_target_best_m5_wp (Env.ofTable tbl))
  have hBtRaw : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5BacktrackRawFn
      ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_backtrack_raw_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 2 _ rfl)) (envRow_mem hnd _ _ _ _ hHeapPush))
  have hBt : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5BacktrackFn
      ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_backtrack_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 3 _ rfl)) (envRow_mem hnd _ _ _ _ (hm 2 _ rfl)))
  have hs1 := (fullSliceTransport 31 5
    [ ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩
    , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩ ]
    (by t_kernel_rfl)
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact fullRow_at 12 _
      · exact fullRow_at 15 _)
    hnd (fun _ h => hown _ (by
      unfold p1InitAssignRows; iterate 2 apply List.mem_append_right
      exact List.mem_append_left _ h))
    (m6_memC hAlloc (m6_mem1 hPush))).2
  have hInitHdr : TableImpl (Env.ofTable tbl) (FullFastBveBudgets.fastBveBudgets_fns.take 1)
      [⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩] := by
    have heq : FullFastBveBudgets.fastBveBudgets_fns.take 1 =
        [⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.full_init_hdr_body⟩] := rfl
    rw [heq]
    exact ⟨SpecEntry.Impl.of (FullFastBveBudgets.fast_init_hdr_canon_wp (Env.ofTable tbl)),
      trivial⟩
  have hs2 := (fullSliceTransport 37 1
    [⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩]
    (by t_kernel_rfl)
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact fullRow_at 34 _)
    hnd (fun _ h => hown _ (by
      unfold p1InitAssignRows; iterate 4 apply List.mem_append_right
      exact List.mem_append_left _ h))
    (m6_mem1 (hm 8 _ rfl))).2
  have hCaps : TableImpl (Env.ofTable tbl) (FullM5Orch.m5Orch_fns.take 2)
      [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
      , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩ ] := by
    have heq : FullM5Orch.m5Orch_fns.take 2 =
        [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.full_calc_ext_cap_m5_body⟩
        , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.full_calc_scr_cap_m5_body⟩ ] := rfl
    rw [heq]
    exact ⟨SpecEntry.Impl.of (FullM5Orch.full_calc_ext_cap_m5_wp (Env.ofTable tbl)),
      SpecEntry.Impl.of (FullM5Orch.full_calc_scr_cap_m5_wp (Env.ofTable tbl)), trivial⟩
  have hs3 := (fullSliceTransport 40 1
    [⟨"full_init_ptrs", [i64, i64, i64], [], Full.fullInitPtrsSpec, true⟩]
    (by t_kernel_rfl)
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact fullRow_at 35 _)
    hnd (fun _ h => hown _ (by
      unfold p1InitAssignRows; iterate 6 apply List.mem_append_right
      exact List.mem_append_left _ h))
    (m6_mem1 (hm 9 _ rfl))).2
  have hInitStM5 : TableImpl (Env.ofTable tbl) ((FullM5Orch.m5Orch_fns.drop 2).take 1)
      [⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
        Full.fullInitStateSpec, true⟩] := by
    have heq : (FullM5Orch.m5Orch_fns.drop 2).take 1 =
        [⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
          FullM5Orch.full_init_state_m5_body⟩] := rfl
    rw [heq]
    refine ⟨SpecEntry.Impl.of (FullM5Orch.full_init_state_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hHdr) (envRow_mem hnd _ _ _ _ (hm 8 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 11 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 12 _ rfl) FullM5Orch.fullCalcExtCapM5Spec_noExit)
      (envRow_mem hnd _ _ _ _ (hm 13 _ rfl) FullM5Orch.fullCalcScrCapM5Spec_noExit)
      (envRow_mem hnd _ _ _ _ (hm 14 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 10 _ rfl)) (envRow_mem hnd _ _ _ _ (hm 6 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 7 _ rfl))), trivial⟩
  have hInitSt : SpecEntry.Impl (Env.ofTable tbl) FullM5.m5InitStateFwdFn
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5.m5_init_state_fwd_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 15 _ rfl)))
  unfold p1InitAssignFns p1InitAssignRows
  refine tableImpl_append rfl hs0 (tableImpl_append rfl ⟨hSave, hBtRaw, hBt, trivial⟩ ?_)
  refine tableImpl_append rfl hs1 (tableImpl_append rfl hInitHdr ?_)
  refine tableImpl_append rfl hs2 (tableImpl_append rfl hCaps ?_)
  exact tableImpl_append rfl hs3 (tableImpl_append rfl hInitStM5 ⟨hInitSt, trivial⟩)

private theorem p1Hdr0_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl)
    (hInitSt : (⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      Full.fullInitStateSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1Hdr0Fns p1Hdr0ExactRows := by
  have hfn : p1Hdr0Fns =
      [ ⟨"full_m6_hdr_sizeof", [], [i64], full_m6_hdr_sizeof_body⟩
      , ⟨"full_m6_ext_sizeof", [], [i64], full_m6_ext_sizeof_body⟩
      , ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
      , ⟨"m6_hdr_reset", [i64], [], m6_hdr_reset_body⟩
      , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
      , ⟨"m6_hdr_ext_ready", [i64], [.bool], m6_hdr_ext_ready_body⟩
      , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], full_m6_mem_init_body⟩
      , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6_hdr_sync_legacy_tiers_body⟩
      , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6_hdr_recompute_tiers_mode_body⟩
      , ⟨"m6_hdr_recompute_tiers", [i64], [], m6_hdr_recompute_tiers_body⟩
      , ⟨"m6_hdr_update_tier_limits", [i64], [], m6_hdr_update_tier_limits_body⟩
      , ⟨"m6_hdr_record_used", [i64, i64], [], m6_hdr_record_used_body⟩
      , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6_hdr_get_tier1_body⟩
      , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6_hdr_get_tier2_body⟩
      , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6_hdr_delaying_body⟩
      , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6_hdr_bump_delay_body⟩
      , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6_hdr_reduce_delay_body⟩
      , ⟨"m6_hdr_reset_delay", [i64, i64], [], m6_hdr_reset_delay_body⟩
      , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6_hdr_get_watermark_body⟩
      , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6_hdr_set_watermark_body⟩
      , ⟨"m6_hdr_add_ticks", [i64, i64], [], m6_hdr_add_ticks_body⟩
      , ⟨"m6_hdr_dr_init", [i64], [], m6_hdr_dr_init_body⟩
      , ⟨"m6_hdr_dr_update", [i64], [], m6_hdr_dr_update_body⟩
      , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6_hdr_dr_allow_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1Hdr0ExactRows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have h_init := envRow_mem hnd _ _ _ _ (hm 2 _ rfl) (fun _ _ _ _ h => m6HdrInitSpec_monoX h)
  have h_ens := envRow_mem hnd _ _ _ _ (hm 4 _ rfl) (fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  have h_sync := envRow_mem hnd _ _ _ _ (hm 7 _ rfl) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have h_mode := envRow_mem hnd _ _ _ _ (hm 8 _ rfl) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have h_rec := envRow_mem hnd _ _ _ _ (hm 9 _ rfl) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have h_dr := envRow_mem hnd _ _ _ _ (hm 21 _ rfl) (fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)
  have h_ist := envRow_mem hnd _ _ _ _ hInitSt
  rw [hfn]; unfold p1Hdr0ExactRows
  exact ⟨ SpecEntry.Impl.of (full_m6_hdr_sizeof_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (full_m6_ext_sizeof_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (m6_hdr_init_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (m6_hdr_reset_wp (Env.ofTable tbl) h_init)
    , SpecEntry.Impl.of (m6_ext_ensure_init_wp (Env.ofTable tbl) h_init)
    , SpecEntry.Impl.of (m6_hdr_ext_ready_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (full_m6_mem_init_exact_wp (Env.ofTable tbl) h_ist h_init)
    , SpecEntry.Impl.of (m6_hdr_sync_legacy_tiers_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_recompute_tiers_mode_wp (Env.ofTable tbl) h_ens h_sync)
    , SpecEntry.Impl.of (m6_hdr_recompute_tiers_wp (Env.ofTable tbl) h_mode)
    , SpecEntry.Impl.of (m6_hdr_update_tier_limits_wp (Env.ofTable tbl) h_ens h_rec)
    , SpecEntry.Impl.of (m6_hdr_record_used_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_get_tier1_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_get_tier2_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_delaying_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_bump_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_reduce_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_reset_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_get_watermark_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_set_watermark_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_add_ticks_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_dr_init_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_dr_update_wp (Env.ofTable tbl) h_dr)
    , SpecEntry.Impl.of (m6_hdr_dr_allow_wp (Env.ofTable tbl) h_ens), trivial ⟩

private theorem p1BcpS15_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1BcpS15Rows, e ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1BcpS15Fns p1BcpS15Rows := by
  refine (tableImpl_transport_of_callsOk FullM6BcpS15.m6BcpS15_moduleOk m6BcpS15SpecTable_nodup
    hnd (allowed := (p1BcpS15Rows ++
      [(⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
        Full.fullWatchPushSpec, true⟩ : SpecEntry)]).map
      fun (e : SpecEntry) => (e.name, e.as, e.rs))
    (exits := []) rfl ?_ (all_mem_of_bool (by t_kernel_rfl)) ?_).2
  · intro p hp
    simp only [p1BcpS15Fns, p1BcpS15Rows, FullM6BcpS15.m6BcpS15_fns,
      FullM6BcpS15.m6BcpS15SpecTable, List.take_succ_cons, List.take_zero,
      List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, hown _ ?_, rfl, rfl, rfl⟩ <;>
      first
      | exact List.mem_of_getElem? (i := 0) rfl
      | exact List.mem_of_getElem? (i := 1) rfl
      | exact List.mem_of_getElem? (i := 2) rfl
      | exact List.mem_of_getElem? (i := 3) rfl
  · intro s hs
    rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
    rcases List.mem_append.mp he with h | h
    · exact ⟨e, List.mem_of_mem_take h, hown e h, rfl⟩
    · have heq : e = ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
          Full.fullWatchPushSpec, true⟩ := by simpa using h
      rw [heq]; exact ⟨_, List.mem_of_getElem? (i := 4) rfl, hPush, rfl⟩

private theorem p1WatchGc0_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1WatchGc0Rows, e ∈ tbl)
    (hSift : (⟨"full_wsort_sift", [i64, i64, i64, i64], [],
      Full.fullWsortSiftSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc0Fns p1WatchGc0Rows := by
  have hfn : p1WatchGc0Fns =
      [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
          FullM6WatchGc.full_wstack_radix_sort_m6_body⟩
      , ⟨"full_wstack_defrag_m6", [i64], [], FullM6WatchGc.full_wstack_defrag_m6_body⟩
      , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
          FullM6WatchGc.full_watch_push_m6_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1WatchGc0Rows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hRad := envRow_mem hnd _ _ _ _ (hm 0 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullWstackRadixSortSpec_xirrel h)
  have hDef := envRow_mem hnd _ _ _ _ (hm 1 _ rfl)
  rw [hfn]; unfold p1WatchGc0Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_wstack_radix_sort_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_wstack_defrag_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSift) hRad)
    , SpecEntry.Impl.of (FullM6WatchGc.full_watch_push_m6_wp (Env.ofTable tbl) hDef), trivial ⟩

private theorem p1WatchGc1_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDefrag : (⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc1Fns p1WatchGc1Rows := by
  have hfn : p1WatchGc1Fns =
      [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], FullM6WatchGc.full_lit_rank_m6_body⟩
      , ⟨"full_sweep_bins_range_m6", [i64, i64], [],
          FullM6WatchGc.full_sweep_bins_range_m6_body⟩ ] := rfl
  rw [hfn]; unfold p1WatchGc1Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_lit_rank_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_sweep_bins_range_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDefrag)), trivial ⟩

private theorem p1WatchGc2_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1WatchGc2Rows, e ∈ tbl)
    (hRank : (⟨"full_lit_rank_m6", [i64, i64, i32], [i64],
      Full.fullLitRankSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc2Fns p1WatchGc2Rows := by
  have hfn : p1WatchGc2Fns =
      [ ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
          FullM6WatchGc.full_rewatch_range_m6_body⟩
      , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool],
          FullM6WatchGc.full_rewatch_arena_m6_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1WatchGc2Rows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hRng := envRow_mem hnd _ _ _ _ (hm 0 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)
  rw [hfn]; unfold p1WatchGc2Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_rewatch_range_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hRank) (envRow_mem hnd _ _ _ _ hPush))
    , SpecEntry.Impl.of (FullM6WatchGc.full_rewatch_arena_m6_wp (Env.ofTable tbl) hRng), trivial ⟩

private theorem p1WatchGc3_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1WatchGc3Rows, e ∈ tbl)
    (hSwR : (⟨"full_sweep_bins_range_m6", [i64, i64], [],
      FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRewR : (⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
      FullM6WatchGc.fullRewatchRangeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hCopy : (⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64],
      Full.fullSweepCopySpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc3Fns p1WatchGc3Rows := by
  have hfn : p1WatchGc3Fns =
      [ ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [],
          FullM6WatchGc.full_move_red_pass2_m6_body⟩
      , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [],
          FullM6WatchGc.full_move_red_end_buf_m6_body⟩
      , ⟨"full_move_red_end_m6", [i64, i64, i64], [], FullM6WatchGc.full_move_red_end_m6_body⟩
      , ⟨"full_arena_sweep_m6", [i64], [i64], FullM6WatchGc.full_arena_sweep_m6_body⟩
      , ⟨"full_mark_reasons_m6", [i64, .bool], [],
          FullM6WatchGc.full_mark_reasons_m6_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1WatchGc3Rows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hP2 := envRow_mem hnd _ _ _ _ (hm 0 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedPass2Spec_xirrel h)
  have hBuf := envRow_mem hnd _ _ _ _ (hm 1 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndBufSpec_xirrel h)
  have hMre := envRow_mem hnd _ _ _ _ (hm 2 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndSpec_xirrel h)
  rw [hfn]; unfold p1WatchGc3Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_move_red_pass2_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_move_red_end_buf_m6_wp (Env.ofTable tbl) hP2)
    , SpecEntry.Impl.of (FullM6WatchGc.full_move_red_end_m6_wp (Env.ofTable tbl) hBuf)
    , SpecEntry.Impl.of (FullM6WatchGc.full_arena_sweep_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSwR
          (fun _ _ _ _ h => FullM6WatchGc.fullSweepBinsRangeSpec_xirrel h))
        (envRow_mem hnd _ _ _ _ hNext) (envRow_mem hnd _ _ _ _ hCopy) hMre
        (envRow_mem hnd _ _ _ _ hRewR
          (fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)))
    , SpecEntry.Impl.of (FullM6WatchGc.full_mark_reasons_m6_wp (Env.ofTable tbl)), trivial ⟩

private theorem p1Reduce_s15_impl {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hIsqrt : (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈ tbl)
    (hIlog : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hRec : (⟨"full_recompute_tiers", [i64], [], Full.fullRecomputeTiersSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hMrk : (⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hSort : (⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩ : SpecEntry) ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩ : SpecEntry) ∈ tbl)
    (hSweep : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p1ReduceFns p1ReduceRows := by
  have hfn : p1ReduceFns = [⟨"full_reduce", [i64, .bool], [i64], Full.full_reduce_body⟩] := rfl
  rw [hfn]; unfold p1ReduceRows
  have rIsqrt := envRow_mem hnd _ _ _ _ hIsqrt
  have rIlog := envRow_mem hnd _ _ _ _ hIlog
  have rNext := envRow_mem hnd _ _ _ _ hNext
  have rRec := envRow_mem hnd _ _ _ _ hRec
  have rMrk := envRow_mem hnd _ _ _ _ hMrk
  have rSort := envRow_mem hnd _ _ _ _ hSort
  have rBt := envRow_mem hnd _ _ _ _ hBt
  have rProp := s15_to_dwPropagate (envRow_mem hnd _ _ _ _ hProp)
  have rSweep := envRow_mem hnd _ _ _ _ hSweep
  have hwp := Full.full_reduce_wp (Env.ofTable tbl)
    (fun ⟨x, ⟨⟩⟩ m Q X hQ => rIsqrt (x, ()) m Q X fun r hsq _ _ =>
      hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq))
    rIlog rNext
    (by
      rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
      exact rRec (c.hdr, ()) m Q X ⟨c, s, R, rfl, hlen, hm, fun _ s' m' hc hlen' hp hm' =>
        by rcases s' with ⟨c', sc'⟩; change c' = s.core at hc; subst hc
           exact hQ sc' m' hlen'.scratch_ok hp.1.1 hp.1.2 hp.2.2.1 hm'⟩)
    (by
      rintro ⟨h, sf, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hm, hQ⟩
      exact rMrk (c.hdr, sf, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hm,
        fun ar' m' hl' hr' hp' hrm' hw' hm' =>
          hQ ar' m' hl' hr' hp' (fun hsf idx hidx => hrm' hsf idx hidx) hw' hm'⟩)
    (by
      rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, hQ⟩
      exact rSort (c.hdr, n, ()) m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, fun rr' m' hrr hm' =>
        hQ { s.scratch with red_refs := rr' } m'
          { hlen.scratch_ok with red_refs_len := hrr } rfl rfl rfl hm'⟩)
    (by
      rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hle, hm, hQ⟩
      have hmx : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
      have hcl_bd : s.core.cur_level < 2 ^ 64 := by
        have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le; omega
      have htg_bd : tgt.toNat < s.core.cur_level → tgt.toNat < c.max_vars := by
        intro _; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le; omega
      exact rBt (c.hdr, tgt, ()) m Q X ⟨c, s, R, rfl, hlen, hcl_bd, htg_bd, hw.trail_lits_lt,
        hm, fun va lv rs tr tp te pr cl un sc m' hl' _ _ hcl' hps _ _ _ hwt _ hm' => by
          have hmin : cl = tgt.toNat := hcl'.trans (Nat.min_eq_right hle)
          subst hmin
          exact hQ va lv rs tr tp te pr un sc m' hl' (hwt F0 Fc hw hle)
            hps.1.1 hps.1.2 hps.2.2.1 hm'⟩)
    rProp
    (by
      rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm, hQ⟩
      exact rSweep (c.hdr, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm,
        fun r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
            hl' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm' =>
          hQ r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
            hl' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'⟩)
  refine ⟨SpecEntry.Impl.of (fun ⟨h, force, ⟨⟩⟩ m Q X hs => ?_), trivial⟩
  rcases hs with ⟨c, F0, Fc, s, R, rfl, ⟨hlen, hw, hlm, hnd0, hext, hdm⟩, hm, hQ⟩
  exact hwp (c.hdr, force, ()) m Q X
    ⟨c, F0, Fc, s, R, rfl, hlen, hw, hlm, hnd0, hext, hdm, hm,
      fun r s' m' hdw hw' hr hu hoom hcl hfu hcv htmp htl _ _ _ _ _ _ hws2 hpos hm' =>
        hQ r s' m' ⟨hdw.1.lengths, hw', hdw.2.1, hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2⟩
          hr hcl hfu hcv htmp htl hws2 hu hoom (fun _ => hpos) hm'⟩

/-- Certifies all `112` functions of `FullM6.m6FnsPart1` against `m6RowsPart1 tPfx` in
`Env.ofTable tbl`. -/
theorem m6RowsPart1_tableImpl {tPfx tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxLen : (m6Orch_fns.take 24).length = tPfx.length)
    (hPfxOk : TableImpl (Env.ofTable tbl) (m6Orch_fns.take 24) tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hOwn : ∀ e ∈ m6RowsPart1 tPfx, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m6FnsPart1 (m6RowsPart1 tPfx) := by
  have hc := m6Part1Callees_of_sub hOwn
  have sub_dim : ∀ e ∈ p1DimacsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; exact List.mem_append_left _ h)
  have sub_f1c : ∀ e ∈ p1Full1CoreRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; apply List.mem_append_right; exact List.mem_append_left _ h)
  have sub_wg0 : ∀ e ∈ p1WatchGc0Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 2 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_heap : ∀ e ∈ p1HeapRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 4 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_bump : ∀ e ∈ p1BumpSchedRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 7 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_init : ∀ e ∈ p1InitAssignRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 9 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_hdr0 : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 10 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_ph : ∀ e ∈ p1ParseHelpersRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 11 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_prph : ∀ e ∈ p1PropHelpersRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 12 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_bcp : ∀ e ∈ p1BcpS15Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 13 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_rec : ∀ e ∈ p1RecomputeTiersRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 17 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_wg1 : ∀ e ∈ p1WatchGc1Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 18 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_wg2 : ∀ e ∈ p1WatchGc2Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 19 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_copy : ∀ e ∈ p1SweepCopyRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 23 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_wg3 : ∀ e ∈ p1WatchGc3Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 25 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_reds : ∀ e ∈ p1RedsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart1; iterate 28 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have rSift := sub_f1c _ (List.mem_of_getElem? (i := 5) rfl)
  have rWs := sub_dim _ (List.mem_of_getElem? (i := 2) rfl)
  have rHdr := sub_dim _ (List.mem_of_getElem? (i := 5) rfl)
  have rNLit := sub_dim _ (List.mem_of_getElem? (i := 6) rfl)
  have rHUp := sub_heap _ (List.mem_of_getElem? (i := 0) rfl)
  have rHPush := sub_heap _ (List.mem_of_getElem? (i := 2) rfl)
  have rInitSt := sub_init _ (List.mem_of_getElem? (i := 16) rfl)
  have rSkip := sub_ph _ (List.mem_of_getElem? (i := 0) rfl)
  have rIng := sub_ph _ (List.mem_of_getElem? (i := 1) rfl)
  have rRec := sub_rec _ (List.mem_of_getElem? (i := 0) rfl)
  have rWDefM6 := sub_wg0 _ (List.mem_of_getElem? (i := 1) rfl)
  have rWPshM6 := sub_wg0 _ (List.mem_of_getElem? (i := 2) rfl)
  have rRankM6 := sub_wg1 _ (List.mem_of_getElem? (i := 0) rfl)
  have rSwRM6 := sub_wg1 _ (List.mem_of_getElem? (i := 1) rfl)
  have rRewRM6 := sub_wg2 _ (List.mem_of_getElem? (i := 0) rfl)
  have rCopy := sub_copy _ (List.mem_of_getElem? (i := 0) rfl)
  have rSortReds := sub_reds _ (List.mem_of_getElem? (i := 2) rfl)
  have rWPush := htPfx _ hPfxSpecs.watchPush
  have rWDefrag := htPfx _ hPfxSpecs.wstackDefrag
  have rRescale := htPfx _ hPfxSpecs.rescale
  have rMrkRsn := htPfx _ hPfxSpecs.markReasons
  have rArSwp := htPfx _ hPfxSpecs.arenaSweep
  have ps : ∀ off n,
      TableImpl (Env.ofTable tbl) (((m6Orch_fns.take 24).drop off).take n)
        ((tPfx.drop off).take n) :=
    tableImpl_drop_take hPfxLen hPfxOk
  have hlen_p : ∀ (off n : Nat),
      (((m6Orch_fns.take 24).drop off).take n).length = ((tPfx.drop off).take n).length := by
    intro off n; simp [hPfxLen]
  have i_dim := (fullSliceTransport 0 8 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_dim
    (fun _ h => nomatch h)).2
  have i_f1c := (fullSliceTransport 8 6 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_f1c
    (fun _ h => nomatch h)).2
  have i_wg0 := p1WatchGc0_impl hnd sub_wg0 rSift
  have i_heap := (fullSliceTransport 16 4 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_heap
    (fun _ h => nomatch h)).2
  have i_resM6 : TableImpl (Env.ofTable tbl) p1RescaleM6Fns p1RescaleM6Rows :=
    m6_oneImpl rfl rfl (FullM6WalkParse.full_rescale_m6_wp (Env.ofTable tbl))
  have i_bump := p1BumpSched_impl hnd sub_bump rHUp rRescale
  have i_adp0 : TableImpl (Env.ofTable tbl) p1Adp0Fns p1Adp0Rows :=
    m6_oneImpl rfl rfl
      (full_scale_delta_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hc.scaleDeltaM5))
  have i_init := p1InitAssign_impl hnd sub_init rHdr hc.allocCl rWPush rHPush
  have i_hdr0 := p1Hdr0_impl hnd sub_hdr0 rInitSt
  have i_ph := (fullSliceTransport 42 2
    [ ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
    , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], Full.fullAddClauseSpec, true⟩ ]
    (by t_kernel_rfl)
    (m6_memC (fullRow_at 6 _) (m6_memC (fullRow_at 27 _) (m6_mem1 (fullRow_at 31 _))))
    hnd sub_ph (m6_memC rNLit (m6_memC hc.assignLvl (m6_mem1 hc.addClause)))).2
  have i_prph : TableImpl (Env.ofTable tbl) p1PropHelpersFns p1PropHelpersRows := by
    have hs := (fullSliceTransport 45 2 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
      (fun _ h => sub_prph _ (List.mem_append_left _ h)) (fun _ h => nomatch h)).2
    have hu : TableImpl (Env.ofTable tbl) (FullM5Otfs.m5Otfs_fns.take 1)
        [⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩] :=
      m6_oneImpl rfl rfl (FullM5Otfs.full_unwatch_large_wp (Env.ofTable tbl))
    exact tableImpl_append rfl hs hu
  have i_bcp := p1BcpS15_impl hnd sub_bcp rWPush
  have i_adp13 : TableImpl (Env.ofTable tbl) p1Adp13Fns p1Adp13Rows := by
    unfold p1Adp13Fns p1Adp13Rows
    exact ⟨ SpecEntry.Impl.of (full_prop_lit_raw_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc.propLitRawS15))
      , SpecEntry.Impl.of (full_propagate_ignore_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc.propagateIgnS15))
      , SpecEntry.Impl.of (full_propagate_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hc.bcpS15))
      , trivial ⟩
  have i_pbM6 : TableImpl (Env.ofTable tbl) p1ParseBodyM6Fns p1ParseBodyM6Rows :=
    m6_oneImpl rfl rfl (FullM6WalkParse.full_parse_body_m6_del_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rSkip) (envRow_mem hnd _ _ _ _ rIng)
      (s15_to_propagateDel (envRow_mem hnd _ _ _ _ hc.propagate)) (envRow_mem hnd _ _ _ _ rWs))
  have i_rec := (fullSliceTransport 50 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_rec
    (fun _ h => nomatch h)).2
  have i_wg1 := p1WatchGc1_impl hnd rWDefM6
  have i_wg2 := p1WatchGc2_impl hnd sub_wg2 rRankM6 rWPshM6
  have i_swb : TableImpl (Env.ofTable tbl) p1SweepBinsM6cfFns p1SweepBinsM6cfRows :=
    m6_oneImpl rfl rfl (FullM6CompactFlush.full_sweep_bins_m6cf_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rWDefrag))
  have i_copy := (fullSliceTransport 58 1
    [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ]
    (by t_kernel_rfl) (m6_memC (fullRow_at 15 _) (m6_mem1 (fullRow_at 27 _)))
    hnd sub_copy (m6_memC rWPush (m6_mem1 hc.assignLvl))).2
  have i_wg3 := p1WatchGc3_impl hnd sub_wg3 rSwRM6 rRewRM6 hc.arenaNext rCopy
  have i_flsh : TableImpl (Env.ofTable tbl) p1FlushTrailFns p1FlushTrailRows :=
    m6_oneImpl rfl rfl (FullM6CompactFlush.full_flush_trail_del_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc.backtrack)
      (s15_to_propagateDel (envRow_mem hnd _ _ _ _ hc.propagate)))
  have i_reds := (fullSliceTransport 52 3 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_reds
    (fun _ h => nomatch h)).2
  have i_red := p1Reduce_s15_impl hnd hc.isqrt hc.ilog10 hc.arenaNext rRec rMrkRsn rSortReds
    hc.backtrack hc.propagate rArSwp
  rw [p1Fns_eq]; unfold p1FnsSeg m6RowsPart1
  refine tableImpl_append rfl i_dim (tableImpl_append rfl i_f1c (tableImpl_append rfl i_wg0 ?_))
  refine tableImpl_append (hlen_p 0 2) (ps 0 2) (tableImpl_append rfl i_heap ?_)
  refine tableImpl_append rfl i_resM6 (tableImpl_append (hlen_p 2 1) (ps 2 1) ?_)
  refine tableImpl_append rfl i_bump (tableImpl_append rfl i_adp0 (tableImpl_append rfl i_init ?_))
  refine tableImpl_append rfl i_hdr0 (tableImpl_append rfl i_ph (tableImpl_append rfl i_prph ?_))
  refine tableImpl_append rfl i_bcp (tableImpl_append rfl i_adp13 (tableImpl_append rfl i_pbM6 ?_))
  refine tableImpl_append (hlen_p 3 1) (ps 3 1) (tableImpl_append rfl i_rec ?_)
  refine tableImpl_append rfl i_wg1 (tableImpl_append rfl i_wg2 ?_)
  refine tableImpl_append (hlen_p 4 1) (ps 4 1) (tableImpl_append rfl i_swb ?_)
  refine tableImpl_append (hlen_p 5 1) (ps 5 1) (tableImpl_append rfl i_copy ?_)
  refine tableImpl_append (hlen_p 6 1) (ps 6 1) (tableImpl_append rfl i_wg3 ?_)
  refine tableImpl_append (hlen_p 7 2) (ps 7 2) (tableImpl_append rfl i_flsh ?_)
  refine tableImpl_append rfl i_reds (tableImpl_append rfl i_red ?_)
  exact ps 9 1

theorem m6_mem_drop_take_of_lt {α : Type _} (xs : List α) {off n i : Nat}
    (hlo : off ≤ i) (hhi : i < off + n) (hit : i < xs.length) :
    xs[i] ∈ (xs.drop off).take n := by
  have hj : i - off < ((xs.drop off).take n).length := by
    rw [List.length_take, List.length_drop]; omega
  have hget : ((xs.drop off).take n)[i - off]'hj = xs[i]'hit := by
    rw [List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [← hget]; exact List.getElem_mem hj

theorem m6RowsPart1_tPfx_mem {tPfx : List SpecEntry} {i : Nat}
    (hi : i < 10) (hit : i < tPfx.length) :
    tPfx[i] ∈ m6RowsPart1 tPfx := by
  unfold m6RowsPart1
  rcases Nat.lt_or_ge i 2 with h02 | h2
  · (iterate 3 apply List.mem_append_right); apply List.mem_append_left
    simpa [List.drop_zero] using m6_mem_drop_take_of_lt tPfx (Nat.zero_le _) h02 hit
  · rcases Nat.lt_or_ge i 3 with h23 | h3
    · (iterate 6 apply List.mem_append_right); apply List.mem_append_left
      exact m6_mem_drop_take_of_lt tPfx h2 h23 hit
    · rcases Nat.lt_or_ge i 4 with h34 | h4
      · (iterate 16 apply List.mem_append_right); apply List.mem_append_left
        exact m6_mem_drop_take_of_lt tPfx h3 h34 hit
      · rcases Nat.lt_or_ge i 5 with h45 | h5
        · (iterate 20 apply List.mem_append_right); apply List.mem_append_left
          exact m6_mem_drop_take_of_lt tPfx h4 h45 hit
        · rcases Nat.lt_or_ge i 6 with h56 | h6
          · (iterate 22 apply List.mem_append_right); apply List.mem_append_left
            exact m6_mem_drop_take_of_lt tPfx h5 h56 hit
          · rcases Nat.lt_or_ge i 7 with h67 | h7
            · (iterate 24 apply List.mem_append_right); apply List.mem_append_left
              exact m6_mem_drop_take_of_lt tPfx h6 h67 hit
            · rcases Nat.lt_or_ge i 9 with h79 | h9
              · (iterate 26 apply List.mem_append_right); apply List.mem_append_left
                exact m6_mem_drop_take_of_lt tPfx h7 h79 hit
              · (iterate 30 apply List.mem_append_right)
                exact m6_mem_drop_take_of_lt tPfx h9 (by omega) hit

theorem m6Part1TailCallees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m6RowsPart1 tPfx, e ∈ tbl) :
    (⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
      fullM6MemInitExactSpec, true⟩ : SpecEntry) ∈ tbl ∧
    (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissatCheckModelExactSpec, true⟩ : SpecEntry) ∈ tbl := by
  have hmi : p1Hdr0ExactRows[6]? = some
      ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
        fullM6MemInitExactSpec, true⟩ := rfl
  have hck : p1DimacsRows[7]? = some
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
        kissatCheckModelExactSpec, true⟩ := rfl
  exact ⟨ hsub _ (by
      unfold m6RowsPart1; (iterate 10 apply List.mem_append_right); apply List.mem_append_left
      exact List.mem_of_getElem? hmi)
    , hsub _ (by
      unfold m6RowsPart1; apply List.mem_append_left; exact List.mem_of_getElem? hck) ⟩

/-- Part 1 external callee memberships required by `m6Orch_fns.take 24`. -/
structure M6Part1ExtCallees (tbl : List SpecEntry) : Prop where
  wstackDefragM6 :
    (⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈ tbl
  watchPushM6 :
    (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl
  rescaleM6 :
    (⟨"full_rescale_m6", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈ tbl
  parseBodyM6 :
    (⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩ : SpecEntry) ∈ tbl
  litRankM6 :
    (⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩ : SpecEntry) ∈ tbl
  sweepBinsM6cf :
    (⟨"full_sweep_bins_m6cf", [i64], [], Full.fullSweepBinsSpec, true⟩ : SpecEntry) ∈ tbl
  rewatchArenaM6 :
    (⟨"full_rewatch_arena_m6", [i64, i64], [.bool],
      Full.fullRewatchArenaSpec, true⟩ : SpecEntry) ∈ tbl
  arenaSweepM6 :
    (⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈ tbl
  markReasonsM6 :
    (⟨"full_mark_reasons_m6", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ : SpecEntry) ∈ tbl
  recomputeTiers :
    (⟨"m6_hdr_recompute_tiers", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩ : SpecEntry) ∈ tbl
  sortReds :
    (⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩ : SpecEntry) ∈ tbl
  setWm :
    (⟨"m6_hdr_set_watermark", [i64, i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64, i64] [], true⟩ :
      SpecEntry) ∈ tbl
  recordUsed :
    (⟨"m6_hdr_record_used", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩ :
      SpecEntry) ∈ tbl
  extReady :
    (⟨"m6_hdr_ext_ready", [i64], [.bool], FullM6Hdr.m6HdrExtReadySpec, true⟩ : SpecEntry) ∈ tbl
  getWm :
    (⟨"m6_hdr_get_watermark", [i64, i64], [i64], FullM6Hdr.m6HdrW2aSpec [i64] [i64], true⟩ :
      SpecEntry) ∈ tbl
  heapDown :
    (⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩ : SpecEntry) ∈ tbl
  delaying :
    (⟨"m6_hdr_delaying", [i64, i64], [.bool], FullM6Hdr.m6HdrW2aSpec [i64] [.bool], true⟩ :
      SpecEntry) ∈ tbl
  reduceDelay :
    (⟨"m6_hdr_reduce_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩ :
      SpecEntry) ∈ tbl
  bumpDelay :
    (⟨"m6_hdr_bump_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩ :
      SpecEntry) ∈ tbl

theorem m6Part1ExtCallees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m6RowsPart1 tPfx, e ∈ tbl) : M6Part1ExtCallees tbl := by
  have sub_wg0 : ∀ e ∈ p1WatchGc0Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 2 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_heap : ∀ e ∈ p1HeapRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 4 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_resc : ∀ e ∈ p1RescaleM6Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 5 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_hdr0 : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 10 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_pb : ∀ e ∈ p1ParseBodyM6Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 15 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_wg1 : ∀ e ∈ p1WatchGc1Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 18 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_wg2 : ∀ e ∈ p1WatchGc2Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 19 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_swb : ∀ e ∈ p1SweepBinsM6cfRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 21 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_wg3 : ∀ e ∈ p1WatchGc3Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 25 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_reds : ∀ e ∈ p1RedsRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart1; iterate 28 apply List.mem_append_right
    exact List.mem_append_left _ h)
  refine ⟨ sub_wg0 _ (List.mem_of_getElem? (i := 1) rfl)
         , sub_wg0 _ (List.mem_of_getElem? (i := 2) rfl)
         , sub_resc _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_pb _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_wg1 _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_swb _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_wg2 _ (List.mem_of_getElem? (i := 1) rfl)
         , sub_wg3 _ (List.mem_of_getElem? (i := 3) rfl)
         , sub_wg3 _ (List.mem_of_getElem? (i := 4) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 9) rfl)
         , sub_reds _ (List.mem_of_getElem? (i := 2) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 19) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 11) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 5) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 18) rfl)
         , sub_heap _ (List.mem_of_getElem? (i := 1) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 14) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 16) rfl)
         , sub_hdr0 _ (List.mem_of_getElem? (i := 15) rfl) ⟩

end LeanQbe.T.Examples.Kissat.FullM6Proof

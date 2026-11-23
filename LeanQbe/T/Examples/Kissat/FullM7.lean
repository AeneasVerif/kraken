module

public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.FullM7BcpHot
public import LeanQbe.T.Examples.Kissat.FullM7CongHash
public import LeanQbe.T.Examples.Kissat.FullM7CongIte
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
public import LeanQbe.T.Examples.Kissat.FullM7Bump
public import LeanQbe.T.Examples.Kissat.FullM7Walk
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
public import LeanQbe.T.Examples.Kissat.FullM7Search
meta import LeanQbe.T.Examples.Kissat.FullM6
meta import LeanQbe.T.Examples.Kissat.FullM7BcpHot
meta import LeanQbe.T.Examples.Kissat.FullM7CongHash
meta import LeanQbe.T.Examples.Kissat.FullM7CongIte
meta import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
meta import LeanQbe.T.Examples.Kissat.FullM7Bump
meta import LeanQbe.T.Examples.Kissat.FullM7Walk
meta import LeanQbe.T.Examples.Kissat.FullM7BveGates
meta import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
meta import LeanQbe.T.Examples.Kissat.FullM7Search
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat `D-Full` Unified `M7` (`M6.2_winning`) Assembly (`FullM7`)

Assembles the closed `M7` (`M6.2_winning`) solver module (`m7Module`, `externs := []`,
`exits := []`) over fixed `FullM6` by splicing all `9` M7 `GO` modules (WITHOUT `FullM6Sweep`
which was `DROP`):

- `FullM7BcpHot` (`full_prop_lit_ovf_hot`, `full_prop_chrono_hot`, `full_propagate_ignore`,
  `full_bcp_hot`, `full_propagate`),
- `FullM7CongHash` (`131072` congruence hash table ceiling) + `FullM7CongIte`
  (`full_cong_extract_ite_all_m7`),
- `FullM7AnalyzeSort` (`full_sort_tmp_sift`, `full_sort_tmp`, `full_sort_u32`, `full_rephase`),
- `FullM7Bump` (`full_rng_next`, `full_scale_delta`, `full_scale_delta_m5`,
  `full_bump_analyzed`),
- `FullM7Walk` (`full_warmup`, `full_walk` -> `full_walk_warmup_m7`),
- `FullM7BveGates` (`full_forward_sub`, `full_bve_collect`, `full_bve_var`, `full_eliminate_m6`),
- `FullM7BvaFactor` (`full_init_fresh_var`, `full_bva_try_lit`, `full_factor`),
- `FullM7Search` (`full_lucky_late_m7` called ONCE before `while (true)` in `full_search_m6`,
  `full_decide_m7`, `full_switch_mode_m7`, `full_ema_swap_m7`),
- `FullM7Reorder` (inherited from `FullM6`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

/-! ## 1. M7 Orchestrator Overrides (`full_congruence_dense`, `full_search_m6`) -/

kissat_c0! m7Overrides "
typedef struct {
  u64 mv, nc, cur, val;
} KissatDimacs;

typedef struct {
  KissatDimacs d;
  u64 arena_cap, wcap, arena_len, wlen;
  u64 values, mark, level, reason, trail;
  u64 watch_vec, arena, watch_stk, delayed, tmp_lits;
  u64 trail_end, propagated, cur_level, fuel, confl_ref;
  u64 tmp_cnt, tmp_len, heap, pos, score;
  u64 phases, min_stk, min_clr, heap_len, scinc;
  u64 min_depth, min_clr_len, min_clr_full, rel_period, rel_limit;
  u64 rel_wait, rel_u, rel_v, rel_trigger, conflicts;
  u64 learned_lits, min_removed, trail_pos, q_prev, q_next;
  u64 q_stamp, phases_target, phases_best, wsort, shrink_stk;
  u64 red_refs, glue_used, red_cap, delayed_cap, delayed_len;
  u64 wusable, arena_garbage, first_reducible, num_irred, num_redundant;
  u64 num_binary, unflushed, probing, confl_type, confl_lit0;
  u64 confl_lit1, stable, switched, mode_count, mode_confl_lim;
  u64 mode_tick_lim, mode_saved_ticks, search_ticks, q_first, q_last;
  u64 q_search_idx, q_search_stamp, q_cur_stamp, target_assigned, best_assigned;
  u64 rephase_limit, rephased, reduce_limit, reductions, tier1;
  u64 tier2, restarts, restart_limit, ema_fast_biased, ema_fast_exp;
  u64 ema_slow_biased, ema_slow_exp, oom;
  u64 max_vars, cur_vars, bva_cap, unassigned;
  u64 flags, lit_mark, repr, sim_sig;
  u64 frame_trail, frame_dec, work_stk1, work_stk2;
  u64 tarjan_mark, tarjan_reach, walk_vals, walk_best;
  u64 extend_stk, extend_cap, extend_len;
  u64 scratch_buf, scratch_cap, last_learned;
  u64 rng_state, chrono_levels, otfs_cnt, eager_sub_cnt;
  u64 probe_limit, probings, elim_limit, eliminations;
  u64 elim_bound, dense_mode, inconsistent, iterating;
  u64 hbr_cnt, trans_cnt, viv_cnt, subst_cnt;
  u64 cong_cnt, sweep_cnt, bve_cnt, bce_cnt;
  u64 bva_cnt, walk_cnt_stat, fwd_sub_cnt, fwd_str_cnt;
  u64 ant_sz, res_sz;
} FullHdr;

extern u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim);
extern u64 full_cong_find_units_equivs(FullHdr *h);
extern u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim);
extern u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap, u64 tick_lim);
extern u64 full_cong_worklist(FullHdr *h, u64 g_len, u64 ctrl_off, u64 tick_lim);
extern u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim);

extern u64 full_lucky_late_m7(FullHdr *h);
extern u64 full_propagate(FullHdr *h);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern void full_switch_mode_m7(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern u64 full_reorder_m6(FullHdr *h, u64 budget);
extern void full_rephase(FullHdr *h);
extern u64 full_simplify_m6(FullHdr *h, bool do_probe, bool do_elim);
extern u64 full_decide_m7(FullHdr *h);

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  h->ant_sz = 0ULL;
  if (full_cong_extract_binaries(h, tick_lim) == 20ULL) { h->ant_sz = 0ULL; return 20ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  if (full_cong_find_units_equivs(h) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  u64 ht_sz = 64ULL;
  while (ht_sz * 8ULL <= h->scratch_cap && ht_sz < 131072ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 occ_bkt = (ht_off >= 16384ULL) ? 512ULL : ((ht_off >= 2048ULL) ? 256ULL :
    ((ht_off >= 256ULL) ? 32ULL : 16ULL));
  u64 bkt_off = ht_off - occ_bkt;
  u64 inq_off = bkt_off - occ_bkt;
  u64 q_off = inq_off - occ_bkt;
  u64 ctrl_off = q_off - 8ULL;
  u64 g_cap = (ctrl_off * 3ULL) >> 2;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = full_cong_extract(h, g_cap, tick_lim);
  if (g_len <= g_cap) {
    g_len = (u64)full_cong_extract_ite_all_m7(h, (u32)g_len, (u32)g_cap, tick_lim);
  }
  if (g_len > 0ULL && g_len <= ctrl_off) {
    i = 0ULL;
    while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    h->res_sz = 0ULL;
    scr[ctrl_off] = (u32)occ_bkt; scr[ctrl_off + 1ULL] = (u32)bkt_off;
    scr[ctrl_off + 2ULL] = (u32)inq_off; scr[ctrl_off + 3ULL] = (u32)q_off;
    scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
    scr[ctrl_off + 6ULL] = (u32)ht_off; scr[ctrl_off + 7ULL] = (u32)ht_sz;
    if (full_cong_worklist(h, g_len, ctrl_off, tick_lim) == 20ULL) {
      i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
      h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
    }
  }
  if (full_cong_fwd_subsume(h, tick_lim) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL; h->ant_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_search_m6(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  u64 lkr = full_lucky_late_m7(h);
  if (lkr == 10ULL || lkr == 20ULL) { return lkr; }
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
      bool mode_due = (h->stable == 0ULL)
        ? (h->conflicts >= h->mode_confl_lim)
        : (h->search_ticks >= h->mode_tick_lim);
      if (h->conflicts >= h->reduce_limit) {
        u64 rr = full_reduce_m6(h, false);
        if (rr == 20ULL) { return 20ULL; }
        if (rr != 1ULL) { return 0ULL; }
      } else if (mode_due) {
        full_switch_mode_m7(h);
      } else if (full_restart_due(h) != 0ULL) {
        full_restart(h);
      } else if (h->stable == 0ULL && h->conflicts >= reorder_limit) {
        reorder_limit = h->conflicts + 10000ULL;
        full_reorder_m6(h, 256ULL);
      } else if (h->conflicts >= h->rephase_limit) {
        full_rephase(h);
      } else if (h->conflicts >= h->probe_limit) {
        u64 sr = full_simplify_m6(h, true, false);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      } else if (h->conflicts >= h->elim_limit) {
        u64 sr = full_simplify_m6(h, false, true);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      }
    } else {
      if (h->unassigned == 0ULL) { return 10ULL; }
      if (full_decide_m7(h) == 0ULL) { return (h->unassigned == 0ULL) ? 10ULL : 0ULL; }
    }
  }
}
"

/-! ## 2. Canonical Rename `Fn` Handles -/

def m7Log10Q16CanonFn : Fn :=
  ⟨"full_log10_q16_m7", [i64], [i64], FullM7Search.full_log10_q16_m7_body⟩

def m7ScaleDeltaM5Fn : Fn :=
  ⟨"full_scale_delta_m5", [i64, i64], [i64], FullM7Bump.full_scale_delta_m7_body⟩

def m7WarmupCanonFn : Fn :=
  ⟨"full_warmup", [i64], [], FullM7Walk.full_warmup_m7_body⟩

def m7WalkCanonFn : Fn :=
  ⟨"full_walk", [i64], [], FullM7Walk.full_walk_warmup_m7_body⟩

def m7CongruenceDenseFn : Fn :=
  ⟨"full_congruence_dense", [i64, i64], [i64], full_congruence_dense_body⟩

def m7ForwardSubCanonFn : Fn :=
  ⟨"full_forward_sub", [i64, i64], [i64], FullM7BveGates.full_forward_sub_m7_body⟩

def m7BveCollectCanonFn : Fn :=
  ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], FullM7BveGates.full_bve_collect_m7_body⟩

def m7BveVarCanonFn : Fn :=
  ⟨"full_bve_var", [i64, i32], [i64], FullM7BveGates.full_bve_var_m7_body⟩

def m7EliminateM6Fn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], FullM7BveGates.full_eliminate_m7_body⟩

def m7SearchM6Fn : Fn :=
  ⟨"full_search_m6", [i64], [i64], full_search_m6_body⟩

/-! ## 3. Spliced `M7` (`M6.2_winning`) Function List -/

/-- Part 1: `Dimacs` through `full_reduce_m6`, with `FullM7Bump` and `FullM7BcpHot`. -/
def m7FnsPart1 : List Fn :=
  FullM5.m5Fns.take 10 ++
  [ FullM7Bump.m7RngNextFn ] ++
  (FullM5.m5Fns.drop 11).take 3 ++
  FullM6WatchGc.m6WatchGc_fns.take 3 ++
  [ FullM6Orch.m6oWstackDefragFn, FullM6Orch.m6oWatchPushFn ] ++
  (FullM5.m5Fns.drop 16).take 4 ++
  FullM6WalkParse.m6WalkParse_fns.take 1 ++
  [ FullM6Orch.m6oRescaleFn ] ++
  (FullM5.m5Fns.drop 21).take 6 ++
  [ m7Log10Q16CanonFn, m7ScaleDeltaM5Fn ] ++
  (FullM5.m5Fns.drop 28).take 1 ++
  [ FullM7Bump.m7ScaleDeltaFn ] ++
  (FullM5.m5Fns.drop 29).take 17 ++
  FullM6Hdr.m6Hdr_fns.take 24 ++
  (FullM5.m5Fns.drop 46).take 2 ++
  (FullM5.m5Fns.drop 49).take 3 ++
  FullM7BcpHot.m7BcpHot_fns ++
  [ FullM7BcpHot.m7PropIgnoreFn, FullM7BcpHot.m7PropFn ] ++
  (FullM6WalkParse.m6WalkParse_fns.drop 1).take 1 ++
  [ FullM6Orch.m6oParseBodyFn ] ++
  (FullM5.m5Fns.drop 57).take 1 ++
  (FullM6WatchGc.m6WatchGc_fns.drop 3).take 2 ++
  (FullM6WatchGc.m6WatchGc_fns.drop 6).take 2 ++
  [ FullM6Orch.m6oLitRankFn ] ++
  (FullM6CompactFlush.m6CompactFlush_fns.drop 1).take 1 ++
  [ FullM6Orch.m6oSweepBinsFn ] ++
  (FullM5.m5Fns.drop 64).take 1 ++
  [ FullM6Orch.m6oRewatchArenaFn ] ++
  (FullM6WatchGc.m6WatchGc_fns.drop 8).take 5 ++
  [ FullM6Orch.m6oArenaSweepFn, FullM6Orch.m6oMarkReasonsFn ] ++
  FullM6CompactFlush.m6CompactFlush_fns.take 1 ++
  (FullM5.m5Fns.drop 59).take 3 ++
  [ FullM6.m6CanonicalReduceFn, FullM6Orch.m6oReduceM6Fn ]

/-- Part 2: analysis, `FullM7AnalyzeSort`, `FullM7Bump`, `FullM7Walk`, viv/bb,
`FullM7CongHash`, `FullM7CongIte`, and upgraded `full_congruence_dense`. -/
def m7FnsPart2 : List Fn :=
  (FullM5.m5Fns.drop 69).take 2 ++
  [ FullM6Orch.m6oAnalyzeRsnM6HdrFn ] ++
  (FullM5.m5Fns.drop 71).take 1 ++
  (FullM6MinShrink.m6MinShrink_fns.drop 4).take 2 ++
  [ FullM6OrchAdapters.m6aBumpAnalyzedM6HdrFn
  , FullM6OrchAdapters.m6aRestoreBumpAnaM6HdrFn
  , FullM6OrchAdapters.m6aAnaFailedLitM6HdrFn ] ++
  (FullM5.m5Fns.drop 74).take 1 ++
  [ FullM6.m6CanonicalOtfsBinFn ] ++
  (FullM5.m5Fns.drop 76).take 2 ++
  (FullM5.m5Fns.drop 79).take 1 ++
  [ FullM7AnalyzeSort.m7SortTmpSiftFn ] ++
  FullM7AnalyzeSort.m7AnalyzeSort_fns.take 1 ++
  [ FullM7AnalyzeSort.m7SortTmpHeapFn
  , FullM7AnalyzeSort.m7SortTmpFn ] ++
  (FullM6MinShrink.m6MinShrink_fns.drop 8).take 7 ++
  [ FullM6Orch.m6oMinShrinkFn
  , FullM6Orch.m6oDeduce1uipFn
  , FullM6Orch.m6oDeduce1uipM6HdrFn ] ++
  (FullM5.m5Fns.drop 85).take 2 ++
  (FullM5.m5Fns.drop 88).take 2 ++
  (FullM7Bump.m7BumpFns.drop 3).take 3 ++
  [ FullM7Bump.m7BumpAnalyzedFn ] ++
  (FullM5.m5Fns.drop 73).take 1 ++
  (FullM5.m5Fns.drop 90).take 1 ++
  [ FullM6Orch.m6oAnalyzeCoreM6Fn, FullM6OrchAdapters.m6aAnalyzeM6HdrFn ] ++
  (FullM5.m5Fns.drop 91).take 1 ++
  (FullM6Hdr.m6Hdr_fns.drop 24).take 1 ++
  FullM7Walk.m7WalkFns ++
  [ m7WarmupCanonFn, m7WalkCanonFn, FullM7AnalyzeSort.m7RephaseFn ] ++
  (FullM5.m5Fns.drop 100).take 2 ++
  [ FullM6CompactFlush.m6cfExtendPush2Fn, FullM6CompactFlush.m6cfExtendPushClFn ] ++
  (FullM5.m5Fns.drop 104).take 3 ++
  FullM6VivBackbone.m6VivBackbone_fns.take 1 ++
  [ FullM6OrchAdapters.m6aAddBinFn ] ++
  (FullM5.m5Fns.drop 108).take 10 ++
  [ FullM6.m6CanonicalProbeAssumePairFn ] ++
  (FullM5.m5Fns.drop 119).take 1 ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 26 ++
  [ FullM6OrchAdapters.m6aVivifyTierM6HdrFn, FullM6OrchAdapters.m6aVivifyM6HdrFn ] ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 29).take 11 ++
  (FullM5.m5Fns.drop 139).take 1 ++
  FullM6CongSubst.m6CongSubst_fns.take 1 ++
  (FullM5.m5Fns.drop 141).take 1 ++
  (FullM6CongSubst.m6CongSubst_fns.drop 1).take 3 ++
  [ FullM6CompactFlush.m6cfEnterDenseFn ] ++
  (FullM5.m5Fns.drop 146).take 1 ++
  (FullM5.m5Fns.drop 162).take 1 ++
  (FullM6CongSubst.m6CongSubst_fns.drop 4).take 1 ++
  (FullM5.m5Fns.drop 170).take 3 ++
  (FullM5.m5Fns.drop 164).take 1 ++
  [ FullM7AnalyzeSort.m7SortU32Fn ] ++
  (FullM6CongSubst.m6CongSubst_fns.drop 5).take 17 ++
  FullM7CongHash.m7CongHashFns ++
  FullM7CongIte.m7CongIteFns ++
  [ m7CongruenceDenseFn ]

/-- Part 3: M5 sweep (no `FullM6Sweep`), `FullM7BveGates`, `FullM7BvaFactor`, compact, reorder,
`FullM7Search`, and top-level M7 search loop + solver entrypoints. -/
def m7FnsPart3 : List Fn :=
  (FullM5.m5Fns.drop 178).take 23 ++
  [ FullM6Orch.m6oSweepDenseM6Fn ] ++
  (FullM5.m5Fns.drop 201).take 1 ++
  FullM7BveGates.m7BveGates_fns.take 10 ++
  [ m7ForwardSubCanonFn, m7BveCollectCanonFn ] ++
  (FullM7BveGates.m7BveGates_fns.drop 10).take 20 ++
  (FullM5.m5Fns.drop 213).take 5 ++
  (FullM7BveGates.m7BveGates_fns.drop 30).take 1 ++
  [ m7BveVarCanonFn
  , FullM7BvaFactor.m7InitFreshVarFn ] ++
  (FullM5.m5Fns.drop 220).take 5 ++
  FullM6BvaNoHops.m6BvaNoHopsFns ++
  (FullM5.m5Fns.drop 226).take 2 ++
  [ FullM7BvaFactor.m7BvaTryLitFn ] ++
  (FullM5.m5Fns.drop 229).take 2 ++
  [ FullM7BvaFactor.m7FactorFn ] ++
  [ FullM6CompactFlush.m6cfCompactNeededFn
  , FullM6CompactFlush.m6cfCompactFlushFn
  , FullM6CompactFlush.m6cfCompactMarkLiveFn ] ++
  (FullM5.m5Fns.drop 235).take 10 ++
  FullM7Reorder.m7ReorderFns ++
  [ FullM6Orch.m6oReorderM6Fn ] ++
  (FullM5.m5Fns.drop 248).take 6 ++
  [ FullM6.m6CanonicalElimDticksFn ] ++
  FullM7BveGates.m7BveGates_fns.drop 31 ++
  [ m7EliminateM6Fn ] ++
  FullM7Search.m7Search_fns.take 4 ++
  FullM7Search.m7Search_fns.drop 5 ++
  [ FullM6OrchAdapters.m6aProbeDticksM6HdrFn
  , FullM6Orch.m6oProbeTailM6Fn
  , FullM6Orch.m6oProbeM6Fn
  , FullM6Orch.m6oPreprocessM6Fn
  , FullM6Orch.m6oSimplifyM6Fn
  , m7SearchM6Fn
  , FullM6Orch.m6oSolveBytesM6Fn
  , FullM6Orch.m6oPreprocessFn
  , FullM6Orch.m6oSearchFn
  , FullM6Orch.m6oSolveBytesFn ]

/-- Unified `M7` (`M6.2_winning`) solver function list in strict topological order. -/
def m7Fns : List Fn :=
  m7FnsPart1 ++ m7FnsPart2 ++ m7FnsPart3

/-- Closed unified `M7` (`M6.2_winning`) solver module (`externs := []`, `exits := []`). -/
def m7Module : LeanQbe.T.Module :=
  { fns := m7Fns, externs := [], exits := [] }

/-! ## 4. Well-Formedness, Length & Acyclicity Proofs -/

private theorem wf_one {f : Fn} (h : f.Wf) : ∀ g ∈ [f], g.Wf := by
  intro g hg
  rcases List.mem_singleton.mp hg with rfl
  exact h

private theorem wf_cons {f : Fn} {l : List Fn} (hf : f.Wf) (hl : ∀ g ∈ l, g.Wf) :
    ∀ g ∈ f :: l, g.Wf := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hl g hg

private theorem wf_app {l₁ l₂ : List Fn} (h₁ : ∀ f ∈ l₁, f.Wf) (h₂ : ∀ f ∈ l₂, f.Wf) :
    ∀ f ∈ l₁ ++ l₂, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h₁ f hf
  · exact h₂ f hf

private theorem wf_take {l : List Fn} (n : Nat) (hl : ∀ f ∈ l, f.Wf) :
    ∀ f ∈ l.take n, f.Wf := fun f hf => hl f (List.mem_of_mem_take hf)

private theorem wf_drop {l : List Fn} (n : Nat) (hl : ∀ f ∈ l, f.Wf) :
    ∀ f ∈ l.drop n, f.Wf := fun f hf => hl f (List.mem_of_mem_drop hf)

private theorem m7Log10Q16Canon_wf : m7Log10Q16CanonFn.Wf :=
  FullM7Search.full_log10_q16_m7_wf

private theorem m7ScaleDeltaM5_wf : m7ScaleDeltaM5Fn.Wf :=
  FullM7Bump.full_scale_delta_m7_wf

private theorem m7WarmupCanon_wf : m7WarmupCanonFn.Wf :=
  FullM7Walk.full_warmup_m7_wf

private theorem m7WalkCanon_wf : m7WalkCanonFn.Wf :=
  FullM7Walk.full_walk_warmup_m7_wf

private theorem m7CongruenceDense_wf : m7CongruenceDenseFn.Wf := by
  dsimp [m7CongruenceDenseFn]
  t_wf_reify

private theorem m7ForwardSubCanon_wf : m7ForwardSubCanonFn.Wf :=
  FullM7BveGates.full_forward_sub_m7_wf

private theorem m7BveCollectCanon_wf : m7BveCollectCanonFn.Wf :=
  FullM7BveGates.full_bve_collect_m7_wf

private theorem m7BveVarCanon_wf : m7BveVarCanonFn.Wf :=
  FullM7BveGates.full_bve_var_m7_wf

private theorem m7EliminateM6_wf : m7EliminateM6Fn.Wf :=
  FullM7BveGates.full_eliminate_m7_wf

private theorem m7SearchM6_wf : m7SearchM6Fn.Wf := by
  dsimp [m7SearchM6Fn]
  t_wf_reify

private theorem m7FnsPart1_wf : ∀ f ∈ m7FnsPart1, f.Wf := by
  unfold m7FnsPart1
  repeat' (first
    | exact FullM7BcpHot.m7BcpHot_fns_wf
    | apply wf_app)
  · exact wf_take _ FullM5.m5Fns_wf
  · exact wf_one FullM7Bump.m7RngNextFn_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6WatchGc.m6WatchGc_fns_wf
  · exact wf_cons FullM6Orch.full_wstack_defrag_wf (wf_one FullM6Orch.full_watch_push_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6WalkParse.m6WalkParse_fns_wf
  · exact wf_one FullM6Orch.full_rescale_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons m7Log10Q16Canon_wf (wf_one m7ScaleDeltaM5_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM7Bump.m7ScaleDeltaFn_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6Hdr.m6Hdr_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM7BcpHot.full_propagate_ignore_hot_wf
      (wf_one FullM7BcpHot.full_propagate_canon_wf)
  · exact wf_take _ (wf_drop _ FullM6WalkParse.m6WalkParse_fns_wf)
  · exact wf_one FullM6Orch.full_parse_body_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6WatchGc.m6WatchGc_fns_wf)
  · exact wf_take _ (wf_drop _ FullM6WatchGc.m6WatchGc_fns_wf)
  · exact wf_one FullM6Orch.full_lit_rank_wf
  · exact wf_take _ (wf_drop _ FullM6CompactFlush.m6CompactFlush_fns_wf)
  · exact wf_one FullM6Orch.full_sweep_bins_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_rewatch_arena_wf
  · exact wf_take _ (wf_drop _ FullM6WatchGc.m6WatchGc_fns_wf)
  · exact wf_cons FullM6Orch.full_arena_sweep_wf (wf_one FullM6Orch.full_mark_reasons_wf)
  · exact wf_take _ FullM6CompactFlush.m6CompactFlush_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM5Orch.full_reduce_m5_wf (wf_one FullM6Orch.full_reduce_m6_wf)

private theorem m7FnsPart2_wf : ∀ f ∈ m7FnsPart2, f.Wf := by
  unfold m7FnsPart2
  repeat' (first
    | exact FullM7Walk.m7WalkFns_wf
    | exact FullM7CongHash.m7CongHashFns_wf
    | exact FullM7CongIte.m7CongIteFns_wf
    | apply wf_app)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_analyze_rsn_m6_hdr_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6MinShrink.m6MinShrink_fns_wf)
  · exact wf_cons FullM6OrchAdapters.full_bump_analyzed_m6_hdr_wf
      (wf_cons FullM6OrchAdapters.full_restore_bump_ana_m6_hdr_wf
        (wf_one FullM6OrchAdapters.full_ana_failed_lit_m6_hdr_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM5Otfs.full_otfs_bin_m5_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM7AnalyzeSort.full_sort_tmp_sift_m7_wf
  · exact wf_take _ FullM7AnalyzeSort.m7AnalyzeSort_fns_wf
  · exact wf_cons FullM7AnalyzeSort.full_sort_tmp_heap_m7_wf
      (wf_one FullM7AnalyzeSort.full_sort_tmp_m7_wf)
  · exact wf_take _ (wf_drop _ FullM6MinShrink.m6MinShrink_fns_wf)
  · exact wf_cons FullM6Orch.full_min_shrink_wf
      (wf_cons FullM6Orch.full_deduce_1uip_wf (wf_one FullM6Orch.full_deduce_1uip_m6_hdr_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM7Bump.m7BumpFns_wf)
  · exact wf_one FullM7Bump.m7BumpAnalyzedFn_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM6Orch.full_analyze_core_m6_wf
      (wf_one FullM6OrchAdapters.full_analyze_m6_hdr_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6Hdr.m6Hdr_fns_wf)
  · exact wf_cons m7WarmupCanon_wf
      (wf_cons m7WalkCanon_wf (wf_one FullM7AnalyzeSort.full_rephase_m7_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM6CompactFlush.full_extend_push2_m6cf_wf
      (wf_one FullM6CompactFlush.full_extend_push_cl_m6cf_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6VivBackbone.m6VivBackbone_fns_wf
  · exact wf_one FullM6OrchAdapters.full_add_bin_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6VivBackbone.full_probe_assume_pair_m6_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6VivBackbone.m6VivBackbone_fns_wf)
  · exact wf_cons FullM6OrchAdapters.full_vivify_tier_m6_hdr_wf
      (wf_one FullM6OrchAdapters.full_vivify_m6_hdr_wf)
  · exact wf_take _ (wf_drop _ FullM6VivBackbone.m6VivBackbone_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6CongSubst.m6CongSubst_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6CongSubst.m6CongSubst_fns_wf)
  · exact wf_one FullM6CompactFlush.full_enter_dense_m6cf_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6CongSubst.m6CongSubst_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM7AnalyzeSort.full_sort_u32_m7_wf
  · exact wf_take _ (wf_drop _ FullM6CongSubst.m6CongSubst_fns_wf)
  · exact wf_one m7CongruenceDense_wf

private theorem m7FnsPart3_wf : ∀ f ∈ m7FnsPart3, f.Wf := by
  unfold m7FnsPart3
  repeat' (first
    | exact FullM6BvaNoHops.m6BvaNoHopsFns_wf
    | exact FullM7Reorder.m7ReorderFns_wf
    | apply wf_app)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_sweep_dense_m6_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM7BveGates.m7BveGates_fns_wf
  · exact wf_cons m7ForwardSubCanon_wf (wf_one m7BveCollectCanon_wf)
  · exact wf_take _ (wf_drop _ FullM7BveGates.m7BveGates_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM7BveGates.m7BveGates_fns_wf)
  · exact wf_cons m7BveVarCanon_wf (wf_one FullM7BvaFactor.m7InitFreshVarFn_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM7BvaFactor.m7BvaTryLitFn_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM7BvaFactor.m7FactorFn_wf
  · exact wf_cons FullM6CompactFlush.full_compact_needed_m6cf_wf
      (wf_cons FullM6CompactFlush.full_compact_flush_m6cf_wf
        (wf_one FullM6CompactFlush.full_compact_mark_live_m6cf_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_reorder_m6_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM5Orch.full_elim_dticks_m5_wf
  · exact wf_drop _ FullM7BveGates.m7BveGates_fns_wf
  · exact wf_one m7EliminateM6_wf
  · exact wf_take _ FullM7Search.m7Search_fns_wf
  · exact wf_drop _ FullM7Search.m7Search_fns_wf
  · exact wf_cons FullM6OrchAdapters.full_probe_dticks_m6_hdr_wf
      (wf_cons FullM6Orch.full_probe_tail_m6_wf
        (wf_cons FullM6Orch.full_probe_m6_wf
          (wf_cons FullM6Orch.full_preprocess_m6_wf
            (wf_cons FullM6Orch.full_simplify_m6_wf
              (wf_cons m7SearchM6_wf
                (wf_cons FullM6Orch.kissat_solve_bytes_m6_wf
                  (wf_cons FullM6Orch.full_preprocess_wf
                    (wf_cons FullM6Orch.full_search_wf
                      (wf_one FullM6Orch.kissat_solve_bytes_wf)))))))))

theorem m7Fns_wf : ∀ f ∈ m7Fns, f.Wf :=
  wf_app (wf_app m7FnsPart1_wf m7FnsPart2_wf) m7FnsPart3_wf

theorem m7Fns_length : m7Fns.length = 410 := by
  t_kernel_rfl

theorem m7_acyclic : m7Module.checkAcyclic = true := by
  t_kernel_rfl

/-! ## 5. Compile-Time `#guard` Verification (Boundary, PrintCpp, PrintQbe, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

mutual
  private def exprCalls {rs : List Ty} :
      Expr (fun _ => Unit) (fun _ => Unit) rs → List Sym
    | .let_ _ k => exprCalls (k (Tup.units _))
    | .load _ _ k => exprCalls (k ())
    | .store _ _ k => exprCalls k
    | .call f _ k => f :: exprCalls (k (Tup.units _))
    | .jnz _ t e => exprCalls t ++ exprCalls e
    | .jump _ _ => []
    | .ret _ => []
    | .exit f _ => [f]
    | .hlt => []
    | .group bodies k =>
        blocksCalls (bodies (Tup.units _)) ++ exprCalls (k (Tup.units _))

  private def blocksCalls {rs : List Ty} :
      {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → List Sym
    | [], .nil => []
    | _ :: _, .cons b bs => exprCalls (b (Tup.units _)) ++ blocksCalls bs
end

private def fnCalls (fn : Fn) : List Sym :=
  (exprCalls (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))).eraseDups

private def m6HdrSet : List Sym :=
  (FullM6Hdr.m6Hdr_fns.take 24).map Fn.name ++
  [ "full_reduce_m6", "full_analyze_rsn_m6_hdr", "full_bump_analyzed_m6_hdr"
  , "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr"
  , "full_deduce_1uip_m6_hdr", "full_analyze_core_m6", "full_analyze_m6_hdr"
  , "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr", "full_probe_dticks_m6_hdr"
  , "full_probe_tail_m6", "full_probe_m6", "full_preprocess_m6"
  , "full_simplify_m6", "full_search_m6", "kissat_solve_bytes_m6"
  , "full_preprocess", "full_search", "kissat_solve_bytes" ]

private def fullMemRoots : List Sym :=
  [ "full_init_state", "full_recompute_tiers", "full_reduce", "full_elim_dticks"
  , "full_analyze_rsn", "full_analyze", "full_min_shrink", "full_deduce_1uip"
  , "full_eliminate_m6", "full_eliminate_m7", "full_extend", "kissat_check_model"
  , "full_lucky", "full_compact" ]

private def fullMemReach : List Sym :=
  m7Fns.reverse.foldl (fun acc fn =>
    if acc.contains fn.name then (fnCalls fn ++ acc).eraseDups else acc) fullMemRoots

#guard (m7Fns.map Fn.name).eraseDups.length == m7Fns.length
#guard m7Module.checkAcyclic
#guard !(fullMemReach.any m6HdrSet.contains)

#guard (ppTModule m7Module).isOk
#guard (PrintQbe.module m7Module).isOk
#guard (ppModule (m7Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7Fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7Fns.map (Fn.legal .x64AVX2))).isOk
#guard m7Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullM7

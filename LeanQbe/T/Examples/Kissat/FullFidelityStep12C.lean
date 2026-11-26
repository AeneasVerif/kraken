/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullM7V2Robust
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 12 Bundle C (`FullFidelityStep12C`)

Purely additive C0 layer (`0` edits to existing `Full*` or `FidelityHub.lean`, `0` `*Proof*`
imports, every function `<= 6` args for SysV x64 & Arm64 ABI) fixing two disjoint Stage-3
P1 items atop `fidStep10Module`:

1. **`P1-4a` — Stage-3 Long-Horizon OOM Recovery (`full_learn_clause_m6` + `FullM7V2Robust`):**
   - Wires the `FullM7V2Robust` atomic `full_add_clause` / `full_sweep_copy` rollback
     (`full_watch_pop_c0`) and 3-step OOM retry ladder (`full_wstack_defrag`,
     `full_reduce_m6(h, true)`, `full_reduce_purge_c0(h)`) into `full_learn_clause_m6`,
     preventing premature `UNKNOWN` (`0ULL`) aborts when `tier1`/`tier2` fills the arena on
     `1M+`-conflict Stage-3 runs while preserving `M6HdrExt` tiers on steps `0..1`.
2. **`P1-9b` — $O(K \log K)$ `full_viv_sort_counts_m6` (`full_viv_sift_counts_m6`):**
   - Replaces the $O(K^2)$ insertion sort on `tmp_lits[0 ..< sz)` in `full_viv_sort_counts_m6`
     with in-place $O(K \log K)$ heapsort via `full_viv_sift_counts_m6`, preserving exact
     descending-count, ascending-literal-ID tie-break order on clauses up to `28,542` lits.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12C

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7V2Robust

@[expose] public section

kissat_c0! fidStep12C "
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

#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_det_new_level(FullHdr *h, u64 jump);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern u64 full_reduce_purge_c0(FullHdr *h);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern void full_eager_subsume(FullHdr *h, u64 new_ref);

u64 full_learn_clause_m6(FullHdr *h, u64 glue) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  i8 *vals = (i8 *)h->values;
  u32 uip_lit = tmp[0];
  if (h->tmp_len == 1ULL) {
    full_backtrack(h, 0ULL);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    full_assign_lvl(h, uip_lit, 0xFFFFFFFFu, 0u);
    return 1ULL;
  }
  u64 tlen = h->tmp_len;
  if (tlen > 2ULL) {
    u64 lo = 1ULL;
    u64 hi = tlen - 1ULL;
    while (lo < hi) {
      u32 sw = tmp[lo]; tmp[lo] = tmp[hi]; tmp[hi] = sw;
      lo = lo + 1ULL;
      hi = hi - 1ULL;
    }
    u64 rb = 1ULL;
    while (rb < tlen) {
      u32 rl = lvl[((u64)tmp[rb]) >> 1];
      u64 re = rb + 1ULL;
      while (re < tlen && lvl[((u64)tmp[re]) >> 1] == rl) {
        re = re + 1ULL;
      }
      u64 rl_i = rb;
      u64 rh_i = re - 1ULL;
      while (rl_i < rh_i) {
        u32 sw = tmp[rl_i]; tmp[rl_i] = tmp[rh_i]; tmp[rh_i] = sw;
        rl_i = rl_i + 1ULL;
        rh_i = rh_i - 1ULL;
      }
      rb = re;
    }
  }
  u64 i = 2ULL;
  while (i < tlen) {
    u32 x = tmp[i];
    u32 lx = lvl[((u64)x) >> 1];
    u64 j = i;
    while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] < lx) {
      tmp[j] = tmp[j - 1ULL];
      j = j - 1ULL;
    }
    tmp[j] = x;
    i = i + 1ULL;
  }
  u64 max_lvl = (u64)lvl[((u64)tmp[1]) >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce_m6(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  u64 step = 0ULL;
  while (new_ref == 0xFFFFFFFFULL && step < 3ULL) {
    if (step == 0ULL) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    } else {
      u64 gr = (step == 1ULL) ? full_reduce_m6(h, true) : full_reduce_purge_c0(h);
      if (gr == 20ULL) { return 20ULL; }
      if (gr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
    new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
    step = step + 1ULL;
  }
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}

void full_viv_sift_counts_m6(FullHdr *h, u64 start, u64 n) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 r = start;
  while ((r << 1) + 1ULL < n) {
    u64 c1 = (r << 1) + 1ULL;
    u64 worst = c1;
    u32 wlit = tmp[c1];
    u32 wc = cnt[wlit];
    u64 c2 = c1 + 1ULL;
    if (c2 < n) {
      u32 lit2 = tmp[c2];
      u32 c2_val = cnt[lit2];
      if (c2_val < wc || (c2_val == wc && lit2 > wlit)) {
        worst = c2;
        wlit = lit2;
        wc = c2_val;
      }
    }
    u32 rlit = tmp[r];
    u32 rc = cnt[rlit];
    if (wc < rc || (wc == rc && wlit > rlit)) {
      tmp[r] = wlit;
      tmp[worst] = rlit;
      r = worst;
    } else {
      return;
    }
  }
}

void full_viv_sort_counts_m6(FullHdr *h, u32 sz) {
  if (sz <= 1u) { return; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 n = (u64)sz;
  u64 i = n >> 1;
  while (i > 0ULL) {
    i = i - 1ULL;
    full_viv_sift_counts_m6(h, i, n);
  }
  u64 m = n;
  while (m > 1ULL) {
    m = m - 1ULL;
    u32 top = tmp[0];
    tmp[0] = tmp[m];
    tmp[m] = top;
    full_viv_sift_counts_m6(h, 0ULL, m);
  }
}
"

/-! ## 1. Canonical `Fn` Handles -/

def fidStep12CWatchPopFn : Fn := v2rWatchPopFn
def fidStep12CAddClauseFn : Fn := v2rAddClauseFn
def fidStep12CSweepCopyFn : Fn := v2rSweepCopyFn
def fidStep12CReducePurgeFn : Fn := v2rReducePurgeFn

def fidStep12CLearnClauseM6Fn : Fn :=
  ⟨"full_learn_clause_m6", [i64, i64], [i64], full_learn_clause_m6_body⟩

def fidStep12CVivSiftCountsM6Fn : Fn :=
  ⟨"full_viv_sift_counts_m6", [i64, i64, i64], [], full_viv_sift_counts_m6_body⟩

def fidStep12CVivSortCountsM6Fn : Fn :=
  ⟨"full_viv_sort_counts_m6", [i64, i32], [], full_viv_sort_counts_m6_body⟩

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_watch_pop_c0_step12c_wf : Func.Wf fidStep12CWatchPopFn.body :=
  full_watch_pop_c0_wf

theorem full_add_clause_step12c_wf : Func.Wf fidStep12CAddClauseFn.body :=
  full_add_clause_wf

theorem full_sweep_copy_step12c_wf : Func.Wf fidStep12CSweepCopyFn.body :=
  full_sweep_copy_wf

theorem full_reduce_purge_c0_step12c_wf : Func.Wf fidStep12CReducePurgeFn.body :=
  full_reduce_purge_c0_wf

theorem full_learn_clause_m6_step12c_wf : Func.Wf fidStep12CLearnClauseM6Fn.body := by
  t_wf_reify

theorem full_viv_sift_counts_m6_step12c_wf : Func.Wf fidStep12CVivSiftCountsM6Fn.body := by
  t_wf_reify

theorem full_viv_sort_counts_m6_step12c_wf : Func.Wf fidStep12CVivSortCountsM6Fn.body := by
  t_wf_reify

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12C

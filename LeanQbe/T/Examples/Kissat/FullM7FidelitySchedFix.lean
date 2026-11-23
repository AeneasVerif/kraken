/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `M7` Upstream 4.0.4 Schedule & Probe Fixes (`FullM7FidelitySchedFix`)

Purely additive Target A (`FullM7Fidelity`) C0 overrides fixing the `4` upstream Kissat 4.0.4
bugs in `FullM7FidelitySched.lean` with `FullM7Splice.patchFns`-ready canonical M7 names:

1. `full_reduce_m6` (`full_reduce_fid2_body`): replaces step-function integer `ilog10` with
   continuous Q16 `full_log10_q16_m7` (`frac = 900 - ((400 << 16) / qlog)`).
2. `full_eliminate_m6` (`full_eliminate_fid2_body`): computes Q16 `NLOG2N`, calls canonical
   `full_forward_sub` + `full_elim_bve_m7`, and drops the non-upstream trailing `full_factor`.
3. `full_probe_tail_m6` (`full_probe_tail_fid2_body`): applies `backboneeffort = 20` (`dticks / 50
   + 65536`), drops obsolete `full_probe_run`, and moves `full_vivify_m6_hdr` into `full_probe_m6`.
4. `full_probe_m6` (`full_probe_fid2_body`): Q16 `NLOGN`, `src/probe.c:33-68` ordering (`vivify`
   at top of non-initial rounds; `rebuild_watches -> substitute -> enter_dense` immediately after
   congruence finds `cong_cnt > cb`), `backboneeffort = 20`, and `factordelay = 4`.
5. `full_preprocess_m6` (`full_preprocess_fid2_body`): deletes the `3` non-upstream `full_eliminate`
   lines (`fastel = 0`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fid_sched_fix "
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

#define PH_GLUE_MASK          0x7FFFFu
#define PH_GARB               0x00080000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL

#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL

extern u64 full_isqrt(u64 x);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_arena_sweep(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_elim_bve_m7(FullHdr *h, u64 budget);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);
extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 kind);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 kind);
extern void m6_hdr_bump_delay(FullHdr *h, u64 kind);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_lucky(FullHdr *h);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);

u64 full_reduce_m6(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + 1000ULL * full_isqrt(h->reductions);
  u64 ret = 1ULL;
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { ret = 20ULL; }
    else if (pr != 0ULL) { ret = 0ULL; }
    else { h->unflushed = 0ULL; }
  }
  if (ret == 1ULL) {
    m6_hdr_recompute_tiers(h);
    full_mark_reasons(h, true);
    u32 *ar = (u32 *)h->arena;
    u32 *rr = (u32 *)h->red_refs;
    u64 rc = 0ULL;
    u64 p = 0ULL;
    u64 t1 = h->tier1;
    u64 t2 = h->tier2;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 n = full_arena_next(h, (u32)p);
      if ((hdr & PH_RED) != 0u && (hdr & PH_GARB) == 0u) {
        u32 old_u = (hdr >> 27) & 31u;
        if (old_u > 0u) { ar[p] = (hdr & 0x07FFFFFFu) | ((old_u - 1u) << 27); }
        if ((hdr & PH_RSN) == 0u) {
          u64 glue = (u64)(hdr & PH_GLUE_MASK);
          bool keep = (glue <= t1 && old_u > 0u) || (glue <= t2 && old_u >= 30u);
          if (!keep && rc < h->red_cap) { rr[rc] = (u32)p; rc = rc + 1ULL; }
        }
      }
      p = (u64)n;
    }
    if (rc > 0ULL) {
      full_sort_reds(h, rc);
      u64 arg = (h->reductions > (~0ULL) - 9ULL) ? (~0ULL) : (h->reductions + 9ULL);
      u64 qlog = full_log10_q16_m7(arg);
      if (qlog < 65536ULL) { qlog = 65536ULL; }
      u64 target = (rc * (900ULL - ((400ULL << 16) / qlog))) / 1000ULL;
      u64 i = 0ULL;
      while (i < target && i < rc) {
        u64 cref = (u64)rr[i];
        u32 hdr = ar[cref];
        if ((hdr & PH_GARB) == 0u) {
          ar[cref] = hdr | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[cref + 2ULL];
        }
        i = i + 1ULL;
      }
    }
    if (force || (h->unflushed == 0ULL &&
        (h->arena_garbage * 4ULL >= h->arena_len ||
         h->arena_len * 5ULL >= h->arena_cap * 4ULL))) {
      while (true) {
        u64 sr = full_arena_sweep(h);
        if (sr == 2ULL) { ret = 20ULL; break; }
        if (sr == 3ULL) { ret = 0ULL; break; }
        if (sr == 0ULL) { break; }
        u64 pr = full_propagate(h);
        if (pr == 1ULL) { ret = 20ULL; break; }
        if (pr != 0ULL) { ret = 0ULL; break; }
        h->unflushed = 0ULL;
      }
    } else {
      full_mark_reasons(h, false);
    }
  }
  m6_hdr_set_watermark(h, M6_WM_REDUCE_CONFL, h->conflicts);
  m6_hdr_set_watermark(h, M6_WM_REDUCE_TICKS, h->search_ticks);
  return ret;
}

u64 full_eliminate_m6(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 arg = (h->eliminations > (~0ULL) - 9ULL) ? (~0ULL) : (h->eliminations + 9ULL);
    u64 qlog = full_log10_q16_m7(arg);
    u64 ec = (h->eliminations > 100000000ULL) ? 100000000ULL : h->eliminations;
    u64 nloge = ((((500ULL * ec) * qlog) >> 16) * qlog) >> 16;
    u64 delta = full_scale_delta(h, nloge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) {
    full_rebuild_watches(h);
    return 20ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = initial ? (cv * 4ULL + 256ULL) : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve_m7(h, bve_lim);
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_tail_m6(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL &&
      full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
    return 20ULL;
  }
  u64 tr_lim = (dticks / 50ULL) + 100000ULL;
  if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
    return 20ULL;
  }
  return 1ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 parg = (h->probings > (~0ULL) - 9ULL) ? (~0ULL) : (h->probings + 9ULL);
    u64 qlog = full_log10_q16_m7(parg);
    u64 pc = (h->probings > 100000000ULL) ? 100000000ULL : h->probings;
    u64 nlogp = (100ULL * pc * qlog) >> 16;
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
  }
  u64 round = 0ULL;
  while (round < 2ULL) {
    if (!initial && full_vivify_m6_hdr(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    u64 before_unass = h->unassigned;
    if (full_enter_dense(h)) {
      u64 dense_ok = 1ULL;
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        if (ca > cb) {
          if (full_rebuild_watches(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (!full_enter_dense(h)) {
            if (h->inconsistent != 0ULL) {
              m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
              return 20ULL;
            }
            dense_ok = 0ULL;
          }
        }
      }
      if (dense_ok != 0ULL) {
        if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
          u64 sb = h->sweep_cnt;
          if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
            full_rebuild_watches(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if ((h->sweep_cnt > sb) && (h->sweep_cnt - sb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
          }
        }
        if (full_rebuild_watches(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
    } else if (h->inconsistent != 0ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->unassigned >= before_unass) { break; }
    round = round + 1ULL;
  }
  if (!initial) {
    if (full_probe_tail_m6(h, dticks) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  }
  u64 fr = 1ULL;
  u64 fp = 10ULL;
  u64 fa = h->unassigned / 10ULL;
  while (fa >= fp && fr < 19ULL) {
    fr = fr + 1ULL;
    fp = fp * 10ULL;
  }
  u64 fe5 = (h->eliminations > (~0ULL) - 5ULL) ? (~0ULL) : (h->eliminations + 5ULL);
  if (fr <= fe5 && full_enter_dense(h)) {
    u64 fbud = full_min_u64(
      initial ? (h->cur_vars * 4ULL + 1024ULL) : (128ULL + (dticks >> 8)),
      8192ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}

u64 full_preprocess_m6(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  u64 lk = full_lucky(h);
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  if (full_probe_m6(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  return 1ULL;
}
"

/-- Canonical external callee signatures referenced by `fidSchedFixFns` (`32` externs). -/
def fidSchedFixExterns : List Extern :=
  [ ⟨"full_isqrt", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], []⟩
  , ⟨"full_mark_reasons", [i64, .bool], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_sort_reds", [i64, i64], []⟩
  , ⟨"full_log10_q16_m7", [i64], [i64]⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_forward_sub", [i64, i64], [i64]⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64]⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64]⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64]⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64]⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], []⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], []⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_lucky", [i64], [i64]⟩
  , ⟨"full_compact_needed", [i64], [.bool]⟩
  , ⟨"full_compact", [i64], [i64]⟩ ]

/-- Body aliases matching `PLAN.md` §4.3 naming (`*_fid2_body`). -/
abbrev full_reduce_fid2_body := full_reduce_m6_body
abbrev full_eliminate_fid2_body := full_eliminate_m6_body
abbrev full_probe_tail_fid2_body := full_probe_tail_m6_body
abbrev full_probe_fid2_body := full_probe_m6_body
abbrev full_preprocess_fid2_body := full_preprocess_m6_body

/-- Canonical M7 `Fn` replacement list (`FullM7Splice.patchFns`-ready). -/
def fidSchedFixFns : List Fn := fid_sched_fix_fns

/-- Drop-in replacement `Fn` handles matching canonical `FullM7.m7Module` slots. -/
def fid2ReduceM6Fn : Fn := ⟨"full_reduce_m6", [i64, .bool], [i64], full_reduce_m6_body⟩
def fid2EliminateM6Fn : Fn := ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m6_body⟩
def fid2ProbeTailM6Fn : Fn := ⟨"full_probe_tail_m6", [i64, i64], [i64], full_probe_tail_m6_body⟩
def fid2ProbeM6Fn : Fn := ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩
def fid2PreprocessM6Fn : Fn := ⟨"full_preprocess_m6", [i64], [i64], full_preprocess_m6_body⟩

/-- `FullM7Splice.patchFns` replacement list and empty helper insertions (`befores := []`). -/
def fidSchedFixPatchFns : List Fn := fidSchedFixFns
def fidSchedFixPatchBefores : List (Sym × List Fn) := []

/-- Closed standalone schedule/probe-fix C0 module (`5` functions + `32` externs, `0` exits). -/
def fidSchedFixModule : LeanQbe.T.Module :=
  { fns := fidSchedFixFns, externs := fidSchedFixExterns, exits := [] }

theorem full_reduce_m6_wf : Func.Wf full_reduce_m6_body := by t_wf_reify
theorem full_eliminate_m6_wf : Func.Wf full_eliminate_m6_body := by t_wf_reify
theorem full_probe_tail_m6_wf : Func.Wf full_probe_tail_m6_body := by t_wf_reify
theorem full_probe_m6_wf : Func.Wf full_probe_m6_body := by t_wf_reify
theorem full_preprocess_m6_wf : Func.Wf full_preprocess_m6_body := by t_wf_reify

theorem full_reduce_fid2_wf : Func.Wf full_reduce_fid2_body := full_reduce_m6_wf
theorem full_eliminate_fid2_wf : Func.Wf full_eliminate_fid2_body := full_eliminate_m6_wf
theorem full_probe_tail_fid2_wf : Func.Wf full_probe_tail_fid2_body := full_probe_tail_m6_wf
theorem full_probe_fid2_wf : Func.Wf full_probe_fid2_body := full_probe_m6_wf
theorem full_preprocess_fid2_wf : Func.Wf full_preprocess_fid2_body := full_preprocess_m6_wf

theorem fidSchedFix_fns_wf : ∀ f ∈ fidSchedFixFns, f.Wf := by
  dsimp only [fidSchedFixFns, fid_sched_fix_fns]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro f (rfl | rfl | rfl | rfl | rfl)
  · exact full_reduce_m6_wf
  · exact full_eliminate_m6_wf
  · exact full_probe_tail_m6_wf
  · exact full_probe_m6_wf
  · exact full_preprocess_m6_wf

theorem fidSchedFix_acyclic : fidSchedFixModule.checkAcyclic = true := by decide

theorem fidSchedFixFns_eq_patchFns :
    fidSchedFixFns =
      [fid2ReduceM6Fn, fid2EliminateM6Fn, fid2ProbeTailM6Fn, fid2ProbeM6Fn,
       fid2PreprocessM6Fn] := by
  rfl

end LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix

end

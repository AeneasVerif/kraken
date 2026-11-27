/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 13 Shard S5-A (`FullFidelityStep13S5ReduceProbe`)

Data-pure Step-13 C0 bodies for Shard S5-A (`8` MOD functions from
`step13_v2_frozen_direct.c`, with coordinator-approved `#3048` Option A scratch `cnt` slice in
`full_sort_reds` and `#3054` `!force &&` guard in `full_reduce_m6`):
- `full_activate_lit_fid` (`L3268-3301`)
- `full_parse_body_m6` (`L4374-4424`)
- `full_sort_reds` (`L5175-5265`)
- `full_reduce_m6` (`L5371-5451`)
- `full_set_inactive` (`L9706-9753`)
- `full_probe_tail_m6` (`L25800-25810`)
- `full_probe_m6` (`L25833-26083`)
- `full_preprocess_m6` (`L26106-26151`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S5ReduceProbe "
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

#define FL_ACTIVE             1u
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u
#define FL_SWEEP              1024u

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL

#define TUM_GU_ACTIVATED      31ULL
#define SWP_GU_SWEPT          32u

extern u64  f64u_inv_u64(u64 k);
extern u64  f64u_sub(u64 a, u64 b);
extern u64  f64u_log10_u64(u64 x);
extern u64  f64u_div(u64 a, u64 b);
extern u64  f64u_to_u64(u64 a);
extern u64  f64u_mul(u64 a, u64 b);
extern u64  f64u_from_u64(u64 x);
extern u64  f64u_nlogpown(u64 count, u64 exponent);

extern void full_heap_push(FullHdr *h, u32 v);
extern bool full_skip_cl(u64 cnf_end, KissatDimacs *d);
extern u64  full_ingest_cl(FullHdr *h, u64 cnf_end);
extern u64  kissat_skip_ws_comments(u64 p, u64 end);
extern void full_tumble_finish_fid(FullHdr *h);
extern void full_wstack_defrag(FullHdr *h);
extern u64  full_propagate(FullHdr *h);
extern void full_red_sift(u32 *ar, u32 *rr, u64 start, u64 n);
extern u64  full_isqrt(u64 x);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_compact_needed(FullHdr *h);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u32  full_arena_next(FullHdr *h, u32 cref);
extern u64  full_arena_sweep(FullHdr *h);
extern u64  full_compact(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64  m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void full_update_classify_fid(FullHdr *h);
extern void full_heap_up(FullHdr *h, u32 v);
extern void full_heap_down(FullHdr *h, u32 v);
extern u64  full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64  full_transitive_m6(FullHdr *h, u64 tick_lim);
extern u64  full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool full_enter_dense(FullHdr *h);
extern u64  full_congruence_dense(FullHdr *h, u64 tick_lim);
extern void full_dense_bin_roundtrip_fid(FullHdr *h);
extern u64  full_rebuild_watches_nosort_fid(FullHdr *h);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64  full_substitute(FullHdr *h);
extern u64  full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern bool full_has_factor_cands_fid(FullHdr *h);
extern bool full_enter_dense_ex_fid(FullHdr *h, bool connect_large);
extern u64  full_factor(FullHdr *h, u64 budget);
extern u64  full_vivify_m6_hdr(FullHdr *h);
extern u64  full_scale_delta_m5(FullHdr *h, u64 delta);
extern u64  full_lucky_late_m7(FullHdr *h);

void full_activate_lit_fid(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *fl = (u32 *)h->flags;
  if ((fl[v] & FL_ACTIVE) != 0u) { return; }
  u32 all_c = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_FACT_P | FL_FACT_N |
              FL_BONE0 | FL_BONE1 | FL_TRANS | FL_SWEEP;
  fl[v] = fl[v] | all_c;
  h->unassigned = h->unassigned + 1ULL;
  u32 *gu = (u32 *)h->glue_used;
  u32 k = gu[TUM_GU_ACTIVATED];
  if (k < 0xFFFFFFFFu) { k = k + 1u; }
  gu[TUM_GU_ACTIVATED] = k;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 old_last = (u32)h->q_last;
  qp[v] = old_last;
  qn[v] = 0xFFFFFFFFu;
  h->q_last = (u64)v;
  if ((u64)old_last >= cv) {
    h->q_first = (u64)v;
  } else {
    qn[old_last] = v;
  }
  h->q_cur_stamp = h->q_cur_stamp + 1ULL;
  qs[v] = (u32)h->q_cur_stamp;
  h->q_search_idx = (u64)v;
  h->q_search_stamp = (u64)qs[v];
  u64 *sc = (u64 *)h->score;
  u64 k64 = (u64)k;
  sc[v] = f64u_sub(0x3FF0000000000000ULL, f64u_inv_u64(k64));
  if (h->stable != 0ULL) { full_heap_push(h, v); }
}

u64 full_parse_body_m6(FullHdr *h, u64 cnf_end) {
  u32 *gu = (u32 *)h->glue_used;
  gu[TUM_GU_ACTIVATED] = 0u;
  if (h->extend_cap > h->d.mv) {
    u32 *fd = (u32 *)h->frame_dec;
    u64 mv = h->d.mv;
    u64 e = 0ULL;
    while (e < mv) {
      fd[e] = 0xFFFFFFFFu;
      e = e + 1ULL;
    }
    h->extend_len = 0ULL;
  }
  bool unsat_seen = false;
  bool oom_seen = false;
  bool has_cl = false;
  u64 i = 0ULL;
  while (i < h->d.nc) {
    if (unsat_seen) {
      if (!full_skip_cl(cnf_end, &h->d)) { return 0ULL; }
    } else if (oom_seen) {
      return 0ULL;
    } else {
      u64 old_te = h->trail_end;
      u64 st = full_ingest_cl(h, cnf_end);
      if (st == 0ULL) { return 0ULL; }
      if (st == 2ULL) { unsat_seen = true; }
      else if (st == 3ULL) { oom_seen = true; }
      else {
        if (h->trail_end == old_te) { has_cl = true; }
        if (has_cl && h->propagated < h->trail_end) {
          u64 saved_fuel = h->fuel;
          u64 saved_ticks = h->search_ticks;
          u64 pr = full_propagate(h);
          h->fuel = saved_fuel;
          h->search_ticks = saved_ticks;
          if (pr == 1ULL) { unsat_seen = true; }
          else if (pr == 2ULL) { h->oom = 0ULL; oom_seen = true; }
        }
      }
    }
    i = i + 1ULL;
  }
  if (oom_seen) { return 0ULL; }
  h->d.cur = kissat_skip_ws_comments(h->d.cur, cnf_end);
  if (h->d.cur != cnf_end) { return 0ULL; }
  full_tumble_finish_fid(h);
  if (unsat_seen) { return 20ULL; }
  full_wstack_defrag(h);
  return 1ULL;
}

void full_sort_reds(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  if (n < 32ULL) {
    u64 i = 1ULL;
    while (i < n) {
      u32 x = rr[i];
      u64 kx = ((u64)(~(ar[x] & PH_GLUE_MASK)) << 32) | (u64)(~ar[(u64)x + 2ULL]);
      u64 j = i;
      while (j > 0ULL) {
        u32 y = rr[j - 1ULL];
        u64 ky = ((u64)(~(ar[y] & PH_GLUE_MASK)) << 32) | (u64)(~ar[(u64)y + 2ULL]);
        if (ky <= kx) { break; }
        rr[j] = y;
        j = j - 1ULL;
      }
      rr[j] = x;
      i = i + 1ULL;
    }
    return;
  }
  if (4ULL * n + 512ULL <= h->scratch_cap) {
    u64 *ranks = (u64 *)h->scratch_buf;
    u32 *idx0 = ((u32 *)h->scratch_buf) + (2ULL * n);
    u32 *idx1 = idx0 + n;
    u64 *cnt = ((u64 *)h->scratch_buf) + (2ULL * n);
    u64 i = 0ULL;
    while (i < n) {
      u32 r = rr[i];
      u32 g = ar[r] & PH_GLUE_MASK;
      u32 sz = ar[(u64)r + 2ULL];
      ranks[i] = ((u64)(0xFFFFFFFFu - g) << 32) | (u64)(0xFFFFFFFFu - sz);
      idx0[i] = (u32)i;
      i = i + 1ULL;
    }
    u32 *src = idx0;
    u32 *dst = idx1;
    u64 shift = 0ULL;
    while (shift < 64ULL) {
      u64 b = 0ULL;
      while (b < 256ULL) { cnt[b] = 0ULL; b = b + 1ULL; }
      u64 lo = 255ULL;
      u64 hi = 0ULL;
      i = 0ULL;
      while (i < n) {
        u64 byte = (ranks[src[i]] >> shift) & 255ULL;
        cnt[byte] = cnt[byte] + 1ULL;
        if (byte < lo) { lo = byte; }
        if (byte > hi) { hi = byte; }
        i = i + 1ULL;
      }
      if (lo != hi) {
        u64 pos = 0ULL;
        b = 0ULL;
        while (b < 256ULL) {
          u64 c = cnt[b];
          cnt[b] = pos;
          pos = pos + c;
          b = b + 1ULL;
        }
        i = 0ULL;
        while (i < n) {
          u32 id = src[i];
          u64 byte = (ranks[id] >> shift) & 255ULL;
          dst[cnt[byte]] = id;
          cnt[byte] = cnt[byte] + 1ULL;
          i = i + 1ULL;
        }
        u32 *t = src; src = dst; dst = t;
      }
      shift = shift + 8ULL;
    }
    u32 *tmp_rr = (src == idx0) ? idx1 : idx0;
    i = 0ULL;
    while (i < n) { tmp_rr[i] = rr[src[i]]; i = i + 1ULL; }
    i = 0ULL;
    while (i < n) { rr[i] = tmp_rr[i]; i = i + 1ULL; }
    return;
  }
  u64 start = n >> 1;
  while (start > 0ULL) { start = start - 1ULL; full_red_sift(ar, rr, start, n); }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = rr[0]; rr[0] = rr[end]; rr[end] = t;
    full_red_sift(ar, rr, 0ULL, end);
    end = end - 1ULL;
  }
}

u64 full_reduce_m6(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + full_isqrt(h->reductions * 1000000ULL);
  u64 ret = 1ULL;
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { ret = 20ULL; }
    else if (pr != 0ULL) { ret = 0ULL; }
    else { h->unflushed = 0ULL; }
  }
  bool do_compact = false;
  if (ret == 1ULL) {
    do_compact = (!force && h->cur_level == 0ULL && full_compact_needed(h));
    m6_hdr_recompute_tiers(h);
    full_mark_reasons(h, true);
    u32 *ar = (u32 *)h->arena;
    u32 *rr = (u32 *)h->red_refs;
    u64 rc = 0ULL;
    u64 alen = h->arena_len;
    u64 p = 0ULL;
    u64 t1 = h->tier1;
    u64 t2 = h->tier2;
    while (p < alen) {
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
      u64 lg = f64u_log10_u64(arg);
      if (lg < 0x3FF0000000000000ULL) { lg = 0x3FF0000000000000ULL; }
      u64 pct = f64u_sub(0x4056800000000000ULL, f64u_div(0x4044000000000000ULL, lg));
      u64 frac = f64u_div(pct, 0x4059000000000000ULL);
      u64 target = f64u_to_u64(f64u_mul(f64u_from_u64(rc), frac));
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
    if (force || do_compact ||
        (h->unflushed == 0ULL && (h->arena_garbage > 0ULL || h->cur_level == 0ULL))) {
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
    if (ret == 1ULL && do_compact) {
      u64 cr = full_compact(h);
      if (cr == 20ULL) { ret = 20ULL; }
      else if (cr != 1ULL) { ret = 0ULL; }
    }
  }
  m6_hdr_set_watermark(h, M6_WM_REDUCE_CONFL, h->conflicts);
  m6_hdr_set_watermark(h, M6_WM_REDUCE_TICKS, h->search_ticks);
  full_update_classify_fid(h);
  return ret;
}

void full_set_inactive(FullHdr *h, u32 v, u32 flag) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  bool was_active = ((fl[v] & FL_ACTIVE) != 0u);
  if (was_active && vals[(u64)v << 1] == (i8)0 && h->unassigned > 0ULL) {
    h->unassigned = h->unassigned - 1ULL;
  }
  fl[v] = (fl[v] & (~FL_ACTIVE)) | flag;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 pv = qp[v];
  u32 nv = qn[v];
  if ((u64)pv < cv || (u64)nv < cv || h->q_first == (u64)v || h->q_last == (u64)v) {
    if (h->q_search_idx == (u64)v) {
      u32 srch = nv;
      if ((u64)srch >= cv) { srch = pv; }
      if ((u64)srch >= cv) {
        h->q_search_idx = 0xFFFFFFFFULL;
        h->q_search_stamp = 0ULL;
      } else {
        h->q_search_idx = (u64)srch;
        h->q_search_stamp = (u64)qs[srch];
      }
    }
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    if ((u64)pv >= cv) { h->q_first = (u64)nv; } else { qn[pv] = nv; }
    if ((u64)nv >= cv) { h->q_last = (u64)pv; } else { qp[nv] = pv; }
  }
  u32 *ps = (u32 *)h->pos;
  u32 *hp = (u32 *)h->heap;
  u64 n__ = h->heap_len;
  u32 p__ = ps[v];
  if (n__ > 0ULL && n__ <= cv && (u64)p__ < n__ && hp[p__] == v) {
    u32 last__ = hp[n__ - 1ULL];
    h->heap_len = n__ - 1ULL;
    ps[v] = 0xFFFFFFFFu;
    if (last__ != v && (u64)last__ < cv) {
      hp[p__] = last__;
      ps[last__] = p__;
      full_heap_up(h, last__);
      full_heap_down(h, last__);
    }
  }
}

u64 full_probe_tail_m6(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL &&
      full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
    return 20ULL;
  }
  u64 tr_lim = dticks / 50ULL;
  if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
    return 20ULL;
  }
  return 1ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  h->probings = h->probings + 1ULL;
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  if (initial) {
    bool subst_at_end = true;
    if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
      if (full_enter_dense(h)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, 0xFFFFFFFFFFFFFFFFULL) == 20ULL) {
          full_dense_bin_roundtrip_fid(h);
          full_rebuild_watches_nosort_fid(h);
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        full_dense_bin_roundtrip_fid(h);
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if (ca > cb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
      h->probing = saved_prob;
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
      if (full_enter_dense(h)) {
        u32 *gu_sw = (u32 *)h->glue_used;
        gu_sw[SWP_GU_SWEPT] = 0u;
        u64 sb = h->sweep_cnt;
        if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 sa = h->sweep_cnt;
        u64 swept = (u64)gu_sw[SWP_GU_SWEPT];
        if (sa > sb && swept > 0ULL && (sa - sb) * 1000ULL >= swept) {
          m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if (sa > sb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (subst_at_end && h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      h->probing = saved_prob;
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    u64 fr = 1ULL; u64 fp = 10ULL; u64 fa = h->unassigned / 10ULL;
    while (fa >= fp && fr < 19ULL) { fr = fr + 1ULL; fp = fp * 10ULL; }
    u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
    if (h->unassigned > 0ULL && fr <= fe4 && full_has_factor_cands_fid(h)) {
      if (full_enter_dense_ex_fid(h, false)) {
        u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
        m6_hdr_set_watermark(h, 1ULL, nfact);
        u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
        full_factor(h, fbud);
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      } else if (h->inconsistent != 0ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
  } else {
    u64 round = 0ULL;
    while (round < 2ULL) {
      u32 *fl_a = (u32 *)h->flags;
      u64 before_act = 0ULL;
      u64 ai = 0ULL;
      while (ai < h->cur_vars) {
        if ((fl_a[ai] & 1u) != 0u) { before_act = before_act + 1ULL; }
        ai = ai + 1ULL;
      }
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        if (full_enter_dense(h)) {
          u64 cb = h->cong_cnt;
          if (full_congruence_dense(h, 0xFFFFFFFFFFFFFFFFULL) == 20ULL) {
            full_dense_bin_roundtrip_fid(h);
            full_rebuild_watches_nosort_fid(h);
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 ca = h->cong_cnt;
          if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
          }
          full_dense_bin_roundtrip_fid(h);
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        } else if (h->inconsistent != 0ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (full_vivify_m6_hdr(h) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
        if (full_enter_dense(h)) {
          u32 *gu_sw = (u32 *)h->glue_used;
          gu_sw[SWP_GU_SWEPT] = 0u;
          u64 sb = h->sweep_cnt;
          if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 swept = (u64)gu_sw[SWP_GU_SWEPT];
          if (h->sweep_cnt > sb && swept > 0ULL && (h->sweep_cnt - sb) * 1000ULL >= swept) {
            m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        } else if (h->inconsistent != 0ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 tr_lim = dticks / 50ULL;
      if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 fr = 1ULL; u64 fp = 10ULL; u64 fa = h->unassigned / 10ULL;
      while (fa >= fp && fr < 19ULL) { fr = fr + 1ULL; fp = fp * 10ULL; }
      u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
      if (h->unassigned > 0ULL && fr <= fe4 && full_has_factor_cands_fid(h)) {
        if (full_enter_dense_ex_fid(h, false)) {
          u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
          m6_hdr_set_watermark(h, 1ULL, nfact);
          u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
          full_factor(h, fbud);
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        } else if (h->inconsistent != 0ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      fl_a = (u32 *)h->flags;
      u64 after_act = 0ULL;
      ai = 0ULL;
      while (ai < h->cur_vars) {
        if ((fl_a[ai] & 1u) != 0u) { after_act = after_act + 1ULL; }
        ai = ai + 1ULL;
      }
      if (before_act == after_act) { break; }
      round = round + 1ULL;
    }
  }
  full_update_classify_fid(h);
  if (!initial) {
    u64 nlogp = f64u_mul(0x4059000000000000ULL, f64u_nlogpown(h->probings, 1ULL));
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, f64u_to_u64(nlogp));
  }
  h->probing = saved_prob;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}

u64 full_preprocess_m6(FullHdr *h) {
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  u64 saved_lk_ticks = h->search_ticks;
  u64 lk = full_lucky_late_m7(h);
  h->search_ticks = saved_lk_ticks;
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL || h->trail_end > 0ULL) {
    while (true) {
      u64 sr2 = full_arena_sweep(h);
      if (sr2 == 2ULL) { return 20ULL; }
      if (sr2 == 3ULL || h->oom != 0ULL) { break; }
      u64 pr2 = full_propagate(h);
      if (pr2 == 1ULL) { return 20ULL; }
      if (pr2 == 2ULL) { break; }
      if (sr2 == 0ULL && h->propagated >= h->trail_end) { break; }
    }
    h->unflushed = 0ULL;
  }
  if (h->trail_end > 0ULL && h->unassigned > 0ULL) {
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

/-! ## 1. Canonical `Fn` Handles -/

def fidStep13S5ActivateLitFn : Fn :=
  ⟨"full_activate_lit_fid", [i64, i32], [], full_activate_lit_fid_body⟩

def fidStep13S5ParseBodyFn : Fn :=
  ⟨"full_parse_body_m6", [i64, i64], [i64], full_parse_body_m6_body⟩

def fidStep13S5SortRedsFn : Fn :=
  ⟨"full_sort_reds", [i64, i64], [], full_sort_reds_body⟩

def fidStep13S5ReduceFn : Fn :=
  ⟨"full_reduce_m6", [i64, .bool], [i64], full_reduce_m6_body⟩

def fidStep13S5SetInactiveFn : Fn :=
  ⟨"full_set_inactive", [i64, i32, i32], [], full_set_inactive_body⟩

def fidStep13S5ProbeTailFn : Fn :=
  ⟨"full_probe_tail_m6", [i64, i64], [i64], full_probe_tail_m6_body⟩

def fidStep13S5ProbeFn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩

def fidStep13S5PreprocessFn : Fn :=
  ⟨"full_preprocess_m6", [i64], [i64], full_preprocess_m6_body⟩

def fidStep13S5ARepls : List Fn :=
  [ fidStep13S5ActivateLitFn
  , fidStep13S5ParseBodyFn
  , fidStep13S5SortRedsFn
  , fidStep13S5ReduceFn
  , fidStep13S5SetInactiveFn
  , fidStep13S5ProbeTailFn
  , fidStep13S5ProbeFn
  , fidStep13S5PreprocessFn ]

def fidStep13S5ABefores : List (Sym × List Fn) := []

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_activate_lit_fid_s5_wf : Func.Wf fidStep13S5ActivateLitFn.body := by t_wf_reify
theorem full_parse_body_m6_s5_wf : Func.Wf fidStep13S5ParseBodyFn.body := by t_wf_reify
theorem full_sort_reds_s5_wf : Func.Wf fidStep13S5SortRedsFn.body := by t_wf_reify
theorem full_reduce_m6_s5_wf : Func.Wf fidStep13S5ReduceFn.body := by t_wf_reify
theorem full_set_inactive_s5_wf : Func.Wf fidStep13S5SetInactiveFn.body := by t_wf_reify
theorem full_probe_tail_m6_s5_wf : Func.Wf fidStep13S5ProbeTailFn.body := by t_wf_reify
theorem full_probe_m6_s5_wf : Func.Wf fidStep13S5ProbeFn.body := by t_wf_reify
theorem full_preprocess_m6_s5_wf : Func.Wf fidStep13S5PreprocessFn.body := by t_wf_reify

theorem fidStep13S5ARepls_wf : ∀ f ∈ fidStep13S5ARepls, f.Wf := by
  intro f hf
  simp only [fidStep13S5ARepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_activate_lit_fid_s5_wf
  · exact full_parse_body_m6_s5_wf
  · exact full_sort_reds_s5_wf
  · exact full_reduce_m6_s5_wf
  · exact full_set_inactive_s5_wf
  · exact full_probe_tail_m6_s5_wf
  · exact full_probe_m6_s5_wf
  · exact full_preprocess_m6_s5_wf

theorem fidStep13S5ABefores_wf :
    ∀ h ∈ fidStep13S5ABefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp [fidStep13S5ABefores] at hh

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe

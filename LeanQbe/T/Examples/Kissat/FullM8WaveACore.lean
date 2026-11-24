/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M8 `FullM8WaveACore` — Verified Stage-2 Wave A Champion `W_1_3in` (`0 B/var`)

Purely additive Class-S standalone C0 module implementing the `0 B/var` Stage-2 Wave A
champion `W_1_3in` (`#1 AE-Kissat-bump` + `#3 Instance-Adaptive Inprocessing Throttling`) atop
`FullHdr` + `M6HdrExt` (`288` `u64` words at `(u64)h - 2304`, capping `M6_GLUE_BINS` to `64`
so freed words `96..159` and `224..287` host all M8 delay/throttle counters strictly inside
existing `m6ExtMem`):

1. **AE-Kissat-bump (`#1`):** `m8_log2_q16` + `full_bump_decay` (`m8_ae_bump_decay_body`) with
   Q16 `log2`, Padé `[1/1]` `tanh` curve for dynamic EVSIDS decay factor, and `1ULL << 56` rescale.
2. **64-Bin Glue Histogram & `delay[8]` Slots (`#3`):** `m6_hdr_recompute_tiers_mode` +
   `m6_hdr_record_used` (`M6_GLUE_BINS = 64`), plus `m6_hdr_delaying`, `m6_hdr_bump_delay`, and
   `m6_hdr_reduce_delay` extended to `id < 8` (slots `4..7` at `M8W_DEL_CNT_BASE = 120..123`,
   `M8W_DEL_CUR_BASE = 124..127`).
3. **Instance-Adaptive Inprocessing Throttling (`#3`):**
   - `full_vivify_tier_m6_hdr`: skips `count`/`keys`/`sort_sched` when
     `tier_mode == 0 && h->num_irred / 10 <= h->num_redundant`, records `e[M8W_VIV_LAST_TRIED]`.
   - `full_vivify_m6_hdr`: applies `M8_DELAY_VIVIFY_IRR` (`4`) backoff on low-yield tier-0 runs.
   - `full_eliminate_m6`: tracks `M8W_BVE_STALL` (`128`) & `M8W_BVE_THROTTLED` (`119`) backoff.
   - `full_probe_tail_m6`: applies `M8_DELAY_BACKBONE` (`6`, cap `4`) backoff before backbone.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM8WaveACore

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! waveACore "
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

#define M6_EXT_BYTES          2304ULL
#define M6W_TIER1             8ULL
#define M6W_TIER2             10ULL
#define M6W_TOTAL_USED        14ULL
#define M6W_DELAY_CNT         16ULL
#define M6W_DELAY_CUR         20ULL
#define M6W_USED0             32ULL
#define M6W_USED1             160ULL
#define M6_GLUE_BINS          64ULL
#define M6_WM_PROBE_TICKS     0ULL

#define M8W_VIV_LAST_TRIED    118ULL
#define M8W_BVE_THROTTLED     119ULL
#define M8W_DEL_CNT_BASE      120ULL
#define M8W_DEL_CUR_BASE      124ULL
#define M8W_BVE_STALL         128ULL
#define M8W_VIV_IRR_SKIPS     133ULL
#define M8W_BACKBONE_SKIPS    134ULL

#define M8_DELAY_VIVIFY_IRR   4ULL
#define M8_DELAY_BVE          5ULL
#define M8_DELAY_BACKBONE     6ULL

extern void full_rescale(FullHdr *h);
extern void m6_ext_ensure_init(FullHdr *h);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_viv_collect_m6(FullHdr *h, u64 tier_mode);
extern void full_viv_count_m6(FullHdr *h, u64 bn);
extern void full_viv_keys_m6(FullHdr *h, u64 bn);
extern void full_viv_sort_sched_m6(FullHdr *h, u64 bn);
extern u64 full_viv_clause_m6(FullHdr *h, u32 cref);
extern u64 full_propagate(FullHdr *h);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_elim_bve_m7(FullHdr *h, u64 budget);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);

u64 m8_log2_q16(u64 x) {
  if (x <= 1ULL) { return 0ULL; }
  u64 bit = 0ULL;
  u64 v = x;
  if (v >= (1ULL << 32)) { v = v >> 32; bit = bit + 32ULL; }
  if (v >= (1ULL << 16)) { v = v >> 16; bit = bit + 16ULL; }
  if (v >= (1ULL << 8))  { v = v >> 8;  bit = bit + 8ULL;  }
  if (v >= (1ULL << 4))  { v = v >> 4;  bit = bit + 4ULL;  }
  if (v >= (1ULL << 2))  { v = v >> 2;  bit = bit + 2ULL;  }
  if (v >= (1ULL << 1))  { bit = bit + 1ULL; }
  u64 frac = 0ULL;
  if (bit >= 16ULL) {
    frac = (x >> (bit - 16ULL)) & 0xFFFFULL;
  } else {
    frac = (x << (16ULL - bit)) & 0xFFFFULL;
  }
  return (bit << 16) + frac;
}

void m8_ae_bump_decay(FullHdr *h) {
  u64 inc = h->scinc;
  if (inc < (1ULL << 20)) { inc = 1ULL << 20; }
  if (inc >= (1ULL << 56)) { full_rescale(h); inc = h->scinc; }
  u64 lg = m8_log2_q16(inc);
  u64 base = 20ULL << 16;
  u64 rel = (lg > base) ? (lg - base) : 0ULL;
  u64 r_q16 = rel / 36ULL;
  if (r_q16 > 65536ULL) { r_q16 = 65536ULL; }
  u64 d0 = 62259ULL;
  u64 d_dyn = d0;
  if (r_q16 < 32768ULL) {
    u64 diff = 32768ULL - r_q16;
    d_dyn = d0 - ((1966ULL * diff) >> 16);
  } else {
    u64 u = (r_q16 - 32768ULL) << 1;
    u64 u2 = (u * u) >> 16;
    u64 th = (u * (27ULL * 65536ULL + u2)) / (27ULL * 65536ULL + 9ULL * u2);
    d_dyn = d0 + ((2621ULL * th) >> 16);
  }
  u64 ratio_q16 = (65536ULL << 16) / d_dyn;
  u64 ninc = ((inc >> 16) * ratio_q16) + (((inc & 0xFFFFULL) * ratio_q16) >> 16);
  if (ninc <= inc) { ninc = inc + 1ULL; }
  h->scinc = ninc;
  if (ninc >= (1ULL << 56)) { full_rescale(h); }
}

void m8_hdr_recompute_tiers_mode(FullHdr *h, u64 st) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 mode = (st != 0ULL) ? 1ULL : 0ULL;
  u64 base = (mode == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < M6_GLUE_BINS) {
    u64 u = e[base + g];
    if (total <= 0xFFFFFFFFFFFFFFFFULL - u) { total = total + u; }
    else { total = 0xFFFFFFFFFFFFFFFFULL; }
    g = g + 1ULL;
  }
  e[M6W_TOTAL_USED + mode] = total;
  u64 t1 = 2ULL; u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total == 1ULL) ? 1ULL : (total >> 1);
    u64 lim2 = (total == 1ULL) ? 1ULL :
      ((total / 10ULL) * 9ULL + (((total % 10ULL) * 9ULL) / 10ULL));
    u64 acc = 0ULL; bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < M6_GLUE_BINS) {
      u64 u = e[base + g];
      if (acc <= 0xFFFFFFFFFFFFFFFFULL - u) { acc = acc + u; }
      else { acc = 0xFFFFFFFFFFFFFFFFULL; }
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  e[M6W_TIER1 + mode] = t1;
  e[M6W_TIER2 + mode] = t2;
  m6_hdr_sync_legacy_tiers(h);
}

void m8_hdr_record_used(FullHdr *h, u64 glue) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 gi = (glue >= M6_GLUE_BINS) ? (M6_GLUE_BINS - 1ULL) : glue;
  u64 base = (st == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 u = e[base + gi];
  if (u < 0xFFFFFFFFFFFFFFFFULL) { e[base + gi] = u + 1ULL; }
  u64 tu = e[M6W_TOTAL_USED + st];
  if (tu < 0xFFFFFFFFFFFFFFFFULL) { e[M6W_TOTAL_USED + st] = tu + 1ULL; }
}

bool m6_hdr_delaying(FullHdr *h, u64 id) {
  if (id >= 8ULL) { return false; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 idx = (id < 4ULL) ? (M6W_DELAY_CNT + id) : (M8W_DEL_CNT_BASE + (id - 4ULL));
  u64 cnt = e[idx];
  if (cnt > 0ULL) {
    e[idx] = cnt - 1ULL;
    return true;
  }
  return false;
}

void m6_hdr_bump_delay(FullHdr *h, u64 id) {
  if (id >= 8ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cidx = (id < 4ULL) ? (M6W_DELAY_CUR + id) : (M8W_DEL_CUR_BASE + (id - 4ULL));
  u64 nidx = (id < 4ULL) ? (M6W_DELAY_CNT + id) : (M8W_DEL_CNT_BASE + (id - 4ULL));
  u64 cur = e[cidx];
  u64 cap = (id == M8_DELAY_BACKBONE) ? 4ULL : ((id >= 4ULL) ? 8ULL : 0xFFFFFFFFULL);
  if (cur < cap) { cur = cur + 1ULL; }
  e[cidx] = cur;
  e[nidx] = cur;
}

void m6_hdr_reduce_delay(FullHdr *h, u64 id) {
  if (id >= 8ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cidx = (id < 4ULL) ? (M6W_DELAY_CUR + id) : (M8W_DEL_CUR_BASE + (id - 4ULL));
  u64 nidx = (id < 4ULL) ? (M6W_DELAY_CNT + id) : (M8W_DEL_CNT_BASE + (id - 4ULL));
  u64 cur = e[cidx] >> 1;
  e[cidx] = cur;
  e[nidx] = cur;
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = full_viv_collect_m6(h, tier_mode);
  if (!(tier_mode == 0ULL && h->num_irred / 10ULL <= h->num_redundant)) {
    full_viv_count_m6(h, bn);
    full_viv_keys_m6(h, bn);
    full_viv_sort_sched_m6(h, bn);
  }
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         h->search_ticks < tick_lim) {
    u32 cr = rr[bi * 3ULL];
    budget = budget - 1ULL;
    u64 vc = full_viv_clause_m6(h, cr);
    if (vc == 20ULL) { res = 20ULL; break; }
    if (vc == 2ULL) { break; }
    if (h->cur_level == 0ULL && full_propagate(h) == 1ULL) { res = 20ULL; break; }
    bi = bi + 1ULL;
  }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (res == 1ULL && bi >= bn && bn < bmax) {
    full_viv_clear_tier_m6(h, tier_mode);
  }
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  e[M8W_VIV_LAST_TRIED] = bi;
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_m6_hdr(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  m6_hdr_sync_legacy_tiers(h);
  u64 start = h->search_ticks;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 delta = (start > last_p) ? (start - last_p) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  u64 res = 1ULL;
  if (h->num_redundant == 0ULL) {
    u64 lim0 = (start > (~0ULL) - total) ? (~0ULL) : (start + total);
    res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim0);
    h->search_ticks = start;
    return res;
  }
  u64 w1 = 3ULL; u64 w2 = 3ULL; u64 w3 = 1ULL; u64 w0 = 3ULL;
  if (h->tier1 >= h->tier2) { w1 = w1 + w2; w2 = 0ULL; }
  u64 lim = start;
  u64 a1 = (total * w1) / 10ULL;
  lim = (lim > (~0ULL) - a1) ? (~0ULL) : (lim + a1);
  res = full_vivify_tier_m6_hdr(h, 1ULL, 0xFFFFFFFFULL, lim);
  if (res != 20ULL && w2 > 0ULL) {
    u64 a2 = (total * w2) / 10ULL;
    lim = (lim > (~0ULL) - a2) ? (~0ULL) : (lim + a2);
    res = full_vivify_tier_m6_hdr(h, 2ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL) {
    u64 a3 = (total * w3) / 10ULL;
    lim = (lim > (~0ULL) - a3) ? (~0ULL) : (lim + a3);
    res = full_vivify_tier_m6_hdr(h, 3ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL) {
    u64 *e_v = (u64 *)((u64)h - M6_EXT_BYTES);
    if (m6_hdr_delaying(h, M8_DELAY_VIVIFY_IRR)) {
      e_v[M8W_VIV_IRR_SKIPS] = e_v[M8W_VIV_IRR_SKIPS] + 1ULL;
    } else {
      u64 a0 = (total * w0) / 10ULL;
      lim = (lim > (~0ULL) - a0) ? (~0ULL) : (lim + a0);
      u64 vb = h->viv_cnt;
      u64 ub = h->unassigned;
      res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim);
      u64 tried = e_v[M8W_VIV_LAST_TRIED];
      if (res != 20ULL && tried > 0ULL) {
        u64 y = (h->viv_cnt - vb) + ((ub > h->unassigned) ? (ub - h->unassigned) : 0ULL);
        if (y * 100ULL < tried) { m6_hdr_bump_delay(h, M8_DELAY_VIVIFY_IRR); }
        else { m6_hdr_reduce_delay(h, M8_DELAY_VIVIFY_IRR); }
      }
    }
  }
  h->search_ticks = start;
  return res;
}

u64 m8_eliminate_m6(FullHdr *h, bool initial) {
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
  u64 bve_b = h->bve_cnt;
  u64 una_b = h->unassigned;
  u64 bve_lim = initial
    ? (cv * 4ULL + 256ULL)
    : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve_m7(h, bve_lim);
  if (!initial && res != 20ULL) {
    u64 *e_b = (u64 *)((u64)h - M6_EXT_BYTES);
    u64 y = (h->bve_cnt - bve_b) +
      ((una_b > h->unassigned) ? (una_b - h->unassigned) : 0ULL);
    if (y * 2000ULL < h->unassigned && h->elim_bound >= 4ULL) {
      u64 st = e_b[M8W_BVE_STALL] + 1ULL;
      if (st > 3ULL) { st = 3ULL; }
      e_b[M8W_BVE_STALL] = st;
      u64 base_d = (h->elim_limit > h->conflicts) ? (h->elim_limit - h->conflicts) : 500ULL;
      h->elim_limit = h->conflicts + (base_d << st);
      e_b[M8W_BVE_THROTTLED] = e_b[M8W_BVE_THROTTLED] + 1ULL;
    } else if (y * 2000ULL >= h->unassigned) {
      e_b[M8W_BVE_STALL] = 0ULL;
    }
  }
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_tail_m6(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL) {
    u64 *e_bn = (u64 *)((u64)h - M6_EXT_BYTES);
    if (m6_hdr_delaying(h, M8_DELAY_BACKBONE)) {
      e_bn[M8W_BACKBONE_SKIPS] = e_bn[M8W_BACKBONE_SKIPS] + 1ULL;
    } else {
      u64 ub = h->unassigned;
      u64 dlb = h->delayed_len;
      if (full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        return 20ULL;
      }
      if (h->unassigned >= ub && h->delayed_len == dlb) {
        m6_hdr_bump_delay(h, M8_DELAY_BACKBONE);
      } else {
        m6_hdr_reduce_delay(h, M8_DELAY_BACKBONE);
      }
    }
  }
  u64 tr_lim = (dticks / 50ULL) + 100000ULL;
  if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
    return 20ULL;
  }
  return 1ULL;
}
"

/-! ## 2. Canonical `PatchModule` Handles & Standalone `waveACoreModule` -/

/-- Helper `m8_log2_q16` handle. -/
def m8Log2Q16Fn : Fn := ⟨"m8_log2_q16", [i64], [i64], m8_log2_q16_body⟩
/-- Drop-in M8 `Fn` replacing `"full_bump_decay"`. -/
def m8AeBumpDecayFn : Fn := ⟨"full_bump_decay", [i64], [], m8_ae_bump_decay_body⟩
/-- Drop-in M8 `Fn` replacing `"m6_hdr_recompute_tiers_mode"`. -/
def m8RecomputeTiersModeFn : Fn :=
  ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m8_hdr_recompute_tiers_mode_body⟩
/-- Drop-in M8 `Fn` replacing `"m6_hdr_record_used"`. -/
def m8RecordUsedFn : Fn := ⟨"m6_hdr_record_used", [i64, i64], [], m8_hdr_record_used_body⟩
/-- Drop-in M8 `Fn` replacing `"m6_hdr_delaying"`. -/
def m8DelayingFn : Fn := ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6_hdr_delaying_body⟩
/-- Drop-in M8 `Fn` replacing `"m6_hdr_bump_delay"`. -/
def m8BumpDelayFn : Fn := ⟨"m6_hdr_bump_delay", [i64, i64], [], m6_hdr_bump_delay_body⟩
/-- Drop-in M8 `Fn` replacing `"m6_hdr_reduce_delay"`. -/
def m8ReduceDelayFn : Fn := ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6_hdr_reduce_delay_body⟩
/-- Drop-in M8 `Fn` replacing `"full_vivify_tier_m6_hdr"`. -/
def m8VivifyTierHdrFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_body⟩
/-- Drop-in M8 `Fn` replacing `"full_vivify_m6_hdr"`. -/
def m8VivifyHdrFn : Fn := ⟨"full_vivify_m6_hdr", [i64], [i64], full_vivify_m6_hdr_body⟩
/-- Drop-in M8 `Fn` replacing `"full_eliminate_m6"`. -/
def m8EliminateM6Fn : Fn := ⟨"full_eliminate_m6", [i64, .bool], [i64], m8_eliminate_m6_body⟩
/-- Drop-in M8 `Fn` replacing `"full_probe_tail_m6"`. -/
def m8ProbeTailM6Fn : Fn := ⟨"full_probe_tail_m6", [i64, i64], [i64], full_probe_tail_m6_body⟩

/-- Canonical `PatchModule.patchFns` replacements (`10` fns) for `W_1_3in` (`0 B/var`). -/
def waveACoreRepls : List Fn :=
  [ m8AeBumpDecayFn
  , m8RecomputeTiersModeFn
  , m8RecordUsedFn
  , m8DelayingFn
  , m8BumpDelayFn
  , m8ReduceDelayFn
  , m8VivifyTierHdrFn
  , m8VivifyHdrFn
  , m8EliminateM6Fn
  , m8ProbeTailM6Fn ]

/-- Helper insertion (`m8_log2_q16` placed before `"full_bump_decay"`). -/
def waveACoreBefores : List (Sym × List Fn) :=
  [("full_bump_decay", [m8Log2Q16Fn])]

/-- Complete canonical `11`-function standalone list (`[m8_log2_q16] ++ waveACoreRepls`). -/
def waveACoreFns : List Fn :=
  [m8Log2Q16Fn] ++ waveACoreRepls

/-- `22` external callee signatures referenced by `waveACoreFns`. -/
def waveACoreExterns : List Extern :=
  [ ⟨"full_rescale", [i64], []⟩
  , ⟨"m6_ext_ensure_init", [i64], []⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], []⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64]⟩
  , ⟨"full_viv_count_m6", [i64, i64], []⟩
  , ⟨"full_viv_keys_m6", [i64, i64], []⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], []⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], []⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_log10_q16_m7", [i64], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_forward_sub", [i64, i64], [i64]⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64]⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64]⟩ ]

/-- Closed-boundary standalone Class-S module (`11` fns, `22` externs, `0` exits). -/
def waveACoreModule : LeanQbe.T.Module :=
  { fns := waveACoreFns, externs := waveACoreExterns, exits := [] }

end LeanQbe.T.Examples.Kissat.FullM8WaveACore

end

public section

namespace LeanQbe.T.Examples.Kissat.FullM8WaveACore

open LeanQbe.T

theorem m8_log2_q16_wf : Func.Wf m8_log2_q16_body := by
  t_wf_reify

theorem m8_ae_bump_decay_wf : Func.Wf m8_ae_bump_decay_body := by
  t_wf_reify

theorem m8_hdr_recompute_tiers_mode_wf : Func.Wf m8_hdr_recompute_tiers_mode_body := by
  t_wf_reify

theorem m8_hdr_record_used_wf : Func.Wf m8_hdr_record_used_body := by
  t_wf_reify

theorem m6_hdr_delaying_wf : Func.Wf m6_hdr_delaying_body := by
  t_wf_reify

theorem m6_hdr_bump_delay_wf : Func.Wf m6_hdr_bump_delay_body := by
  t_wf_reify

theorem m6_hdr_reduce_delay_wf : Func.Wf m6_hdr_reduce_delay_body := by
  t_wf_reify

theorem full_vivify_tier_m6_hdr_wf : Func.Wf full_vivify_tier_m6_hdr_body := by
  t_wf_reify

theorem full_vivify_m6_hdr_wf : Func.Wf full_vivify_m6_hdr_body := by
  t_wf_reify

theorem m8_eliminate_m6_wf : Func.Wf m8_eliminate_m6_body := by
  t_wf_reify

theorem full_probe_tail_m6_wf : Func.Wf full_probe_tail_m6_body := by
  t_wf_reify

theorem waveACore_fns_wf : ∀ f ∈ waveACore_fns, f.Wf := by
  simp only [waveACore_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨m8_log2_q16_wf, m8_ae_bump_decay_wf, m8_hdr_recompute_tiers_mode_wf,
    m8_hdr_record_used_wf, m6_hdr_delaying_wf, m6_hdr_bump_delay_wf,
    m6_hdr_reduce_delay_wf, full_vivify_tier_m6_hdr_wf, full_vivify_m6_hdr_wf,
    m8_eliminate_m6_wf, full_probe_tail_m6_wf⟩

theorem waveACoreRepls_wf : ∀ f ∈ waveACoreRepls, f.Wf := by
  simp only [waveACoreRepls, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨m8_ae_bump_decay_wf, m8_hdr_recompute_tiers_mode_wf, m8_hdr_record_used_wf,
    m6_hdr_delaying_wf, m6_hdr_bump_delay_wf, m6_hdr_reduce_delay_wf,
    full_vivify_tier_m6_hdr_wf, full_vivify_m6_hdr_wf, m8_eliminate_m6_wf,
    full_probe_tail_m6_wf⟩

theorem waveACoreFns_wf : ∀ f ∈ waveACoreFns, f.Wf := by
  simp only [waveACoreFns, waveACoreRepls, List.singleton_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨m8_log2_q16_wf, m8_ae_bump_decay_wf, m8_hdr_recompute_tiers_mode_wf,
    m8_hdr_record_used_wf, m6_hdr_delaying_wf, m6_hdr_bump_delay_wf,
    m6_hdr_reduce_delay_wf, full_vivify_tier_m6_hdr_wf, full_vivify_m6_hdr_wf,
    m8_eliminate_m6_wf, full_probe_tail_m6_wf⟩

theorem waveACore_acyclic : waveACoreModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM8WaveACore

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat Fidelity Step 7 Pure-C0 Parity (`FullFidelityStep7`, `501` fns)

Additive pure-C0 upgrade matching `fid_v8_pure_c0.diff` (`20` replacements + `2` new helpers =
`499 -> 501` fns, `0` externs, `0` exits, `0` beyond-upstream heuristics, `0` quadratic hazards):
- `full_learn_clause`: O(n) block-preserving reverse before descending insertion sort.
- `full_sort_bin_watches_fid`: 6-line Knuth Shellsort on binary watch prefixes before
  `full_rebuild_watches`.
- `full_sort_tmp`: `<= 32` insertion sort, `> 32` `lvl`-only counting sort in `wsort` with stable
  bottom-up merge-sort fallback in `wsort`.
- `full_probe_m6` + `m6_hdr_init`: `watermarks[1]` (`factorizations`) budget gating;
  `full_bump_analyzed_m6_hdr`: `M6_DELAY_BUMPREASONS` (`0ULL`) gating; BVA matrix compaction +
  post-commit `full_bva_upd_lit_fid` heap refresh; Step-7 `eliminate`, `reduce`, `search`,
  `vivify`, `calc_max_v`, `calc_scr_cap_m5`, `walk_cb_inv_m7`, `bve_var_key_m7`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.PatchModule

kissat_c0! fidStep7 "
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

#define FL_ACTIVE             1u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define PH_GARB               0x00080000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u
#define PH_GLUE_MASK          0x7FFFFu
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu
#define M6_EXT_BYTES          2304ULL
#define M6_EXT_WORDS          288ULL
#define M6_HDR_MAGIC          0x4D36484452455831ULL
#define M6W_MAGIC             0ULL
#define M6W_DR_STATE          1ULL
#define M6W_DR_SE             6ULL
#define M6W_TIER1             8ULL
#define M6W_TIER2             10ULL
#define M6W_GLUE_INTV         13ULL
#define M6W_WM_BASE           24ULL
#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_DELAY_VIVIFYIRR    3ULL
#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL

extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_arena_sweep(FullHdr *h);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_bump_decay(FullHdr *h);
extern void full_bump_var(FullHdr *h, u32 v);
extern void full_bva_connect_clauses_fid(FullHdr *h);
extern u32 full_bva_count_lit_deg_fid(FullHdr *h, u32 lit);
extern u32 full_bva_filter_row(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off, u32 cur_qn,
  u32 best_lit);
extern u32 full_bva_pick_cand(FullHdr *h, u32 ncntd, u32 f0);
extern u32 full_bva_scan_cands(FullHdr *h, u32 row_off, u32 cur_qn, u64 init_lits);
extern u32 full_bva_steps_cap_fid(u64 cap);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern u64 full_det_new_level(FullHdr *h, u64 jump);
extern void full_eager_subsume(FullHdr *h, u64 new_ref);
extern u64 full_elim_bve_m7(FullHdr *h, u64 res_lim);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern bool full_enter_dense(FullHdr *h);
extern void full_fheap_down_fid(u32 *hp, u32 *ps, u32 *deg, u32 p, u32 n);
extern void full_fheap_up_fid(u32 *hp, u32 *ps, u32 *deg, u32 p);
extern u64 full_fixed_bytes(u64 max_v);
extern u64 full_forward_sub_m7(FullHdr *h, u64 budget);
extern u64 full_ilog10(u64 x);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern u64 full_isqrt(u64 x);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_lucky_late_m7(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_probe_tail_m6(FullHdr *h, u64 dticks);
extern u64 full_propagate(FullHdr *h);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_recompute_tiers(FullHdr *h);
extern u64 full_reorder_m6(FullHdr *h, u64 budget);
extern void full_rephase(FullHdr *h);
extern void full_restart(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern u64 full_simplify_m6(FullHdr *h, bool do_probe, bool do_elim);
extern void full_sort_ana_qs_m6(FullHdr *h, u64 n);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_substitute(FullHdr *h);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern void full_switch_mode_m7(FullHdr *h);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64 full_viv_clause_m6(FullHdr *h, u32 cref);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern u64 full_viv_collect_fid(FullHdr *h, u64 tier_mode);
extern void full_viv_count_fid(FullHdr *h, u64 bn);
extern void full_viv_sort_fid(FullHdr *h, u64 bn);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_wstack_defrag(FullHdr *h);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64 m6_hdr_decide_fid(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool m6_hdr_dr_allow(FullHdr *h);
extern u64 m6_hdr_get_tier1(FullHdr *h, bool vivify_mode);
extern u64 m6_hdr_get_tier2(FullHdr *h, bool vivify_mode);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);

u64 full_calc_max_v(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = 32768ULL;
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 fixed = full_fixed_bytes(max_v);
  if (avail < fixed || avail - fixed < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_calc_scr_cap_m5(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = (rem >= 16384ULL) ? (rem >> 4) : (rem >> 5);
  if (c > 8388608ULL) { c = 8388608ULL; }
  return c & (~1ULL);
}

void m6_hdr_init(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 i = 0ULL;
  while (i < M6_EXT_WORDS) {
    e[i] = 0ULL;
    i = i + 1ULL;
  }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_SE] = 1ULL << 32;
  e[M6W_DR_SE + 1ULL] = 1ULL << 32;
  e[M6W_TIER1] = 2ULL;
  e[M6W_TIER1 + 1ULL] = 2ULL;
  e[M6W_TIER2] = 6ULL;
  e[M6W_TIER2 + 1ULL] = 6ULL;
  e[M6W_GLUE_INTV] = 2ULL;
  e[M6W_WM_BASE] = h->fwd_sub_cnt;
  e[M6W_WM_BASE + 1ULL] = 0ULL;
  e[M6W_MAGIC] = M6_HDR_MAGIC;
}

u64 full_reduce(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + full_isqrt(h->reductions * 1000000ULL);
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  full_recompute_tiers(h);
  full_mark_reasons(h, true);
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 rc = 0ULL; u64 p = 0ULL;
  u64 t1 = h->tier1; u64 t2 = h->tier2;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 n = full_arena_next(h, (u32)p);
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
    u64 logv = full_ilog10(h->reductions + 9ULL);
    u64 target = (rc * (900ULL - (400ULL / logv))) / 1000ULL;
    u64 i = 0ULL;
    while (i < target && i < rc) {
      u64 cref = (u64)rr[i]; u32 hdr = ar[cref];
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
      if (sr == 2ULL) { return 20ULL; }
      if (sr == 3ULL) { return 0ULL; }
      if (sr == 0ULL) { break; }
      u64 pr = full_propagate(h);
      if (pr == 1ULL) { return 20ULL; }
      if (pr != 0ULL) { return 0ULL; }
      h->unflushed = 0ULL;
    }
  } else { full_mark_reasons(h, false); }
  return 1ULL;
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
    if (force || h->unflushed == 0ULL) {
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

void full_bump_analyzed_m6_hdr(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  if (!m6_hdr_delaying(h, 0ULL) && m6_hdr_dr_allow(h)) {
    u64 lim = saved * 10ULL;
    u64 i = 0ULL;
    u64 tlen = h->tmp_len;
    if (tlen > cv) { tlen = cv; }
    while (i < tlen && h->min_clr_len <= lim) {
      u32 uv = tmp[i] >> 1;
      u32 rsn = ((u64)uv < cv) ? rsns[uv] : 0xFFFFFFFFu;
      if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) != 0u) {
        u32 ov = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
          mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
          h->min_clr_len = h->min_clr_len + 1ULL;
        }
      } else if (rsn != 0xFFFFFFFFu && (u64)rsn + 3ULL <= h->arena_len) {
        u32 sz = ar[(u64)rsn + 2ULL];
        if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len) {
          h->search_ticks = h->search_ticks + 1ULL;
          u32 j = 0u;
          while (j < sz && h->min_clr_len <= lim) {
            u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
            if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
              mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
              h->min_clr_len = h->min_clr_len + 1ULL;
            }
            j = j + 1u;
          }
        }
      }
      i = i + 1ULL;
    }
    if (h->min_clr_len > lim) {
      while (h->min_clr_len > saved) {
        h->min_clr_len = h->min_clr_len - 1ULL;
        u32 rv = ana[h->min_clr_len];
        if ((u64)rv < cv) { mrk[rv] = (u8)0; }
      }
      m6_hdr_bump_delay(h, 0ULL);
    } else {
      m6_hdr_reduce_delay(h, 0ULL);
    }
  }
  u64 cnt = h->min_clr_len;
  if (h->stable == 0ULL) {
    if (cnt <= cv) { full_sort_ana_qs_m6(h, cnt); }
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_queue_mtf(h, bv);
      }
      k = k + 1ULL;
    }
  } else {
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_bump_var(h, bv);
      }
      k = k + 1ULL;
    }
    full_bump_decay(h);
  }
}

void full_sort_tmp(FullHdr *h) {
  u64 tlen = h->tmp_len;
  u64 mv = h->max_vars;
  if (tlen <= 2ULL || tlen > mv) {
    return;
  }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  if (tlen <= 32ULL) {
    u64 i = 2ULL;
    while (i < tlen) {
      u32 x = tmp[i];
      u32 lx = lvl[((u64)x) >> 1];
      u64 j = i;
      while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] > lx) {
        tmp[j] = tmp[j - 1ULL];
        j = j - 1ULL;
      }
      tmp[j] = x;
      i = i + 1ULL;
    }
    return;
  }
  u32 *sh = (u32 *)h->wsort;
  u32 x1 = tmp[1];
  sh[1] = x1;
  u32 l1 = lvl[((u64)x1) >> 1];
  u32 min_l = l1;
  u32 max_l = l1;
  u64 k = 2ULL;
  while (k < tlen) {
    u32 x = tmp[k];
    sh[k] = x;
    u32 lx = lvl[((u64)x) >> 1];
    if (lx < min_l) { min_l = lx; }
    if (lx > max_l) { max_l = lx; }
    k = k + 1ULL;
  }
  u64 span = (u64)max_l - (u64)min_l + 1ULL;
  u64 n = tlen - 1ULL;
  if (span == 1ULL) {
    return;
  }
  if (span <= mv && span <= (n << 2)) {
    u64 b = 0ULL;
    while (b < span) {
      sh[mv + b] = 0u;
      b = b + 1ULL;
    }
    k = 1ULL;
    while (k < tlen) {
      u32 x = sh[k];
      u64 bi = (u64)lvl[((u64)x) >> 1] - (u64)min_l;
      sh[mv + bi] = sh[mv + bi] + 1u;
      k = k + 1ULL;
    }
    u64 pos = 1ULL;
    b = 0ULL;
    while (b < span) {
      u32 c = sh[mv + b];
      sh[mv + b] = (u32)pos;
      pos = pos + (u64)c;
      b = b + 1ULL;
    }
    k = 1ULL;
    while (k < tlen) {
      u32 x = sh[k];
      u64 bi = (u64)lvl[((u64)x) >> 1] - (u64)min_l;
      u64 dst = (u64)sh[mv + bi];
      sh[mv + bi] = (u32)(dst + 1ULL);
      tmp[dst] = x;
      k = k + 1ULL;
    }
    return;
  }
  u64 w = 1ULL;
  while (w < n) {
    u64 lo = 1ULL;
    while (lo < tlen) {
      u64 mid = (lo + w < tlen) ? (lo + w) : tlen;
      u64 hi = (lo + (w << 1) < tlen) ? (lo + (w << 1)) : tlen;
      u64 i0 = lo;
      u64 i1 = mid;
      u64 dst = lo;
      while (i0 < mid && i1 < hi) {
        if (lvl[((u64)tmp[i0]) >> 1] <= lvl[((u64)tmp[i1]) >> 1]) {
          sh[dst] = tmp[i0]; i0 = i0 + 1ULL;
        } else {
          sh[dst] = tmp[i1]; i1 = i1 + 1ULL;
        }
        dst = dst + 1ULL;
      }
      while (i0 < mid) { sh[dst] = tmp[i0]; i0 = i0 + 1ULL; dst = dst + 1ULL; }
      while (i1 < hi) { sh[dst] = tmp[i1]; i1 = i1 + 1ULL; dst = dst + 1ULL; }
      u64 cp = lo;
      while (cp < hi) { tmp[cp] = sh[cp]; cp = cp + 1ULL; }
      lo = hi;
    }
    w = w << 1;
  }
}

u64 full_learn_clause(FullHdr *h, u64 glue) {
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
      u64 rr = full_reduce(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
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

u64 full_walk_cb_inv_m7(FullHdr *h, u64 ncl, u64 tot_lits) {
  if ((h->walk_cnt_stat & 1ULL) != 0ULL || ncl == 0ULL) {
    return 32768ULL;
  }
  u64 occ = (tot_lits > 0x0000FFFFFFFFFFFFULL) ? 0x0000FFFFFFFFFFFFULL : tot_lits;
  u64 avg = (occ << 16) / ncl;
  u64 cb = 2000ULL;
  if (avg < 196608ULL) {
    cb = 2000ULL + (500ULL * avg) / 196608ULL;
  } else if (avg < 262144ULL) {
    cb = 2500ULL + ((350ULL * (avg - 196608ULL)) >> 16);
  } else if (avg < 327680ULL) {
    cb = 2850ULL + ((850ULL * (avg - 262144ULL)) >> 16);
  } else if (avg < 393216ULL) {
    cb = 3700ULL + ((1400ULL * (avg - 327680ULL)) >> 16);
  } else {
    u64 ex = avg - 393216ULL;
    if (ex > 2621440ULL) { ex = 2621440ULL; }
    cb = 5100ULL + ((2300ULL * ex) >> 16);
  }
  if (cb < 2000ULL) { cb = 2000ULL; }
  u64 inv = (65536000ULL + (cb >> 1)) / cb;
  if (inv == 0ULL) { inv = 1ULL; }
  if (inv > 32768ULL) { inv = 32768ULL; }
  return inv;
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = full_viv_collect_fid(h, tier_mode);
  bool do_sort = (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant);
  if (do_sort) {
    full_viv_count_fid(h, bn);
    full_viv_sort_fid(h, bn);
  }
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         h->search_ticks < tick_lim) {
    u32 cr = rr[do_sort ? bi : (bn - 1ULL - bi)];
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
  h->res_sz = bi;
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_m6_hdr(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->tier1 = m6_hdr_get_tier1(h, true);
  h->tier2 = m6_hdr_get_tier2(h, true);
  u64 w0 = m6_hdr_delaying(h, M6_DELAY_VIVIFYIRR) ? 0ULL : 3ULL;
  u64 w1 = (h->num_redundant == 0ULL) ? 0ULL : 3ULL;
  u64 w2 = (h->num_redundant == 0ULL) ? 0ULL : 3ULL;
  u64 w3 = (h->num_redundant == 0ULL) ? 0ULL : 1ULL;
  u64 sum = w0 + w1 + w2 + w3;
  if (sum == 0ULL) { h->probing = 0ULL; return 1ULL; }
  u64 start = h->search_ticks;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 delta = (start > last_p) ? (start - last_p) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  if (w1 > 0ULL && w2 > 0ULL && h->tier1 >= h->tier2) { w1 = w1 + w2; w2 = 0ULL; }
  u64 res = 1ULL;
  u64 lim = start;
  if (w1 > 0ULL) {
    u64 a1 = (total * w1) / sum;
    lim = (lim > (~0ULL) - a1) ? (~0ULL) : (lim + a1);
    res = full_vivify_tier_m6_hdr(h, 1ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w2 > 0ULL) {
    u64 a2 = (total * w2) / sum;
    lim = (lim > (~0ULL) - a2) ? (~0ULL) : (lim + a2);
    res = full_vivify_tier_m6_hdr(h, 2ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w3 > 0ULL) {
    u64 a3 = (total * w3) / sum;
    lim = (lim > (~0ULL) - a3) ? (~0ULL) : (lim + a3);
    res = full_vivify_tier_m6_hdr(h, 3ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w0 > 0ULL) {
    u64 a0 = (total * w0) / sum;
    lim = (lim > (~0ULL) - a0) ? (~0ULL) : (lim + a0);
    u64 vb = h->viv_cnt;
    u64 ub = h->unassigned;
    res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim);
    u64 tried = h->res_sz;
    if (res != 20ULL) {
      u64 y = (h->viv_cnt - vb) + ((ub > h->unassigned) ? (ub - h->unassigned) : 0ULL);
      if (tried == 0ULL || y * 100ULL < tried) { m6_hdr_bump_delay(h, M6_DELAY_VIVIFYIRR); }
      else { m6_hdr_reduce_delay(h, M6_DELAY_VIVIFYIRR); }
    }
  }
  m6_hdr_sync_legacy_tiers(h);
  h->search_ticks = start;
  return res;
}

void full_sort_bin_watches_fid(FullHdr *h) {
  u64 nl = h->cur_vars << 1;
  u32 *wv = (u32 *)h->watch_vec;
  u32 *ws = (u32 *)h->watch_stk;
  u64 l = 0ULL;
  while (l < nl) {
    u64 off = (u64)wv[l << 1];
    u64 sz = (u64)wv[(l << 1) + 1ULL];
    u64 bn = 0ULL;
    while (bn < sz && (ws[off + bn] & 0x80000000u) != 0u) {
      bn = bn + 1ULL;
    }
    if (bn > 1ULL) {
      u64 gap = 1ULL;
      u64 lim = bn / 3ULL;
      while (gap < lim) {
        gap = 3ULL * gap + 1ULL;
      }
      while (gap > 0ULL) {
        u64 i = gap;
        while (i < bn) {
          u32 x = ws[off + i];
          u32 xo = x & 0x7FFFFFFFu;
          u64 j = i;
          while (j >= gap && (ws[off + j - gap] & 0x7FFFFFFFu) > xo) {
            ws[off + j] = ws[off + j - gap];
            j = j - gap;
          }
          ws[off + j] = x;
          i = i + 1ULL;
        }
        gap = gap / 3ULL;
      }
    }
    l = l + 1ULL;
  }
}

u64 full_rebuild_watches(FullHdr *h) {
  h->dense_mode = 0ULL;
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    if (sr == 0ULL) { break; }
  }
  full_sort_bin_watches_fid(h);
  return 1ULL;
}

bool full_bva_commit(FullHdr *h, u32 best_k) {
  if (h->oom != 0ULL) { return false; }
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (sc == 0u || best_k >= sc) { return false; }
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *fl = (u32 *)h->flags;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 dm = best_k + 1u;
  u32 brow_off = scr[sc + best_k];
  u32 mn = scr[2u * sc + best_k];
  u64 need_ar = 16ULL;
  u64 need_w = (((u64)dm + (u64)mn + 8ULL) << 3);
  u32 si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 fsz = (u64)wvec[((u64)fs << 1) + 1ULL];
    need_w = need_w + (fsz << 1) + 2ULL;
    si = si + 1u;
  }
  u32 m = 0u;
  while (m < mn) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      need_w = need_w + (qsz << 1) + 2ULL;
    } else {
      u32 csz = ar[(u64)c_top + 2ULL];
      need_ar = need_ar + 3ULL + (u64)csz;
      u32 flit = scr[best_k]; u32 j = 0u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) {
          u64 lsz = (u64)wvec[((u64)l << 1) + 1ULL];
          need_w = need_w + (lsz << 1) + 2ULL;
        }
        j = j + 1u;
      }
    }
    m = m + 1u;
  }
  if (h->cur_vars >= h->max_vars || h->arena_cap < h->arena_len ||
      h->arena_cap - h->arena_len < need_ar) { return false; }
  if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
      u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
      while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
      return false;
    }
  }
  u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
  full_init_fresh_var(h, fv);
  u32 *deg = (u32 *)h->repr;
  deg[fv << 1] = 0u; deg[(fv << 1) | 1u] = 0u;
  cnt[fv << 1] = 0u; cnt[(fv << 1) | 1u] = 0u;
  u32 fresh = fv << 1; u32 *tmp = (u32 *)h->tmp_lits;
  bool ok = true;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 br = full_add_bin(h, fresh, fs);
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    fl[fs >> 1] = fl[fs >> 1] | (((fs & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
    fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_P;
    si = si + 1u;
  }
  m = 0u;
  while (m < mn && ok) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      u64 br = full_add_bin(h, fresh ^ 1u, q);
      fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_N;
      fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr == 0xFFFFFFFFULL) { ok = false; break; }
      j = 0u; while (j < tk) { ar[ncr + 3ULL + (u64)j] = tmp[j]; j = j + 1u; }
      j = 0u;
      while (j < tk) {
        if (!full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u)) {
          u32 uk = 0u;
          while (uk < j) { full_unwatch_large(h, tmp[uk], (u32)ncr); uk = uk + 1u; }
          ar[ncr] = ar[ncr] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)tk;
          ok = false; break;
        }
        u32 tv = tmp[j] >> 1;
        fl[tv] = fl[tv] | (((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        j = j + 1u;
      }
      if (ok) { h->num_irred = h->num_irred + 1ULL; }
    }
    m = m + 1u;
  }
  if (!ok) {
    u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
    while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
    return false;
  }
  u32 fs_i = best_k;
  while (fs_i > 0u) {
    u32 ro_prev = scr[sc + (fs_i - 1u)];
    u32 po_s = scr[3u * sc + fs_i];
    u32 po_prev = (fs_i > 1u) ? scr[3u * sc + (fs_i - 1u)] : 0u;
    u32 fi = 0u;
    while (fi < mn) {
      u32 fj = scr[po_s + fi];
      if (fs_i > 1u) { scr[po_prev + fi] = scr[po_prev + fj]; }
      scr[ro_prev + fi] = scr[ro_prev + fj];
      fi = fi + 1u;
    }
    scr[2u * sc + (fs_i - 1u)] = mn;
    fs_i = fs_i - 1u;
  }
  u32 qs = best_k + 1u;
  while (qs > 0u) {
    qs = qs - 1u;
    u32 ro = scr[sc + qs];
    u32 fs = scr[qs];
    m = 0u;
    while (m < mn) {
      u32 cs = scr[ro + m];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          full_unwatch_large(h, dl, cs);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      }
      m = m + 1u;
    }
  }
  u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
  while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  deg[fresh] = dm; deg[fresh ^ 1u] = mn;
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv) {
  u64 cap = h->scratch_cap;
  u32 sc = full_bva_steps_cap_fid(cap);
  if (h->cur_vars >= h->max_vars || sc == 0u) { return false; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *arena = (u32 *)h->arena;
  u8 *counted = (u8 *)h->lit_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  if (vals[f0] != (i8)0) { return false; }
  u64 init_lits = (init_cv <= h->cur_vars) ? (init_cv << 1) : (h->cur_vars << 1);
  u32 hdr_sz = sc << 2;
  u32 row0_max = (u32)((cap - (u64)hdr_sz) / 3ULL);
  if (row0_max < 2u) { return false; }
  u64 off0 = (u64)wvec[(u64)f0 << 1];
  u64 sz0 = (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 wi = 0ULL;
  u32 r0n = 0u;
  u64 fticks = 0ULL;
  while (wi < sz0 && r0n < row0_max) {
    u32 w0 = wstk[off0 + wi]; wi = wi + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      fticks = fticks + 1ULL;
      u32 other = w0 & PW_LIT_MASK;
      if (vals[other] == (i8)0) {
        scr[hdr_sz + r0n] = w0;
        r0n = r0n + 1u;
      }
    } else if (wi < sz0) {
      u32 cr = wstk[off0 + wi]; wi = wi + 1ULL;
      fticks = fticks + 1ULL;
      u32 csz = arena[(u64)cr + 2ULL];
      u32 cfl = arena[(u64)cr];
      if ((cfl & (PH_GARB | PH_RED)) == 0u && csz >= 3u && csz <= 5u) {
        u32 j = 0u; bool has_f0 = false; bool sat = false;
        while (j < csz) {
          u32 l = arena[(u64)cr + 3ULL + (u64)j];
          if (vals[l] > (i8)0) { sat = true; break; }
          if (l == f0) { has_f0 = true; }
          j = j + 1u;
        }
        if (!sat && has_f0) {
          scr[hdr_sz + r0n] = cr;
          r0n = r0n + 1u;
        }
      }
    }
  }
  h->ant_sz = (h->ant_sz > fticks) ? (h->ant_sz - fticks) : 0ULL;
  if (r0n < 2u) { return false; }
  u64 elim_bound = h->elim_bound;
  scr[0] = f0;
  scr[sc] = hdr_sz;
  scr[2u * sc] = r0n;
  scr[3u * sc] = hdr_sz;
  u32 bump = hdr_sz + r0n;
  counted[f0] = (u8)1;
  u32 step = 1u;
  u32 cur_qn = r0n;
  u32 best_k = 0u;
  u64 best_red = 0ULL;
  while (step < sc && cur_qn >= 2u && h->ant_sz > 0ULL) {
    u32 row_off = scr[sc + step - 1u];
    u32 ncntd = full_bva_scan_cands(h, row_off, cur_qn, init_lits);
    u32 best_lit = full_bva_pick_cand(h, ncntd, f0);
    if (best_lit == 0xFFFFFFFFu || h->ant_sz == 0ULL) { break; }
    u32 rem = (u32)(cap - (u64)bump);
    u32 max_new = rem >> 1;
    if (max_new > cur_qn) { max_new = cur_qn; }
    if (max_new < 2u) { break; }
    u32 nrow_off = bump;
    u32 par_off = bump + max_new;
    cur_qn = full_bva_filter_row(h, row_off, nrow_off, par_off, cur_qn, best_lit);
    if (cur_qn < 2u) { break; }
    scr[step] = best_lit;
    scr[sc + step] = nrow_off;
    scr[2u * sc + step] = cur_qn;
    scr[3u * sc + step] = par_off;
    bump = par_off + cur_qn;
    counted[best_lit] = (u8)1;
    step = step + 1u;
    u64 dm = (u64)step;
    u64 mn = (u64)cur_qn;
    u64 prod = dm * mn;
    u64 sum = dm + mn;
    if (prod > sum) {
      u64 red = prod - sum;
      if (red > elim_bound && red > best_red) {
        best_red = red;
        best_k = step - 1u;
      }
    }
  }
  u32 ci = 0u;
  while (ci < step) {
    counted[scr[ci]] = (u8)0;
    ci = ci + 1u;
  }
  if (best_k == 0u) { return false; }
  h->res_sz = (u64)best_k;
  return full_bva_commit(h, best_k);
}

u32 full_bva_upd_lit_fid(FullHdr *h, u32 *fheap, u32 *fpos,
    u32 *deg, u32 hsz, u64 cur_nl, u32 tl) {
  u32 nd = full_bva_count_lit_deg_fid(h, tl);
  u32 od = deg[tl];
  if (nd > 1u) {
    if (nd != od) {
      deg[tl] = nd;
      u32 p = fpos[tl];
      if (p < hsz) {
        if (nd > od) { full_fheap_up_fid(fheap, fpos, deg, p); }
        else { full_fheap_down_fid(fheap, fpos, deg, p, hsz); }
      }
    }
    if (fpos[tl] == 0xFFFFFFFFu && (u64)hsz < cur_nl) {
      fheap[hsz] = tl; fpos[tl] = hsz;
      full_fheap_up_fid(fheap, fpos, deg, hsz);
      hsz = hsz + 1u;
    }
  } else {
    deg[tl] = nd;
    u32 p = fpos[tl];
    if (p < hsz) {
      hsz = hsz - 1u;
      u32 last = fheap[hsz];
      fpos[last] = 0xFFFFFFFFu;
      fpos[tl] = 0xFFFFFFFFu;
      if (p < hsz) {
        fheap[p] = last; fpos[last] = p;
        full_fheap_up_fid(fheap, fpos, deg, p);
        u32 lp = fpos[last];
        if (lp < hsz) { full_fheap_down_fid(fheap, fpos, deg, lp, hsz); }
      }
    }
  }
  return hsz;
}

u64 full_factor(FullHdr *h, u64 budget) {
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (h->cur_vars >= h->max_vars || sc == 0u || budget == 0ULL) {
    return 1ULL;
  }
  full_bva_connect_clauses_fid(h);
  if (h->oom != 0ULL) { return 1ULL; }
  h->ant_sz = budget;
  u64 init_cv = h->cur_vars;
  u64 max_nl = h->max_vars << 1;
  u32 *tmark = (u32 *)h->wsort;
  u32 *fheap = (u32 *)h->tarjan_mark;
  u32 *fpos = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags;
  u32 *deg = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u64 zi = 0ULL;
  while (zi < max_nl) {
    tmark[zi] = 0u; fheap[zi] = 0u; fpos[zi] = 0xFFFFFFFFu;
    zi = zi + 1ULL;
  }
  u32 hsz = 0u;
  u64 v = 0ULL;
  while (v < init_cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 pl = (u32)(v << 1);
      u32 nl = pl | 1u;
      if ((fl[v] & FL_FACT_P) != 0u && deg[pl] > 1u) {
        fheap[hsz] = pl; fpos[pl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
      if ((fl[v] & FL_FACT_N) != 0u && deg[nl] > 1u) {
        fheap[hsz] = nl; fpos[nl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
    }
    v = v + 1ULL;
  }
  while (hsz > 0u && h->cur_vars < h->max_vars && h->ant_sz > 0ULL && h->oom == 0ULL) {
    u32 f0 = fheap[0];
    hsz = hsz - 1u;
    fpos[f0] = 0xFFFFFFFFu;
    if (hsz > 0u) {
      fheap[0] = fheap[hsz];
      fpos[fheap[0]] = 0u;
      full_fheap_down_fid(fheap, fpos, deg, 0u, hsz);
    }
    u32 fv = f0 >> 1;
    u32 fbit = ((f0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    if ((fl[fv] & FL_ACTIVE) == 0u) { continue; }
    if ((fl[fv] & fbit) == 0u) { continue; }
    if (vals[f0] != (i8)0) { continue; }
    fl[fv] = fl[fv] & (~fbit);
    if (deg[f0] <= 1u) { continue; }
    if (full_bva_try_lit(h, f0, init_cv)) {
      u32 *scr_b = (u32 *)h->scratch_buf;
      u32 *ar_b = (u32 *)h->arena;
      u32 sc_b = full_bva_steps_cap_fid(h->scratch_cap);
      u32 bk = (u32)h->res_sz;
      u64 cur_nl = h->cur_vars << 1;
      u32 qs_idx = bk + 1u;
      while (qs_idx > 0u) {
        qs_idx = qs_idx - 1u;
        u32 factor = scr_b[qs_idx];
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, hsz, cur_nl, factor);
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, hsz, cur_nl, factor ^ 1u);
        u32 ro = scr_b[sc_b + qs_idx];
        u32 qn = scr_b[2u * sc_b + qs_idx];
        u32 qi = 0u;
        while (qi < qn) {
          u32 cw = scr_b[ro + qi];
          if ((cw & PW_BIN_FLAG) != 0u) {
            hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, hsz, cur_nl, cw & PW_LIT_MASK);
          } else {
            u32 csz = ar_b[(u64)cw + 2ULL];
            u32 lj = 0u;
            while (lj < csz) {
              u32 l = ar_b[(u64)cw + 3ULL + (u64)lj];
              if (l != factor) {
                hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, hsz, cur_nl, l);
              }
              lj = lj + 1u;
            }
          }
          qi = qi + 1u;
        }
      }
    }
  }
  u64 end_nlits = h->cur_vars << 1;
  u64 ci = 0ULL;
  while (ci < end_nlits) {
    fheap[ci] = 0u; fpos[ci] = 0u;
    ci = ci + 1ULL;
  }
  if (h->cur_vars > init_cv) {
    u64 cv = h->cur_vars;
    u32 *qn = (u32 *)h->q_next;
    u32 *qs = (u32 *)h->q_stamp;
    u64 p = h->q_first;
    u64 s = 0ULL;
    while (p < cv && s < cv) {
      s = s + 1ULL;
      qs[p] = (u32)s;
      p = (u64)qn[p];
    }
    h->q_cur_stamp = s;
    if (h->q_search_idx < cv) {
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  return 1ULL;
}

u64 full_bve_var_key_m7(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u64 pos = (u64)wvec[((u64)v << 2) + 1ULL];
  u64 neg = (u64)wvec[((u64)v << 2) + 3ULL];
  if (pos > 2000ULL) { pos = 2000ULL; }
  if (neg > 2000ULL) { neg = 2000ULL; }
  u64 base = (4004000ULL + pos + neg) - (pos * neg);
  u64 rel = 0ULL;
  if (h->stable != 0ULL) {
    u64 *sc = (u64 *)h->score;
    rel = sc[v] >> 28;
  } else {
    u32 *qs = (u32 *)h->q_stamp;
    rel = (u64)qs[v];
  }
  if (rel > (1ULL << 61)) { rel = 1ULL << 61; }
  return ((1ULL << 62) + base) - rel;
}

u64 full_eliminate_m7(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    u64 delta = full_scale_delta(h, 500ULL * loge * loge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = dticks / 10ULL;
  u64 fs = full_forward_sub_m7(h, fbud);
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
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 1024ULL)) {
    u64 fact_bud = full_min_u64(initial ? 128ULL : (16ULL + (dticks >> 10)), 256ULL);
    u64 saved_eb = h->elim_bound;
    h->elim_bound = 0ULL;
    full_factor(h, fact_bud);
    h->elim_bound = saved_eb;
  }
  u64 rr = full_rebuild_watches(h);
  h->search_ticks = saved_st;
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_eliminate_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
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
  u64 fbase = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 fbud = fbase / 10ULL;
  u64 fs = full_forward_sub_m7(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) {
    full_rebuild_watches(h);
    return 20ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 base_t = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 res_lim = base_t / 10ULL;
  u64 res = full_elim_bve_m7(h, res_lim);
  u64 rr = full_rebuild_watches(h);
  h->search_ticks = saved_st;
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  h->probings = h->probings + 1ULL;
  if (!initial) {
    u64 parg = (h->probings > (~0ULL) - 9ULL) ? (~0ULL) : (h->probings + 9ULL);
    u64 qlog = full_log10_q16_m7(parg);
    u64 pc = (h->probings > 100000000ULL) ? 100000000ULL : h->probings;
    u64 nlogp = (100ULL * pc * qlog) >> 16;
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
  }
  u64 max_r = initial ? 1ULL : 2ULL;
  u64 round = 0ULL;
  while (round < max_r) {
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
  u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
  if (h->unassigned > 0ULL && fr <= fe4 && full_enter_dense(h)) {
    u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
    m6_hdr_set_watermark(h, 1ULL, nfact);
    u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  h->search_ticks = saved_st;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}

u64 full_search_m6(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  u64 reordered = 0ULL;
  u64 last_reduce_cfl = 0xFFFFFFFFFFFFFFFFULL;
  u64 lkr = full_lucky_late_m7(h);
  if (lkr == 10ULL || lkr == 20ULL) { return lkr; }
  h->search_ticks = 0ULL; h->mode_saved_ticks = 0ULL;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, 0ULL); h->fwd_str_cnt = 0ULL;
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
    } else if (h->unassigned == 0ULL) {
      return 10ULL;
    } else if (h->fuel == 0ULL) {
      return 0ULL;
    } else if (h->conflicts >= h->reduce_limit) {
      last_reduce_cfl = h->conflicts;
      h->fuel = h->fuel - 1ULL;
      u64 rr = full_reduce_m6(h, false);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
    } else if ((h->stable == 0ULL) ? (h->conflicts >= h->mode_confl_lim)
                                   : (h->search_ticks >= h->mode_tick_lim)) {
      h->fuel = h->fuel - 1ULL;
      full_switch_mode_m7(h);
    } else if (full_restart_due(h) != 0ULL) {
      h->fuel = h->fuel - 1ULL;
      full_restart(h);
    } else if (h->cur_level == 0ULL && h->conflicts >= reorder_limit) {
      reordered = reordered + 1ULL;
      reorder_limit = h->conflicts + 10000ULL * reordered;
      h->fuel = h->fuel - 1ULL;
      full_reorder_m6(h, 256ULL);
    } else if (h->stable != 0ULL && h->conflicts >= h->rephase_limit) {
      h->fuel = h->fuel - 1ULL;
      full_rephase(h);
    } else if (h->conflicts != last_reduce_cfl && h->conflicts > h->probe_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, true, false);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else if (h->conflicts != last_reduce_cfl && h->conflicts >= h->elim_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, false, true);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else {
      if (m6_hdr_decide_fid(h) == 0ULL) {
        return (h->unassigned == 0ULL) ? 10ULL : 0ULL;
      }
    }
  }
}
"

/-! ## 1. Exported `Fn` Handles, Replacement / Helper Tables & Spliced `501`-Fn Module -/

def fidStep7CalcMaxVFn : Fn :=
  ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], full_calc_max_v_body⟩
def fidStep7CalcScrCapM5Fn : Fn :=
  ⟨"full_calc_scr_cap_m5", [i64], [i64], full_calc_scr_cap_m5_body⟩
def fidStep7M6HdrInitFn : Fn :=
  ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
def fidStep7ReduceFn : Fn :=
  ⟨"full_reduce", [i64, .bool], [i64], full_reduce_body⟩
def fidStep7ReduceM6Fn : Fn :=
  ⟨"full_reduce_m6", [i64, .bool], [i64], full_reduce_m6_body⟩
def fidStep7BumpAnalyzedM6HdrFn : Fn :=
  ⟨"full_bump_analyzed_m6_hdr", [i64], [], full_bump_analyzed_m6_hdr_body⟩
def fidStep7SortTmpFn : Fn :=
  ⟨"full_sort_tmp", [i64], [], full_sort_tmp_body⟩
def fidStep7LearnClauseFn : Fn :=
  ⟨"full_learn_clause", [i64, i64], [i64], full_learn_clause_body⟩
def fidStep7WalkCbInvM7Fn : Fn :=
  ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], full_walk_cb_inv_m7_body⟩
def fidStep7VivifyTierM6HdrFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_body⟩
def fidStep7VivifyM6HdrFn : Fn :=
  ⟨"full_vivify_m6_hdr", [i64], [i64], full_vivify_m6_hdr_body⟩
def fidStep7SortBinWatchesFn : Fn :=
  ⟨"full_sort_bin_watches_fid", [i64], [], full_sort_bin_watches_fid_body⟩
def fidStep7RebuildWatchesFn : Fn :=
  ⟨"full_rebuild_watches", [i64], [i64], full_rebuild_watches_body⟩
def fidStep7BvaCommitFn : Fn :=
  ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_body⟩
def fidStep7BvaTryLitFn : Fn :=
  ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], full_bva_try_lit_body⟩
def fidStep7BvaUpdLitFn : Fn :=
  ⟨"full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32], full_bva_upd_lit_fid_body⟩
def fidStep7FactorFn : Fn :=
  ⟨"full_factor", [i64, i64], [i64], full_factor_body⟩
def fidStep7BveVarKeyM7Fn : Fn :=
  ⟨"full_bve_var_key_m7", [i64, i32], [i64], full_bve_var_key_m7_body⟩
def fidStep7EliminateM7Fn : Fn :=
  ⟨"full_eliminate_m7", [i64, .bool], [i64], full_eliminate_m7_body⟩
def fidStep7EliminateM6Fn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m6_body⟩
def fidStep7ProbeM6Fn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩
def fidStep7SearchM6Fn : Fn :=
  ⟨"full_search_m6", [i64], [i64], full_search_m6_body⟩

/-- `20` pure-C0 Step-7 replacement functions matching `fid_v8_pure_c0.diff`. -/
def fidStep7Repls : List Fn :=
  [ fidStep7CalcMaxVFn, fidStep7CalcScrCapM5Fn, fidStep7M6HdrInitFn
  , fidStep7ReduceFn, fidStep7ReduceM6Fn, fidStep7BumpAnalyzedM6HdrFn
  , fidStep7SortTmpFn, fidStep7LearnClauseFn, fidStep7WalkCbInvM7Fn
  , fidStep7VivifyTierM6HdrFn, fidStep7VivifyM6HdrFn, fidStep7RebuildWatchesFn
  , fidStep7BvaCommitFn, fidStep7BvaTryLitFn, fidStep7FactorFn
  , fidStep7BveVarKeyM7Fn, fidStep7EliminateM7Fn, fidStep7EliminateM6Fn
  , fidStep7ProbeM6Fn, fidStep7SearchM6Fn ]

/-- `2` new Step-7 helper functions (`full_sort_bin_watches_fid`, `full_bva_upd_lit_fid`). -/
def fidStep7Helpers : List Fn :=
  [ fidStep7SortBinWatchesFn, fidStep7BvaUpdLitFn ]

/-- Anchor insertions for `PatchModule`: `full_sort_bin_watches_fid` before
`full_rebuild_watches`, and `full_bva_upd_lit_fid` before `full_factor`. -/
def fidStep7Befores : List (Sym × List Fn) :=
  [ ("full_rebuild_watches", [fidStep7SortBinWatchesFn])
  , ("full_factor", [fidStep7BvaUpdLitFn]) ]

/-- Complete `22`-function Step-7 delta (`20` replacements + `2` new helpers). -/
def fidStep7Fns : List Fn :=
  fidStep7Repls ++ fidStep7Helpers

/-- Ordered `501`-fn Step-7 `KissatFidelity` function list (`fidFns` + `fidStep7Repls` +
`fidStep7Befores`). -/
def fidStep7ModuleFns : List Fn :=
  patchFns fidStep7Repls fidStep7Befores fidFns

/-- Closed `501`-function Gate-1 Step-7 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep7Module : LeanQbe.T.Module :=
  { fidModule with fns := fidStep7ModuleFns }

theorem fidStep7ModuleFns_eq : fidStep7Module.fns = fidStep7ModuleFns :=
  rfl

/-! ## 2. Function Well-Formedness (`Func.Wf`), Acyclicity & 4-ISA Guards -/

theorem full_calc_max_v_step7_wf : Func.Wf fidStep7CalcMaxVFn.body := by t_wf_reify
theorem full_calc_scr_cap_m5_step7_wf : Func.Wf fidStep7CalcScrCapM5Fn.body := by t_wf_reify
theorem m6_hdr_init_step7_wf : Func.Wf fidStep7M6HdrInitFn.body := by t_wf_reify
theorem full_reduce_step7_wf : Func.Wf fidStep7ReduceFn.body := by t_wf_reify
theorem full_reduce_m6_step7_wf : Func.Wf fidStep7ReduceM6Fn.body := by t_wf_reify
theorem full_bump_analyzed_m6_hdr_step7_wf :
    Func.Wf fidStep7BumpAnalyzedM6HdrFn.body := by
  t_wf_reify
theorem full_sort_tmp_step7_wf : Func.Wf fidStep7SortTmpFn.body := by t_wf_reify
theorem full_learn_clause_step7_wf : Func.Wf fidStep7LearnClauseFn.body := by t_wf_reify
theorem full_walk_cb_inv_m7_step7_wf : Func.Wf fidStep7WalkCbInvM7Fn.body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_step7_wf : Func.Wf fidStep7VivifyTierM6HdrFn.body := by t_wf_reify
theorem full_vivify_m6_hdr_step7_wf : Func.Wf fidStep7VivifyM6HdrFn.body := by t_wf_reify
theorem full_sort_bin_watches_fid_step7_wf : Func.Wf fidStep7SortBinWatchesFn.body := by t_wf_reify
theorem full_rebuild_watches_step7_wf : Func.Wf fidStep7RebuildWatchesFn.body := by t_wf_reify
theorem full_bva_commit_step7_wf : Func.Wf fidStep7BvaCommitFn.body := by t_wf_reify
theorem full_bva_try_lit_step7_wf : Func.Wf fidStep7BvaTryLitFn.body := by t_wf_reify
theorem full_bva_upd_lit_fid_step7_wf : Func.Wf fidStep7BvaUpdLitFn.body := by t_wf_reify
theorem full_factor_step7_wf : Func.Wf fidStep7FactorFn.body := by t_wf_reify
theorem full_bve_var_key_m7_step7_wf : Func.Wf fidStep7BveVarKeyM7Fn.body := by t_wf_reify
theorem full_eliminate_m7_step7_wf : Func.Wf fidStep7EliminateM7Fn.body := by t_wf_reify
theorem full_eliminate_m6_step7_wf : Func.Wf fidStep7EliminateM6Fn.body := by t_wf_reify
theorem full_probe_m6_step7_wf : Func.Wf fidStep7ProbeM6Fn.body := by t_wf_reify
theorem full_search_m6_step7_wf : Func.Wf fidStep7SearchM6Fn.body := by t_wf_reify

theorem fidStep7Helpers_wf : ∀ f ∈ fidStep7Helpers, f.Wf := by
  intro f hf
  simp only [fidStep7Helpers, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact full_sort_bin_watches_fid_step7_wf
  · exact full_bva_upd_lit_fid_step7_wf

theorem fidStep7Befores_wf : ∀ h ∈ fidStep7Befores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep7Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hh
  exact fidStep7Helpers_wf h hh

theorem fidStep7Repls_wf : ∀ f ∈ fidStep7Repls, f.Wf := by
  intro f hf
  simp only [fidStep7Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_calc_max_v_step7_wf
  · exact full_calc_scr_cap_m5_step7_wf
  · exact m6_hdr_init_step7_wf
  · exact full_reduce_step7_wf
  · exact full_reduce_m6_step7_wf
  · exact full_bump_analyzed_m6_hdr_step7_wf
  · exact full_sort_tmp_step7_wf
  · exact full_learn_clause_step7_wf
  · exact full_walk_cb_inv_m7_step7_wf
  · exact full_vivify_tier_m6_hdr_step7_wf
  · exact full_vivify_m6_hdr_step7_wf
  · exact full_rebuild_watches_step7_wf
  · exact full_bva_commit_step7_wf
  · exact full_bva_try_lit_step7_wf
  · exact full_factor_step7_wf
  · exact full_bve_var_key_m7_step7_wf
  · exact full_eliminate_m7_step7_wf
  · exact full_eliminate_m6_step7_wf
  · exact full_probe_m6_step7_wf
  · exact full_search_m6_step7_wf

theorem fidStep7Fns_wf : ∀ f ∈ fidStep7Fns, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact fidStep7Repls_wf f h1
  · exact fidStep7Helpers_wf f h2

theorem fidStep7Module_wf : ∀ f ∈ fidStep7Module.fns, f.Wf :=
  patchFns_wf fidModule_wf fidStep7Repls_wf fidStep7Befores_wf

theorem fidStep7_noExit : fidStep7Module.exits = [] :=
  fid_noExit

#guard fidStep7ModuleFns.length == 501
#guard (fidStep7ModuleFns.map Fn.name).eraseDups.length == 501
#guard fidStep7Module.checkAcyclic == true
#guard fidStep7Module.externs.isEmpty && fidStep7Module.exits.isEmpty
#guard (fidStep7ModuleFns.map Fn.name).contains "full_sort_bin_watches_fid"
#guard (fidStep7ModuleFns.map Fn.name).contains "full_bva_upd_lit_fid"
#guard !(fidStep7ModuleFns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep7ModuleFns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep7ModuleFns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep7ModuleFns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep7ModuleFns.map Fn.name).contains "full_prelearn_m8"
#guard (PrintCpp.ppTModule fidStep7Module).isOk
#guard (PrintQbe.module fidStep7Module).isOk
#guard (PrintCpp.ppModule (fidStep7Fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep7Fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep7Fns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep7Fns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep7Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep7Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep7Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep7Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

end LeanQbe.T.Examples.Kissat.FullFidelityStep7

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 9 Parity & Hot-Path Closures (`FullFidelityStep9`)

Pure C0 parity & optimization layer (`11` replacements + `3` inserted helpers = `504` fns,
`0` externs, `0` exits) atop Step 8 `fidStep8Module` (`501` fns):
1. `S9-0`: Pack `full_bva_upd_lit_fid` from 7 args to 6 args (`(hsz << 32) | tl`) and update
   its `4` call sites in `full_factor` for SysV x64 & Arm64 6-arg ABI compliance.
2. `S9-P0.1`: Upstream `compactlim=10` (`dead * 10 > cv`) in `full_compact_needed`, scan
   `full_reduce_m6` from `h->first_reducible`, skip zero-garbage non-forced sweeps, drop
   redundant pre-compact `full_arena_sweep` loop in `full_compact_flush`, and fuse `PH_RSN`
   prefix clearing into the single `[0..fp)` scan in `full_arena_sweep_m6`.
3. `S9-P0.2`: Skip `enter_dense`/`rebuild_watches` in `full_probe_m6` when congruence and sweep
   are both delayed, split `full_rebuild_watches_nosort_fid` so `full_sort_bin_watches_fid`
   runs once at final probe exit, and align inproc/initial stages with `probe.c:33-67`, plus
   entry clearing of `tarjan_mark[0..cv]` in `full_congruence_dense`.
4. `S9-P1.1` & `S9-P1.2`: Split cold realloc fallback (`full_prop_flush_slow_fid`) out of
   `full_prop_flush_del_fid` so fast-path `wlen`/`wusable` stay in registers, and restore
   alignment-guarded `u64` copy + `full_fill_u64_m7` `cnt` wipe in `full_bva_commit`.
5. Experimental `S9-P0.3` (`MemShrinkV5` + `cand = 32768` + `scr_cap = 8M`) is factored into
   `LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.PatchModule

kissat_c0! fidStep9 "
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
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u
#define FL_SWEEP              1024u
#define PH_GLUE_MASK          0x7FFFFu
#define PH_GARB               0x00080000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u
#define PH_SHRK               0x00800000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu
#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern u64 full_flush_trail(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_arena_sweep(FullHdr *h);
extern void full_sweep_bins_range_m6(FullHdr *h, u64 start);
extern u64 full_sweep_copy(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root);
extern void full_move_red_end_m6(FullHdr *h, u64 first_red, u64 dst);
extern bool full_rewatch_range_m6(FullHdr *h, u64 start, u64 dst);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u64 full_isqrt(u64 x);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_log10_q16_m7(u64 x);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void full_sort_bin_watches_fid(FullHdr *h);
extern u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim);
extern u64 full_cong_find_units_equivs(FullHdr *h);
extern u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim);
extern u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap, u64 tick_lim);
extern u64 full_cong_worklist(FullHdr *h, u64 g_len, u64 ctrl_off, u64 tick_lim);
extern u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim);
extern u32 full_bva_steps_cap_fid(u64 scap);
extern void full_wstack_defrag(FullHdr *h);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern u32 full_bva_count_lit_deg_fid(FullHdr *h, u32 tl);
extern void full_fheap_up_fid(u32 *hp, u32 *ps, u32 *deg, u32 p);
extern void full_fheap_down_fid(u32 *hp, u32 *ps, u32 *deg, u32 p, u32 n);
extern void full_bva_connect_clauses_fid(FullHdr *h);
extern bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv);
extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64 full_substitute(FullHdr *h);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);

void full_fill_u64_m7(u64 *dst, u64 n, u64 val) {
  u64 i = 0ULL;
  while (i + 4ULL <= n) {
    dst[i] = val;
    dst[i + 1ULL] = val;
    dst[i + 2ULL] = val;
    dst[i + 3ULL] = val;
    i = i + 4ULL;
  }
  while (i < n) {
    dst[i] = val;
    i = i + 1ULL;
  }
}

bool full_prop_flush_slow_fid(FullHdr *h, u64 j, u64 di) {
  u32 *del = (u32 *)h->delayed;
  if (!full_watch_push(h, del[j], del[j + 1ULL], del[j + 2ULL], 2u)) { return false; }
  j = j + 3ULL;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  while (j < di) {
    u32 rw = del[j];
    u32 ow = del[j + 1ULL];
    u32 cr = del[j + 2ULL];
    u64 wlen = h->wlen;
    u64 wu = h->wusable;
    u64 rw64 = (u64)rw << 1;
    u64 roff = (u64)wvec[rw64];
    u64 rsz = (u64)wvec[rw64 + 1ULL];
    if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
        wstk[roff + rsz] == 0xFFFFFFFFu &&
        wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
      wstk[roff + rsz] = ow;
      wstk[roff + rsz + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      if (wu >= 2ULL) { h->wusable = wu - 2ULL; }
    } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      h->wlen = wlen + 2ULL;
    } else if (rsz == 0ULL && wlen > 0ULL && wlen + 2ULL <= wcap) {
      wvec[rw64] = (u32)wlen;
      wvec[rw64 + 1ULL] = 2u;
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      h->wlen = wlen + 2ULL;
    } else {
      if (!full_watch_push(h, rw, ow, cr, 2u)) { return false; }
      wstk = (u32 *)h->watch_stk;
    }
    j = j + 3ULL;
  }
  return true;
}

bool full_prop_flush_del_fid(FullHdr *h, u64 di) {
  u32 *del = (u32 *)h->delayed;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  u64 wlen = h->wlen;
  u64 wu = h->wusable;
  u64 j = 0ULL;
  while (j < di) {
    u32 rw = del[j];
    u32 ow = del[j + 1ULL];
    u32 cr = del[j + 2ULL];
    u64 rw64 = (u64)rw << 1;
    u64 roff = (u64)wvec[rw64];
    u64 rsz = (u64)wvec[rw64 + 1ULL];
    if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
        wstk[roff + rsz] == 0xFFFFFFFFu &&
        wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
      wstk[roff + rsz] = ow;
      wstk[roff + rsz + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      if (wu >= 2ULL) { wu = wu - 2ULL; }
    } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      wlen = wlen + 2ULL;
    } else if (rsz == 0ULL && wlen > 0ULL && wlen + 2ULL <= wcap) {
      wvec[rw64] = (u32)wlen;
      wvec[rw64 + 1ULL] = 2u;
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wlen = wlen + 2ULL;
    } else {
      h->wlen = wlen;
      h->wusable = wu;
      return full_prop_flush_slow_fid(h, j, di);
    }
    j = j + 3ULL;
  }
  h->wlen = wlen;
  h->wusable = wu;
  return true;
}

u64 full_arena_sweep_m6(FullHdr *h) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  bool at_root = (h->cur_level == 0ULL);
  u64 start = 0ULL;
  u64 pre_irred = 0ULL;
  if (!at_root && h->unflushed == 0ULL && h->first_reducible > 0ULL &&
      h->first_reducible < alen) {
    u64 fp = h->first_reducible;
    u64 p = 0ULL;
    u64 cnt = 0ULL;
    bool pre_ok = true;
    while (p < fp) {
      if (p + 3ULL > fp) { pre_ok = false; break; }
      u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
      if ((hdr & (PH_GARB | PH_SHRK | PH_RED)) != 0u || sz < 3u ||
          p + 3ULL + (u64)sz > fp) {
        pre_ok = false; break;
      }
      p = p + 3ULL + (u64)sz;
      cnt = cnt + 1ULL;
    }
    if (pre_ok && p == fp) {
      u64 cp0 = 0ULL;
      while (cp0 < fp) {
        u32 hdr = ar[cp0]; u32 sz = ar[cp0 + 2ULL];
        if ((hdr & PH_RSN) != 0u) { ar[cp0] = hdr & (~PH_RSN); }
        cp0 = cp0 + 3ULL + (u64)sz;
      }
      start = fp;
      pre_irred = cnt;
    }
  }
  full_sweep_bins_range_m6(h, start);
  u64 src = start;
  u64 dst = start;
  u64 first_red = 0xFFFFFFFFULL;
  u64 irred = pre_irred;
  u64 redd = 0ULL;
  bool has_irred_after_red = false;
  bool unsat = false;
  bool new_unit = false;
  while (src < alen) {
    if (src + 3ULL > alen) { break; }
    u32 hdr = ar[src]; u32 old_sz = ar[src + 2ULL];
    u64 nsrc = (u64)full_arena_next(h, (u32)src);
    if ((hdr & PH_GARB) != 0u || old_sz < 3u ||
        src + 3ULL + (u64)old_sz > alen) {
      src = nsrc; continue;
    }
    u64 st = full_sweep_copy(h, src, dst, old_sz, at_root);
    if (st == 0xFFFFFFFEULL) { unsat = true; break; }
    if (st == 0xFFFFFFFDULL) { break; }
    if (st == 1ULL) { new_unit = true; src = nsrc; continue; }
    if (st == 0xFFFFFFFFULL) { src = nsrc; continue; }
    u32 new_sz = (u32)st;
    u32 nhdr = hdr & (~(PH_SHRK | PH_RSN));
    ar[dst] = nhdr;
    ar[dst + 1ULL] = 2u;
    ar[dst + 2ULL] = new_sz;
    if ((hdr & PH_RSN) != 0u) {
      u32 i = 0u;
      while (i < new_sz) {
        u32 lit = ar[dst + 3ULL + (u64)i]; u32 v = lit >> 1;
        if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
          rsns[v] = (u32)dst;
          if (!at_root && (first_red != 0xFFFFFFFFULL || (hdr & PH_RED) != 0u)) {
            ar[dst] = nhdr | PH_RSN;
          }
          break;
        }
        i = i + 1u;
      }
    }
    if ((hdr & PH_RED) != 0u) {
      if (first_red == 0xFFFFFFFFULL) { first_red = dst; }
      redd = redd + 1ULL;
    } else {
      if (first_red != 0xFFFFFFFFULL) { has_irred_after_red = true; }
      irred = irred + 1ULL;
    }
    dst = dst + 3ULL + (u64)new_sz;
    src = nsrc;
  }
  if (!unsat && h->oom == 0ULL && has_irred_after_red && first_red < dst) {
    full_move_red_end_m6(h, first_red, dst);
  } else {
    h->first_reducible = first_red;
    if (!at_root && first_red < dst) {
      u64 cp = first_red;
      while (cp < dst) {
        u32 sz = ar[cp + 2ULL];
        ar[cp] = ar[cp] & (~PH_RSN);
        cp = cp + 3ULL + (u64)sz;
      }
    }
  }
  h->arena_len = dst;
  h->arena_garbage = 0ULL;
  h->num_irred = irred;
  h->num_redundant = redd;
  u32 *ll = (u32 *)h->last_learned;
  u64 li = 0ULL;
  while (li < 16ULL) { ll[li] = 0xFFFFFFFFu; li = li + 1ULL; }
  if (unsat) { return 2ULL; }
  if (h->oom != 0ULL) { return 3ULL; }
  if (!full_rewatch_range_m6(h, start, dst)) { return 3ULL; }
  return new_unit ? 1ULL : 0ULL;
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
    if (force || (h->unflushed == 0ULL && (h->arena_garbage > 0ULL || h->cur_level == 0ULL))) {
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

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  h->ant_sz = 0ULL;
  if (full_cong_extract_binaries(h, tick_lim) == 20ULL) { h->ant_sz = 0ULL; return 20ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  if (full_cong_find_units_equivs(h) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  u64 g_cap = h->scratch_cap >> 1;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = full_cong_extract(h, g_cap, tick_lim);
  if (g_len <= g_cap) {
    g_len = (u64)full_cong_extract_ite_all_m7(h, (u32)g_len, (u32)g_cap, tick_lim);
  }
  if (g_len > 0ULL && g_len <= g_cap) {
    u64 free_scr = h->scratch_cap - g_len;
    u64 ht_max = 64ULL;
    while (ht_max * 4ULL <= free_scr && ht_max < 1048576ULL) { ht_max = ht_max << 1; }
    u64 ht_off = h->scratch_cap - ht_max;
    u64 rem_occ = ht_off - g_len;
    u64 occ_bkt = (rem_occ >= 262144ULL) ? 8192ULL : ((rem_occ >= 65536ULL) ? 2048ULL :
      ((rem_occ >= 16384ULL) ? 512ULL : ((rem_occ >= 2048ULL) ? 256ULL :
      ((rem_occ >= 256ULL) ? 32ULL : 16ULL))));
    u64 bkt_off = ht_off - occ_bkt;
    u64 inq_off = bkt_off - occ_bkt;
    u64 q_off = inq_off - occ_bkt;
    u64 ctrl_off = q_off - 8ULL;
    u64 ht_sz = 64ULL;
    while (ht_sz < g_len && (ht_sz << 1) <= ht_max) { ht_sz = ht_sz << 1; }
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

u64 full_rebuild_watches_nosort_fid(FullHdr *h) {
  h->dense_mode = 0ULL;
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    if (sr == 0ULL) { break; }
  }
  return 1ULL;
}

u64 full_rebuild_watches(FullHdr *h) {
  u64 rr = full_rebuild_watches_nosort_fid(h);
  if (rr == 1ULL) { full_sort_bin_watches_fid(h); }
  return rr;
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
  bool defrag_dirty = false;
  if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); defrag_dirty = true; }
    if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
      if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
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
  u64 garb_add = 0ULL;
  u64 irred_add = 0ULL;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    if (!defrag_dirty) {
      u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
      u64 sza = (u64)wvec[((u64)fresh << 1) + 1ULL];
      u64 szb = (u64)wvec[((u64)fs << 1) + 1ULL];
      u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
      u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
      if (wl_c == 0ULL || fresh == fs || wc_c < wl_c || wl_c + na + nb > wc_c ||
          ((wl_c + na) * 4ULL >= wc_c * 3ULL && (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
        defrag_dirty = true;
      }
    }
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
      if (!defrag_dirty) {
        u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
        u32 nf = fresh ^ 1u;
        u64 sza = (u64)wvec[((u64)nf << 1) + 1ULL];
        u64 szb = (u64)wvec[((u64)q << 1) + 1ULL];
        u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
        u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
        if (wl_c == 0ULL || nf == q || wc_c < wl_c || wl_c + na + nb > wc_c ||
            ((wl_c + na) * 4ULL >= wc_c * 3ULL && (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      u64 br = full_add_bin(h, fresh ^ 1u, q);
      fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_N;
      fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      if (!defrag_dirty) {
        u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
        u32 nf = fresh ^ 1u;
        u64 sz0 = (u64)wvec[((u64)nf << 1) + 1ULL];
        u64 sum_nw = (sz0 == 0ULL) ? 2ULL : ((sz0 == 1ULL) ? 3ULL : (sz0 << 1));
        u32 dj = 0u;
        while (dj < csz) {
          u32 dl = ar[(u64)c_top + 3ULL + (u64)dj];
          if (dl != flit) {
            u64 szl = (u64)wvec[((u64)dl << 1) + 1ULL];
            sum_nw = sum_nw + ((szl == 0ULL) ? 2ULL : ((szl == 1ULL) ? 3ULL : (szl << 1)));
          }
          dj = dj + 1u;
        }
        if (wl_c == 0ULL || wc_c < wl_c || wl_c + sum_nw > wc_c ||
            ((wl_c + sum_nw) * 4ULL >= wc_c * 3ULL &&
             (wu_c + sum_nw) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr == 0xFFFFFFFFULL) { ok = false; break; }
      u32 *dst_cl = ar + (ncr + 3ULL);
      if ((ncr & 1ULL) != 0ULL) {
        j = 0u;
        while (j + 2u <= tk) {
          u64 *dp = (u64 *)(dst_cl + (u64)j);
          u64 *sp = (u64 *)(tmp + (u64)j);
          dp[0] = sp[0];
          j = j + 2u;
        }
        if (j < tk) { dst_cl[j] = tmp[j]; }
      } else {
        j = 0u;
        while (j < tk) { dst_cl[j] = tmp[j]; j = j + 1u; }
      }
      j = 0u;
      while (j < tk) {
        if (!full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u)) {
          u32 uk = 0u;
          while (uk < j) { full_unwatch_large(h, tmp[uk], (u32)ncr); uk = uk + 1u; }
          ar[ncr] = ar[ncr] | PH_GARB;
          garb_add = garb_add + 3ULL + (u64)tk;
          ok = false; break;
        }
        u32 tv = tmp[j] >> 1;
        fl[tv] = fl[tv] | (((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        j = j + 1u;
      }
      if (ok) { irred_add = irred_add + 1ULL; }
    }
    m = m + 1u;
  }
  if (!ok) {
    if (garb_add > 0ULL) { h->arena_garbage = h->arena_garbage + garb_add; }
    if (irred_add > 0ULL) { h->num_irred = h->num_irred + irred_add; }
    if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
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
        ar[cs] = ar[cs] | PH_GARB;
        garb_add = garb_add + 3ULL + (u64)csz;
      }
      m = m + 1u;
    }
  }
  if (garb_add > 0ULL) { h->arena_garbage = h->arena_garbage + garb_add; }
  if (irred_add > 0ULL) { h->num_irred = h->num_irred + irred_add; }
  if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
  deg[fresh] = dm; deg[fresh ^ 1u] = mn;
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

u32 full_bva_upd_lit_fid(FullHdr *h, u32 *fheap, u32 *fpos,
    u32 *deg, u64 cur_nl, u64 hsz_tl) {
  u32 hsz = (u32)(hsz_tl >> 32);
  u32 tl = (u32)(hsz_tl & 0xFFFFFFFFULL);
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
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
          ((u64)hsz << 32) | (u64)factor);
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
          ((u64)hsz << 32) | (u64)(factor ^ 1u));
        u32 ro = scr_b[sc_b + qs_idx];
        u32 qn = scr_b[2u * sc_b + qs_idx];
        u32 qi = 0u;
        while (qi < qn) {
          u32 cw = scr_b[ro + qi];
          if ((cw & PW_BIN_FLAG) != 0u) {
            hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
              ((u64)hsz << 32) | (u64)(cw & PW_LIT_MASK));
          } else {
            u32 csz = ar_b[(u64)cw + 2ULL];
            u32 lj = 0u;
            while (lj < csz) {
              u32 l = ar_b[(u64)cw + 3ULL + (u64)lj];
              if (l != factor) {
                hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
                  ((u64)hsz << 32) | (u64)l);
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

bool full_compact_needed(FullHdr *h) {
  if (h->cur_level != 0ULL || h->dense_mode != 0ULL) { return false; }
  u64 cv = h->cur_vars;
  if (cv < 128ULL || cv <= h->unassigned) { return false; }
  u64 dead = cv - h->unassigned;
  return (dead * 10ULL > cv);
}

u64 full_compact_flush(FullHdr *h) {
  return full_flush_trail(h);
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
  bool bin_dirty = false;
  if (initial) {
    bool subst_at_end = true;
    if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
      if (full_enter_dense(h)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        bin_dirty = true;
        if (ca > cb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
      if (full_enter_dense(h)) {
        u64 sb = h->sweep_cnt;
        if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 sa = h->sweep_cnt;
        if (sa > sb && (sa - sb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        bin_dirty = true;
        if (sa > sb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (subst_at_end && h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    u64 round = 0ULL;
    while (round < 2ULL) {
      u64 before_unass = h->unassigned;
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        if (full_enter_dense(h)) {
          u64 cb = h->cong_cnt;
          if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 ca = h->cong_cnt;
          if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          bin_dirty = true;
        } else if (h->inconsistent != 0ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (full_vivify_m6_hdr(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
        if (full_enter_dense(h)) {
          u64 sb = h->sweep_cnt;
          if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (h->sweep_cnt > sb && (h->sweep_cnt - sb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          bin_dirty = true;
        } else if (h->inconsistent != 0ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 tr_lim = (dticks / 50ULL) + 100000ULL;
      if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->unassigned >= before_unass) { break; }
      round = round + 1ULL;
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
    if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    bin_dirty = true;
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  if (bin_dirty) { full_sort_bin_watches_fid(h); }
  h->search_ticks = saved_st;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}
"

/-! ## 1. Canonical `Fn` Handles, Replacement / Insertion Lists & Module (`504` fns) -/

def fidStep9FillU64Fn : Fn :=
  ⟨"full_fill_u64_m7", [i64, i64, i64], [], full_fill_u64_m7_body⟩

def fidStep9PropFlushSlowFn : Fn :=
  ⟨"full_prop_flush_slow_fid", [i64, i64, i64], [.bool], full_prop_flush_slow_fid_body⟩

def fidStep9PropFlushDelFn : Fn :=
  ⟨"full_prop_flush_del_fid", [i64, i64], [.bool], full_prop_flush_del_fid_body⟩

def fidStep9ArenaSweepM6Fn : Fn :=
  ⟨"full_arena_sweep_m6", [i64], [i64], full_arena_sweep_m6_body⟩

def fidStep9ReduceM6Fn : Fn :=
  ⟨"full_reduce_m6", [i64, .bool], [i64], full_reduce_m6_body⟩

def fidStep9CongruenceDenseFn : Fn :=
  ⟨"full_congruence_dense", [i64, i64], [i64], full_congruence_dense_body⟩

def fidStep9RebuildWatchesNosortFn : Fn :=
  ⟨"full_rebuild_watches_nosort_fid", [i64], [i64], full_rebuild_watches_nosort_fid_body⟩

def fidStep9RebuildWatchesFn : Fn :=
  ⟨"full_rebuild_watches", [i64], [i64], full_rebuild_watches_body⟩

def fidStep9BvaCommitFn : Fn :=
  ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_body⟩

def fidStep9BvaUpdLitFn : Fn :=
  ⟨"full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32], full_bva_upd_lit_fid_body⟩

def fidStep9FactorFn : Fn :=
  ⟨"full_factor", [i64, i64], [i64], full_factor_body⟩

def fidStep9CompactNeededFn : Fn :=
  ⟨"full_compact_needed", [i64], [.bool], full_compact_needed_body⟩

def fidStep9CompactFlushFn : Fn :=
  ⟨"full_compact_flush", [i64], [i64], full_compact_flush_body⟩

def fidStep9ProbeM6Fn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩

/-- Exact `11`-function non-MemShrink Step-9 replacement list over `fidStep8Fns`. -/
def fidStep9Repls : List Fn :=
  [ fidStep9PropFlushDelFn
  , fidStep9ArenaSweepM6Fn
  , fidStep9ReduceM6Fn
  , fidStep9CongruenceDenseFn
  , fidStep9RebuildWatchesFn
  , fidStep9BvaCommitFn
  , fidStep9BvaUpdLitFn
  , fidStep9FactorFn
  , fidStep9CompactNeededFn
  , fidStep9CompactFlushFn
  , fidStep9ProbeM6Fn ]

/-- Ordered helper insertions (`+3` helpers, net `501 -> 504` functions). -/
def fidStep9Befores : List (Sym × List Fn) :=
  [ ("full_zero_tables1", [fidStep9FillU64Fn])
  , ("full_prop_flush_del_fid", [fidStep9PropFlushSlowFn])
  , ("full_rebuild_watches", [fidStep9RebuildWatchesNosortFn]) ]

/-- Ordered `504`-fn Step-9 `KissatFidelity` function list (`patchFns` over `fidStep8Fns`). -/
def fidStep9ModuleFns : List Fn :=
  patchFns fidStep9Repls fidStep9Befores fidStep8Fns

/-- Closed `504`-function Gate-1 Step-9 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep9Module : LeanQbe.T.Module :=
  { fidStep8Module with fns := fidStep9ModuleFns }

theorem fidStep9ModuleFns_eq : fidStep9Module.fns = fidStep9ModuleFns :=
  rfl

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Exit-Freedom -/

theorem full_fill_u64_m7_step9_wf : Func.Wf fidStep9FillU64Fn.body := by t_wf_reify
theorem full_prop_flush_slow_step9_wf : Func.Wf fidStep9PropFlushSlowFn.body := by t_wf_reify
theorem full_prop_flush_del_step9_wf : Func.Wf fidStep9PropFlushDelFn.body := by t_wf_reify
theorem full_arena_sweep_m6_step9_wf : Func.Wf fidStep9ArenaSweepM6Fn.body := by t_wf_reify
theorem full_reduce_m6_step9_wf : Func.Wf fidStep9ReduceM6Fn.body := by t_wf_reify
theorem full_congruence_dense_step9_wf : Func.Wf fidStep9CongruenceDenseFn.body := by t_wf_reify
theorem full_rebuild_watches_nosort_step9_wf :
    Func.Wf fidStep9RebuildWatchesNosortFn.body := by
  t_wf_reify
theorem full_rebuild_watches_step9_wf : Func.Wf fidStep9RebuildWatchesFn.body := by t_wf_reify
theorem full_bva_commit_step9_wf : Func.Wf fidStep9BvaCommitFn.body := by t_wf_reify
theorem full_bva_upd_lit_step9_wf : Func.Wf fidStep9BvaUpdLitFn.body := by t_wf_reify
theorem full_factor_step9_wf : Func.Wf fidStep9FactorFn.body := by t_wf_reify
theorem full_compact_needed_step9_wf : Func.Wf fidStep9CompactNeededFn.body := by t_wf_reify
theorem full_compact_flush_step9_wf : Func.Wf fidStep9CompactFlushFn.body := by t_wf_reify
theorem full_probe_m6_step9_wf : Func.Wf fidStep9ProbeM6Fn.body := by t_wf_reify

theorem fidStep9Befores_wf : ∀ h ∈ fidStep9Befores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep9Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact full_fill_u64_m7_step9_wf
  · exact full_prop_flush_slow_step9_wf
  · exact full_rebuild_watches_nosort_step9_wf

theorem fidStep9Repls_wf : ∀ f ∈ fidStep9Repls, f.Wf := by
  intro f hf
  simp only [fidStep9Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_prop_flush_del_step9_wf
  · exact full_arena_sweep_m6_step9_wf
  · exact full_reduce_m6_step9_wf
  · exact full_congruence_dense_step9_wf
  · exact full_rebuild_watches_step9_wf
  · exact full_bva_commit_step9_wf
  · exact full_bva_upd_lit_step9_wf
  · exact full_factor_step9_wf
  · exact full_compact_needed_step9_wf
  · exact full_compact_flush_step9_wf
  · exact full_probe_m6_step9_wf

theorem fidStep9Module_wf : ∀ f ∈ fidStep9Module.fns, f.Wf :=
  patchFns_wf fidStep8Module_wf fidStep9Repls_wf fidStep9Befores_wf

theorem fidStep9_noExit : fidStep9Module.exits = [] :=
  fidStep8_noExit

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end

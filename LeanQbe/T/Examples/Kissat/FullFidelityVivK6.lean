/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Legal
meta import LeanQbe.T.PrintCpp

/-!
# Kissat Fidelity Vivification, `u64` Copy & Kitten Pointer-Caching (`FullFidelityVivK6`)

Purely additive Class-S C0 module (`0` edits to existing `FullM6*`/`FullM7*`/`FullM8*` files,
`0` `FullHdr` word growth, `0` `M6HdrExt` word growth, `0` beyond-upstream heuristics) closing
three Gate-1 fidelity and hot-loop C0 gaps for `KissatFidelity`:

1. **`GAP-VIV-01/02` (`vivify.c:210-245, 1269-1270, 1405-1458`, `options.h:163-167`):**
   - `full_viv_collect_fid`: stride-1 2-pass unvivified-first collection directly into
     `red_refs[0 ..< h->red_cap)` (3x larger schedule capacity vs static `h->red_cap / 3ULL`).
   - `full_viv_count_fid` & `full_viv_sort_fid`: dynamic key-storage Shell sort over
     `red_refs[0 ..< bn)` using `red_refs[bn ..< 3*bn)` (2 keys `(k0, k1)` when `3*bn <= red_cap`),
     `scratch_buf[0 ..< 2*bn)` (2 keys when `2*bn <= scratch_cap`), `red_refs[bn ..< 2*bn)`
     (1 key `k0`, matching `vivify.c:136` `COUNTREF_COUNTS = 1`, when `2*bn <= red_cap`), or
     untruncated unvivified-first order on extreme clause databases.
   - `full_vivify_tier_m6_hdr_fid` (`"full_vivify_tier_m6_hdr"`): keeps exact `D-01` (`899103a5`,
     `vivify.c:1269-1270`) sort guard `tier_mode != 0 || num_irred / 10 <= num_redundant`, uses
     dynamic `bmax = h->red_cap`, and records `h->res_sz = bi` (scratch field, `0` header growth).
   - `full_vivify_m6_hdr_fid` (`"full_vivify_m6_hdr"`): exact upstream Kissat 4.0.4 weights
     (`vivifytier1 = 3`, `vivifytier2 = 3`, `vivifytier3 = 1`, `vivifyirr = 3`, `options.h:163-167`)
     with `M6_DELAY_VIVIFYIRR = 3ULL` (existing `M6HdrExt` slot `3`) and dynamic active-tier
     weight normalization `/ sum` (`sum = 7` when `vivifyirr` is delayed instead of fixed `/ 10ULL`
     which dropped 30% of the vivification tick budget, and early exit when `sum == 0`).

2. **`G1-P2.1b` (`full_unwatch_large` + `full_bva_commit` `u64` copy loops):**
   - `full_unwatch_large_fid` (`"full_unwatch_large"`): replaces the scalar `u32` shift loop
     (`full_bva_commit.L110`, `218.8M Ir` in `C4-W3` when inlined into `full_bva_commit`) with
     non-overlapping 4-literal (`2 x u64`) + 2-literal (`u64`) copy steps + 1-literal tail and a
     single `u64` sentinel store (`0xFFFFFFFFFFFFFFFFULL`).
   - `full_bva_commit_fid` (`"full_bva_commit"`): widens the inner literal copy loop
     `ar[ncr + 3 + j] = tmp[j]` with 2-literal `u64` copy steps + 1-literal tail, and widens the
     `cnt[zi] = 0u` clearing loops with `u64` 2-word zeroing (preserving exact `m4BvaCommitSpec`).

3. **`G1-P2.1c` (`full_k6_propagate` & `full_k6_core_m8` sub-array pointer caching):**
   - `full_k6_propagate_fid` (`"full_k6_propagate"`): computes all Kitten sub-array pointers once
     at entry via multiply-free shift/add chaining (`0` `imul`s), caches `prop`/`trl_end`/`lvl`/
     `unass` in local scalars across the propagation loops, and inlines `assign` & saturating
     `ticks` updates so `full_k6_propagate_fid` is a 100% leaf function (`0` calls, `0` pointer
     recomputations or caller-save spills per step).
   - `full_k6_core_m8_fid` (`"full_k6_core_m8"`): caches all 8 Kitten sub-array pointers
     (`klvl`, `krsn`, `ktrl`, `kflags`, `cl_off`, `cl_meta`, `cl_aux`, `arena`) and inner clause
     slice pointers outside the loops instead of recomputing `scr[M8_KO_* + idx]` per step.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fidVivK6 "
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
#define PH_VIV                0x00100000u
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define FL_FACT_P             32u
#define FL_FACT_N             64u

#define M6_WM_PROBE_TICKS     0ULL
#define M6_DELAY_VIVIFYIRR    3ULL

#define K6_BIN_FLAG           0x80000000u
#define K6_LIT_MASK           0x7FFFFFFFu

#define K6H_LVL               2u
#define K6H_PROP              3u
#define K6H_TRL_END           4u
#define K6H_UNASS             5u
#define K6H_TICKS             11u
#define K6H_MAX_V             21u

#define M8_K6_MV              256u
#define M8_K6_MC              1024u
#define KM_LRN                0x40000000u
#define KM_CORE               0x80000000u

#define M8_KH_NV              4192u
#define M8_KH_NC              4193u
#define M8_KH_TRL_END         4197u
#define M8_KH_INCONS          4199u
#define M8_KH_ACAP            4207u

#define M8_KO_LVL             4224u
#define M8_KO_RSN             4480u
#define M8_KO_TRL             5504u
#define M8_KO_FLAGS           5760u
#define M8_KO_CL_OFF          11648u
#define M8_KO_CL_META         12672u
#define M8_KO_CL_AUX          13696u
#define M8_KO_ARENA           15744u

extern u32  full_arena_next(FullHdr *h, u32 cref);
extern bool full_viv_tier_match_m6(FullHdr *h, u32 hdr, u64 tier_mode);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64  full_viv_clause_m6(FullHdr *h, u32 cref);
extern u64  full_propagate(FullHdr *h);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern u64  full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);
extern u64  m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern u64  full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64  full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_init_fresh_var(FullHdr *h, u32 fv);

/* === G1-P2.1b (Part 1): full_unwatch_large with 2x-u64 / u64 copy steps === */

void full_unwatch_large_fid(FullHdr *h, u32 lit, u32 cref) {
  if ((u64)lit >= (h->cur_vars << 1) || (cref & PW_BIN_FLAG) != 0u) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz < 2ULL) { return; }
  u64 end = off + sz;
  u64 off2 = off + 2ULL;
  u64 p = end;
  while (p >= off2) {
    u32 w = wstk[p - 1ULL];
    if (w == cref) {
      u64 q = p - 2ULL;
      while (p + 4ULL <= end) {
        u64 *sp4 = (u64 *)(wstk + p);
        u64 *dp4 = (u64 *)(wstk + q);
        u64 v0 = sp4[0];
        u64 v1 = sp4[1];
        dp4[0] = v0;
        dp4[1] = v1;
        q = q + 4ULL;
        p = p + 4ULL;
      }
      if (p + 2ULL <= end) {
        u64 *sp2 = (u64 *)(wstk + p);
        u64 *dp2 = (u64 *)(wstk + q);
        dp2[0] = sp2[0];
        q = q + 2ULL;
        p = p + 2ULL;
      }
      if (p < end) {
        wstk[q] = wstk[p];
      }
      u64 *tail = (u64 *)(wstk + (end - 2ULL));
      tail[0] = 0xFFFFFFFFFFFFFFFFULL;
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - 2ULL);
      h->wusable = h->wusable + 2ULL;
      return;
    }
    p = p - 2ULL + (u64)(w >> 31);
  }
}

/* === GAP-VIV-01/02: Dynamic vivification schedule cap & active-tier normalization === */

u64 full_viv_collect_fid(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = 0ULL;
  u64 pass = 0ULL;
  while (pass < 2ULL && bn < bmax) {
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_GARB) == 0u) {
        bool want = (pass == 0ULL) ? ((hdr & PH_VIV) == 0u) : ((hdr & PH_VIV) != 0u);
        if (want && full_viv_tier_match_m6(h, hdr, tier_mode) && bn < bmax) {
          rr[bn] = (u32)p;
          bn = bn + 1ULL;
        }
      }
      p = np;
    }
    pass = pass + 1ULL;
  }
  return bn;
}

void full_viv_count_fid(FullHdr *h, u64 bn) {
  u64 nlits = h->cur_vars << 1;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 l = 0ULL;
  while (l < nlits) { cnt[l] = 0u; l = l + 1ULL; }
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k = 0u;
    while (k < sz) {
      u32 lit = ar[(u64)cr + 3ULL + (u64)k];
      if ((u64)lit < nlits && cnt[lit] < 0xFFFFFFFFu) { cnt[lit] = cnt[lit] + 1u; }
      k = k + 1u;
    }
    bi = bi + 1ULL;
  }
}

void full_viv_sort2_fid(FullHdr *h, u64 bn, u64 mode) {
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 nlits = h->cur_vars << 1;
  u32 *keys = (mode == 1ULL) ? (rr + bn) : ((u32 *)h->scratch_buf);
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k0 = 0xFFFFFFFFu; u32 d0 = 0u;
    u32 k1 = 0xFFFFFFFFu; u32 d1 = 0u;
    u32 j = 0u;
    while (j < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)j];
      u32 dl = ((u64)l < nlits) ? cnt[l] : 0u;
      if (k0 == 0xFFFFFFFFu || dl > d0 || (dl == d0 && l < k0)) {
        k1 = k0; d1 = d0; k0 = l; d0 = dl;
      } else if (k1 == 0xFFFFFFFFu || dl > d1 || (dl == d1 && l < k1)) {
        k1 = l; d1 = dl;
      }
      j = j + 1u;
    }
    keys[bi << 1] = k0;
    keys[(bi << 1) + 1ULL] = k1;
    bi = bi + 1ULL;
  }
  u64 gap = bn >> 1;
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < bn) {
      u32 cr = rr[si];
      u32 k0 = keys[si << 1]; u32 k1 = keys[(si << 1) + 1ULL];
      bool v0 = ((ar[cr] & PH_VIV) != 0u);
      u32 dk0 = ((u64)k0 < nlits) ? cnt[k0] : 0u;
      u32 dk1 = ((u64)k1 < nlits) ? cnt[k1] : 0u;
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pcr = rr[pj];
        u32 pk0 = keys[pj << 1]; u32 pk1 = keys[(pj << 1) + 1ULL];
        bool pv0 = ((ar[pcr] & PH_VIV) != 0u);
        u32 dpk0 = ((u64)pk0 < nlits) ? cnt[pk0] : 0u;
        u32 dpk1 = ((u64)pk1 < nlits) ? cnt[pk1] : 0u;
        if (!pv0 && v0) { break; }
        if (pv0 == v0) {
          if (dpk0 > dk0) { break; }
          if (dpk0 == dk0) {
            if (pk0 < k0) { break; }
            if (pk0 == k0) {
              if (dpk1 > dk1) { break; }
              if (dpk1 == dk1) {
                if (pk1 < k1 || (pk1 == k1 && pcr <= cr)) { break; }
              }
            }
          }
        }
        rr[sj] = pcr;
        keys[sj << 1] = pk0; keys[(sj << 1) + 1ULL] = pk1;
        sj = pj;
      }
      rr[sj] = cr;
      keys[sj << 1] = k0; keys[(sj << 1) + 1ULL] = k1;
      si = si + 1ULL;
    }
    gap = gap >> 1;
  }
}

void full_viv_sort_fid(FullHdr *h, u64 bn) {
  if (bn <= 1ULL) { return; }
  u64 rcap = h->red_cap;
  u64 scap = h->scratch_cap;
  if (bn <= rcap / 3ULL) { full_viv_sort2_fid(h, bn, 1ULL); return; }
  if (bn <= (scap >> 1)) { full_viv_sort2_fid(h, bn, 2ULL); return; }
  if (bn > (rcap >> 1)) { return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 nlits = h->cur_vars << 1;
  u32 *keys1 = rr + bn;
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k0 = 0xFFFFFFFFu; u32 d0 = 0u;
    u32 j = 0u;
    while (j < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)j];
      u32 dl = ((u64)l < nlits) ? cnt[l] : 0u;
      if (k0 == 0xFFFFFFFFu || dl > d0 || (dl == d0 && l < k0)) { k0 = l; d0 = dl; }
      j = j + 1u;
    }
    keys1[bi] = k0;
    bi = bi + 1ULL;
  }
  u64 gap = bn >> 1;
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < bn) {
      u32 cr = rr[si]; u32 k0 = keys1[si];
      bool v0 = ((ar[cr] & PH_VIV) != 0u);
      u32 dk0 = ((u64)k0 < nlits) ? cnt[k0] : 0u;
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pcr = rr[pj]; u32 pk0 = keys1[pj];
        bool pv0 = ((ar[pcr] & PH_VIV) != 0u);
        u32 dpk0 = ((u64)pk0 < nlits) ? cnt[pk0] : 0u;
        if (!pv0 && v0) { break; }
        if (pv0 == v0) {
          if (dpk0 > dk0) { break; }
          if (dpk0 == dk0 && (pk0 < k0 || (pk0 == k0 && pcr <= cr))) { break; }
        }
        rr[sj] = pcr; keys1[sj] = pk0;
        sj = pj;
      }
      rr[sj] = cr; keys1[sj] = k0;
      si = si + 1ULL;
    }
    gap = gap >> 1;
  }
}

u64 full_vivify_tier_m6_hdr_fid(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = full_viv_collect_fid(h, tier_mode);
  if (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant) {
    full_viv_count_fid(h, bn);
    full_viv_sort_fid(h, bn);
  }
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         h->search_ticks < tick_lim) {
    u32 cr = rr[bi];
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

u64 full_vivify_m6_hdr_fid(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  m6_hdr_sync_legacy_tiers(h);
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
  h->search_ticks = start;
  return res;
}

/* === G1-P2.1c: Kitten sub-array pointer caching (full_k6_propagate & full_k6_core_m8) === */

u32 full_k6_propagate_fid(u32 *k) {
  u32 mv = k[K6H_MAX_V];
  u32 mv2 = mv << 1;
  u32 mv4 = mv << 2;
  u32 mv8 = mv << 3;
  u32 *lvl = k + 32u;
  u32 *rsn = lvl + mv;
  u32 *trl = rsn + mv4;
  u32 *flags = trl + mv;
  u32 *vals = flags + mv4;
  u32 *whead = vals + mv2;
  u32 *wnext = whead + mv2;
  u32 *wblit = wnext + mv8;
  u32 *cl_off = wblit + mv8;
  u32 *cl_sz = cl_off + mv4;
  u32 *arena = cl_sz + mv4;
  u32 prop = k[K6H_PROP];
  u32 te = k[K6H_TRL_END];
  u32 klvl = k[K6H_LVL];
  u32 unass = k[K6H_UNASS];
  u64 ticks = 0ULL;
  while (prop < te) {
    u32 lit = trl[prop];
    prop = prop + 1u;
    u32 nl = lit ^ 1u;
    u64 visits = 0ULL;
    u32 prev = 0xFFFFFFFFu;
    u32 w = whead[nl];
    while (w != 0xFFFFFFFFu) {
      u32 nxt = wnext[w];
      visits = visits + 1ULL;
      u32 wb = wblit[w];
      u32 bv = wb & K6_LIT_MASK;
      u32 bvv = vals[bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          k[K6H_PROP] = prop;
          k[K6H_TRL_END] = te;
          k[K6H_UNASS] = unass;
          u64 cur_t = (u64)k[K6H_TICKS];
          u64 dt = ticks + (visits >> 4) + 1ULL;
          u64 rem = 0xFFFFFFFFULL - cur_t;
          k[K6H_TICKS] = (dt >= rem) ? 0xFFFFFFFFu : (u32)(cur_t + dt);
          return cid;
        }
        if (bvv == 0u) {
          u32 v = bv >> 1;
          vals[bv] = 1u; vals[bv ^ 1u] = 2u;
          lvl[v] = klvl; rsn[v] = cid;
          trl[te] = bv; te = te + 1u;
          if (unass > 0u) { unass = unass - 1u; }
          u32 fl = flags[v];
          flags[v] = ((bv & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
        }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u;
      u32 off = cl_off[cid];
      u32 sz = cl_sz[cid];
      u32 *cl = arena + off;
      u32 other = cl[slot ^ 1u];
      ticks = ticks + 1ULL;
      if (vals[other] == 1u) { wblit[w] = other; prev = w; w = nxt; continue; }
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = cl[r];
        if (vals[cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        cl[slot] = repl; cl[ri] = nl;
        if (prev == 0xFFFFFFFFu) { whead[nl] = nxt; } else { wnext[prev] = nxt; }
        wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
        w = nxt; continue;
      }
      wblit[w] = other; prev = w; w = nxt;
      u32 ov = vals[other];
      if (ov == 2u) {
        k[K6H_PROP] = prop;
        k[K6H_TRL_END] = te;
        k[K6H_UNASS] = unass;
        u64 cur_t = (u64)k[K6H_TICKS];
        u64 dt = ticks + (visits >> 4) + 1ULL;
        u64 rem = 0xFFFFFFFFULL - cur_t;
        k[K6H_TICKS] = (dt >= rem) ? 0xFFFFFFFFu : (u32)(cur_t + dt);
        return cid;
      }
      if (ov == 0u) {
        u32 v = other >> 1;
        vals[other] = 1u; vals[other ^ 1u] = 2u;
        lvl[v] = klvl; rsn[v] = cid;
        trl[te] = other; te = te + 1u;
        if (unass > 0u) { unass = unass - 1u; }
        u32 fl = flags[v];
        flags[v] = ((other & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
      }
    }
    ticks = ticks + (visits >> 4) + 1ULL;
  }
  k[K6H_PROP] = prop;
  k[K6H_TRL_END] = te;
  k[K6H_UNASS] = unass;
  u64 cur_t = (u64)k[K6H_TICKS];
  u64 rem = 0xFFFFFFFFULL - cur_t;
  k[K6H_TICKS] = (ticks >= rem) ? 0xFFFFFFFFu : (u32)(cur_t + ticks);
  return 0xFFFFFFFFu;
}

void full_k6_core_m8_fid(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nc = scr[M8_KH_NC]; u32 nv = scr[M8_KH_NV]; u32 acap = scr[M8_KH_ACAP];
  if (nc > M8_K6_MC || nv > M8_K6_MV) { return; }
  u32 *klvl    = scr + M8_KO_LVL;
  u32 *krsn    = scr + M8_KO_RSN;
  u32 *ktrl    = scr + M8_KO_TRL;
  u32 *kflags  = scr + M8_KO_FLAGS;
  u32 *cl_off  = scr + M8_KO_CL_OFF;
  u32 *cl_meta = scr + M8_KO_CL_META;
  u32 *cl_aux  = scr + M8_KO_CL_AUX;
  u32 *arena   = scr + M8_KO_ARENA;
  u32 i = 0u;
  while (i < nc) { cl_meta[i] = cl_meta[i] & (~KM_CORE); i = i + 1u; }
  u32 inc = scr[M8_KH_INCONS];
  if (inc < nc) {
    i = 0u; while (i < nv) { kflags[i] = kflags[i] & (~2u); i = i + 1u; }
    cl_meta[inc] = cl_meta[inc] | KM_CORE;
    u32 off = cl_off[inc]; u32 sz = cl_meta[inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 *cl = arena + off;
      u32 j = 0u;
      while (j < sz) {
        u32 lv = cl[j] >> 1;
        if (lv < nv) { kflags[lv] = kflags[lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = scr[M8_KH_TRL_END]; if (ti > M8_K6_MV) { ti = M8_K6_MV; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = ktrl[ti] >> 1;
      if (v >= nv || (kflags[v] & 2u) == 0u) { continue; }
      kflags[v] = kflags[v] & (~2u);
      u32 rsn = krsn[v];
      if (rsn >= nc) { continue; }
      cl_meta[rsn] = cl_meta[rsn] | KM_CORE;
      u32 roff = cl_off[rsn]; u32 rsz = cl_meta[rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 *rcl = arena + roff;
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = rcl[j] >> 1;
          if (lv < nv && lv != v) { kflags[lv] = kflags[lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u; while (i < nv) { kflags[i] = kflags[i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u; bool changed = true;
  while (changed && pass < nc) {
    changed = false; pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = cl_meta[cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = cl_off[cid]; u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = cl_aux[cid];
          if (off + sz + na <= acap) {
            u32 *ants = arena + (off + sz);
            u32 j = 0u;
            while (j < na) {
              u32 ant = ants[j];
              if (ant < nc && (cl_meta[ant] & KM_CORE) == 0u) {
                cl_meta[ant] = cl_meta[ant] | KM_CORE; changed = true;
              }
              j = j + 1u;
            }
          }
        } else if (off + sz <= acap) {
          u32 *cl = arena + off;
          u32 j = 0u;
          while (j < sz) {
            u32 lv = cl[j] >> 1;
            if (lv < nv && klvl[lv] == 0u) {
              u32 r0 = krsn[lv];
              if (r0 < nc && (cl_meta[r0] & KM_CORE) == 0u) {
                cl_meta[r0] = cl_meta[r0] | KM_CORE; changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
}

/* === G1-P2.1b (Part 2): full_bva_commit with safe 2-literal u64 copy & zeroing loops === */

bool full_bva_commit_fid(FullHdr *h, u32 best_k) {
  if (h->oom != 0ULL) { return false; }
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *fl = (u32 *)h->flags;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 dm = best_k + 1u; u32 mn = scr[32u + best_k];
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
    u32 c_top = scr[64u + best_k * 256u + m];
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
      while (zi + 2ULL <= zl) {
        u64 *zp = (u64 *)(cnt + zi); zp[0] = 0ULL; zi = zi + 2ULL;
      }
      return false;
    }
  }
  u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
  full_init_fresh_var(h, fv);
  u64 *s1 = (u64 *)h->repr; u64 *s2 = (u64 *)h->sim_sig; s1[fv] = 0ULL; s2[fv] = 0ULL;
  cnt[fv << 1] = 0u; cnt[(fv << 1) | 1u] = 0u;
  u32 fresh = fv << 1; u32 *tmp = (u32 *)h->tmp_lits;
  bool ok = true;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 br = full_add_bin(h, fresh, fs);
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    fl[fs >> 1] = fl[fs >> 1] | FL_FACT_P | FL_FACT_N;
    si = si + 1u;
  }
  m = 0u;
  while (m < mn && ok) {
    u32 c_top = scr[64u + best_k * 256u + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u64 br = full_add_bin(h, fresh ^ 1u, c_top & PW_LIT_MASK);
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
      u32 *dst_cl = ar + (ncr + 3ULL);
      j = 0u;
      while (j + 2u <= tk) {
        u64 *dp = (u64 *)(dst_cl + (u64)j);
        u64 *sp = (u64 *)(tmp + (u64)j);
        dp[0] = sp[0];
        j = j + 2u;
      }
      if (j < tk) { dst_cl[j] = tmp[j]; }
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
    while (zi + 2ULL <= zl) {
      u64 *zp = (u64 *)(cnt + zi); zp[0] = 0ULL; zi = zi + 2ULL;
    }
    return false;
  }
  m = 0u;
  while (m < mn) {
    u32 idx = m;
    u32 s = best_k;
    while (true) {
      u32 cs = scr[64u + s * 256u + idx]; u32 fs = scr[s];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
        fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          full_unwatch_large(h, dl, cs);
          fl[dl >> 1] = fl[dl >> 1] | (((dl & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      }
      if (s == 0u) { break; }
      idx = scr[8256u + s * 256u + idx]; s = s - 1u;
    }
    m = m + 1u;
  }
  u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
  while (zi + 2ULL <= zl) {
    u64 *zp = (u64 *)(cnt + zi); zp[0] = 0ULL; zi = zi + 2ULL;
  }
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}
"

/-! ## 2. Canonical `Fn` Handles, Replacement Lists, & Standalone Module -/

/-- Drop-in replacement for `"full_unwatch_large"` (`G1-P2.1b`, `2x-u64` + `u64` shift loop). -/
def fidUnwatchLargeFn : Fn :=
  ⟨"full_unwatch_large", [i64, i32, i32], [], full_unwatch_large_fid_body⟩

/-- Helper `"full_viv_collect_fid"` (`GAP-VIV-01`, stride-1 `red_cap` collector). -/
def fidVivCollectFn : Fn :=
  ⟨"full_viv_collect_fid", [i64, i64], [i64], full_viv_collect_fid_body⟩

/-- Helper `"full_viv_count_fid"` (`GAP-VIV-01`, stride-1 literal counter). -/
def fidVivCountFn : Fn :=
  ⟨"full_viv_count_fid", [i64, i64], [], full_viv_count_fid_body⟩

/-- Helper `"full_viv_sort2_fid"` (`GAP-VIV-01`, 2-key Shell sort for modes 1 & 2). -/
def fidVivSort2Fn : Fn :=
  ⟨"full_viv_sort2_fid", [i64, i64, i64], [], full_viv_sort2_fid_body⟩

/-- Helper `"full_viv_sort_fid"` (`GAP-VIV-01`, dynamic key-storage Shell sort). -/
def fidVivSortFn : Fn :=
  ⟨"full_viv_sort_fid", [i64, i64], [], full_viv_sort_fid_body⟩

/-- Drop-in replacement for `"full_vivify_tier_m6_hdr"` (`GAP-VIV-01` + `D-01`). -/
def fidVivifyTierHdrFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_fid_body⟩

/-- Drop-in replacement for `"full_vivify_m6_hdr"` (`GAP-VIV-02`, dynamic `/ sum`). -/
def fidVivifyHdrFn : Fn :=
  ⟨"full_vivify_m6_hdr", [i64], [i64], full_vivify_m6_hdr_fid_body⟩

/-- Drop-in replacement for `"full_k6_propagate"` (`G1-P2.1c`, leaf + cached sub-array ptrs). -/
def fidK6PropagateFn : Fn :=
  ⟨"full_k6_propagate", [i64], [i32], full_k6_propagate_fid_body⟩

/-- Drop-in replacement for `"full_k6_core_m8"` (`G1-P2.1c`, cached sub-array ptrs). -/
def fidK6CoreM8Fn : Fn :=
  ⟨"full_k6_core_m8", [i64], [], full_k6_core_m8_fid_body⟩

/-- Drop-in replacement for `"full_bva_commit"` (`G1-P2.1b`, `u64` copy & zero loops). -/
def fidBvaCommitFn : Fn :=
  ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_fid_body⟩

/-- The `4` new dynamic vivification helpers inserted before `"full_vivify_tier_m6_hdr"`. -/
def fidVivHelpers : List Fn :=
  [fidVivCollectFn, fidVivCountFn, fidVivSort2Fn, fidVivSortFn]

/-- Insertion plan placing `fidVivHelpers` before `"full_vivify_tier_m6_hdr"`. -/
def fidVivK6Befores : List (Sym × List Fn) :=
  [("full_vivify_tier_m6_hdr", fidVivHelpers)]

/-- Full `6`-function replacement table (`unwatch_large`, `vivify_{tier_,}m6_hdr`,
`k6_propagate`, `k6_core_m8`, `bva_commit`). -/
def fidVivK6Repls : List Fn :=
  [ fidUnwatchLargeFn
  , fidVivifyTierHdrFn
  , fidVivifyHdrFn
  , fidK6PropagateFn
  , fidK6CoreM8Fn
  , fidBvaCommitFn ]

/-- Composable `5`-function replacement table omitting `full_bva_commit` for assemblies that
supply a scaled `full_bva_commit` (e.g. `FullFidelityBva`) while keeping `full_unwatch_large_fid`
(`full_bva_commit.L110` `u64` copy speedup). -/
def fidVivK6NoBvaCommitRepls : List Fn :=
  [ fidUnwatchLargeFn
  , fidVivifyTierHdrFn
  , fidVivifyHdrFn
  , fidK6PropagateFn
  , fidK6CoreM8Fn ]

/-- Standalone function list (`10` functions in topological callee-first order). -/
def fidVivK6Fns : List Fn :=
  [ fidUnwatchLargeFn
  , fidVivCollectFn
  , fidVivCountFn
  , fidVivSort2Fn
  , fidVivSortFn
  , fidVivifyTierHdrFn
  , fidVivifyHdrFn
  , fidK6PropagateFn
  , fidK6CoreM8Fn
  , fidBvaCommitFn ]

/-- External callee declarations for standalone `fidVivK6Module` verification (`17` externs). -/
def fidVivK6Externs : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], []⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], []⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64]⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool]⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], []⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], []⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_init_fresh_var", [i64, i32], []⟩ ]

/-- Standalone closed module (`9` functions + `17` externs, `0` exits). -/
def fidVivK6Module : LeanQbe.T.Module :=
  { fns := fidVivK6Fns, externs := fidVivK6Externs, exits := [] }

/-! ## 3. Well-Formedness, Acyclicity, & Multi-ISA Legality -/

theorem full_unwatch_large_fid_wf : Func.Wf full_unwatch_large_fid_body := by t_wf_reify
theorem full_viv_collect_fid_wf : Func.Wf full_viv_collect_fid_body := by t_wf_reify
theorem full_viv_count_fid_wf : Func.Wf full_viv_count_fid_body := by t_wf_reify
theorem full_viv_sort2_fid_wf : Func.Wf full_viv_sort2_fid_body := by t_wf_reify
theorem full_viv_sort_fid_wf : Func.Wf full_viv_sort_fid_body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_fid_wf : Func.Wf full_vivify_tier_m6_hdr_fid_body := by t_wf_reify
theorem full_vivify_m6_hdr_fid_wf : Func.Wf full_vivify_m6_hdr_fid_body := by t_wf_reify
theorem full_k6_propagate_fid_wf : Func.Wf full_k6_propagate_fid_body := by t_wf_reify
theorem full_k6_core_m8_fid_wf : Func.Wf full_k6_core_m8_fid_body := by t_wf_reify
theorem full_bva_commit_fid_wf : Func.Wf full_bva_commit_fid_body := by t_wf_reify

theorem fidVivHelpers_wf : ∀ f ∈ fidVivHelpers, f.Wf := by
  intro f hf
  simp only [fidVivHelpers, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_viv_collect_fid_wf
  · exact full_viv_count_fid_wf
  · exact full_viv_sort2_fid_wf
  · exact full_viv_sort_fid_wf

theorem fidVivK6Repls_wf : ∀ f ∈ fidVivK6Repls, f.Wf := by
  intro f hf
  simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_unwatch_large_fid_wf
  · exact full_vivify_tier_m6_hdr_fid_wf
  · exact full_vivify_m6_hdr_fid_wf
  · exact full_k6_propagate_fid_wf
  · exact full_k6_core_m8_fid_wf
  · exact full_bva_commit_fid_wf

theorem fidVivK6NoBvaCommitRepls_wf : ∀ f ∈ fidVivK6NoBvaCommitRepls, f.Wf := by
  intro f hf
  simp only [fidVivK6NoBvaCommitRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_unwatch_large_fid_wf
  · exact full_vivify_tier_m6_hdr_fid_wf
  · exact full_vivify_m6_hdr_fid_wf
  · exact full_k6_propagate_fid_wf
  · exact full_k6_core_m8_fid_wf

theorem fidVivK6Befores_wf : ∀ f ∈ fidVivK6Befores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidVivK6Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hf
  exact fidVivHelpers_wf f hf

theorem fidVivK6Fns_wf : ∀ f ∈ fidVivK6Fns, f.Wf := by
  intro f hf
  simp only [fidVivK6Fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_unwatch_large_fid_wf
  · exact full_viv_collect_fid_wf
  · exact full_viv_count_fid_wf
  · exact full_viv_sort2_fid_wf
  · exact full_viv_sort_fid_wf
  · exact full_vivify_tier_m6_hdr_fid_wf
  · exact full_vivify_m6_hdr_fid_wf
  · exact full_k6_propagate_fid_wf
  · exact full_k6_core_m8_fid_wf
  · exact full_bva_commit_fid_wf

theorem fidVivK6_acyclic : fidVivK6Module.checkAcyclic = true := by t_kernel_rfl

#guard fidVivK6Fns.length == 10
#guard (fidVivK6Fns.map Fn.name).eraseDups.length == 10
#guard fidVivK6Module.checkAcyclic
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .x64AVX512))).isOk
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .x64AVX2))).isOk
#guard fidVivK6Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidVivK6Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidVivK6Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard fidVivK6Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6

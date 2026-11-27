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
# Kissat Fidelity Step 13 Shard S1-A — Sweep & Dense (`FullFidelityStep13S1SweepDense`)

Data-pure C0 module (`0` `*Proof*` imports, `0` edits to Step-12 files) containing the `13`
Step-13 S1-A functions (`5` ADD + `8` MOD) copied verbatim from frozen `step13_v2_frozen_direct.c`:
- **ADD (`5`):** `full_dense_occ_cnt_fid`, `full_enter_dense_ex_fid`,
  `full_dense_bin_roundtrip_fid`, `full_dense_bin_sort_roundtrip_fid`,
  `full_watch_large_clauses_fid`.
- **MOD (`8`):** `full_enter_dense`, `full_sort_bin_watches_fid`, `full_m6_els_ar`,
  `full_m6_els_lit`, `full_m6_dense_els`, `full_m6_sweep_var`, `full_m6_collect_cands`,
  `full_m6_sweep_vars`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

@[expose] public section

kissat_c0! fidStep13S1SweepDense "
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

#define PH_GARB           0x00080000u
#define PH_RED            0x00400000u
#define PH_SHRK           0x00800000u
#define PW_BIN_FLAG       0x80000000u
#define PW_LIT_MASK       0x7FFFFFFFu

#define FL_ACTIVE         1u
#define FL_SWEEP          1024u
#define FL_SWEEP_INR      0x20000000u
#define FL_SWEEP_INC      0x40000000u

#define K6H_INCONS        6u
#define K6H_TICKS         11u
#define K6H_NEQ           24u

#define SWP_GU_COMPLETED  28u
#define SWP_GU_INCOMPLETE 29u
#define SWP_GU_CURSOR     30u
#define SWP_GU_SWEPT      32u

extern u32  full_arena_next(FullHdr *h, u32 cref);
extern u64  full_arena_sweep(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64  full_flush_trail(FullHdr *h);
extern u64  full_propagate(FullHdr *h);
extern void full_sweep_bins(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_fwd_flush_large_m7(FullHdr *h);
extern u64  full_lit_rank_m6(i8 *vals, u32 *lvl, u32 lit);
extern u32  full_cong_find(u32 *repr, u32 l);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64  full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_m6_dense_prop(FullHdr *h);
extern u64  full_m6_max_v(u64 cap);
extern u64  full_m6_sweep_cone(FullHdr *h, u32 root_v);
extern u32  full_m6_sweep_sim(FullHdr *h, u32 nv, u64 tick_lim);
extern u64  full_m6_sweep_units(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim);
extern u64  full_m6_sweep_classes(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim);
extern void full_m6_cand_sift(u32 *cands, u32 *deg, u32 start, u32 n);

u64 full_dense_occ_cnt_fid(FullHdr *h, u32 lit, u64 cap) {
  u32 *wvec = (u32 *)h->watch_vec;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz <= cap) { return sz; }
  u32 *wstk = (u32 *)h->watch_stk;
  u64 p = off;
  u64 end = off + sz;
  u64 cnt = 0ULL;
  while (p < end) {
    u32 w0 = wstk[p];
    if ((w0 & 0x80000000u) != 0u) { p = p + 1ULL; }
    else { p = p + 2ULL; }
    cnt = cnt + 1ULL;
    if (cnt > cap) { return cnt; }
  }
  return cnt;
}

bool full_enter_dense_ex_fid(FullHdr *h, bool connect_large) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return false; }
  if (h->dense_mode != 0ULL) { return true; }
  bool had_unfl = (h->unflushed > 0ULL);
  if (full_flush_trail(h) != 1ULL) { return false; }
  if (had_unfl) {
    u64 sr_d = full_arena_sweep(h);
    if (sr_d == 2ULL) { h->inconsistent = 1ULL; return false; }
    if (full_propagate(h) == 1ULL) { h->inconsistent = 1ULL; return false; }
    if (full_flush_trail(h) != 1ULL) { return false; }
    h->unflushed = 0ULL;
  }
  full_sweep_bins(h);
  if (connect_large) {
    i8 *vals = (i8 *)h->values;
    u32 *ar = (u32 *)h->arena;
    u64 nlits = h->cur_vars << 1;
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
      if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
        bool sat = false;
        u32 k = 0u;
        while (k < sz) {
          u32 lit = ar[p + 3ULL + (u64)k];
          if ((u64)lit < nlits && vals[lit] > (i8)0) { sat = true; break; }
          k = k + 1u;
        }
        if (sat) {
          ar[p] = hdr | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
          if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
        } else {
          k = 0u;
          while (k < sz) {
            u32 lit = ar[p + 3ULL + (u64)k];
            if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
              h->oom = 0ULL; full_arena_sweep(h); return false;
            }
            k = k + 1u;
          }
        }
      }
      p = (u64)full_arena_next(h, (u32)p);
    }
  }
  h->dense_mode = 1ULL;
  return true;
}

bool full_enter_dense(FullHdr *h) {
  return full_enter_dense_ex_fid(h, true);
}

void full_dense_bin_roundtrip_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (nlits == 0ULL) { return; }
  full_fwd_flush_large_m7(h);
  if (h->num_binary == 0ULL || h->wcap == 0ULL) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  i8 *vals = (i8 *)h->values;
  u8 *lm = (u8 *)h->lit_mark;
  u32 *pairs = (u32 *)h->scratch_buf;
  u64 scap_pairs = h->scratch_cap >> 1;
  u64 nb = 0ULL;
  bool overflow = false;
  u64 l = 0ULL;
  while (l < nlits && !overflow) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 0ULL) {
      i8 lv = vals[l];
      u64 p = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && lm[ot] == (u8)0) {
            lm[ot] = (u8)1;
            if (lv <= (i8)0 && vals[ot] <= (i8)0 && l < (u64)ot) {
              if (nb < scap_pairs) {
                pairs[nb << 1] = (u32)l;
                pairs[(nb << 1) + 1ULL] = ot;
                nb = nb + 1ULL;
              } else {
                overflow = true;
                break;
              }
            }
          }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits) { lm[ot] = (u8)0; }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
    }
    l = l + 1ULL;
  }
  if (overflow) {
    full_sweep_bins(h);
    return;
  }
  l = 0ULL;
  while (l < nlits) {
    wvec[l << 1] = 0u;
    wvec[(l << 1) + 1ULL] = 0u;
    l = l + 1ULL;
  }
  wstk[0] = 0u;
  h->wlen = 1ULL;
  h->wusable = 0ULL;
  h->num_binary = nb;
  u64 k = 0ULL;
  while (k < nb) {
    u32 a = pairs[k << 1];
    u32 b = pairs[(k << 1) + 1ULL];
    full_watch_push(h, a, (b & PW_LIT_MASK) | PW_BIN_FLAG, 0u, 1u);
    full_watch_push(h, b, (a & PW_LIT_MASK) | PW_BIN_FLAG, 0u, 1u);
    k = k + 1ULL;
  }
}

void full_dense_bin_sort_roundtrip_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (nlits == 0ULL) { return; }
  full_fwd_flush_large_m7(h);
  if (h->num_binary == 0ULL || h->wcap == 0ULL) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  i8 *vals = (i8 *)h->values;
  u8 *lm = (u8 *)h->lit_mark;
  u32 *pairs = (u32 *)h->scratch_buf;
  u64 scap_pairs = h->scratch_cap >> 1;
  u64 nb = 0ULL;
  bool overflow = false;
  u64 l = 0ULL;
  while (l < nlits && !overflow) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 0ULL) {
      i8 lv = vals[l];
      u64 p = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && lm[ot] == (u8)0) {
            lm[ot] = (u8)1;
            if (lv <= (i8)0 && vals[ot] <= (i8)0 && l < (u64)ot) {
              if (nb < scap_pairs) {
                pairs[nb << 1] = (u32)l;
                pairs[(nb << 1) + 1ULL] = ot;
                nb = nb + 1ULL;
              } else {
                overflow = true;
                break;
              }
            }
          }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits) { lm[ot] = (u8)0; }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
    }
    l = l + 1ULL;
  }
  if (overflow) {
    full_sweep_bins(h);
    return;
  }
  if (nb > 1ULL) {
    u64 gap = 1ULL;
    u64 lim = nb / 3ULL;
    while (gap < lim) { gap = gap * 3ULL + 1ULL; }
    while (gap >= 1ULL) {
      u64 i = gap;
      while (i < nb) {
        u32 pa = pairs[i << 1];
        u32 pb = pairs[(i << 1) + 1ULL];
        u64 j = i;
        while (j >= gap) {
          u32 qa = pairs[(j - gap) << 1];
          u32 qb = pairs[((j - gap) << 1) + 1ULL];
          if (qa < pa || (qa == pa && qb <= pb)) { break; }
          pairs[j << 1] = qa;
          pairs[(j << 1) + 1ULL] = qb;
          j = j - gap;
        }
        pairs[j << 1] = pa;
        pairs[(j << 1) + 1ULL] = pb;
        i = i + 1ULL;
      }
      gap = gap / 3ULL;
    }
  }
  l = 0ULL;
  while (l < nlits) {
    wvec[l << 1] = 0u;
    wvec[(l << 1) + 1ULL] = 0u;
    l = l + 1ULL;
  }
  wstk[0] = 0u;
  h->wlen = 1ULL;
  h->wusable = 0ULL;
  h->num_binary = nb;
  u64 k = 0ULL;
  while (k < nb) {
    u32 a = pairs[k << 1];
    u32 b = pairs[(k << 1) + 1ULL];
    full_watch_push(h, a, (b & PW_LIT_MASK) | PW_BIN_FLAG, 0u, 1u);
    full_watch_push(h, b, (a & PW_LIT_MASK) | PW_BIN_FLAG, 0u, 1u);
    k = k + 1ULL;
  }
}

void full_watch_large_clauses_fid(FullHdr *h) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool at_root = (h->cur_level == 0ULL);
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) == 0u && sz >= 3u && p + 3ULL + (u64)sz <= h->arena_len) {
      if (!at_root) {
        u32 i0 = 0u; u64 r0 = full_lit_rank_m6(vals, lvl, ar[p + 3ULL]);
        u32 i = 1u;
        while (i < sz) {
          u64 rk = full_lit_rank_m6(vals, lvl, ar[p + 3ULL + (u64)i]);
          if (rk > r0) { r0 = rk; i0 = i; }
          i = i + 1u;
        }
        if (i0 != 0u) {
          u32 t = ar[p + 3ULL]; ar[p + 3ULL] = ar[p + 3ULL + (u64)i0];
          ar[p + 3ULL + (u64)i0] = t;
        }
        u32 i1 = 1u; u64 r1 = full_lit_rank_m6(vals, lvl, ar[p + 4ULL]);
        i = 2u;
        while (i < sz) {
          u64 rk = full_lit_rank_m6(vals, lvl, ar[p + 3ULL + (u64)i]);
          if (rk > r1) { r1 = rk; i1 = i; }
          i = i + 1u;
        }
        if (i1 != 1u) {
          u32 t = ar[p + 4ULL]; ar[p + 4ULL] = ar[p + 3ULL + (u64)i1];
          ar[p + 3ULL + (u64)i1] = t;
        }
      }
      ar[p + 1ULL] = 2u;
      u32 l0 = ar[p + 3ULL]; u32 l1 = ar[p + 4ULL];
      if (!full_watch_push_m6(h, l0, l1 & PW_LIT_MASK, (u32)p, 2u) ||
          !full_watch_push_m6(h, l1, l0 & PW_LIT_MASK, (u32)p, 2u)) {
        h->oom = 1ULL; return;
      }
    }
    if (np <= p) { break; }
    p = np;
  }
}

void full_sort_bin_watches_fid(FullHdr *h) {
  (void)h;
}

bool full_m6_els_ar(FullHdr *h, u32 cr, u32 rl) {
  if ((u64)cr + 3ULL > h->arena_len) { return true; }
  u32 *ar = (u32 *)h->arena; u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
  if ((hdr & PH_GARB) != 0u || sz < 3u || (u64)cr + 3ULL + (u64)sz > h->arena_len) {
    return true;
  }
  u32 *repr = (u32 *)h->repr; u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  u64 nlits = h->cur_vars << 1;
  bool chg = false; u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if ((u64)l < nlits && full_cong_find(repr, l) != l) { chg = true; break; }
    k = k + 1u;
  }
  if (!chg) {
    if (!full_watch_push(h, rl, sz & PW_LIT_MASK, cr, 2u)) { h->oom = 1ULL; }
    return true;
  }
  bool has_rl = false;
  u32 hk = 0u;
  while (hk < sz) {
    if (ar[(u64)cr + 3ULL + (u64)hk] == rl) { has_rl = true; break; }
    hk = hk + 1u;
  }
  bool taut = false; u32 nsz = 0u; k = 0u;
  while (k < sz) {
    u32 x = ar[(u64)cr + 3ULL + (u64)k];
    u32 rx = ((u64)x < nlits) ? full_cong_find(repr, x) : x;
    if ((u64)rx < nlits) {
      if (lm[rx ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rx] == (u8)0 && (u64)nsz < h->max_vars) {
        lm[rx] = (u8)1; tmp[nsz] = rx; nsz = nsz + 1u;
      }
    }
    k = k + 1u;
  }
  k = 0u; while (k < nsz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  if (taut || nsz <= 2u) {
    ar[cr] = hdr | PH_GARB;
    h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
    if (!taut && nsz == 1u && !full_add_unit(h, tmp[0])) { return false; }
    if (!taut && nsz == 2u) {
      u64 ab = full_add_bin(h, tmp[0], tmp[1]);
      if (ab == 20ULL) { return false; }
      if (ab == 2ULL) { h->oom = 1ULL; }
    }
    return true;
  }
  k = 0u; while (k < nsz) { ar[(u64)cr + 3ULL + (u64)k] = tmp[k]; k = k + 1u; }
  if (nsz < sz) {
    ar[(u64)cr + 2ULL] = nsz; ar[(u64)cr + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[cr] = hdr | PH_SHRK; ar[(u64)cr + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
    }
  }
  if (!has_rl && !full_watch_push(h, rl, nsz & PW_LIT_MASK, cr, 2u)) { h->oom = 1ULL; }
  return true;
}

bool full_m6_els_lit(FullHdr *h, u32 l, u32 rl) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *repr = (u32 *)h->repr; u64 nlits = h->cur_vars << 1;
  u64 guard = (u64)wvec[((u64)l << 1) + 1ULL];
  while (guard > 0ULL && wvec[((u64)l << 1) + 1ULL] > 0u &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    guard = guard - 1ULL;
    u64 off = (u64)wvec[(u64)l << 1];
    u64 sz = (u64)wvec[((u64)l << 1) + 1ULL];
    u32 w0 = wstk[off];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wvec[(u64)l << 1] = (u32)(off + 1ULL);
      wvec[((u64)l << 1) + 1ULL] = (u32)(sz - 1ULL);
      h->wusable = h->wusable + 1ULL;
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        u64 ooff = (u64)wvec[(u64)ot << 1];
        u64 osz = (u64)wvec[((u64)ot << 1) + 1ULL];
        if (osz > 0ULL) {
          u64 op = ooff; u64 oq = ooff; u64 oend = ooff + osz; bool orem = false;
          while (op < oend) {
            u32 ow = wstk[op]; op = op + 1ULL;
            if ((ow & PW_BIN_FLAG) != 0u) {
              if (!orem && (ow & PW_LIT_MASK) == l) { orem = true; }
              else { wstk[oq] = ow; oq = oq + 1ULL; }
            } else if (op < oend) {
              wstk[oq] = ow; wstk[oq + 1ULL] = wstk[op]; oq = oq + 2ULL; op = op + 1ULL;
            }
          }
          u64 ok = oq; while (ok < oend) { wstk[ok] = 0xFFFFFFFFu; ok = ok + 1ULL; }
          wvec[((u64)ot << 1) + 1ULL] = (u32)(oq - ooff);
          h->wusable = h->wusable + (oend - oq);
          if (orem && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
        }
      }
      u32 rot = ot;
      if ((u64)rot >= nlits || rl == (rot ^ 1u)) { continue; }
      if (rl == rot) { if (!full_add_unit(h, rl)) { return false; } continue; }
      u64 ab = full_add_bin(h, rl, rot);
      if (ab == 20ULL) { return false; }
      if (ab == 2ULL) { h->oom = 1ULL; return true; }
      continue;
    }
    if (sz < 2ULL) { wvec[((u64)l << 1) + 1ULL] = 0u; break; }
    u32 cr = wstk[off + 1ULL];
    wvec[(u64)l << 1] = (u32)(off + 2ULL);
    wvec[((u64)l << 1) + 1ULL] = (u32)(sz - 2ULL);
    h->wusable = h->wusable + 2ULL;
    if (!full_m6_els_ar(h, cr, rl)) { return false; }
  }
  return h->inconsistent == 0ULL;
}

bool full_m6_dense_els(FullHdr *h, u32 neq) {
  if (neq == 0u || h->inconsistent != 0ULL) { return h->inconsistent == 0ULL; }
  u32 *repr = (u32 *)h->repr; u32 *eqb = (u32 *)h->work_stk2;
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u64 ei = 0ULL;
  while (ei < (u64)neq && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 a = eqb[ei << 1]; u32 b = eqb[(ei << 1) + 1u];
    ei = ei + 1ULL;
    if ((u64)a >= nlits || (u64)b >= nlits) { continue; }
    u32 ra = full_cong_find(repr, a);
    u32 rb = full_cong_find(repr, b);
    if (ra == rb) { continue; }
    if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return false; }
    if (rb < ra) { u32 tmp = ra; ra = rb; rb = tmp; }
    i8 va = vals[ra]; i8 vb = vals[rb];
    if (va != (i8)0 && vb != (i8)0) {
      if (va != vb) { h->inconsistent = 1ULL; return false; }
      continue;
    }
    if (va != (i8)0) {
      u32 u = (va > (i8)0) ? rb : (rb ^ 1u);
      if (!full_add_unit(h, u)) { return false; }
      continue;
    }
    if (vb != (i8)0) {
      u32 u = (vb > (i8)0) ? ra : (ra ^ 1u);
      if (!full_add_unit(h, u)) { return false; }
      continue;
    }
    if ((fl[ra >> 1] & FL_ACTIVE) == 0u || (fl[rb >> 1] & FL_ACTIVE) == 0u) { continue; }
    repr[rb] = ra;
    repr[rb ^ 1u] = ra ^ 1u;
    fl[rb >> 1] = fl[rb >> 1] & (~(FL_SWEEP | 0x40000000u | 0x20000000u));
    h->sweep_cnt = h->sweep_cnt + 1ULL;
    if (!full_m6_els_lit(h, rb, ra)) { return false; }
    if (!full_m6_els_lit(h, rb ^ 1u, ra ^ 1u)) { return false; }
    u64 ab1 = full_add_bin(h, rb | 0u, ra ^ 1u);
    if (ab1 == 20ULL) { return false; }
    if (ab1 == 2ULL) { h->oom = 1ULL; return true; }
    u64 ab2 = full_add_bin(h, rb ^ 1u, ra);
    if (ab2 == 20ULL) { return false; }
    if (ab2 == 2ULL) { h->oom = 1ULL; return true; }
  }
  if (h->inconsistent != 0ULL) { return false; }
  return full_m6_dense_prop(h);
}

u64 full_m6_sweep_var(FullHdr *h, u32 root_v, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 1ULL; }
  u32 *s_repr = (u32 *)h->repr;
  if (full_cong_find(s_repr, root_v << 1) != (root_v << 1)) { return 1ULL; }
  u64 pk = full_m6_sweep_cone(h, root_v);
  u32 nv = (u32)(pk & 0xFFFFULL); u32 nc = (u32)(pk >> 16);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (k[K6H_INCONS] != 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (nv < 2u || nc == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 1ULL;
  }
  u32 rbit = full_m6_sweep_sim(h, nv, tick_lim);
  if (rbit == 0xFFFFFFFFu) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (rbit == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 1ULL;
  }
  u64 ur = full_m6_sweep_units(h, nv, rbit, tick_lim);
  if (ur == 0xFFFFFFFFFFFFFFFFULL) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 20ULL;
  }
  u64 cr = full_m6_sweep_classes(h, nv, (u32)ur, tick_lim);
  u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
  if (cr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  u32 neq = k[K6H_NEQ];
  if (neq > 0u && !full_m6_dense_els(h, neq)) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u32 full_m6_collect_cands(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv == 0ULL) { return 0u; }
  u32 *gu = (u32 *)h->glue_used;
  u32 comp = gu[SWP_GU_COMPLETED];
  if (comp > 5u) { comp = 5u; }
  u64 max_occ = (u64)(1024u << comp);
  u64 cur = (u64)gu[SWP_GU_CURSOR];
  if (cur >= cv) { cur = 0ULL; }
  u32 *cands = (u32 *)h->tarjan_reach; u32 *deg = (u32 *)h->work_stk2;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 nc = 0u; u64 step = 0ULL;
  while (step < cv) {
    u64 v = cur + step;
    if (v >= cv) { v = v - cv; }
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
      u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
      if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
        u64 d = dp + dn;
        u32 d32 = (d > 0x3FFFFFFFULL) ? 0x3FFFFFFFu : (u32)d;
        u32 flv = fl[v];
        if ((flv & FL_SWEEP_INR) == 0u) {
          d32 = d32 | (((flv & FL_SWEEP_INC) != 0u) ? 0x40000000u : 0x80000000u);
        }
        deg[v] = d32;
        cands[nc] = (u32)v; nc = nc + 1u;
      }
    }
    step = step + 1ULL;
  }
  if (nc < 2u) { return nc; }
  u32 s = nc >> 1;
  while (s > 0u) { s = s - 1u; full_m6_cand_sift(cands, deg, s, nc); }
  u32 end = nc;
  while (end > 1u) {
    end = end - 1u;
    u32 t = cands[0]; cands[0] = cands[end]; cands[end] = t;
    full_m6_cand_sift(cands, deg, 0u, end);
  }
  return nc;
}

u64 full_m6_sweep_vars(FullHdr *h, u64 budget, u64 tick_lim) {
  u32 *gu = (u32 *)h->glue_used;
  gu[33] = 0xFFFFFFFFu;
  gu[SWP_GU_SWEPT] = 0u;
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (!full_m6_dense_prop(h)) { return 20ULL; }
  u64 cv = h->cur_vars;
  if (cv == 0ULL) { return 1ULL; }
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 comp = gu[SWP_GU_COMPLETED];
  if (comp > 5u) { comp = 5u; }
  u64 max_occ = (u64)(1024u << comp);
  bool need_mark = (gu[SWP_GU_INCOMPLETE] == 0u);
  if (!need_mark) {
    u64 rem_inc = 0ULL; u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) ==
          (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) {
        if (vals[v << 1] == (i8)0) {
          u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
          u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
          if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
            rem_inc = rem_inc + 1ULL;
          } else {
            fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
          }
        } else {
          fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
        }
      }
      v = v + 1ULL;
    }
    if (rem_inc == 0ULL) {
      if (gu[SWP_GU_COMPLETED] < 0xFFFFFFFFu) {
        gu[SWP_GU_COMPLETED] = gu[SWP_GU_COMPLETED] + 1u;
      }
      comp = gu[SWP_GU_COMPLETED];
      if (comp > 5u) { comp = 5u; }
      max_occ = (u64)(1024u << comp);
      need_mark = true;
    }
  }
  if (need_mark) {
    u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
        u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
        if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
          fl[v] = (fl[v] & (~FL_SWEEP_INR)) | FL_SWEEP | FL_SWEEP_INC;
        } else {
          fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
        }
      } else {
        fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
      }
      v = v + 1ULL;
    }
    gu[SWP_GU_INCOMPLETE] = 1u;
    gu[SWP_GU_CURSOR] = 0u;
  }
  u32 *rp_arr = (u32 *)h->repr;
  u64 nlits_sw = cv << 1;
  u64 ri_sw = 0ULL;
  while (ri_sw < nlits_sw) { rp_arr[ri_sw] = (u32)ri_sw; ri_sw = ri_sw + 1ULL; }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *eqb = (u32 *)h->work_stk2;
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 rem_b = budget;
  u32 nc = full_m6_collect_cands(h);
  u32 ci = 0u;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci]; ci = ci + 1u;
    gu[SWP_GU_CURSOR] = ((u64)v + 1ULL < cv) ? (v + 1u) : 0u;
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
      rem_b = rem_b - 1ULL;
      u64 sw0 = h->sweep_cnt;
      if (full_m6_sweep_var(h, v, rem_ticks) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
      u64 spent = (u64)k[K6H_TICKS];
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
      if (h->sweep_cnt > sw0) {
        u32 neq = k[K6H_NEQ]; u32 ei = 0u;
        while (ei < neq && (u64)ei < cv) {
          u32 lit = eqb[ei << 1];
          if ((u64)lit < nlits_sw) {
            u32 rv = full_cong_find(rp_arr, lit) >> 1;
            if ((u64)rv < cv && (fl[rv] & FL_ACTIVE) != 0u && vals[rv << 1] == (i8)0) {
              if ((fl[rv] & FL_SWEEP_INR) == 0u && (u64)nc < (cv << 1)) {
                cands[nc] = rv; nc = nc + 1u;
              }
              fl[rv] = fl[rv] | FL_SWEEP | FL_SWEEP_INR;
            }
          }
          ei = ei + 1u;
        }
      }
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  u64 left_inc = 0ULL; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) ==
        (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) {
      if (vals[v << 1] == (i8)0) {
        u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
        u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
        if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
          left_inc = 1ULL;
          break;
        }
      }
      fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
    }
    v = v + 1ULL;
  }
  if (left_inc == 0ULL) {
    gu[SWP_GU_INCOMPLETE] = 0u;
    gu[SWP_GU_CURSOR] = 0u;
    if (gu[SWP_GU_COMPLETED] < 0xFFFFFFFFu) {
      gu[SWP_GU_COMPLETED] = gu[SWP_GU_COMPLETED] + 1u;
    }
  }
  u64 swept = budget - rem_b;
  gu[SWP_GU_SWEPT] = (swept > 0xFFFFFFFFULL) ? 0xFFFFFFFFu : (u32)swept;
  return 1ULL;
}
"

/-- Step-13 `full_dense_occ_cnt_fid` (added helper). -/
def fidStep13S1DenseOccCntFn : Fn :=
  ⟨"full_dense_occ_cnt_fid", [i64, i32, i64], [i64], full_dense_occ_cnt_fid_body⟩

/-- Step-13 `full_enter_dense_ex_fid` (added helper). -/
def fidStep13S1EnterDenseExFn : Fn :=
  ⟨"full_enter_dense_ex_fid", [i64, .bool], [.bool], full_enter_dense_ex_fid_body⟩

/-- Step-13 `full_enter_dense` (replacement). -/
def fidStep13S1EnterDenseFn : Fn :=
  ⟨"full_enter_dense", [i64], [.bool], full_enter_dense_body⟩

/-- Step-13 `full_dense_bin_roundtrip_fid` (added helper). -/
def fidStep13S1DenseBinRoundtripFn : Fn :=
  ⟨"full_dense_bin_roundtrip_fid", [i64], [], full_dense_bin_roundtrip_fid_body⟩

/-- Step-13 `full_dense_bin_sort_roundtrip_fid` (added helper). -/
def fidStep13S1DenseBinSortRoundtripFn : Fn :=
  ⟨"full_dense_bin_sort_roundtrip_fid", [i64], [], full_dense_bin_sort_roundtrip_fid_body⟩

/-- Step-13 `full_watch_large_clauses_fid` (added helper). -/
def fidStep13S1WatchLargeClausesFn : Fn :=
  ⟨"full_watch_large_clauses_fid", [i64], [], full_watch_large_clauses_fid_body⟩

/-- Step-13 `full_sort_bin_watches_fid` (replacement). -/
def fidStep13S1SortBinWatchesFn : Fn :=
  ⟨"full_sort_bin_watches_fid", [i64], [], full_sort_bin_watches_fid_body⟩

/-- Step-13 `full_m6_els_ar` (replacement). -/
def fidStep13S1ElsArFn : Fn :=
  ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], full_m6_els_ar_body⟩

/-- Step-13 `full_m6_els_lit` (replacement). -/
def fidStep13S1ElsLitFn : Fn :=
  ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], full_m6_els_lit_body⟩

/-- Step-13 `full_m6_dense_els` (replacement). -/
def fidStep13S1DenseElsFn : Fn :=
  ⟨"full_m6_dense_els", [i64, i32], [.bool], full_m6_dense_els_body⟩

/-- Step-13 `full_m6_sweep_var` (replacement). -/
def fidStep13S1SweepVarFn : Fn :=
  ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], full_m6_sweep_var_body⟩

/-- Step-13 `full_m6_collect_cands` (replacement). -/
def fidStep13S1CollectCandsFn : Fn :=
  ⟨"full_m6_collect_cands", [i64], [i32], full_m6_collect_cands_body⟩

/-- Step-13 `full_m6_sweep_vars` (replacement). -/
def fidStep13S1SweepVarsFn : Fn :=
  ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_body⟩

/-- Ordered `5`-function Step-13 S1-A addition list. -/
def fidStep13S1SweepDenseAdds : List Fn :=
  [ fidStep13S1DenseOccCntFn
  , fidStep13S1EnterDenseExFn
  , fidStep13S1DenseBinRoundtripFn
  , fidStep13S1DenseBinSortRoundtripFn
  , fidStep13S1WatchLargeClausesFn ]

/-- Ordered `8`-function Step-13 S1-A replacement list. -/
def fidStep13S1SweepDenseRepls : List Fn :=
  [ fidStep13S1EnterDenseFn
  , fidStep13S1SortBinWatchesFn
  , fidStep13S1ElsArFn
  , fidStep13S1ElsLitFn
  , fidStep13S1DenseElsFn
  , fidStep13S1SweepVarFn
  , fidStep13S1CollectCandsFn
  , fidStep13S1SweepVarsFn ]

end

public section

theorem fidStep13S1DenseOccCnt_wf : Func.Wf fidStep13S1DenseOccCntFn.body := by t_wf_reify
theorem fidStep13S1EnterDenseEx_wf : Func.Wf fidStep13S1EnterDenseExFn.body := by t_wf_reify
theorem fidStep13S1EnterDense_wf : Func.Wf fidStep13S1EnterDenseFn.body := by t_wf_reify
theorem fidStep13S1DenseBinRoundtrip_wf :
    Func.Wf fidStep13S1DenseBinRoundtripFn.body := by t_wf_reify
theorem fidStep13S1DenseBinSortRoundtrip_wf :
    Func.Wf fidStep13S1DenseBinSortRoundtripFn.body := by t_wf_reify
theorem fidStep13S1WatchLargeClauses_wf :
    Func.Wf fidStep13S1WatchLargeClausesFn.body := by t_wf_reify
theorem fidStep13S1SortBinWatches_wf :
    Func.Wf fidStep13S1SortBinWatchesFn.body := by t_wf_reify
theorem fidStep13S1ElsAr_wf : Func.Wf fidStep13S1ElsArFn.body := by t_wf_reify
theorem fidStep13S1ElsLit_wf : Func.Wf fidStep13S1ElsLitFn.body := by t_wf_reify
theorem fidStep13S1DenseEls_wf : Func.Wf fidStep13S1DenseElsFn.body := by t_wf_reify
theorem fidStep13S1SweepVar_wf : Func.Wf fidStep13S1SweepVarFn.body := by t_wf_reify
theorem fidStep13S1CollectCands_wf : Func.Wf fidStep13S1CollectCandsFn.body := by t_wf_reify
theorem fidStep13S1SweepVars_wf : Func.Wf fidStep13S1SweepVarsFn.body := by t_wf_reify

theorem fidStep13S1SweepDenseAdds_wf : ∀ f ∈ fidStep13S1SweepDenseAdds, f.Wf := by
  intro f hf
  simp only [fidStep13S1SweepDenseAdds, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact fidStep13S1DenseOccCnt_wf
  · exact fidStep13S1EnterDenseEx_wf
  · exact fidStep13S1DenseBinRoundtrip_wf
  · exact fidStep13S1DenseBinSortRoundtrip_wf
  · exact fidStep13S1WatchLargeClauses_wf

theorem fidStep13S1SweepDenseRepls_wf : ∀ f ∈ fidStep13S1SweepDenseRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S1SweepDenseRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fidStep13S1EnterDense_wf
  · exact fidStep13S1SortBinWatches_wf
  · exact fidStep13S1ElsAr_wf
  · exact fidStep13S1ElsLit_wf
  · exact fidStep13S1DenseEls_wf
  · exact fidStep13S1SweepVar_wf
  · exact fidStep13S1CollectCands_wf
  · exact fidStep13S1SweepVars_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

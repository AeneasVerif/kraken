module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave-4E (`FullM7BveGates`): Faithful BVE Gate Extraction & `>1000`-Occ Forward Skip

100% additive drop-in replacement for `FullM6BveFwd` (`0` `FullHdr` edits — `144` words frozen):
1. **`full_fwd_scan_lit_m7` (`forward.c` `subsumeocclim = 1000`):** skips literals with
   `wsz == 0` or `wsz > 1000` upfront before scanning watches (`0` wasted clause visits on
   high-degree literals).
2. **`full_bve_gates_m7`:**
   - `O(np + nn)` equivalence extraction (`full_bve_find_equiv_m7`).
   - Dual-polarity `O(np + nn)` AND extraction (`full_bve_find_and_m7` on `pl` & `nl`).
   - Dual-polarity `ifthenelse` extraction (`full_bve_find_ite_side_m7` on `pl` & `nl`,
     `large^2 <= 2000`, `steps < 2000`, shortened `resolve_gate = 1`, `j0 != j1`).
   - Structural XOR extraction (`full_bve_find_xor_m7`, `k = 2..4`, `lp * ln <= 4096`,
     `resolve_gate = 0`).
   - Self-contained bounded `K6` semantic definition fallback (`mv = 64`, `mc = 256`,
     `max_orig = 128`, `tick_lim = 512`, `scratch_buf[1096..)` when `scratch_cap >= 8192`),
     dropping the unbounded `full_find_definition` (`K512`) extern (`23` canonical externs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7BveGates "
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

#define PH_GARB      0x00080000u
#define PH_RED       0x00400000u
#define PH_SHRK      0x00800000u
#define PH_SUBSUME   0x01000000u
#define PW_BIN_FLAG  0x80000000u
#define PW_LIT_MASK  0x7FFFFFFFu

#define FL_ACTIVE    1u
#define FL_ELIM      2u
#define FL_SUBSUME   8u
#define FL_ELIM_C    16u

#define K6_BASE      1096u
#define K6_MV        64u
#define K6_MC        256u
#define K6_MAX_ORIG  128u
#define K6_BIN_FLAG  0x80000000u
#define K6_LIT_MASK  0x7FFFFFFFu
#define KM_LRN       0x40000000u
#define KM_CORE      0x20000000u

#define KH_NV        0u
#define KH_NC        1u
#define KH_ORIG_NC   2u
#define KH_LVL       3u
#define KH_PROP      4u
#define KH_TRL_END   5u
#define KH_UNASS     6u
#define KH_INCONS    7u
#define KH_QFIRST    8u
#define KH_QLAST     9u
#define KH_QSEARCH   10u
#define KH_QSTAMP    11u
#define KH_TICKS     12u
#define KH_TICK_LIM  13u
#define KH_ALEN      14u
#define KH_ACAP      15u
#define KH_NANA      16u
#define KH_NKL       17u
#define KH_NRES      18u
#define KH_NUNITS    19u
#define KH_OPEN      20u
#define KH_PHASE     21u

#define KO_LVL       32u
#define KO_RSN       96u
#define KO_QPREV     160u
#define KO_QNEXT     224u
#define KO_QST       288u
#define KO_TRL       352u
#define KO_FLAGS     416u
#define KO_ANA       480u
#define KO_KL        544u
#define KO_VALS      608u
#define KO_WHEAD     736u
#define KO_WNEXT     864u
#define KO_WBLIT     1376u
#define KO_CL_OFF    1888u
#define KO_CL_META   2144u
#define KO_CL_AUX    2400u
#define KO_UNITS     2656u
#define KO_RES       2784u
#define KO_ARENA     2912u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref);
extern bool full_fwd_dedup_bins(FullHdr *h);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern bool full_bve_try_bce(FullHdr *h, u32 blk_lit, u32 cr, u32 opp_off, u32 opp_n);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_ilog10(u64 x);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_min_u64(u64 a, u64 b);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_rebuild_watches(FullHdr *h);

bool full_dense_prop_unit_m7(FullHdr *h, u32 lit) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  if ((u64)lit >= nlits || vals[lit] <= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 nl = lit ^ 1u;
  u64 off = (u64)wvec[(u64)nl << 1];
  u64 end = off + (u64)wvec[((u64)nl << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      i8 vo = vals[ot];
      if (vo < (i8)0) { h->inconsistent = 1ULL; return false; }
      if (vo == (i8)0 && !full_add_unit(h, ot)) { return false; }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    u32 hdr = ar[cr];
    if ((hdr & PH_GARB) != 0u) { continue; }
    u32 sz = ar[(u64)cr + 2ULL];
    bool sat = false;
    u32 unass = 0u;
    u32 ulit = 0u;
    u32 k = 0u;
    while (k < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)k];
      i8 vl = vals[cl];
      if (vl > (i8)0) { sat = true; break; }
      if (vl == (i8)0) { unass = unass + 1u; ulit = cl; }
      k = k + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    } else if (unass == 0u) {
      h->inconsistent = 1ULL;
      return false;
    } else if (unass == 1u) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, ulit)) { return false; }
    }
  }
  off = (u64)wvec[(u64)lit << 1];
  end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    u32 hdr = ar[cr];
    if ((hdr & PH_GARB) != 0u) { continue; }
    u32 sz = ar[(u64)cr + 2ULL];
    bool sat = false;
    u32 k = 0u;
    while (k < sz) {
      if (vals[ar[(u64)cr + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
      k = k + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    }
  }
  return true;
}

bool full_dense_flush_units_m7(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  u64 q = h->propagated;
  while (q < h->trail_end && h->inconsistent == 0ULL) {
    u32 lit = trl[q];
    q = q + 1ULL;
    if (!full_dense_prop_unit_m7(h, lit)) { return false; }
  }
  h->propagated = (q <= h->trail_end) ? q : h->trail_end;
  return h->inconsistent == 0ULL;
}

void full_fwd_flush_large_m7(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 0ULL) {
      u64 p = off;
      u64 q = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          wstk[q] = w0;
          q = q + 1ULL;
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      u64 c = q;
      while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
      wvec[(l << 1) + 1ULL] = (u32)(q - off);
      h->wusable = h->wusable + (end - q);
    }
    l = l + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
}

void full_fwd_reconnect_irred_m7(FullHdr *h) {
  full_fwd_flush_large_m7(h);
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 p = 0ULL;
  while (p < h->arena_len && h->oom == 0ULL) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      bool sat = false;
      u32 k = 0u;
      while (k < sz) {
        if (vals[ar[p + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
        k = k + 1u;
      }
      if (sat) {
        ar[p] = hdr | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      } else {
        k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (!full_watch_push(h, l, sz & PW_LIT_MASK, (u32)p, 2u)) {
            h->oom = 1ULL;
            break;
          }
          k = k + 1u;
        }
      }
    }
    p = np;
  }
}

u32 full_fwd_scan_lit_m7(FullHdr *h, u32 cref, u32 sz, u32 scan_lit, bool check_bins) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)scan_lit << 1];
  u64 wsz = (u64)wvec[((u64)scan_lit << 1) + 1ULL];
  if (wsz == 0ULL || wsz > 1000ULL) { return 0xFFFFFFFFu; }
  u64 end = off + wsz;
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if (check_bins) {
        u32 ot = w0 & PW_LIT_MASK;
        if (lm[ot] != (u8)0) { return 0xFFFFFFFEu; }
        if ((ot ^ 1u) != scan_lit && lm[ot ^ 1u] != (u8)0) { return ot ^ 1u; }
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    if (cr == cref || (ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
    u32 dsz = ar[(u64)cr + 2ULL];
    if (dsz > sz) { continue; }
    u32 miss = 0u;
    u32 cand = 0xFFFFFFFFu;
    u32 j = 0u;
    while (j < dsz) {
      u32 dl = ar[(u64)cr + 3ULL + (u64)j];
      if (lm[dl] == (u8)0 && vals[dl] >= (i8)0) {
        if (lm[dl ^ 1u] != (u8)0 && cand == 0xFFFFFFFFu) { cand = dl ^ 1u; }
        else { miss = 1u; break; }
      }
      j = j + 1u;
    }
    if (miss == 0u) {
      if (cand == 0xFFFFFFFFu) { return 0xFFFFFFFEu; }
      return cand;
    }
  }
  return 0xFFFFFFFFu;
}

bool full_fwd_check_cl_m7(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return true; }
  while (true) {
    bool sat = false;
    u32 drop = 0xFFFFFFFFu;
    u32 i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      i8 vl = vals[l];
      if (vl > (i8)0) { sat = true; break; }
      if (vl < (i8)0 && drop == 0xFFFFFFFFu) { drop = l; }
      i = i + 1u;
    }
    if (sat) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      return true;
    }
    bool subsumed = false;
    if (drop == 0xFFFFFFFFu) {
      u32 min_l = ar[(u64)cref + 3ULL];
      u32 min_deg = wvec[((u64)min_l << 1) + 1ULL];
      i = 0u;
      while (i < sz) {
        u32 l = ar[(u64)cref + 3ULL + (u64)i];
        lm[l] = (u8)1;
        u32 d = wvec[((u64)l << 1) + 1ULL];
        if (d < min_deg) { min_deg = d; min_l = l; }
        i = i + 1u;
      }
      i = 0u;
      while (i < sz && !subsumed && drop == 0xFFFFFFFFu) {
        u32 l = (i == 0u) ? min_l : ar[(u64)cref + 3ULL + (u64)i];
        if (i > 0u && l == min_l) { l = ar[(u64)cref + 3ULL]; }
        u32 r1 = full_fwd_scan_lit_m7(h, cref, sz, l, true);
        if (r1 == 0xFFFFFFFEu) { subsumed = true; break; }
        if (r1 != 0xFFFFFFFFu) { drop = r1; break; }
        u32 r2 = full_fwd_scan_lit_m7(h, cref, sz, l ^ 1u, false);
        if (r2 == 0xFFFFFFFEu) { subsumed = true; break; }
        if (r2 != 0xFFFFFFFFu) { drop = r2; break; }
        i = i + 1u;
      }
      i = 0u;
      while (i < sz) { lm[ar[(u64)cref + 3ULL + (u64)i]] = (u8)0; i = i + 1u; }
    }
    if (subsumed) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      h->fwd_sub_cnt = h->fwd_sub_cnt + 1ULL;
      return true;
    }
    if (drop == 0xFFFFFFFFu) { return true; }
    h->fwd_str_cnt = h->fwd_str_cnt + 1ULL;
    full_unwatch_large(h, drop, cref);
    u32 nsz = 0u;
    i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      if (l != drop) { tmp[nsz] = l; nsz = nsz + 1u; }
      i = i + 1u;
    }
    if (nsz >= sz) { return true; }
    if (nsz == 0u) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      h->inconsistent = 1ULL;
      return false;
    }
    if (nsz == 1u) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, tmp[0])) { return false; }
      return full_dense_flush_units_m7(h);
    }
    if (nsz == 2u) {
      u32 b0 = tmp[0];
      u32 b1 = tmp[1];
      u64 br = full_add_bin(h, b0, b1);
      if (br == 20ULL) { return false; }
      if (br == 2ULL) { return true; }
      ar[cref] = hdr | PH_GARB | PH_SUBSUME;
      ar[(u64)cref + 3ULL] = b0;
      ar[(u64)cref + 4ULL] = b1;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      return full_dense_flush_units_m7(h);
    }
    i = 0u;
    while (i < nsz) { ar[(u64)cref + 3ULL + (u64)i] = tmp[i]; i = i + 1u; }
    ar[(u64)cref + 2ULL] = nsz;
    ar[(u64)cref + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[(u64)cref + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
      hdr = hdr | PH_SHRK;
      ar[cref] = hdr;
    }
    hdr = hdr | PH_SUBSUME;
    ar[cref] = hdr;
    sz = nsz;
  }
  return true;
}

void full_fwd_connect_subsumer_m7(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *fl = (u32 *)h->flags;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return; }
  u32 best_l = ar[(u64)cref + 3ULL];
  u32 best_d = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if ((fl[l >> 1] & FL_SUBSUME) != 0u) {
      u32 d = wvec[((u64)l << 1) + 1ULL];
      if (d < best_d) { best_d = d; best_l = l; }
    }
    i = i + 1u;
  }
  if (best_d == 0xFFFFFFFFu) {
    best_d = wvec[((u64)best_l << 1) + 1ULL];
    i = 1u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      u32 d = wvec[((u64)l << 1) + 1ULL];
      if (d < best_d) { best_d = d; best_l = l; }
      i = i + 1u;
    }
  }
  if (best_d <= 1000u) {
    if (!full_watch_push(h, best_l, sz & PW_LIT_MASK, cref, 2u)) { h->oom = 1ULL; }
  }
}

u64 full_fwd_collect_sort_m7(FullHdr *h) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *rr = (u32 *)h->red_refs;
  u64 half = h->red_cap >> 1;
  u64 ncand = 0ULL;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      if ((hdr & PH_SUBSUME) != 0u) {
        hdr = hdr & (~PH_SUBSUME);
        ar[p] = hdr;
      }
      bool sat = false;
      u32 scnt = 0u;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        i8 vl = vals[l];
        if (vl > (i8)0) { sat = true; break; }
        if (vl == (i8)0 && (fl[l >> 1] & FL_SUBSUME) != 0u) { scnt = scnt + 1u; }
        k = k + 1u;
      }
      if (sat) {
        ar[p] = hdr | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      } else if (sz <= 1000u && scnt >= 2u && ncand < half) {
        rr[ncand] = (u32)p;
        ncand = ncand + 1ULL;
      }
    }
    p = np;
  }
  if (ncand > 1ULL && h->scratch_cap >= 1008ULL) {
    u32 *scr = (u32 *)h->scratch_buf;
    u64 b = 0ULL;
    while (b <= 1000ULL) { scr[b] = 0u; b = b + 1ULL; }
    u64 i = 0ULL;
    while (i < ncand) {
      u32 cr = rr[i];
      rr[half + i] = cr;
      u32 sz = ar[(u64)cr + 2ULL];
      if (sz <= 1000u) { scr[sz] = scr[sz] + 1u; }
      i = i + 1ULL;
    }
    u32 sum = 0u;
    b = 0ULL;
    while (b <= 1000ULL) {
      u32 cnt = scr[b];
      scr[b] = sum;
      sum = sum + cnt;
      b = b + 1ULL;
    }
    i = 0ULL;
    while (i < ncand) {
      u32 cr = rr[i];
      u32 sz = ar[(u64)cr + 2ULL];
      if (sz <= 1000u) {
        u64 pos = (u64)scr[sz];
        if (pos < ncand) {
          rr[half + pos] = cr;
          scr[sz] = (u32)(pos + 1ULL);
        }
      }
      i = i + 1ULL;
    }
    i = 0ULL;
    while (i < ncand) { rr[i] = rr[half + i]; i = i + 1ULL; }
  }
  return ncand;
}

u64 full_forward_sub_m7(FullHdr *h, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  u64 ncand = full_fwd_collect_sort_m7(h);
  if (ncand == 0ULL) { return (h->inconsistent != 0ULL) ? 20ULL : 1ULL; }
  full_fwd_flush_large_m7(h);
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  u64 rem = budget;
  while (i < ncand && rem > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 cr = rr[i];
    rem = rem - 1ULL;
    if (!full_fwd_check_cl_m7(h, cr)) { return 20ULL; }
    if (h->oom == 0ULL && h->inconsistent == 0ULL && (ar[cr] & PH_GARB) == 0u) {
      full_fwd_connect_subsumer_m7(h, cr);
    }
    i = i + 1ULL;
  }
  if (i == ncand && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 *fl = (u32 *)h->flags;
    u64 cv = h->cur_vars;
    u64 v = 0ULL;
    while (v < cv) { fl[v] = fl[v] & (~FL_SUBSUME); v = v + 1ULL; }
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_SUBSUME) != 0u) {
        ar[p] = hdr & (~PH_SUBSUME);
        if ((hdr & PH_GARB) == 0u) {
          u32 k = 0u;
          while (k < sz) {
            u32 lv = ar[p + 3ULL + (u64)k] >> 1;
            if ((u64)lv < cv) { fl[lv] = fl[lv] | FL_SUBSUME | FL_ELIM_C; }
            k = k + 1u;
          }
        } else if (sz >= 2u) {
          u32 v0 = ar[p + 3ULL] >> 1;
          u32 v1 = ar[p + 4ULL] >> 1;
          if ((u64)v0 < cv) { fl[v0] = fl[v0] | FL_SUBSUME | FL_ELIM_C; }
          if ((u64)v1 < cv) { fl[v1] = fl[v1] | FL_SUBSUME | FL_ELIM_C; }
        }
      }
      p = np;
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  full_fwd_reconnect_irred_m7(h);
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 p = off;
  u32 cnt = 0u;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if (vals[ot] > (i8)0) { continue; }
      if (cnt >= cap) { return 0xFFFFFFFFu; }
      out[cnt] = w0;
      cnt = cnt + 1u;
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    if ((ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
    if (ar[(u64)cr + 2ULL] > 100u) { return 0xFFFFFFFFu; }
    if (cnt >= cap) { return 0xFFFFFFFFu; }
    out[cnt] = cr;
    cnt = cnt + 1u;
  }
  return cnt;
}

bool full_bve_mark_and_m7(FullHdr *h, u32 v_lit, u32 cr, u32 n_off, u32 nn, u32 mask_off) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 sz = ar[(u64)cr + 2ULL];
  u32 need = 0u;
  bool sat = false;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) {
      i8 vl = vals[l];
      if (vl > (i8)0) { sat = true; break; }
      if (vl == (i8)0) {
        lm[l ^ 1u] = (u8)1;
        need = need + 1u;
      }
    }
    i = i + 1u;
  }
  if (sat || need == 0u) {
    i = 0u;
    while (i < sz) { lm[ar[(u64)cr + 3ULL + (u64)i] ^ 1u] = (u8)0; i = i + 1u; }
    return false;
  }
  u32 k = 0u;
  while (k < 16u) { scr[mask_off + k] = 0u; k = k + 1u; }
  u32 matched = 0u;
  u32 j = 0u;
  while (j < nn) {
    u32 w = scr[n_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (lm[ot] == (u8)1) {
        lm[ot] = (u8)2;
        u32 idx = mask_off + (j >> 5);
        scr[idx] = scr[idx] | (1u << (j & 31u));
        matched = matched + 1u;
      }
    }
    j = j + 1u;
  }
  i = 0u;
  while (i < sz) { lm[ar[(u64)cr + 3ULL + (u64)i] ^ 1u] = (u8)0; i = i + 1u; }
  if (matched >= need) { return true; }
  k = 0u;
  while (k < 16u) { scr[mask_off + k] = 0u; k = k + 1u; }
  return false;
}

bool full_bve_find_equiv_m7(FullHdr *h, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 bin_p = 0u;
  u32 i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) {
      u32 ot = wp & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { lm[ot] = (u8)1; bin_p = bin_p + 1u; }
    }
    i = i + 1u;
  }
  if (bin_p == 0u) { return false; }
  u32 match_lit = 0xFFFFFFFFu;
  u32 match_j = 0u;
  u32 j = 0u;
  while (j < nn) {
    u32 wn = scr[512u + j];
    if ((wn & PW_BIN_FLAG) != 0u) {
      u32 ot = wn & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot ^ 1u] != (u8)0) {
        match_lit = ot ^ 1u;
        match_j = j;
        break;
      }
    }
    j = j + 1u;
  }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) { lm[wp & PW_LIT_MASK] = (u8)0; }
    i = i + 1u;
  }
  if (match_lit == 0xFFFFFFFFu) { return false; }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u && (wp & PW_LIT_MASK) == match_lit) {
      scr[1024u + (i >> 5)] = 1u << (i & 31u);
      scr[1040u + (match_j >> 5)] = 1u << (match_j & 31u);
      scr[1056] = 1u;
      scr[1057] = 0u;
      return true;
    }
    i = i + 1u;
  }
  return false;
}

bool full_bve_find_and_m7(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n) {
  u32 pol = lit & 1u;
  u32 lit_off = pol << 9;
  u32 opp_off = 512u - lit_off;
  u32 lit_mask = 1024u + (pol << 4);
  u32 opp_mask = 2064u - lit_mask;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 bin_cnt = 0u;
  u32 j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot] == (u8)0) { lm[ot] = (u8)1; bin_cnt = bin_cnt + 1u; }
    }
    j = j + 1u;
  }
  if (bin_cnt < 1u) {
    j = 0u;
    while (j < opp_n) {
      u32 w = scr[opp_off + j];
      if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
      j = j + 1u;
    }
    return false;
  }
  u32 found_i = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < lit_n) {
    u32 w = scr[lit_off + i];
    if ((w & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true;
      u32 need = 0u;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        if (l != lit) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if (lm[l ^ 1u] == (u8)0) { ok = false; break; }
            need = need + 1u;
          }
        }
        k = k + 1u;
      }
      if (ok && need >= 1u) { found_i = i; break; }
    }
    i = i + 1u;
  }
  j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
    j = j + 1u;
  }
  if (found_i == 0xFFFFFFFFu) { return false; }
  u32 cr = scr[lit_off + found_i];
  u32 sz = ar[(u64)cr + 2ULL];
  u32 uniq_need = 0u;
  u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit && vals[l] == (i8)0 && lm[l ^ 1u] == (u8)0) {
      lm[l ^ 1u] = (u8)1;
      uniq_need = uniq_need + 1u;
    }
    k = k + 1u;
  }
  u32 matched = 0u;
  j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (lm[ot] == (u8)1) {
        lm[ot] = (u8)0;
        u32 midx = opp_mask + (j >> 5);
        scr[midx] = scr[midx] | (1u << (j & 31u));
        matched = matched + 1u;
      }
    }
    j = j + 1u;
  }
  k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit) { lm[l ^ 1u] = (u8)0; }
    k = k + 1u;
  }
  if (matched == uniq_need && uniq_need >= 1u) {
    scr[lit_mask + (found_i >> 5)] = 1u << (found_i & 31u);
    scr[1056] = 1u;
    scr[1057] = 0u;
    return true;
  }
  k = 0u;
  while (k < 16u) { scr[opp_mask + k] = 0u; k = k + 1u; }
  return false;
}

bool full_bve_get_tern_m7(FullHdr *h, u32 v_lit, u32 cr, u32 out_off) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 sz = ar[(u64)cr + 2ULL];
  u32 cnt = 0u;
  u32 l0 = 0u;
  u32 l1 = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) {
      i8 vl = vals[l];
      if (vl > (i8)0) { return false; }
      if (vl == (i8)0) {
        if (cnt == 0u) { l0 = l; }
        else if (cnt == 1u) { l1 = l; }
        else { return false; }
        cnt = cnt + 1u;
      }
    }
    i = i + 1u;
  }
  if (cnt != 2u) { return false; }
  scr[out_off] = l0;
  scr[out_off + 1u] = l1;
  return true;
}

u32 full_bve_match_tern_m7(FullHdr *h, u32 opp_lit, u32 x, u32 y, u32 opp_off, u32 opp_n) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 j = 0u;
  while (j < opp_n && scr[1058] < 2000u) {
    scr[1058] = scr[1058] + 1u;
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (ot == x || ot == y) { return j | 0x80000000u; }
    } else {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true;
      bool sx = false;
      bool sy = false;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        i8 vl = vals[l];
        if (vl > (i8)0) { ok = false; break; }
        if (vl == (i8)0 && l != opp_lit) {
          if (l == x) { sx = true; }
          else if (l == y) { sy = true; }
          else { ok = false; break; }
        }
        k = k + 1u;
      }
      if (ok) {
        if (sx && sy) { return j; }
        if (sx || sy) { return j | 0x80000000u; }
      }
    }
    j = j + 1u;
  }
  return 0xFFFFFFFFu;
}

bool full_bve_find_ite_side_m7(FullHdr *h, u32 v, u32 np, u32 nn, bool neg) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 lit = (v << 1) | (neg ? 1u : 0u);
  u32 opp = lit ^ 1u;
  u32 lit_off = neg ? 512u : 0u;
  u32 lit_n = neg ? nn : np;
  u32 opp_off = neg ? 0u : 512u;
  u32 opp_n = neg ? np : nn;
  u32 lit_mask = neg ? 1040u : 1024u;
  u32 opp_mask = neg ? 1024u : 1040u;
  if (lit_n < 2u || opp_n < 2u) { return false; }
  u64 large_clauses = 0ULL;
  u32 idx = 0u;
  while (idx < lit_n) {
    if ((scr[lit_off + idx] & PW_BIN_FLAG) == 0u) { large_clauses = large_clauses + 1ULL; }
    idx = idx + 1u;
  }
  if (large_clauses < 2ULL || large_clauses * large_clauses > 2000ULL) { return false; }
  scr[1058] = 0u;
  u32 i0 = 0u;
  while (i0 + 1u < lit_n && scr[1058] < 2000u) {
    u32 w0 = scr[lit_off + i0];
    if ((w0 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w0, 1060u)) {
      u32 a0 = scr[1060];
      u32 a1 = scr[1061];
      u32 i1 = i0 + 1u;
      while (i1 < lit_n && scr[1058] < 2000u) {
        u32 w1 = scr[lit_off + i1];
        if ((w1 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w1, 1062u)) {
          u32 b0 = scr[1062];
          u32 b1 = scr[1063];
          bool ok = false;
          u32 cond = 0u;
          u32 u = 0u;
          u32 w = 0u;
          if (a0 == (b0 ^ 1u)) { ok = true; cond = a0; u = a1; w = b1; }
          else if (a0 == (b1 ^ 1u)) { ok = true; cond = a0; u = a1; w = b0; }
          else if (a1 == (b0 ^ 1u)) { ok = true; cond = a1; u = a0; w = b1; }
          else if (a1 == (b1 ^ 1u)) { ok = true; cond = a1; u = a0; w = b0; }
          if (ok && (u >> 1) != (w >> 1)) {
            u32 m0 = full_bve_match_tern_m7(h, opp, cond, u ^ 1u, opp_off, opp_n);
            if (m0 != 0xFFFFFFFFu) {
              u32 m1 = full_bve_match_tern_m7(h, opp, cond ^ 1u, w ^ 1u, opp_off, opp_n);
              if (m1 != 0xFFFFFFFFu) {
                u32 j0 = m0 & 0x7FFFFFFFu;
                u32 j1 = m1 & 0x7FFFFFFFu;
                if (j0 != j1) {
                  u32 k0 = lit_mask + (i0 >> 5);
                  scr[k0] = scr[k0] | (1u << (i0 & 31u));
                  u32 k1 = lit_mask + (i1 >> 5);
                  scr[k1] = scr[k1] | (1u << (i1 & 31u));
                  u32 o0 = opp_mask + (j0 >> 5);
                  scr[o0] = scr[o0] | (1u << (j0 & 31u));
                  u32 o1 = opp_mask + (j1 >> 5);
                  scr[o1] = scr[o1] | (1u << (j1 & 31u));
                  scr[1056] = 1u;
                  scr[1057] = (((m0 | m1) & 0x80000000u) != 0u) ? 1u : 0u;
                  return true;
                }
              }
            }
          }
        }
        i1 = i1 + 1u;
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

bool full_bve_find_ite_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (full_bve_find_ite_side_m7(h, v, np, nn, false)) { return true; }
  return full_bve_find_ite_side_m7(h, v, np, nn, true);
}

u32 full_bve_xor_pat_m7(FullHdr *h, u32 v_lit, u32 cr, u32 k) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 sz = ar[(u64)cr + 2ULL];
  u32 pat = 0u;
  u32 seen = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) {
      i8 vl = vals[l];
      if (vl > (i8)0) { return 0xFFFFFFFFu; }
      if (vl == (i8)0) {
        u8 m = lm[l];
        if (m < (u8)2) { return 0xFFFFFFFFu; }
        u32 mv = (u32)(m - (u8)2);
        u32 idx = mv >> 1;
        u32 sgn = mv & 1u;
        if (idx >= k || ((seen >> idx) & 1u) != 0u) { return 0xFFFFFFFFu; }
        seen = seen | (1u << idx);
        if (sgn != 0u) { pat = pat | (1u << idx); }
      }
    }
    i = i + 1u;
  }
  u32 full_seen = (1u << k) - 1u;
  return (seen == full_seen) ? pat : 0xFFFFFFFFu;
}

bool full_bve_find_xor_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 1096ULL) { return false; }
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 lp = 0u;
  u32 ln = 0u;
  u32 i = 0u;
  while (i < np) {
    if ((scr[i] & PW_BIN_FLAG) == 0u) { lp = lp + 1u; }
    i = i + 1u;
  }
  i = 0u;
  while (i < nn) {
    if ((scr[512u + i] & PW_BIN_FLAG) == 0u) { ln = ln + 1u; }
    i = i + 1u;
  }
  if (lp < 2u || ln < 2u || (u64)lp * (u64)ln > 4096ULL) { return false; }
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 i0 = 0u;
  while (i0 < np) {
    u32 w0 = scr[i0];
    if ((w0 & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w0 + 2ULL];
      bool ok = true;
      u32 k = 0u;
      u32 u = 0u;
      while (u < sz) {
        u32 l = ar[(u64)w0 + 3ULL + (u64)u];
        if (l != pl) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if ((l >> 1) == v || lm[l] != (u8)0 || k >= 4u) { ok = false; break; }
            lm[l] = (u8)(2u + (k << 1));
            lm[l ^ 1u] = (u8)(3u + (k << 1));
            scr[1092u + k] = l;
            k = k + 1u;
          }
        }
        u = u + 1u;
      }
      if (ok && k >= 2u && k <= 4u) {
        u32 etgt = (k == 2u) ? 0x9u : ((k == 3u) ? 0x69u : 0x9669u);
        u32 otgt = (k == 2u) ? 0x6u : ((k == 3u) ? 0x96u : 0x6996u);
        u32 emask = 1u;
        scr[1060] = i0;
        u32 p_idx = 0u;
        while (p_idx < np && emask != etgt) {
          u32 w = scr[p_idx];
          if (p_idx != i0 && (w & PW_BIN_FLAG) == 0u) {
            u32 pat = full_bve_xor_pat_m7(h, pl, w, k);
            if (pat < 16u && ((etgt >> pat) & 1u) != 0u && ((emask >> pat) & 1u) == 0u) {
              emask = emask | (1u << pat);
              scr[1060u + pat] = p_idx;
            }
          }
          p_idx = p_idx + 1u;
        }
        u32 omask = 0u;
        if (emask == etgt) {
          u32 n_idx = 0u;
          while (n_idx < nn && omask != otgt) {
            u32 w = scr[512u + n_idx];
            if ((w & PW_BIN_FLAG) == 0u) {
              u32 pat = full_bve_xor_pat_m7(h, nl, w, k);
              if (pat < 16u && ((otgt >> pat) & 1u) != 0u && ((omask >> pat) & 1u) == 0u) {
                omask = omask | (1u << pat);
                scr[1076u + pat] = n_idx;
              }
            }
            n_idx = n_idx + 1u;
          }
        }
        u32 c = 0u;
        while (c < k) {
          u32 l = scr[1092u + c];
          lm[l] = (u8)0;
          lm[l ^ 1u] = (u8)0;
          c = c + 1u;
        }
        if (emask == etgt && omask == otgt) {
          u32 p = 0u;
          u32 nlim = 1u << k;
          while (p < nlim) {
            if (((etgt >> p) & 1u) != 0u) {
              u32 pi = scr[1060u + p];
              u32 m = 1024u + (pi >> 5);
              scr[m] = scr[m] | (1u << (pi & 31u));
            }
            if (((otgt >> p) & 1u) != 0u) {
              u32 ni = scr[1076u + p];
              u32 m = 1040u + (ni >> 5);
              scr[m] = scr[m] | (1u << (ni & 31u));
            }
            p = p + 1u;
          }
          scr[1056] = 1u;
          scr[1057] = 0u;
          return true;
        }
      } else {
        u32 c = 0u;
        while (c < k) {
          u32 l = scr[1092u + c];
          lm[l] = (u8)0;
          lm[l ^ 1u] = (u8)0;
          c = c + 1u;
        }
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

void full_k6_watch_m7(u32 *k, u32 cid, u32 l0, u32 l1, u32 sz) {
  if (cid >= K6_MC || l0 >= 128u || l1 >= 128u) { return; }
  u32 bf = (sz == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1;
  u32 w1 = w0 | 1u;
  k[KO_WBLIT + w0] = l1 | bf;
  k[KO_WNEXT + w0] = k[KO_WHEAD + l0];
  k[KO_WHEAD + l0] = w0;
  k[KO_WBLIT + w1] = l0 | bf;
  k[KO_WNEXT + w1] = k[KO_WHEAD + l1];
  k[KO_WHEAD + l1] = w1;
}

void full_k6_assign_m7(u32 *k, u32 lit, u32 rsn_cid) {
  u32 te = k[KH_TRL_END];
  if (lit >= 128u || te >= K6_MV) { return; }
  u32 v = lit >> 1;
  k[KO_VALS + lit] = 1u;
  k[KO_VALS + (lit ^ 1u)] = 2u;
  k[KO_LVL + v] = k[KH_LVL];
  k[KO_RSN + v] = rsn_cid;
  k[KO_TRL + te] = lit;
  k[KH_TRL_END] = te + 1u;
  if (k[KH_UNASS] > 0u) { k[KH_UNASS] = k[KH_UNASS] - 1u; }
  u32 fl = k[KO_FLAGS + v];
  k[KO_FLAGS + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

void full_k6_mtf_m7(u32 *k, u32 v) {
  u32 nv = k[KH_NV];
  if (nv > K6_MV || v >= nv || v == k[KH_QLAST]) { return; }
  u32 pv = k[KO_QPREV + v];
  u32 nxt = k[KO_QNEXT + v];
  if (k[KO_VALS + (v << 1)] != 0u && v == k[KH_QSEARCH]) {
    if (pv < nv) { k[KH_QSEARCH] = pv; }
    else if (nxt < nv) { k[KH_QSEARCH] = nxt; }
  }
  if (pv >= nv) { k[KH_QFIRST] = nxt; } else { k[KO_QNEXT + pv] = nxt; }
  if (nxt >= nv) { k[KH_QLAST] = pv; } else { k[KO_QPREV + nxt] = pv; }
  u32 ol = k[KH_QLAST];
  k[KO_QPREV + v] = ol;
  k[KO_QNEXT + v] = 0xFFFFFFFFu;
  k[KH_QLAST] = v;
  if (ol >= nv) { k[KH_QFIRST] = v; } else { k[KO_QNEXT + ol] = v; }
  if (k[KH_QSTAMP] < 0xFFFFFFF0u) {
    k[KH_QSTAMP] = k[KH_QSTAMP] + 1u;
    k[KO_QST + v] = k[KH_QSTAMP];
  }
  if (k[KO_VALS + (v << 1)] == 0u) { k[KH_QSEARCH] = v; }
}

void full_k6_backtrack_m7(u32 *k, u32 target_lvl) {
  u32 nv = k[KH_NV];
  if (nv > K6_MV) { return; }
  u32 te = k[KH_TRL_END];
  if (te > K6_MV) { te = K6_MV; }
  u32 best_st = 0u;
  if (k[KH_QSEARCH] < nv) { best_st = k[KO_QST + k[KH_QSEARCH]]; }
  while (te > 0u) {
    u32 lit = k[KO_TRL + te - 1u];
    if (lit >= (nv << 1)) { break; }
    u32 v = lit >> 1;
    if (k[KO_LVL + v] <= target_lvl) { break; }
    te = te - 1u;
    k[KO_VALS + lit] = 0u;
    k[KO_VALS + (lit ^ 1u)] = 0u;
    k[KO_LVL + v] = 0u;
    k[KO_RSN + v] = 0xFFFFFFFFu;
    k[KH_UNASS] = k[KH_UNASS] + 1u;
    if (k[KO_QST + v] > best_st) { best_st = k[KO_QST + v]; k[KH_QSEARCH] = v; }
  }
  k[KH_TRL_END] = te;
  if (k[KH_PROP] > te) { k[KH_PROP] = te; }
  k[KH_LVL] = target_lvl;
}

u32 full_k6_prop_m7(u32 *k) {
  u64 ticks = 0ULL;
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (nc > K6_MC || nv > K6_MV) { return 0xFFFFFFFFu; }
  while (k[KH_PROP] < k[KH_TRL_END] && k[KH_PROP] < K6_MV) {
    u32 lit = k[KO_TRL + k[KH_PROP]];
    k[KH_PROP] = k[KH_PROP] + 1u;
    if (lit >= (nv << 1)) { continue; }
    u32 nl = lit ^ 1u;
    u64 visits = 0ULL;
    u32 prev = 0xFFFFFFFFu;
    u32 w = k[KO_WHEAD + nl];
    u32 wsteps = 0u;
    while (w < (nc << 1) && wsteps < 512u) {
      wsteps = wsteps + 1u;
      u32 nxt = k[KO_WNEXT + w];
      visits = visits + 1ULL;
      u32 wb = k[KO_WBLIT + w];
      u32 bv = wb & K6_LIT_MASK;
      if (bv >= (nv << 1)) { prev = w; w = nxt; continue; }
      u32 bvv = k[KO_VALS + bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          k[KH_TICKS] = k[KH_TICKS] + (u32)(ticks + (visits >> 7) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign_m7(k, bv, cid); }
        prev = w;
        w = nxt;
        continue;
      }
      u32 slot = w & 1u;
      u32 off = k[KO_CL_OFF + cid];
      u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
      if (sz < 2u || off + sz > acap) { prev = w; w = nxt; continue; }
      u32 other = k[KO_ARENA + off + (slot ^ 1u)];
      if (other >= (nv << 1)) { prev = w; w = nxt; continue; }
      if (k[KO_VALS + other] == 1u) {
        k[KO_WBLIT + w] = other;
        prev = w;
        w = nxt;
        continue;
      }
      ticks = ticks + 1ULL;
      u32 r = 2u;
      u32 ri = 0xFFFFFFFFu;
      u32 repl = 0u;
      while (r < sz) {
        u32 cand = k[KO_ARENA + off + r];
        if (cand < (nv << 1) && k[KO_VALS + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        k[KO_ARENA + off + slot] = repl;
        k[KO_ARENA + off + ri] = nl;
        if (prev >= (nc << 1)) { k[KO_WHEAD + nl] = nxt; }
        else { k[KO_WNEXT + prev] = nxt; }
        k[KO_WBLIT + w] = other;
        k[KO_WNEXT + w] = k[KO_WHEAD + repl];
        k[KO_WHEAD + repl] = w;
        w = nxt;
        continue;
      }
      k[KO_WBLIT + w] = other;
      prev = w;
      w = nxt;
      u32 ov = k[KO_VALS + other];
      if (ov == 2u) {
        k[KH_TICKS] = k[KH_TICKS] + (u32)(ticks + (visits >> 7) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign_m7(k, other, cid); }
    }
    ticks = ticks + (visits >> 7) + 1ULL;
  }
  k[KH_TICKS] = k[KH_TICKS] + (u32)ticks;
  return 0xFFFFFFFFu;
}

void full_k6_ana_cl_m7(u32 *k, u32 cid, u32 skip_v) {
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (cid >= nc || nc > K6_MC || nv > K6_MV) { return; }
  u32 clvl = k[KH_LVL];
  u32 off = k[KO_CL_OFF + cid];
  u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
  if (off + sz > acap) { return; }
  if (k[KH_NRES] < 128u) { k[KO_RES + k[KH_NRES]] = cid; k[KH_NRES] = k[KH_NRES] + 1u; }
  else { k[KH_NRES] = 129u; }
  u32 i = 0u;
  while (i < sz) {
    u32 l = k[KO_ARENA + off + i];
    u32 v = l >> 1;
    if (v < nv && v != skip_v && (k[KO_FLAGS + v] & 2u) == 0u) {
      k[KO_FLAGS + v] = k[KO_FLAGS + v] | 2u;
      if (k[KH_NANA] < K6_MV) { k[KO_ANA + k[KH_NANA]] = v; k[KH_NANA] = k[KH_NANA] + 1u; }
      u32 vlvl = k[KO_LVL + v];
      if (vlvl == 0u) {
        u32 r0 = k[KO_RSN + v];
        if (r0 != 0xFFFFFFFFu) {
          if (k[KH_NRES] < 128u) { k[KO_RES + k[KH_NRES]] = r0; k[KH_NRES] = k[KH_NRES] + 1u; }
          else { k[KH_NRES] = 129u; }
        }
      } else if (vlvl == clvl) {
        k[KH_OPEN] = k[KH_OPEN] + 1u;
      } else if (k[KH_NKL] < K6_MV) {
        k[KO_KL + k[KH_NKL]] = l;
        k[KH_NKL] = k[KH_NKL] + 1u;
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze_m7(u32 *k, u32 confl_cid) {
  u32 nv = k[KH_NV];
  if (nv > K6_MV) { return false; }
  k[KH_NKL] = 1u;
  k[KH_NANA] = 0u;
  k[KH_NRES] = 0u;
  k[KH_OPEN] = 0u;
  full_k6_ana_cl_m7(k, confl_cid, 0xFFFFFFFFu);
  u32 clvl = k[KH_LVL];
  u32 idx = k[KH_TRL_END];
  if (idx > K6_MV) { idx = K6_MV; }
  u32 uip = 0xFFFFFFFFu;
  while (k[KH_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = k[KO_TRL + idx];
    u32 pv = p >> 1;
    if (pv < nv && (k[KO_FLAGS + pv] & 2u) != 0u && k[KO_LVL + pv] == clvl) {
      k[KH_OPEN] = k[KH_OPEN] - 1u;
      if (k[KH_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = k[KO_RSN + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_cl_m7(k, rsn, pv);
    }
  }
  u32 nana = k[KH_NANA];
  if (nana > K6_MV) { nana = K6_MV; }
  u32 ai = 0u;
  while (ai < nana) {
    u32 av = k[KO_ANA + ai];
    if (av < nv) { k[KO_FLAGS + av] = k[KO_FLAGS + av] & (~2u); }
    ai = ai + 1u;
  }
  u32 nres = k[KH_NRES];
  u32 nkl = k[KH_NKL];
  if (uip == 0xFFFFFFFFu || uip >= (nv << 1) || nres > 128u || nkl == 0u || nkl > K6_MV) {
    return false;
  }
  k[KO_KL] = uip;
  u32 jlvl = 0u;
  u32 wi = 1u;
  u32 i = 1u;
  while (i < nkl) {
    u32 kv = k[KO_KL + i] >> 1;
    if (kv < nv) {
      u32 il = k[KO_LVL + kv];
      if (il > jlvl) { jlvl = il; wi = i; }
    }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = k[KO_KL + 1u];
    k[KO_KL + 1u] = k[KO_KL + wi];
    k[KO_KL + wi] = t;
  }
  full_k6_backtrack_m7(k, jlvl);
  ai = 0u;
  while (ai < nana) { full_k6_mtf_m7(k, k[KO_ANA + ai]); ai = ai + 1u; }
  u32 nc = k[KH_NC];
  u32 off = k[KH_ALEN];
  if (nc >= K6_MC || off + nkl + nres > k[KH_ACAP]) { return false; }
  i = 0u;
  while (i < nkl) { k[KO_ARENA + off + i] = k[KO_KL + i]; i = i + 1u; }
  i = 0u;
  while (i < nres) { k[KO_ARENA + off + nkl + i] = k[KO_RES + i]; i = i + 1u; }
  k[KH_ALEN] = off + nkl + nres;
  k[KO_CL_OFF + nc] = off;
  k[KO_CL_META + nc] = nkl | KM_LRN;
  k[KO_CL_AUX + nc] = nres;
  k[KH_NC] = nc + 1u;
  if (nkl == 1u) { full_k6_assign_m7(k, uip, nc); return true; }
  full_k6_watch_m7(k, nc, k[KO_KL], k[KO_KL + 1u], nkl);
  full_k6_assign_m7(k, uip, nc);
  return true;
}

u64 full_k6_solve_m7(FullHdr *h, u32 *k, u32 tick_lim) {
  full_k6_backtrack_m7(k, 0u);
  if (k[KH_INCONS] != 0xFFFFFFFFu) { return 20ULL; }
  k[KH_TICK_LIM] = tick_lim;
  k[KH_TICKS] = 0u;
  u32 nv = k[KH_NV];
  u32 nc = k[KH_NC];
  u32 acap = k[KH_ACAP];
  u32 nunits = k[KH_NUNITS];
  if (nv > K6_MV || nc > K6_MC || nunits > K6_MAX_ORIG) { return 0ULL; }
  u32 ui = 0u;
  while (ui < nunits) {
    u32 ucid = k[KO_UNITS + ui];
    if (ucid < nc) {
      u32 off = k[KO_CL_OFF + ucid];
      if (off < acap) {
        u32 ul = k[KO_ARENA + off];
        if (ul < (nv << 1)) {
          u32 uv = k[KO_VALS + ul];
          if (uv == 2u) { k[KH_INCONS] = ucid; return 20ULL; }
          if (uv == 0u) { full_k6_assign_m7(k, ul, ucid); }
        }
      }
    }
    ui = ui + 1u;
  }
  u32 confl = full_k6_prop_m7(k);
  if (confl != 0xFFFFFFFFu) { k[KH_INCONS] = confl; return 20ULL; }
  while (k[KH_TICKS] < k[KH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[KH_LVL] == 0u) { k[KH_INCONS] = confl; return 20ULL; }
      if (!full_k6_analyze_m7(k, confl)) { return 0ULL; }
      confl = full_k6_prop_m7(k);
      continue;
    }
    if (k[KH_UNASS] == 0u) { return 10ULL; }
    u32 cur = k[KH_QSEARCH];
    u32 pick = 0xFFFFFFFFu;
    u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
      cur = k[KO_QPREV + cur];
      steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[KH_QLAST];
      steps = 0u;
      while (cur < nv && steps < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = k[KO_QPREV + cur];
        steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    k[KH_QSEARCH] = pick;
    u32 ph = (k[KO_FLAGS + pick] ^ k[KH_PHASE]) & 1u;
    k[KH_LVL] = k[KH_LVL] + 1u;
    full_k6_assign_m7(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_prop_m7(k);
  }
  return 0ULL;
}

void full_k6_core_m7(u32 *k) {
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (nc > K6_MC || nv > K6_MV) { return; }
  u32 i = 0u;
  while (i < nc) { k[KO_CL_META + i] = k[KO_CL_META + i] & (~KM_CORE); i = i + 1u; }
  u32 inc = k[KH_INCONS];
  if (inc < nc) {
    i = 0u;
    while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
    k[KO_CL_META + inc] = k[KO_CL_META + inc] | KM_CORE;
    u32 off = k[KO_CL_OFF + inc];
    u32 sz = k[KO_CL_META + inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 j = 0u;
      while (j < sz) {
        u32 lv = k[KO_ARENA + off + j] >> 1;
        if (lv < nv) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = k[KH_TRL_END];
    if (ti > K6_MV) { ti = K6_MV; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = k[KO_TRL + ti] >> 1;
      if (v >= nv || (k[KO_FLAGS + v] & 2u) == 0u) { continue; }
      k[KO_FLAGS + v] = k[KO_FLAGS + v] & (~2u);
      u32 rsn = k[KO_RSN + v];
      if (rsn >= nc) { continue; }
      k[KO_CL_META + rsn] = k[KO_CL_META + rsn] | KM_CORE;
      u32 roff = k[KO_CL_OFF + rsn];
      u32 rsz = k[KO_CL_META + rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = k[KO_ARENA + roff + j] >> 1;
          if (lv < nv && lv != v) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u;
    while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u;
  bool changed = true;
  while (changed && pass < nc) {
    changed = false;
    pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = k[KO_CL_META + cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = k[KO_CL_OFF + cid];
        u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = k[KO_CL_AUX + cid];
          if (off + sz + na <= acap) {
            u32 j = 0u;
            while (j < na) {
              u32 ant = k[KO_ARENA + off + sz + j];
              if (ant < nc && (k[KO_CL_META + ant] & KM_CORE) == 0u) {
                k[KO_CL_META + ant] = k[KO_CL_META + ant] | KM_CORE;
                changed = true;
              }
              j = j + 1u;
            }
          }
        } else if (off + sz <= acap) {
          u32 j = 0u;
          while (j < sz) {
            u32 lv = k[KO_ARENA + off + j] >> 1;
            if (lv < nv && k[KO_LVL + lv] == 0u) {
              u32 r0 = k[KO_RSN + lv];
              if (r0 < nc && (k[KO_CL_META + r0] & KM_CORE) == 0u) {
                k[KO_CL_META + r0] = k[KO_CL_META + r0] | KM_CORE;
                changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
}

void full_bve_def_k6_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 8192ULL || np == 0u || nn == 0u || np + nn < 3u ||
      np + nn > K6_MAX_ORIG) {
    return;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *k = scr + K6_BASE;
  u32 acap = (u32)(h->scratch_cap - (u64)(K6_BASE + KO_ARENA));
  u32 max_csz = (h->max_vars < 100ULL) ? (u32)h->max_vars : 100u;
  u32 nv = 0u;
  u32 nc = 0u;
  u32 alen = 0u;
  u32 nunits = 0u;
  u32 trivial_eid = 0xFFFFFFFFu;
  bool abort_def = false;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 side = 0u;
  while (side < 2u && !abort_def && trivial_eid == 0xFFFFFFFFu) {
    u32 cnt = (side == 0u) ? np : nn;
    u32 off_s = (side == 0u) ? 0u : 512u;
    u32 except = (side == 0u) ? pl : nl;
    u32 idx = 0u;
    while (idx < cnt && !abort_def) {
      u32 w = scr[off_s + idx];
      u32 eid = (side << 10) | idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { trivial_eid = eid; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= K6_MV || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
            exp[nv] = lv;
            nv = nv + 1u;
            tmk[lv] = nv;
          }
          if (nc >= K6_MAX_ORIG || alen + 1u > acap) { abort_def = true; break; }
          k[KO_ARENA + alen] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          k[KO_CL_OFF + nc] = alen;
          k[KO_CL_META + nc] = 1u;
          k[KO_CL_AUX + nc] = eid;
          k[KO_UNITS + nunits] = nc;
          nunits = nunits + 1u;
          nc = nc + 1u;
          alen = alen + 1u;
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false;
        u32 csz = 0u;
        u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= K6_MV || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
                exp[nv] = lv;
                nv = nv + 1u;
                tmk[lv] = nv;
              }
              if (csz >= max_csz) { abort_def = true; break; }
              tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u);
              csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_eid = eid; break; }
          if (nc >= K6_MAX_ORIG || alen + csz > acap) { abort_def = true; break; }
          m = 0u;
          while (m < csz) { k[KO_ARENA + alen + m] = tmp[m]; m = m + 1u; }
          k[KO_CL_OFF + nc] = alen;
          k[KO_CL_META + nc] = csz;
          k[KO_CL_AUX + nc] = eid;
          if (csz == 1u) {
            k[KO_UNITS + nunits] = nc;
            nunits = nunits + 1u;
          }
          nc = nc + 1u;
          alen = alen + csz;
        }
      }
      idx = idx + 1u;
    }
    side = side + 1u;
  }
  u32 ci = 0u;
  while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_eid != 0xFFFFFFFFu) {
    u32 idx = trivial_eid & 0x3FFu;
    u32 mbase = ((trivial_eid >> 10) == 0u) ? 1024u : 1040u;
    scr[mbase + (idx >> 5)] = 1u << (idx & 31u);
    scr[1056] = 1u;
    scr[1057] = 1u;
    return;
  }
  if (abort_def || nv == 0u || nc < 2u) { return; }
  k[KH_NV] = nv;
  k[KH_NC] = nc;
  k[KH_ORIG_NC] = nc;
  k[KH_LVL] = 0u;
  k[KH_PROP] = 0u;
  k[KH_TRL_END] = 0u;
  k[KH_UNASS] = nv;
  k[KH_INCONS] = 0xFFFFFFFFu;
  k[KH_QFIRST] = 0u;
  k[KH_QLAST] = nv - 1u;
  k[KH_QSEARCH] = nv - 1u;
  k[KH_QSTAMP] = nv;
  k[KH_TICKS] = 0u;
  k[KH_TICK_LIM] = 512u;
  k[KH_ALEN] = alen;
  k[KH_ACAP] = acap;
  k[KH_NANA] = 0u;
  k[KH_NKL] = 0u;
  k[KH_NRES] = 0u;
  k[KH_NUNITS] = nunits;
  k[KH_OPEN] = 0u;
  k[KH_PHASE] = 0u;
  u32 i = 0u;
  while (i < nv) {
    k[KO_LVL + i] = 0u;
    k[KO_RSN + i] = 0xFFFFFFFFu;
    k[KO_FLAGS + i] = 0u;
    k[KO_QST + i] = i + 1u;
    k[KO_QPREV + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    k[KO_QNEXT + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  i = 0u;
  while (i < (nv << 1)) {
    k[KO_VALS + i] = 0u;
    k[KO_WHEAD + i] = 0xFFFFFFFFu;
    i = i + 1u;
  }
  i = 0u;
  while (i < nc) {
    u32 sz = k[KO_CL_META + i] & 0xFFFFu;
    if (sz >= 2u) {
      u32 off = k[KO_CL_OFF + i];
      full_k6_watch_m7(k, i, k[KO_ARENA + off], k[KO_ARENA + off + 1u], sz);
    }
    i = i + 1u;
  }
  if (full_k6_solve_m7(h, k, 512u) != 20ULL) { return; }
  full_k6_core_m7(k);
  bool any = false;
  u32 onc = k[KH_ORIG_NC];
  i = 0u;
  while (i < onc) {
    if ((k[KO_CL_META + i] & KM_CORE) != 0u) {
      u32 eid = k[KO_CL_AUX + i];
      u32 idx = eid & 0x3FFu;
      u32 mbase = ((eid >> 10) == 0u) ? 1024u : 1040u;
      u32 widx = mbase + (idx >> 5);
      scr[widx] = scr[widx] | (1u << (idx & 31u));
      any = true;
    }
    i = i + 1u;
  }
  if (any) {
    scr[1056] = 1u;
    scr[1057] = 1u;
  }
}

void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 34u) { scr[1024u + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m7(h, np, nn)) { return; }
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  if (full_bve_find_and_m7(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m7(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m7(h, v, np, nn)) { return; }
  if (full_bve_find_xor_m7(h, v, np, nn)) { return; }
  full_bve_def_k6_m7(h, v, np, nn);
}

u64 full_bve_var_m7(FullHdr *h, u32 v) {
  if (h->scratch_cap < 2048ULL) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m7(h, pl, scr, 512u);
  u32 nn = full_bve_collect_m7(h, nl, scr + 512, 512u);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  u64 ext_need = full_bve_ext_need(h, 0u, np) + full_bve_ext_need(h, 512u, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, 512u, nn))) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    return 1ULL;
  }
  u64 r_off = 1088ULL;
  u64 rp = r_off;
  u64 r_cnt = 0ULL;
  u64 w_est = 0ULL;
  u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    full_bve_gates_m7(h, v, np, nn);
    bool gf = (scr[1056] != 0u);
    bool rg = (scr[1057] != 0u);
    u32 *wvec = (u32 *)h->watch_vec;
    u32 i = 0u;
    while (i < np && fit) {
      bool pi = ((scr[1024u + (i >> 5)] >> (i & 31u)) & 1u) != 0u;
      u32 j = 0u;
      while (j < nn && fit) {
        bool nj = ((scr[1040u + (j >> 5)] >> (j & 31u)) & 1u) != 0u;
        bool need_pair = !gf || (rg ? (pi || nj) : (pi != nj));
        if (need_pair && full_bve_resolve_pair(h, v, scr[i], scr[512u + j])) {
          u64 rlen = h->tmp_len;
          r_cnt = r_cnt + 1ULL;
          if (rlen > 100ULL || r_cnt > lim_cls || rp + 1ULL + rlen > h->scratch_cap) {
            fit = false;
            break;
          }
          scr[rp] = (u32)rlen;
          u32 *tmp = (u32 *)h->tmp_lits;
          u32 k = 0u;
          while ((u64)k < rlen) {
            u32 lk = tmp[k];
            scr[rp + 1ULL + (u64)k] = lk;
            if (rlen >= 2ULL && (u64)lk < (h->cur_vars << 1)) {
              w_est = w_est + (((u64)wvec[((u64)lk << 1) + 1ULL]) << 1) + 4ULL;
            }
            k = k + 1u;
          }
          rp = rp + 1ULL + rlen;
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
  }
  if (fit) {
    u64 ar_need = (rp - r_off) + (r_cnt * 2ULL) + 16ULL;
    u64 w_need = w_est + (r_cnt * 4ULL) + 16ULL;
    if (ar_need > h->arena_cap - h->arena_len) {
      fit = false;
    } else if (w_need > h->wcap - h->wlen) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (w_need > h->wcap - h->wlen) { fit = false; }
    }
  }
  if (fit) {
    if (!full_bve_weaken(h, pl, 0u, np) || !full_bve_weaken(h, nl, 512u, nn)) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    u64 cr = full_bve_commit_res(h, r_off, rp);
    if (cr == 20ULL) { return 20ULL; }
    if (cr == 1ULL && !full_dense_flush_units_m7(h)) { return 20ULL; }
    return cr;
  }
  u32 i = 0u;
  while (i < np) {
    if (full_bve_try_bce(h, pl, scr[i], 512u, nn)) {
      if ((scr[i] & PW_BIN_FLAG) != 0u) {
        if (full_extend_push2(h, pl, scr[i] & PW_LIT_MASK)) {
          full_delete_binary(h, pl, scr[i] & PW_LIT_MASK);
          h->bce_cnt = h->bce_cnt + 1ULL;
        }
      } else if (full_extend_push_cl(h, pl, scr[i])) {
        u32 *ar = (u32 *)h->arena;
        u32 ccr = scr[i];
        ar[ccr] = ar[ccr] | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)ccr + 2ULL];
        h->bce_cnt = h->bce_cnt + 1ULL;
      }
    }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < nn) {
    u32 w = scr[512u + j];
    if (full_bve_try_bce(h, nl, w, 0u, np)) {
      if ((w & PW_BIN_FLAG) != 0u) {
        if (full_extend_push2(h, nl, w & PW_LIT_MASK)) {
          full_delete_binary(h, nl, w & PW_LIT_MASK);
          h->bce_cnt = h->bce_cnt + 1ULL;
        }
      } else if (full_extend_push_cl(h, nl, w)) {
        u32 *ar = (u32 *)h->arena;
        ar[w] = ar[w] | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
        h->bce_cnt = h->bce_cnt + 1ULL;
      }
    }
    j = j + 1u;
  }
  return 1ULL;
}

u64 full_bve_var_key_m7(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u64 pos = (u64)wvec[((u64)v << 2) + 1ULL];
  u64 neg = (u64)wvec[((u64)v << 2) + 3ULL];
  if (pos > 1024ULL) { pos = 1024ULL; }
  if (neg > 1024ULL) { neg = 1024ULL; }
  u64 base = (1050624ULL + pos + neg) - (pos * neg);
  u64 rel = 0ULL;
  if (h->stable != 0ULL) {
    u64 *sc = (u64 *)h->score;
    rel = sc[v] >> 32;
  } else {
    u32 *qs = (u32 *)h->q_stamp;
    rel = (u64)qs[v];
  }
  return (base << 32) | (0xFFFFFFFFULL - (rel & 0xFFFFFFFFULL));
}

void full_bve_heap_up_m7(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 p = (u64)hp[mv + (u64)v];
  if (p >= hlen) { return; }
  u64 kv = keys[v];
  while (p > 0ULL) {
    u64 par = (p - 1ULL) >> 1;
    u32 pv = hp[par];
    if ((u64)pv >= cv || keys[pv] >= kv) { break; }
    hp[p] = pv;
    hp[mv + (u64)pv] = (u32)p;
    p = par;
  }
  hp[p] = v;
  hp[mv + (u64)v] = (u32)p;
}

void full_bve_heap_down_m7(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 p = (u64)hp[mv + (u64)v];
  if (p >= hlen) { return; }
  u64 kv = keys[v];
  while (true) {
    u64 l = (p << 1) + 1ULL;
    if (l >= hlen) { break; }
    u32 bv = hp[l];
    if ((u64)bv >= cv) { break; }
    u64 bk = keys[bv];
    u64 best = l;
    u64 r = l + 1ULL;
    if (r < hlen) {
      u32 rv = hp[r];
      if ((u64)rv < cv && keys[rv] > bk) {
        best = r;
        bv = rv;
        bk = keys[rv];
      }
    }
    if (kv >= bk) { break; }
    hp[p] = bv;
    hp[mv + (u64)bv] = (u32)p;
    p = best;
  }
  hp[p] = v;
  hp[mv + (u64)v] = (u32)p;
}

u64 full_bve_heap_push_m7(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return hlen; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 nk = full_bve_var_key_m7(h, v);
  u64 old_k = keys[v];
  keys[v] = nk;
  u64 cur_p = (u64)hp[mv + (u64)v];
  if (cur_p < hlen) {
    if (nk > old_k) { full_bve_heap_up_m7(h, hlen, v); }
    else if (nk < old_k) { full_bve_heap_down_m7(h, hlen, v); }
    return hlen;
  }
  if (hlen >= cv) { return hlen; }
  hp[hlen] = v;
  hp[mv + (u64)v] = (u32)hlen;
  u64 nlen = hlen + 1ULL;
  full_bve_heap_up_m7(h, nlen, v);
  return nlen;
}

u32 full_bve_heap_pop_m7(FullHdr *h, u64 hlen) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if (hlen == 0ULL || hlen > cv) { return 0xFFFFFFFFu; }
  u32 *hp = (u32 *)h->work_stk1;
  u32 top = hp[0];
  if ((u64)top < cv) { hp[mv + (u64)top] = 0xFFFFFFFFu; }
  u64 nlen = hlen - 1ULL;
  if (nlen > 0ULL) {
    u32 last = hp[nlen];
    hp[0] = last;
    if ((u64)last < cv) {
      hp[mv + (u64)last] = 0u;
      full_bve_heap_down_m7(h, nlen, last);
    }
  }
  return ((u64)top < cv) ? top : 0xFFFFFFFFu;
}

u64 full_bve_collect_nbrs_m7(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *mclr = (u32 *)h->min_clr;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 nn = 0ULL;
  u32 side = 0u;
  while (side < 2u) {
    u32 lit = (v << 1) | side;
    if ((u64)lit < (cv << 1)) {
      u64 off = (u64)wvec[(u64)lit << 1];
      u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      u64 p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 u = (w0 & PW_LIT_MASK) >> 1;
          if (u != v && (u64)u < cv && (fl[u] & FL_ACTIVE) != 0u &&
              vals[(u64)u << 1] == (i8)0 && mclr[u] == 0u && nn < cv) {
            mclr[u] = 1u;
            nbrs[nn] = u;
            nn = nn + 1ULL;
          }
          continue;
        }
        if (p >= end) { break; }
        u32 cr = wstk[p];
        p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
        u32 sz = ar[(u64)cr + 2ULL];
        u32 k = 0u;
        while (k < sz) {
          u32 u = ar[(u64)cr + 3ULL + (u64)k] >> 1;
          if (u != v && (u64)u < cv && (fl[u] & FL_ACTIVE) != 0u &&
              vals[(u64)u << 1] == (i8)0 && mclr[u] == 0u && nn < cv) {
            mclr[u] = 1u;
            nbrs[nn] = u;
            nn = nn + 1ULL;
          }
          k = k + 1u;
        }
      }
    }
    side = side + 1u;
  }
  u64 c = 0ULL;
  while (c < nn) { mclr[nbrs[c]] = 0u; c = c + 1ULL; }
  return nn;
}

u64 full_elim_bve_m7(FullHdr *h, u64 bve_lim) {
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *hp = (u32 *)h->work_stk1;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 mv = h->max_vars;
  u32 *mclr = (u32 *)h->min_clr;
  u64 cv0 = h->cur_vars;
  u64 ci = 0ULL;
  while (ci < cv0) { mclr[ci] = 0u; ci = ci + 1ULL; }
  u64 tried = 0ULL;
  u64 hlen = 0ULL;
  bool last_round_elim = false;
  u64 round = 0ULL;
  while (round < 16ULL && tried < bve_lim && h->fuel > 0ULL &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    if (!full_dense_flush_units_m7(h)) { return 20ULL; }
    u64 cv = h->cur_vars;
    u64 i = 0ULL;
    while (i < cv) { hp[mv + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    hlen = 0ULL;
    i = 0ULL;
    while (i < cv) {
      if ((fl[i] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) &&
          vals[i << 1] == (i8)0) {
        hlen = full_bve_heap_push_m7(h, hlen, (u32)i);
      }
      i = i + 1ULL;
    }
    if (hlen == 0ULL) { last_round_elim = false; break; }
    bool round_elim = false;
    while (hlen > 0ULL && tried < bve_lim && h->fuel > 0ULL &&
           h->oom == 0ULL && h->inconsistent == 0ULL) {
      u32 v = full_bve_heap_pop_m7(h, hlen);
      hlen = hlen - 1ULL;
      u64 cv1 = h->cur_vars;
      if (v == 0xFFFFFFFFu || (u64)v >= cv1) { continue; }
      if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) != (FL_ACTIVE | FL_ELIM_C) ||
          vals[(u64)v << 1] != (i8)0) { continue; }
      fl[v] = fl[v] & (~FL_ELIM_C);
      tried = tried + 1ULL;
      u64 nn = full_bve_collect_nbrs_m7(h, v);
      u64 b0 = h->bve_cnt;
      u64 c0 = h->bce_cnt;
      u64 st = full_bve_var_m7(h, v);
      if (st == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
      if (st == 2ULL) { break; }
      if (h->bve_cnt > b0 || h->bce_cnt > c0) {
        if (h->bve_cnt > b0) { round_elim = true; }
        u64 cv2 = h->cur_vars;
        u64 k = 0ULL;
        while (k < nn) {
          u32 u = nbrs[k];
          if ((u64)u < cv2 && (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
            fl[u] = fl[u] | FL_ELIM_C;
            hlen = full_bve_heap_push_m7(h, hlen, u);
          }
          k = k + 1ULL;
        }
      }
    }
    last_round_elim = round_elim;
    if (!round_elim) { break; }
    round = round + 1ULL;
  }
  if (h->inconsistent == 0ULL) {
    u64 cvf = h->cur_vars;
    bool complete = (hlen == 0ULL && !last_round_elim && h->oom == 0ULL && h->fuel > 0ULL);
    if (complete) {
      u64 cur_b = h->elim_bound;
      if (cur_b < 16ULL) {
        u64 next_b = (cur_b == 0ULL) ? 1ULL : (cur_b << 1);
        if (next_b > 16ULL) { next_b = 16ULL; }
        h->elim_bound = next_b;
        u64 k = 0ULL;
        while (k < cvf) { fl[k] = fl[k] | FL_ELIM_C; k = k + 1ULL; }
      }
    } else {
      u64 k = 0ULL;
      while (k < cvf) { fl[k] = fl[k] & (~FL_ELIM_C); k = k + 1ULL; }
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_eliminate_m7(FullHdr *h, bool initial) {
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
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
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
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}
"

/-- External callee signatures referenced by `m7BveGates_fns` (`23` canonical externs). -/
def m7BveGatesExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_set_inactive", [i64, i32, i32], []⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool]⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool]⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool]⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64]⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64]⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩ ]

/-- Standalone Wave-4E module (`39` owned `_m7` functions, `23` canonical externs). -/
def m7BveGatesModule : LeanQbe.T.Module :=
  { fns := m7BveGates_fns, externs := m7BveGatesExterns, exits := [] }

theorem full_dense_prop_unit_m7_wf : Func.Wf full_dense_prop_unit_m7_body := by t_wf_reify
theorem full_dense_flush_units_m7_wf : Func.Wf full_dense_flush_units_m7_body := by t_wf_reify
theorem full_fwd_flush_large_m7_wf : Func.Wf full_fwd_flush_large_m7_body := by t_wf_reify
theorem full_fwd_reconnect_irred_m7_wf : Func.Wf full_fwd_reconnect_irred_m7_body := by t_wf_reify
theorem full_fwd_scan_lit_m7_wf : Func.Wf full_fwd_scan_lit_m7_body := by t_wf_reify
theorem full_fwd_check_cl_m7_wf : Func.Wf full_fwd_check_cl_m7_body := by t_wf_reify
theorem full_fwd_connect_subsumer_m7_wf : Func.Wf full_fwd_connect_subsumer_m7_body := by
  t_wf_reify
theorem full_fwd_collect_sort_m7_wf : Func.Wf full_fwd_collect_sort_m7_body := by t_wf_reify
theorem full_forward_sub_m7_wf : Func.Wf full_forward_sub_m7_body := by t_wf_reify
theorem full_bve_collect_m7_wf : Func.Wf full_bve_collect_m7_body := by t_wf_reify
theorem full_bve_mark_and_m7_wf : Func.Wf full_bve_mark_and_m7_body := by t_wf_reify
theorem full_bve_find_equiv_m7_wf : Func.Wf full_bve_find_equiv_m7_body := by t_wf_reify
theorem full_bve_find_and_m7_wf : Func.Wf full_bve_find_and_m7_body := by t_wf_reify
theorem full_bve_get_tern_m7_wf : Func.Wf full_bve_get_tern_m7_body := by t_wf_reify
theorem full_bve_match_tern_m7_wf : Func.Wf full_bve_match_tern_m7_body := by t_wf_reify
theorem full_bve_find_ite_side_m7_wf : Func.Wf full_bve_find_ite_side_m7_body := by t_wf_reify
theorem full_bve_find_ite_m7_wf : Func.Wf full_bve_find_ite_m7_body := by t_wf_reify
theorem full_bve_xor_pat_m7_wf : Func.Wf full_bve_xor_pat_m7_body := by t_wf_reify
theorem full_bve_find_xor_m7_wf : Func.Wf full_bve_find_xor_m7_body := by t_wf_reify
theorem full_k6_watch_m7_wf : Func.Wf full_k6_watch_m7_body := by t_wf_reify
theorem full_k6_assign_m7_wf : Func.Wf full_k6_assign_m7_body := by t_wf_reify
theorem full_k6_mtf_m7_wf : Func.Wf full_k6_mtf_m7_body := by t_wf_reify
theorem full_k6_backtrack_m7_wf : Func.Wf full_k6_backtrack_m7_body := by t_wf_reify
theorem full_k6_prop_m7_wf : Func.Wf full_k6_prop_m7_body := by t_wf_reify
theorem full_k6_ana_cl_m7_wf : Func.Wf full_k6_ana_cl_m7_body := by t_wf_reify
theorem full_k6_analyze_m7_wf : Func.Wf full_k6_analyze_m7_body := by t_wf_reify
theorem full_k6_solve_m7_wf : Func.Wf full_k6_solve_m7_body := by t_wf_reify
theorem full_k6_core_m7_wf : Func.Wf full_k6_core_m7_body := by t_wf_reify
theorem full_bve_def_k6_m7_wf : Func.Wf full_bve_def_k6_m7_body := by t_wf_reify
theorem full_bve_gates_m7_wf : Func.Wf full_bve_gates_m7_body := by t_wf_reify
theorem full_bve_var_m7_wf : Func.Wf full_bve_var_m7_body := by t_wf_reify
theorem full_bve_var_key_m7_wf : Func.Wf full_bve_var_key_m7_body := by t_wf_reify
theorem full_bve_heap_up_m7_wf : Func.Wf full_bve_heap_up_m7_body := by t_wf_reify
theorem full_bve_heap_down_m7_wf : Func.Wf full_bve_heap_down_m7_body := by t_wf_reify
theorem full_bve_heap_push_m7_wf : Func.Wf full_bve_heap_push_m7_body := by t_wf_reify
theorem full_bve_heap_pop_m7_wf : Func.Wf full_bve_heap_pop_m7_body := by t_wf_reify
theorem full_bve_collect_nbrs_m7_wf : Func.Wf full_bve_collect_nbrs_m7_body := by t_wf_reify
theorem full_elim_bve_m7_wf : Func.Wf full_elim_bve_m7_body := by t_wf_reify
theorem full_eliminate_m7_wf : Func.Wf full_eliminate_m7_body := by t_wf_reify

theorem m7BveGates_fns_wf : ∀ f ∈ m7BveGates_fns, f.Wf := by
  simp only [m7BveGates_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_dense_prop_unit_m7_wf, full_dense_flush_units_m7_wf, full_fwd_flush_large_m7_wf,
    full_fwd_reconnect_irred_m7_wf, full_fwd_scan_lit_m7_wf, full_fwd_check_cl_m7_wf,
    full_fwd_connect_subsumer_m7_wf, full_fwd_collect_sort_m7_wf, full_forward_sub_m7_wf,
    full_bve_collect_m7_wf, full_bve_mark_and_m7_wf, full_bve_find_equiv_m7_wf,
    full_bve_find_and_m7_wf, full_bve_get_tern_m7_wf, full_bve_match_tern_m7_wf,
    full_bve_find_ite_side_m7_wf, full_bve_find_ite_m7_wf, full_bve_xor_pat_m7_wf,
    full_bve_find_xor_m7_wf, full_k6_watch_m7_wf, full_k6_assign_m7_wf, full_k6_mtf_m7_wf,
    full_k6_backtrack_m7_wf, full_k6_prop_m7_wf, full_k6_ana_cl_m7_wf, full_k6_analyze_m7_wf,
    full_k6_solve_m7_wf, full_k6_core_m7_wf, full_bve_def_k6_m7_wf, full_bve_gates_m7_wf,
    full_bve_var_m7_wf, full_bve_var_key_m7_wf, full_bve_heap_up_m7_wf, full_bve_heap_down_m7_wf,
    full_bve_heap_push_m7_wf, full_bve_heap_pop_m7_wf, full_bve_collect_nbrs_m7_wf,
    full_elim_bve_m7_wf, full_eliminate_m7_wf⟩

theorem m7BveGatesModule_acyclic : m7BveGatesModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7BveGates

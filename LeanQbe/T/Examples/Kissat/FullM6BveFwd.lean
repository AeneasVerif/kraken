module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M6 BVE Max-Heap, Adaptive `elim_bound`, ITE Gates & `forward.c` (`FullM6BveFwd`)

Standalone drop-in C0 upgrades (`0` `FullHdr` edits — `144` words frozen; `0` edits to
`Full1..3`, `FullM4*`, `FullM5*`, `M5Hub`, or `LeanQbe`):
1. **Cluster 1 — Dense-Mode Unit Propagation & Flush (`full_dense_{prop_unit,flush_units}_m6`)**:
   Propagates level-`0` binary & large clauses while dense occurrences are connected and marks
   root-satisfied clauses `PH_GARB` (`kissat_flush_units_while_connected`).
2. **Cluster 2 — `forward.c` Forward Subsumption Parity (`full_fwd_*_m6`, `full_forward_sub_m6`)**:
   - Ascending-length bucket sort for `3 <= sz <= 1000` (`FL_SUBSUME >= 2` filtering).
   - 1-watched min-occ subsumer connection (`subsumeocclim = 1000`) after flushing large occs,
     plus full irredundant clause reconnection for BVE.
   - `NOT(lit)` self-subsuming resolution (`check_bins=true` on `l`, `check_bins=false` on `l^1`),
     multi-shrink loop, `PH_SUBSUME` (`0x01000000u`) tracking + `FL_SUBSUME` reactivation, dense
     unit flush, and OOM-safe `full_add_bin` check before marking `PH_GARB`.
3. **Cluster 3 — BVE & Gate Extraction (`full_bve_*_m6`)**:
   - `occlim = 512` per side (`1024` total) + `clslim = 100` on inputs and resolvents.
   - `vals[l]` check in `full_bve_mark_and_m6`, structural `ifthenelse` gate extraction
     (`full_bve_{get_tern,match_tern,find_ite}_m6`), Kitten `full_find_definition` fallback, and
     `resolve_gate` polarity (`false` for Equiv/AND/exact-4-ternary ITE; `true` for shortened ITE
     and Kitten definitions).
   - Safe `watch_stk` OOM pre-check (with `full_wstack_defrag` retry) before weakening.
4. **Cluster 4 — BVE Max-Heap & Completion-Gated `elim_bound` (`full_bve_{var_key,heap_*}_m6`,
   `full_bve_collect_nbrs_m6`, `full_elim_bve_m6`, `full_eliminate_m6`)**:
   - Binary max-heap in `work_stk1` + `sim_sig` scoring `pos*neg - (pos+neg)` with relevancy
     tie-break (`eliminate.c`).
   - Completion-gated `elim_bound` progression (`0 -> 1 -> 2 -> 4 -> 8 -> 16`), `FL_ELIM_C`
     neighbor re-arming with in-heap priority updates, and incomplete-round candidate drop.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6BveFwd

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6BveFwd "
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
extern void full_find_definition(FullHdr *h, u32 v, u32 np, u32 nn);
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

bool full_dense_prop_unit_m6(FullHdr *h, u32 lit) {
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

bool full_dense_flush_units_m6(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  u64 q = h->propagated;
  while (q < h->trail_end && h->inconsistent == 0ULL) {
    u32 lit = trl[q];
    q = q + 1ULL;
    if (!full_dense_prop_unit_m6(h, lit)) { return false; }
  }
  h->propagated = (q <= h->trail_end) ? q : h->trail_end;
  return h->inconsistent == 0ULL;
}

void full_fwd_flush_large_m6(FullHdr *h) {
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

void full_fwd_reconnect_irred_m6(FullHdr *h) {
  full_fwd_flush_large_m6(h);
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

u32 full_fwd_scan_lit_m6(FullHdr *h, u32 cref, u32 sz, u32 scan_lit, bool check_bins) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)scan_lit << 1];
  u64 end = off + (u64)wvec[((u64)scan_lit << 1) + 1ULL];
  u64 p = off;
  u64 occ = 0ULL;
  while (p < end && occ < 1000ULL) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    occ = occ + 1ULL;
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

bool full_fwd_check_cl_m6(FullHdr *h, u32 cref) {
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
        u32 r1 = full_fwd_scan_lit_m6(h, cref, sz, l, true);
        if (r1 == 0xFFFFFFFEu) { subsumed = true; break; }
        if (r1 != 0xFFFFFFFFu) { drop = r1; break; }
        u32 r2 = full_fwd_scan_lit_m6(h, cref, sz, l ^ 1u, false);
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
      return full_dense_flush_units_m6(h);
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
      return full_dense_flush_units_m6(h);
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

void full_fwd_connect_subsumer_m6(FullHdr *h, u32 cref) {
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

u64 full_fwd_collect_sort_m6(FullHdr *h) {
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

u64 full_forward_sub_m6(FullHdr *h, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  if (!full_dense_flush_units_m6(h)) { return 20ULL; }
  u64 ncand = full_fwd_collect_sort_m6(h);
  if (ncand == 0ULL) { return (h->inconsistent != 0ULL) ? 20ULL : 1ULL; }
  full_fwd_flush_large_m6(h);
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  u64 rem = budget;
  while (i < ncand && rem > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 cr = rr[i];
    rem = rem - 1ULL;
    if (!full_fwd_check_cl_m6(h, cr)) { return 20ULL; }
    if (h->oom == 0ULL && h->inconsistent == 0ULL && (ar[cr] & PH_GARB) == 0u) {
      full_fwd_connect_subsumer_m6(h, cr);
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
  if (!full_dense_flush_units_m6(h)) { return 20ULL; }
  full_fwd_reconnect_irred_m6(h);
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u32 full_bve_collect_m6(FullHdr *h, u32 lit, u32 *out, u32 cap) {
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

bool full_bve_mark_and_m6(FullHdr *h, u32 v_lit, u32 cr, u32 n_off, u32 nn, u32 mask_off) {
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

bool full_bve_get_tern_m6(FullHdr *h, u32 v_lit, u32 cr, u32 out_off) {
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

u32 full_bve_match_tern_m6(FullHdr *h, u32 nl, u32 x, u32 y, u32 n_off, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 j = 0u;
  while (j < nn) {
    u32 w = scr[n_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (ot == x || ot == y) { return j | 0x80000000u; }
    } else if (full_bve_get_tern_m6(h, nl, w, 1064u)) {
      u32 c0 = scr[1064];
      u32 c1 = scr[1065];
      if ((c0 == x && c1 == y) || (c0 == y && c1 == x)) { return j; }
    }
    j = j + 1u;
  }
  return 0xFFFFFFFFu;
}

bool full_bve_find_ite_m6(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 plim = (np <= 64u) ? np : 64u;
  u32 i0 = 0u;
  while (i0 < plim) {
    u32 w0 = scr[i0];
    if ((w0 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m6(h, pl, w0, 1060u)) {
      u32 a0 = scr[1060];
      u32 a1 = scr[1061];
      u32 i1 = i0 + 1u;
      while (i1 < plim) {
        u32 w1 = scr[i1];
        if ((w1 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m6(h, pl, w1, 1062u)) {
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
          if (ok && u != w && u != (w ^ 1u)) {
            u32 m0 = full_bve_match_tern_m6(h, nl, cond, u ^ 1u, 512u, nn);
            if (m0 != 0xFFFFFFFFu) {
              u32 m1 = full_bve_match_tern_m6(h, nl, cond ^ 1u, w ^ 1u, 512u, nn);
              if (m1 != 0xFFFFFFFFu) {
                u32 j0 = m0 & 0x7FFFFFFFu;
                u32 j1 = m1 & 0x7FFFFFFFu;
                if (j0 != j1) {
                  scr[1024u + (i0 >> 5)] = scr[1024u + (i0 >> 5)] | (1u << (i0 & 31u));
                  scr[1024u + (i1 >> 5)] = scr[1024u + (i1 >> 5)] | (1u << (i1 & 31u));
                  scr[1040u + (j0 >> 5)] = scr[1040u + (j0 >> 5)] | (1u << (j0 & 31u));
                  scr[1040u + (j1 >> 5)] = scr[1040u + (j1 >> 5)] | (1u << (j1 & 31u));
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

void full_bve_gates_m6(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 34u) { scr[1024u + k] = 0u; k = k + 1u; }
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) {
      u32 ot = wp & PW_LIT_MASK;
      u32 j = 0u;
      while (j < nn) {
        u32 wn = scr[512u + j];
        if ((wn & PW_BIN_FLAG) != 0u && (wn & PW_LIT_MASK) == (ot ^ 1u)) {
          scr[1024u + (i >> 5)] = 1u << (i & 31u);
          scr[1040u + (j >> 5)] = 1u << (j & 31u);
          scr[1056] = 1u;
          scr[1057] = 0u;
          return;
        }
        j = j + 1u;
      }
    } else if (full_bve_mark_and_m6(h, pl, wp, 512u, nn, 1040u)) {
      scr[1024u + (i >> 5)] = 1u << (i & 31u);
      scr[1056] = 1u;
      scr[1057] = 0u;
      return;
    }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < nn) {
    u32 wn = scr[512u + j];
    if ((wn & PW_BIN_FLAG) == 0u && full_bve_mark_and_m6(h, nl, wn, 0u, np, 1024u)) {
      scr[1040u + (j >> 5)] = 1u << (j & 31u);
      scr[1056] = 1u;
      scr[1057] = 0u;
      return;
    }
    j = j + 1u;
  }
  if (full_bve_find_ite_m6(h, v, np, nn)) { return; }
  if (np <= 64u && nn <= 64u && h->scratch_cap >= 10240ULL) {
    j = 0u;
    while (j < nn) { scr[64u + j] = scr[512u + j]; j = j + 1u; }
    scr[128] = 0u;
    scr[129] = 0u;
    scr[130] = 0u;
    scr[131] = 0u;
    full_find_definition(h, v, np, nn);
    u32 p0 = scr[128];
    u32 p1 = scr[129];
    u32 n0 = scr[130];
    u32 n1 = scr[131];
    j = 0u;
    while (j < nn) { scr[512u + j] = scr[64u + j]; j = j + 1u; }
    k = 0u;
    while (k < 34u) { scr[1024u + k] = 0u; k = k + 1u; }
    if ((p0 | p1 | n0 | n1) != 0u) {
      scr[1024] = p0;
      scr[1025] = p1;
      scr[1040] = n0;
      scr[1041] = n1;
      scr[1056] = 1u;
      scr[1057] = 1u;
    }
  }
}

u64 full_bve_var_m6(FullHdr *h, u32 v) {
  if (h->scratch_cap < 2048ULL) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m6(h, pl, scr, 512u);
  u32 nn = full_bve_collect_m6(h, nl, scr + 512, 512u);
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
    full_bve_gates_m6(h, v, np, nn);
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
    if (cr == 1ULL && !full_dense_flush_units_m6(h)) { return 20ULL; }
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

u64 full_bve_var_key_m6(FullHdr *h, u32 v) {
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

void full_bve_heap_up_m6(FullHdr *h, u64 hlen, u32 v) {
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

void full_bve_heap_down_m6(FullHdr *h, u64 hlen, u32 v) {
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

u64 full_bve_heap_push_m6(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return hlen; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 nk = full_bve_var_key_m6(h, v);
  u64 old_k = keys[v];
  keys[v] = nk;
  u64 cur_p = (u64)hp[mv + (u64)v];
  if (cur_p < hlen) {
    if (nk > old_k) { full_bve_heap_up_m6(h, hlen, v); }
    else if (nk < old_k) { full_bve_heap_down_m6(h, hlen, v); }
    return hlen;
  }
  if (hlen >= cv) { return hlen; }
  hp[hlen] = v;
  hp[mv + (u64)v] = (u32)hlen;
  u64 nlen = hlen + 1ULL;
  full_bve_heap_up_m6(h, nlen, v);
  return nlen;
}

u32 full_bve_heap_pop_m6(FullHdr *h, u64 hlen) {
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
      full_bve_heap_down_m6(h, nlen, last);
    }
  }
  return ((u64)top < cv) ? top : 0xFFFFFFFFu;
}

u64 full_bve_collect_nbrs_m6(FullHdr *h, u32 v) {
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

u64 full_elim_bve_m6(FullHdr *h, u64 bve_lim) {
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
    if (!full_dense_flush_units_m6(h)) { return 20ULL; }
    u64 cv = h->cur_vars;
    u64 i = 0ULL;
    while (i < cv) { hp[mv + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    hlen = 0ULL;
    i = 0ULL;
    while (i < cv) {
      if ((fl[i] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) &&
          vals[i << 1] == (i8)0) {
        hlen = full_bve_heap_push_m6(h, hlen, (u32)i);
      }
      i = i + 1ULL;
    }
    if (hlen == 0ULL) { last_round_elim = false; break; }
    bool round_elim = false;
    while (hlen > 0ULL && tried < bve_lim && h->fuel > 0ULL &&
           h->oom == 0ULL && h->inconsistent == 0ULL) {
      u32 v = full_bve_heap_pop_m6(h, hlen);
      hlen = hlen - 1ULL;
      u64 cv1 = h->cur_vars;
      if (v == 0xFFFFFFFFu || (u64)v >= cv1) { continue; }
      if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) != (FL_ACTIVE | FL_ELIM_C) ||
          vals[(u64)v << 1] != (i8)0) { continue; }
      fl[v] = fl[v] & (~FL_ELIM_C);
      tried = tried + 1ULL;
      u64 nn = full_bve_collect_nbrs_m6(h, v);
      u64 b0 = h->bve_cnt;
      u64 c0 = h->bce_cnt;
      u64 st = full_bve_var_m6(h, v);
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
            hlen = full_bve_heap_push_m6(h, hlen, u);
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

u64 full_eliminate_m6(FullHdr *h, bool initial) {
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
  u64 fs = full_forward_sub_m6(h, fbud);
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
  u64 res = full_elim_bve_m6(h, bve_lim);
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

/-- External callee signatures referenced by `m6BveFwd_fns` (`24` canonical externs). -/
def m6BveFwdExterns : List Extern :=
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
  , ⟨"full_find_definition", [i64, i32, i32, i32], []⟩
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

/-- Standalone M6 BVE/forward module (`24` `_m6` functions, `24` canonical externs). -/
def m6BveFwdModule : LeanQbe.T.Module :=
  { fns := m6BveFwd_fns, externs := m6BveFwdExterns, exits := [] }

theorem full_dense_prop_unit_m6_wf : Func.Wf full_dense_prop_unit_m6_body := by t_wf_reify
theorem full_dense_flush_units_m6_wf : Func.Wf full_dense_flush_units_m6_body := by t_wf_reify
theorem full_fwd_flush_large_m6_wf : Func.Wf full_fwd_flush_large_m6_body := by t_wf_reify
theorem full_fwd_reconnect_irred_m6_wf : Func.Wf full_fwd_reconnect_irred_m6_body := by t_wf_reify
theorem full_fwd_scan_lit_m6_wf : Func.Wf full_fwd_scan_lit_m6_body := by t_wf_reify
theorem full_fwd_check_cl_m6_wf : Func.Wf full_fwd_check_cl_m6_body := by t_wf_reify
theorem full_fwd_connect_subsumer_m6_wf : Func.Wf full_fwd_connect_subsumer_m6_body := by
  t_wf_reify
theorem full_fwd_collect_sort_m6_wf : Func.Wf full_fwd_collect_sort_m6_body := by t_wf_reify
theorem full_forward_sub_m6_wf : Func.Wf full_forward_sub_m6_body := by t_wf_reify
theorem full_bve_collect_m6_wf : Func.Wf full_bve_collect_m6_body := by t_wf_reify
theorem full_bve_mark_and_m6_wf : Func.Wf full_bve_mark_and_m6_body := by t_wf_reify
theorem full_bve_get_tern_m6_wf : Func.Wf full_bve_get_tern_m6_body := by t_wf_reify
theorem full_bve_match_tern_m6_wf : Func.Wf full_bve_match_tern_m6_body := by t_wf_reify
theorem full_bve_find_ite_m6_wf : Func.Wf full_bve_find_ite_m6_body := by t_wf_reify
theorem full_bve_gates_m6_wf : Func.Wf full_bve_gates_m6_body := by t_wf_reify
theorem full_bve_var_m6_wf : Func.Wf full_bve_var_m6_body := by t_wf_reify
theorem full_bve_var_key_m6_wf : Func.Wf full_bve_var_key_m6_body := by t_wf_reify
theorem full_bve_heap_up_m6_wf : Func.Wf full_bve_heap_up_m6_body := by t_wf_reify
theorem full_bve_heap_down_m6_wf : Func.Wf full_bve_heap_down_m6_body := by t_wf_reify
theorem full_bve_heap_push_m6_wf : Func.Wf full_bve_heap_push_m6_body := by t_wf_reify
theorem full_bve_heap_pop_m6_wf : Func.Wf full_bve_heap_pop_m6_body := by t_wf_reify
theorem full_bve_collect_nbrs_m6_wf : Func.Wf full_bve_collect_nbrs_m6_body := by t_wf_reify
theorem full_elim_bve_m6_wf : Func.Wf full_elim_bve_m6_body := by t_wf_reify
theorem full_eliminate_m6_wf : Func.Wf full_eliminate_m6_body := by t_wf_reify

theorem m6BveFwd_fns_wf : ∀ f ∈ m6BveFwd_fns, f.Wf := by
  simp only [m6BveFwd_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_dense_prop_unit_m6_wf, full_dense_flush_units_m6_wf, full_fwd_flush_large_m6_wf,
    full_fwd_reconnect_irred_m6_wf, full_fwd_scan_lit_m6_wf, full_fwd_check_cl_m6_wf,
    full_fwd_connect_subsumer_m6_wf, full_fwd_collect_sort_m6_wf, full_forward_sub_m6_wf,
    full_bve_collect_m6_wf, full_bve_mark_and_m6_wf, full_bve_get_tern_m6_wf,
    full_bve_match_tern_m6_wf, full_bve_find_ite_m6_wf, full_bve_gates_m6_wf,
    full_bve_var_m6_wf, full_bve_var_key_m6_wf, full_bve_heap_up_m6_wf, full_bve_heap_down_m6_wf,
    full_bve_heap_push_m6_wf, full_bve_heap_pop_m6_wf, full_bve_collect_nbrs_m6_wf,
    full_elim_bve_m6_wf, full_eliminate_m6_wf⟩

theorem m6BveFwdModule_acyclic : m6BveFwdModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6BveFwd

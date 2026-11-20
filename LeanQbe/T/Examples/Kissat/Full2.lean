module

public import LeanQbe.T.Examples.Kissat.Full1

set_option autoImplicit false

@[expose] public section

/-!
# Kissat `D-Full` C0 Solver — Part 2 (`Reduce`, `OTFS`, `Shrink/Min`, `Heuristics`)

Implements:
1. Tier-aware `full_reduce` & `full_arena_sweep` (`PH_SHRK` & `PH_RSN` aware compaction).
2. Chronological conflict analysis (`full_one_lit_confl`), 1UIP + **OTFS** (`full_otfs_large`,
   `full_otfs_bin`, `full_otfs_subsume`), reason-side bumping (`full_bump_reasons`),
   lexicographic recursive minimization + block shrinking, and **eager subsumption**.
3. Dual-mode VMTF/VSIDS decision, **bounded WalkSAT** (`full_walk` over scratch buffers),
   `full_warmup`, `full_rephase` (`best`/`walk`/`inverted`/`original` + `target`),
   `full_restart` with trail reuse, and `full_lucky`.
-/

namespace LeanQbe.T.Examples.Kissat.Full

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

kissat_c0! full2 "
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

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_RSN  0x00200000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE  1u
#define FL_ELIM    2u
#define FL_SUBST   4u
#define EXT_BLK_FLAG 0x80000000u

extern u64 full_isqrt(u64 x);
extern u64 full_ilog10(u64 x);
extern u64 full_rng_next(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_heap_down(FullHdr *h, u32 v);
extern u64 full_heap_pop(FullHdr *h);
extern void full_bump_var(FullHdr *h, u32 v);
extern void full_bump_decay(FullHdr *h);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_tick_rel(FullHdr *h);
extern void full_ema_update(FullHdr *h, u64 glue);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern u64 full_propagate(FullHdr *h);
extern void full_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_lit_rank(i8 *vals, u32 *lvl, u32 l);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_sweep_bins(FullHdr *h);
extern u64 full_sweep_copy(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root);

bool full_rewatch_arena(FullHdr *h, u64 dst) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool at_root = (h->cur_level == 0ULL);
  u64 p = 0ULL;
  while (p < dst) {
    u32 sz = ar[p + 2ULL];
    if (!at_root && sz >= 3u) {
      u32 i0 = 0u; u64 r0 = full_lit_rank(vals, lvl, ar[p + 3ULL]);
      u32 i = 1u;
      while (i < sz) {
        u64 rk = full_lit_rank(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r0) { r0 = rk; i0 = i; }
        i = i + 1u;
      }
      if (i0 != 0u) {
        u32 t = ar[p + 3ULL]; ar[p + 3ULL] = ar[p + 3ULL + (u64)i0];
        ar[p + 3ULL + (u64)i0] = t;
      }
      u32 i1 = 1u; u64 r1 = full_lit_rank(vals, lvl, ar[p + 4ULL]);
      i = 2u;
      while (i < sz) {
        u64 rk = full_lit_rank(vals, lvl, ar[p + 3ULL + (u64)i]);
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
    if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, (u32)p, 2u) ||
        !full_watch_push(h, l1, l0 & PW_LIT_MASK, (u32)p, 2u)) {
      h->oom = 1ULL; return false;
    }
    p = p + 3ULL + (u64)sz;
  }
  return true;
}

u64 full_arena_sweep(FullHdr *h) {
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  bool at_root = (h->cur_level == 0ULL);
  u64 src = 0ULL; u64 dst = 0ULL;
  u64 first_red = 0xFFFFFFFFULL; u64 irred = 0ULL; u64 redd = 0ULL;
  bool unsat = false; bool new_unit = false;
  while (src < alen) {
    if (src + 3ULL > alen) { break; }
    u32 hdr = ar[src]; u32 old_sz = ar[src + 2ULL];
    u64 nsrc = (u64)full_arena_next(h, (u32)src);
    if ((hdr & PH_GARB) != 0u || old_sz < 3u || src + 3ULL + (u64)old_sz > alen) {
      src = nsrc; continue;
    }
    u64 st = full_sweep_copy(h, src, dst, old_sz, at_root);
    if (st == 0xFFFFFFFEULL) { unsat = true; break; }
    if (st == 0xFFFFFFFDULL) { break; }
    if (st == 1ULL) { new_unit = true; src = nsrc; continue; }
    if (st == 0xFFFFFFFFULL) { src = nsrc; continue; }
    u32 new_sz = (u32)st;
    ar[dst] = hdr & (~(PH_SHRK | PH_RSN));
    ar[dst + 1ULL] = 2u; ar[dst + 2ULL] = new_sz;
    if ((hdr & PH_RSN) != 0u) {
      u32 i = 0u;
      while (i < new_sz) {
        u32 lit = ar[dst + 3ULL + (u64)i]; u32 v = lit >> 1;
        if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
          rsns[v] = (u32)dst; break;
        }
        i = i + 1u;
      }
    }
    if ((hdr & PH_RED) != 0u) {
      if (first_red == 0xFFFFFFFFULL) { first_red = dst; }
      redd = redd + 1ULL;
    } else { irred = irred + 1ULL; }
    dst = dst + 3ULL + (u64)new_sz;
    src = nsrc;
  }
  h->arena_len = dst; h->arena_garbage = 0ULL;
  h->first_reducible = first_red; h->num_irred = irred; h->num_redundant = redd;
  u32 *ll = (u32 *)h->last_learned; u64 li = 0ULL;
  while (li < 16ULL) { ll[li] = 0xFFFFFFFFu; li = li + 1ULL; }
  if (unsat) { return 2ULL; }
  if (h->oom != 0ULL) { return 3ULL; }
  if (!full_rewatch_arena(h, dst)) { return 3ULL; }
  return new_unit ? 1ULL : 0ULL;
}

u64 full_reduce(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + 1000ULL * full_isqrt(h->reductions);
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

bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var) {
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ana = (u32 *)h->work_stk1;
  u32 cur_lvl = (u32)h->cur_level;
  u32 v = l >> 1;
  if ((u64)v >= h->cur_vars) { return false; }
  u32 vlvl = lvl[v];
  if (vlvl == 0u) { return true; }
  if (vlvl > cur_lvl) { return false; }
  h->ant_sz = h->ant_sz + 1ULL;
  if (v != skip_var && mrk[v] == (u8)0) {
    mrk[v] = (u8)1;
    if (h->min_clr_len < h->cur_vars) {
      ana[h->min_clr_len] = v;
      h->min_clr_len = h->min_clr_len + 1ULL;
    }
    h->res_sz = h->res_sz + 1ULL;
    if (vlvl == cur_lvl) {
      h->tmp_cnt = h->tmp_cnt + 1ULL;
    } else {
      if (h->tmp_len >= h->cur_vars) { return false; }
      tmp[h->tmp_len] = l;
      h->tmp_len = h->tmp_len + 1ULL;
    }
  }
  return true;
}

bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    u32 *gu = (u32 *)h->glue_used;
    u64 gi = (glue > 63ULL) ? 63ULL : glue;
    if (gu[gi] < 0xFFFFFFFFu) { gu[gi] = gu[gi] + 1u; }
    u32 new_u = (glue <= h->tier2) ? 31u : 1u;
    u32 old_u = (hdr >> 27) & 31u;
    if (new_u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (new_u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

void full_clear_ana(FullHdr *h) {
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u64 cv = h->cur_vars;
  u64 i = 0ULL;
  while (i < h->min_clr_len) {
    u32 v = ana[i];
    if ((u64)v < cv) { mrk[v] = (u8)0; }
    i = i + 1ULL;
  }
  h->min_clr_len = 0ULL;
}

void full_bump_analyzed(FullHdr *h) {
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  u64 lim = saved * 10ULL;
  u64 i = 0ULL;
  while (i < h->tmp_len && h->min_clr_len <= lim) {
    u32 uv = tmp[i] >> 1;
    u32 rsn = ((u64)uv < cv) ? rsns[uv] : 0xFFFFFFFFu;
    if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) != 0u) {
      u32 ov = (rsn & PW_LIT_MASK) >> 1;
      if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
        mrk[ov] = (u8)1; ana[h->min_clr_len] = ov; h->min_clr_len = h->min_clr_len + 1ULL;
      }
    } else if (rsn != 0xFFFFFFFFu && (u64)rsn + 3ULL <= h->arena_len) {
      u32 sz = ar[(u64)rsn + 2ULL];
      if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len) {
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
  }
  i = 0ULL;
  while (i < h->min_clr_len) {
    u32 bv = ana[i];
    if ((u64)bv < cv) { full_bump_var(h, bv); full_queue_mtf(h, bv); }
    i = i + 1ULL;
  }
  full_bump_decay(h);
}

bool full_otfs_large(FullHdr *h, u32 cref, u32 uip) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  if (l0 == uip) { l0 = l1; }
  else if (l1 != uip) { return false; }
  u32 old_sz = ar[(u64)cref + 2ULL];
  u32 cnt = 1u; u32 i = 2u;
  while (i < old_sz) {
    if (lvl[ar[(u64)cref + 3ULL + (u64)i] >> 1] > 0u) { cnt = cnt + 1u; }
    i = i + 1u;
  }
  if (cnt < 3u) { return false; }
  ar[(u64)cref + 3ULL] = l0; ar[(u64)cref + 4ULL] = uip;
  full_unwatch_large(h, uip, cref);
  u32 new_sz = 1u; i = 2u;
  while (i < old_sz) {
    u32 ot = ar[(u64)cref + 3ULL + (u64)i];
    if (lvl[ot >> 1] > 0u) { ar[(u64)cref + 3ULL + (u64)new_sz] = ot; new_sz = new_sz + 1u; }
    i = i + 1u;
  }
  u32 hdr = ar[cref];
  ar[(u64)cref + 2ULL] = new_sz; ar[(u64)cref + 1ULL] = 2u;
  if ((hdr & PH_SHRK) == 0u) {
    ar[cref] = hdr | PH_SHRK;
    ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
  }
  u32 hp = 1u; u32 hl = lvl[ar[(u64)cref + 4ULL] >> 1];
  i = 2u;
  while (i < new_sz) {
    u32 cl = lvl[ar[(u64)cref + 3ULL + (u64)i] >> 1];
    if (cl > hl) { hl = cl; hp = i; }
    i = i + 1u;
  }
  if (hp != 1u) {
    u32 t = ar[(u64)cref + 4ULL]; ar[(u64)cref + 4ULL] = ar[(u64)cref + 3ULL + (u64)hp];
    ar[(u64)cref + 3ULL + (u64)hp] = t;
  }
  u32 nl1 = ar[(u64)cref + 4ULL];
  if (!full_watch_push(h, nl1, l0 & PW_LIT_MASK, cref, 2u)) { h->oom = 1ULL; return false; }
  u64 off = (u64)wvec[(u64)l0 << 1];
  u64 end = off + (u64)wvec[((u64)l0 << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) == 0u && p < end) {
      if (wstk[p] == cref) { wstk[p - 1ULL] = nl1 & PW_LIT_MASK; break; }
      p = p + 1ULL;
    }
  }
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

bool full_otfs_bin(FullHdr *h, u32 cref, u32 uip) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 old_sz = ar[(u64)cref + 2ULL];
  u32 f0 = 0xFFFFFFFFu; u32 f1 = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < old_sz) {
    u32 ot = ar[(u64)cref + 3ULL + (u64)i];
    if (ot != uip && lvl[ot >> 1] > 0u) {
      if (f0 == 0xFFFFFFFFu) { f0 = ot; } else { f1 = ot; break; }
    }
    i = i + 1u;
  }
  if (f0 == 0xFFFFFFFFu || f1 == 0xFFFFFFFFu) { return false; }
  u32 b0 = (f1 & PW_LIT_MASK) | PW_BIN_FLAG;
  u32 b1 = (f0 & PW_LIT_MASK) | PW_BIN_FLAG;
  if (!full_watch_push(h, f0, b0, 0u, 1u) || !full_watch_push(h, f1, b1, 0u, 1u)) {
    h->oom = 1ULL; return false;
  }
  h->num_binary = h->num_binary + 1ULL;
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  ar[cref] = ar[cref] | PH_GARB;
  h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
  h->confl_type = 1ULL; h->confl_lit0 = (u64)f0; h->confl_lit1 = (u64)f1;
  h->confl_ref = 0xFFFFFFFFULL;
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

void full_otfs_subsume(FullHdr *h, u32 new_confl, u64 old_ctype, u64 old_cref, bool to_bin) {
  if (old_ctype != 2ULL || old_cref == 0xFFFFFFFFULL) { return; }
  u32 *ar = (u32 *)h->arena;
  u32 dhdr = ar[old_cref];
  if ((dhdr & PH_GARB) != 0u) { return; }
  ar[old_cref] = dhdr | PH_GARB;
  h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[old_cref + 2ULL];
  if (!to_bin && (dhdr & PH_RED) == 0u && (ar[new_confl] & PH_RED) != 0u) {
    ar[new_confl] = ar[new_confl] & (~PH_RED);
    if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    h->num_irred = h->num_irred + 1ULL;
  }
}

void full_min_mark(FullHdr *h, u32 v, u8 tag) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[v] & tag) != (u8)0) { return; }
  if (mrk[v] == (u8)0) {
    if (h->min_clr_len < cv) {
      u32 *mclr = (u32 *)h->min_clr;
      mclr[h->min_clr_len] = v;
      h->min_clr_len = h->min_clr_len + 1ULL;
    } else { h->min_clr_full = 1ULL; }
  }
  mrk[v] = mrk[v] | tag;
}

bool full_min_lit(FullHdr *h, u32 root_lit) {
  u64 cv = h->cur_vars;
  u32 root_v = root_lit >> 1;
  if ((u64)root_v >= cv || h->min_depth == 0ULL) { return false; }
  u32 *rsns = (u32 *)h->reason;
  if (rsns[root_v] == 0xFFFFFFFFu) { return false; }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena; u32 *stk = (u32 *)h->min_stk;
  stk[0] = root_v; stk[1] = 0u;
  u64 sp = 0ULL; bool ok = false; u64 steps = 0ULL;
  u64 max_steps = (h->arena_len + cv) * 4ULL + 64ULL;
  while (steps < max_steps) {
    steps = steps + 1ULL;
    u32 v = stk[sp << 1]; u32 pos = stk[(sp << 1) + 1ULL];
    if ((u64)v >= cv) { break; }
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) { break; }
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    u32 sz = 1u;
    if (!is_bin) {
      if ((u64)rsn + 3ULL > h->arena_len) { break; }
      sz = ar[(u64)rsn + 2ULL];
      if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { break; }
    }
    if (pos < sz) {
      stk[(sp << 1) + 1ULL] = pos + 1u;
      u32 l = is_bin ? (rsn & PW_LIT_MASK) : ar[(u64)rsn + 3ULL + (u64)pos];
      u32 u = l >> 1;
      if ((u64)u >= cv) { break; }
      if (u == v || lvl[u] == 0u) { continue; }
      u8 mu = mrk[u];
      if ((mu & (u8)2) != (u8)0) { continue; }
      if ((mu & (u8)4) != (u8)0) { break; }
      if (rsns[u] == 0xFFFFFFFFu) { full_min_mark(h, u, (u8)4); break; }
      if (sp + 1ULL >= h->min_depth) { break; }
      sp = sp + 1ULL; stk[sp << 1] = u; stk[(sp << 1) + 1ULL] = 0u;
      continue;
    }
    if (sp == 0ULL) { ok = true; break; }
    full_min_mark(h, v, (u8)2); sp = sp - 1ULL;
  }
  if (!ok) {
    u64 j = 1ULL;
    while (j <= sp) { full_min_mark(h, stk[j << 1], (u8)4); j = j + 1ULL; }
    return false;
  }
  return true;
}

bool full_tmp_less(u32 *lvl, u32 *tpos, u32 a, u32 b) {
  u32 va = a >> 1; u32 vb = b >> 1;
  u32 la = lvl[va]; u32 lb = lvl[vb];
  if (la != lb) { return la < lb; }
  return tpos[va] < tpos[vb];
}

void full_sort_tmp_sift(u32 *tmp, u32 *lvl, u32 *tpos, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    if (ch + 1ULL < n && full_tmp_less(lvl, tpos, tmp[1ULL + ch], tmp[2ULL + ch])) {
      ch = ch + 1ULL;
    }
    if (!full_tmp_less(lvl, tpos, tmp[1ULL + root], tmp[1ULL + ch])) { break; }
    u32 t = tmp[1ULL + root]; tmp[1ULL + root] = tmp[1ULL + ch]; tmp[1ULL + ch] = t;
    root = ch;
  }
}

void full_sort_tmp(FullHdr *h) {
  u64 tlen = h->tmp_len;
  if (tlen <= 2ULL) { return; }
  u64 n = tlen - 1ULL;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u32 *tpos = (u32 *)h->trail_pos;
  u64 start = n >> 1;
  while (start > 0ULL) { start = start - 1ULL; full_sort_tmp_sift(tmp, lvl, tpos, start, n); }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = tmp[1ULL]; tmp[1ULL] = tmp[1ULL + end]; tmp[1ULL + end] = t;
    full_sort_tmp_sift(tmp, lvl, tpos, 0ULL, end);
    end = end - 1ULL;
  }
}

bool full_shrink_lower(FullHdr *h, u32 ot, u32 ov) {
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[ov] & (u8)2) != (u8)0) { return true; }
  if ((mrk[ov] & (u8)4) != (u8)0 || !full_min_lit(h, ot)) {
    full_min_mark(h, ov, (u8)4);
    return false;
  }
  full_min_mark(h, ov, (u8)2);
  return true;
}

void full_shrink_blk(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *sstk = (u32 *)h->shrink_stk;
  u32 *ar = (u32 *)h->arena; u64 cv = h->cur_vars;
  u64 open = end_b - beg; u64 slen = 0ULL; u64 k = beg;
  while (k < end_b) {
    u32 v = tmp[k] >> 1; mrk[v] = mrk[v] | (u8)8;
    sstk[slen] = v; slen = slen + 1ULL; k = k + 1ULL;
  }
  bool failed = false; u32 uip = 0xFFFFFFFFu; u64 t = max_tr;
  while (!failed) {
    while (true) {
      if (t >= h->trail_end) { failed = true; break; }
      u32 lit = trl[t];
      if ((mrk[lit >> 1] & (u8)8) != (u8)0) { uip = lit; break; }
      if (t == 0ULL) { failed = true; break; }
      t = t - 1ULL;
    }
    if (failed || open == 1ULL || t == 0ULL) { if (open != 1ULL) { failed = true; } break; }
    t = t - 1ULL;
    u32 rsn = rsns[uip >> 1];
    if (rsn == 0xFFFFFFFFu) { failed = true; break; }
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    u32 csz = 1u;
    if (!is_bin) {
      if ((u64)rsn + 3ULL > h->arena_len) { failed = true; break; }
      csz = ar[(u64)rsn + 2ULL];
      if (csz < 3u || (u64)rsn + 3ULL + (u64)csz > h->arena_len) { failed = true; break; }
    }
    u32 i = 0u;
    while (i < csz && !failed) {
      u32 ot = is_bin ? (rsn & PW_LIT_MASK) : ar[(u64)rsn + 3ULL + (u64)i];
      u32 ov = ot >> 1;
      if (ot != uip && (u64)ov < cv && lvl[ov] > 0u && (mrk[ov] & (u8)8) == (u8)0) {
        if (lvl[ov] < blvl) { if (!full_shrink_lower(h, ot, ov)) { failed = true; } }
        else if (lvl[ov] == blvl && slen < cv) {
          mrk[ov] = mrk[ov] | (u8)8; sstk[slen] = ov;
          slen = slen + 1ULL; open = open + 1ULL;
        } else { failed = true; }
      }
      i = i + 1u;
    }
    if (!failed) { open = open - 1ULL; }
  }
  if (failed || uip == 0xFFFFFFFFu) {
    u64 i = 0ULL;
    while (i < slen) { u32 sv = sstk[i]; mrk[sv] = mrk[sv] & (u8)0xF7; i = i + 1ULL; }
    return;
  }
  k = beg;
  while (k < end_b) { tmp[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  tmp[beg] = uip ^ 1u;
  u64 i = 0ULL;
  while (i < slen) {
    u32 sv = sstk[i]; mrk[sv] = mrk[sv] & (u8)0xF7; full_min_mark(h, sv, (u8)2); i = i + 1ULL;
  }
}

void full_min_shrink(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 tlen = h->tmp_len;
  h->conflicts = h->conflicts + 1ULL;
  if (tlen <= 1ULL || tlen > cv) { h->learned_lits = h->learned_lits + tlen; return; }
  full_sort_tmp(h);
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u32 *tpos = (u32 *)h->trail_pos;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  u64 i = 0ULL;
  while (i < tlen) { full_min_mark(h, tmp[i] >> 1, (u8)2); i = i + 1ULL; }
  u64 end_b = tlen;
  while (end_b > 1ULL) {
    u64 beg = end_b - 1ULL;
    u32 blvl = lvl[tmp[beg] >> 1];
    u64 max_tr = (u64)tpos[tmp[beg] >> 1];
    while (beg > 1ULL && lvl[tmp[beg - 1ULL] >> 1] == blvl) {
      beg = beg - 1ULL;
      u64 tp = (u64)tpos[tmp[beg] >> 1];
      if (tp > max_tr) { max_tr = tp; }
    }
    if (end_b - beg == 1ULL) {
      if (full_min_lit(h, tmp[beg])) { tmp[beg] = 0xFFFFFFFFu; }
    } else { full_shrink_blk(h, beg, end_b, blvl, max_tr); }
    end_b = beg;
  }
  u64 keep = 1ULL; u64 k = 1ULL;
  while (k < tlen) {
    if (tmp[k] != 0xFFFFFFFFu) { tmp[keep] = tmp[k]; keep = keep + 1ULL; }
    k = k + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  if (h->min_clr_full != 0ULL) {
    u64 v = 0ULL; while (v < cv) { mrk[v] = (u8)0; v = v + 1ULL; }
  } else {
    u32 *mclr = (u32 *)h->min_clr; u64 z = 0ULL;
    while (z < h->min_clr_len) {
      u32 z_v = mclr[z]; if ((u64)z_v < cv) { mrk[z_v] = (u8)0; } z = z + 1ULL;
    }
  }
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  h->tmp_len = keep;
  h->min_removed = h->min_removed + (tlen - keep);
  h->learned_lits = h->learned_lits + keep;
}

u64 full_det_new_level(FullHdr *h, u64 jump) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  u64 back = h->cur_level - 1ULL;
  if (jump >= back) { return jump; }
  if (back - jump > h->chrono_levels) { return back; }
  return jump;
}

u64 full_one_lit_confl(FullHdr *h) {
  u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena;
  if (h->confl_type == 1ULL) {
    u32 a = (u32)h->confl_lit0; u32 b = (u32)h->confl_lit1;
    u32 la = lvl[a >> 1]; u32 lb = lvl[b >> 1];
    u64 clvl = (la >= lb) ? (u64)la : (u64)lb;
    if (clvl == 0ULL) { return 20ULL; }
    if (clvl < h->cur_level) { full_backtrack(h, clvl); }
    if (la == lb) { return 0ULL; }
    u32 forced = (la > lb) ? a : b;
    u32 other = (la > lb) ? b : a;
    u64 jlvl = (la > lb) ? (u64)lb : (u64)la;
    u64 nlvl = full_det_new_level(h, jlvl);
    full_backtrack(h, nlvl);
    full_assign_lvl(h, forced, (other & PW_LIT_MASK) | PW_BIN_FLAG, (u32)jlvl);
    return 1ULL;
  }
  u32 cref = (u32)h->confl_ref;
  if ((u64)cref + 3ULL > h->arena_len) { return 2ULL; }
  u32 csz = ar[(u64)cref + 2ULL];
  u64 clvl = 0ULL; u64 jlvl = 0ULL; u64 cnt = 0ULL; u32 forced = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < csz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u64 ll = (u64)lvl[l >> 1];
    if (cnt == 0ULL || ll > clvl) {
      jlvl = (cnt == 0ULL) ? 0ULL : clvl; clvl = ll; cnt = 1ULL; forced = l;
    } else if (ll == clvl) {
      if (clvl > jlvl) { jlvl = ll; } cnt = cnt + 1ULL;
    } else if (ll > jlvl) { jlvl = ll; }
    i = i + 1u;
  }
  if (clvl == 0ULL) { return 20ULL; }
  if (clvl < h->cur_level) { full_backtrack(h, clvl); }
  if (cnt > 1ULL) { return 0ULL; }
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  if (l0 != forced && l1 != forced) {
    u32 j = 2u; while (j < csz && ar[(u64)cref + 3ULL + (u64)j] != forced) { j = j + 1u; }
    if (j < csz) {
      full_unwatch_large(h, l0, cref);
      ar[(u64)cref + 3ULL] = forced; ar[(u64)cref + 3ULL + (u64)j] = l0;
      if (!full_watch_push(h, forced, ar[(u64)cref + 4ULL] & PW_LIT_MASK, cref, 2u)) {
        h->oom = 1ULL; return 2ULL;
      }
    }
  } else if (l1 == forced) {
    ar[(u64)cref + 3ULL] = l1; ar[(u64)cref + 4ULL] = l0;
  }
  u64 nlvl = full_det_new_level(h, jlvl);
  full_backtrack(h, nlvl);
  full_assign_lvl(h, forced, cref, (u32)jlvl);
  return 1ULL;
}

u64 full_deduce_1uip(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  if (!seed_ok || h->tmp_cnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (h->tmp_cnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= h->cur_vars) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      h->tmp_cnt = h->tmp_cnt - 1ULL;
      if (h->tmp_cnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      if (h->res_sz > 0ULL) { h->res_sz = h->res_sz - 1ULL; }
      if (h->ant_sz >= 3ULL && h->res_sz < h->ant_sz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (h->ant_sz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            full_bump_analyzed(h); full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          full_bump_analyzed(h); full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  full_bump_analyzed(h);
  full_clear_ana(h);
  return 1ULL;
}

void full_eager_subsume(FullHdr *h, u64 new_ref) {
  u8 *lm = (u8 *)h->lit_mark;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *ll = (u32 *)h->last_learned;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u64 tlen = h->tmp_len;
  u64 i = 0ULL;
  while (i < tlen) { lm[tmp[i]] = (u8)1; i = i + 1ULL; }
  i = 0ULL;
  while (i < 8ULL) {
    u32 cr = ll[i];
    if (cr != 0xFFFFFFFFu && (u64)cr + 3ULL <= h->arena_len) {
      u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
      if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) != 0u && (u64)csz > tlen &&
          (u64)cr + 3ULL + (u64)csz <= h->arena_len) {
        u64 need = tlen; u64 rem = (u64)csz; u32 j = 0u;
        while (j < csz) {
          if (lm[ar[(u64)cr + 3ULL + (u64)j]] != (u8)0) {
            need = need - 1ULL; if (need == 0ULL) { break; }
          } else { rem = rem - 1ULL; if (rem < need) { break; } }
          j = j + 1u;
        }
        if (need == 0ULL) {
          bool act = false; u32 rj = 0u;
          while (rj < csz) {
            u32 rl = ar[(u64)cr + 3ULL + (u64)rj];
            if ((u64)rl < (h->cur_vars << 1) && vals[rl] > (i8)0 &&
                lvl[rl >> 1] > 0u && rsns[rl >> 1] == cr) { act = true; break; }
            rj = rj + 1u;
          }
          if (!act) {
            ar[cr] = hdr | PH_GARB;
            h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
            ll[i] = 0xFFFFFFFFu;
            h->eager_sub_cnt = h->eager_sub_cnt + 1ULL;
          }
        }
      }
    }
    i = i + 1ULL;
  }
  i = 0ULL;
  while (i < tlen) { lm[tmp[i]] = (u8)0; i = i + 1ULL; }
  if (new_ref < 0x80000000ULL) {
    u64 k = 7ULL;
    while (k > 0ULL) { ll[k] = ll[k - 1ULL]; k = k - 1ULL; }
    ll[0] = (u32)new_ref;
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
  u64 max_idx = h->tmp_len - 1ULL;
  u64 max_lvl = (u64)lvl[tmp[max_idx] >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u32 w1 = tmp[1]; tmp[1] = tmp[max_idx]; tmp[max_idx] = w1;
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
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}

u64 full_analyze(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 iter = 0ULL;
  u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) { return 1ULL; }
    if (ol == 2ULL) { return 0ULL; }
    u64 dst = full_deduce_1uip(h);
    if (dst == 20ULL) { return 20ULL; }
    if (dst == 0ULL) { return 0ULL; }
    if (dst == 2ULL) { h->conflicts = h->conflicts + 1ULL; continue; }
    full_min_shrink(h);
    full_tick_rel(h);
    u64 glue = 1ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    full_ema_update(h, glue);
    return full_learn_clause(h, glue);
  }
  return 0ULL;
}

u64 full_next_dec_var(FullHdr *h) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *hp = (u32 *)h->heap;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qs = (u32 *)h->q_stamp;
  u64 cv = h->cur_vars;
  if (h->stable != 0ULL) {
    while (h->heap_len > 0ULL && h->heap_len <= cv) {
      u32 top = hp[0];
      if ((u64)top >= cv) { break; }
      if ((fl[top] & FL_ACTIVE) != 0u && vals[(u64)top << 1] == (i8)0) { return (u64)top; }
      full_heap_pop(h);
    }
  } else {
    u64 cur = h->q_search_idx; u64 steps = 0ULL;
    while (cur < cv && steps < cv) {
      if ((fl[cur] & FL_ACTIVE) != 0u && vals[cur << 1] == (i8)0) {
        h->q_search_idx = cur; h->q_search_stamp = (u64)qs[cur]; return cur;
      }
      cur = (u64)qp[cur]; steps = steps + 1ULL;
    }
    cur = h->q_last; steps = 0ULL;
    while (cur < cv && steps < cv) {
      if ((fl[cur] & FL_ACTIVE) != 0u && vals[cur << 1] == (i8)0) {
        h->q_search_idx = cur; h->q_search_stamp = (u64)qs[cur]; return cur;
      }
      cur = (u64)qp[cur]; steps = steps + 1ULL;
    }
  }
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) { return v; }
    v = v + 1ULL;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

u64 full_decide(FullHdr *h) {
  u64 chosen = full_next_dec_var(h);
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) { return 0ULL; }
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 dph = ph[chosen];
  if (h->stable != 0ULL && ptgt[chosen] != (i8)0) { dph = ptgt[chosen]; }
  u32 lit = (dph < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
  u64 nlvl = h->cur_level + 1ULL;
  if (nlvl > h->max_vars) { return 0ULL; }
  ftrl[nlvl] = (u32)h->trail_end;
  fdec[nlvl] = lit;
  h->cur_level = nlvl;
  full_assign(h, lit, 0xFFFFFFFFu);
  return 1ULL;
}

void full_warmup(FullHdr *h) {
  if (h->cur_level != 0ULL || h->unassigned == 0ULL) { return; }
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *ph = (i8 *)h->phases;
  h->probing = 1ULL;
  u64 steps = 0ULL;
  while (h->unassigned > 0ULL && steps < h->cur_vars && h->fuel > 0ULL) {
    steps = steps + 1ULL;
    u64 v = full_next_dec_var(h);
    if (v == 0xFFFFFFFFFFFFFFFFULL) { break; }
    u32 lit = (ph[v] < (i8)0) ? ((u32)(v << 1) | 1u) : (u32)(v << 1);
    u64 nlvl = h->cur_level + 1ULL;
    if (nlvl > h->max_vars) { break; }
    ftrl[nlvl] = (u32)h->trail_end;
    fdec[nlvl] = lit;
    h->cur_level = nlvl;
    full_assign(h, lit, 0xFFFFFFFFu);
    if (full_propagate(h) != 0ULL) { break; }
  }
  full_backtrack(h, 0ULL);
  h->probing = 0ULL;
}

u64 full_walk_collect(FullHdr *h) {
  if (h->scratch_cap < 4ULL) { return 0ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 max_cl = h->scratch_cap >> 1;
  if (max_cl > 4096ULL) { max_cl = 4096ULL; }
  u64 n = 0ULL;
  u64 nlits = h->cur_vars << 1;
  u64 l = 0ULL;
  while (l < nlits && n < max_cl) {
    u64 off = (u64)wvec[l << 1];
    u64 end = off + (u64)wvec[(l << 1) + 1ULL];
    while (off < end && n < max_cl) {
      u32 w0 = wstk[off];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if (l < (u64)ot) {
          scr[n << 1] = ((u32)l) | PW_BIN_FLAG;
          scr[(n << 1) + 1ULL] = ot;
          n = n + 1ULL;
        }
        off = off + 1ULL;
      } else { off = off + 2ULL; }
    }
    l = l + 1ULL;
  }
  u64 p = 0ULL;
  while (p < h->arena_len && n < max_cl) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) == 0u && sz >= 3u) {
      scr[n << 1] = (u32)p; scr[(n << 1) + 1ULL] = 0u; n = n + 1ULL;
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  return n;
}

bool full_walk_cl_sat(FullHdr *h, u32 *scr, u64 idx) {
  i8 *wv = (i8 *)h->walk_vals;
  i8 *vals = (i8 *)h->values;
  u32 *ar = (u32 *)h->arena;
  u32 w0 = scr[idx << 1];
  if ((w0 & PW_BIN_FLAG) != 0u) {
    u32 a = w0 & PW_LIT_MASK; u32 b = scr[(idx << 1) + 1ULL];
    return vals[a] > (i8)0 || vals[b] > (i8)0 || wv[a] > (i8)0 || wv[b] > (i8)0;
  }
  u32 sz = ar[(u64)w0 + 2ULL];
  u32 i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)w0 + 3ULL + (u64)i];
    if (vals[lit] > (i8)0 || wv[lit] > (i8)0) { return true; }
    i = i + 1u;
  }
  return false;
}

u32 full_walk_pick_lit(FullHdr *h, u32 *scr, u64 idx) {
  i8 *vals = (i8 *)h->values;
  u32 *ar = (u32 *)h->arena;
  u32 w0 = scr[idx << 1];
  u32 chosen = 0xFFFFFFFFu; u64 seen = 0ULL;
  if ((w0 & PW_BIN_FLAG) != 0u) {
    u32 a = w0 & PW_LIT_MASK; u32 b = scr[(idx << 1) + 1ULL];
    if (vals[a] == (i8)0) { chosen = a; seen = 1ULL; }
    if (vals[b] == (i8)0) {
      seen = seen + 1ULL;
      if (chosen == 0xFFFFFFFFu || (full_rng_next(h) % seen) == 0ULL) { chosen = b; }
    }
    return chosen;
  }
  u32 sz = ar[(u64)w0 + 2ULL]; u32 i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)w0 + 3ULL + (u64)i];
    if (vals[lit] == (i8)0) {
      seen = seen + 1ULL;
      if (chosen == 0xFFFFFFFFu || (full_rng_next(h) % seen) == 0ULL) { chosen = lit; }
    }
    i = i + 1u;
  }
  return chosen;
}

void full_walk(FullHdr *h) {
  u64 ncl = full_walk_collect(h);
  if (ncl == 0ULL) { return; }
  i8 *wv = (i8 *)h->walk_vals;
  i8 *wb = (i8 *)h->walk_best;
  i8 *ph = (i8 *)h->phases;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  while (v < cv) {
    i8 p = (ph[v] < (i8)0) ? (i8)(-1) : (i8)1;
    wv[v << 1] = p; wv[(v << 1) + 1ULL] = (i8)(-p); wb[v] = p;
    v = v + 1ULL;
  }
  u64 best_unsat = ncl + 1ULL;
  u64 flip = 0ULL;
  while (flip < 256ULL && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    u64 unsat_c = 0ULL; u64 picked_idx = 0ULL; u64 i = 0ULL;
    while (i < ncl) {
      if (!full_walk_cl_sat(h, scr, i)) {
        unsat_c = unsat_c + 1ULL;
        if ((full_rng_next(h) % unsat_c) == 0ULL) { picked_idx = i; }
      }
      i = i + 1ULL;
    }
    if (unsat_c < best_unsat) {
      best_unsat = unsat_c;
      v = 0ULL; while (v < cv) { wb[v] = wv[v << 1]; v = v + 1ULL; }
    }
    if (unsat_c == 0ULL) { break; }
    u32 lit = full_walk_pick_lit(h, scr, picked_idx);
    if (lit == 0xFFFFFFFFu) { break; }
    u32 lv = lit >> 1;
    i8 nv = (wv[(u64)lv << 1] > (i8)0) ? (i8)(-1) : (i8)1;
    wv[(u64)lv << 1] = nv; wv[((u64)lv << 1) + 1ULL] = (i8)(-nv);
    flip = flip + 1ULL;
  }
  v = 0ULL; while (v < cv) { ph[v] = wb[v]; v = v + 1ULL; }
  h->walk_cnt_stat = h->walk_cnt_stat + 1ULL;
}

void full_rephase(FullHdr *h) {
  full_backtrack(h, 0ULL);
  h->rephased = h->rephased + 1ULL;
  u64 sel = (h->rephased - 1ULL) % 6ULL;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  u64 k = 0ULL;
  if (sel == 0ULL || sel == 3ULL) {
    while (k < cv) { if (pbst[k] != (i8)0) { ph[k] = pbst[k]; } k = k + 1ULL; }
    h->best_assigned = 0ULL;
  } else if (sel == 1ULL || sel == 4ULL) {
    full_walk(h);
  } else if (sel == 2ULL) {
    while (k < cv) { ph[k] = (i8)(-1); k = k + 1ULL; }
  } else {
    while (k < cv) { ph[k] = (i8)1; k = k + 1ULL; }
  }
  k = 0ULL;
  while (k < cv) { ptgt[k] = ph[k]; k = k + 1ULL; }
  h->target_assigned = 0ULL;
  u64 lg = full_ilog10(h->rephased + 2ULL);
  h->rephase_limit = h->conflicts + 1000ULL + (100ULL * h->rephased * lg);
}

void full_switch_mode(FullHdr *h) {
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    h->stable = 1ULL;
    u64 dticks = h->search_ticks - h->mode_saved_ticks;
    if (dticks < 1000ULL) { dticks = 1000ULL; }
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 cv = h->cur_vars;
    i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap; u32 *ps = (u32 *)h->pos;
    u64 n = 0ULL; u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        hp[n] = (u32)v; ps[v] = (u32)n; n = n + 1ULL;
      } else { ps[v] = 0xFFFFFFFFu; }
      v = v + 1ULL;
    }
    h->heap_len = n;
    u64 s = n >> 1;
    while (s > 0ULL) { s = s - 1ULL; full_heap_down(h, hp[s]); }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    h->stable = 0ULL;
    u64 cnt = (h->switched + 2ULL) >> 1;
    h->mode_confl_lim = h->conflicts + 1000ULL * cnt * full_ilog10(cnt + 2ULL);
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < h->cur_vars) {
      u32 *qs = (u32 *)h->q_stamp; h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL; h->mode_count = h->mode_count + 1ULL;
  h->ema_fast_biased = 0ULL; h->ema_fast_exp = 1ULL << 24;
  h->ema_slow_biased = 0ULL; h->ema_slow_exp = 1ULL << 24;
  h->restart_limit = h->conflicts + 1ULL;
}

u64 full_restart_due(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  if (h->stable != 0ULL) {
    if (h->rel_trigger != 0ULL) { h->rel_trigger = 0ULL; return 1ULL; }
    return 0ULL;
  }
  if (h->conflicts < h->restart_limit) { return 0ULL; }
  u64 scale = 1ULL << 24;
  u64 fd = scale - h->ema_fast_exp;
  u64 sd = scale - h->ema_slow_exp;
  if (fd <= 256ULL || sd <= 256ULL) { return 0ULL; }
  u64 fval = h->ema_fast_biased / (fd >> 8);
  u64 sval = h->ema_slow_biased / (sd >> 8);
  if (fval * 100ULL > sval * 110ULL) {
    h->restart_limit = h->conflicts + 1ULL; return 1ULL;
  }
  return 0ULL;
}

void full_restart(FullHdr *h) {
  h->restarts = h->restarts + 1ULL;
  u64 nv = full_next_dec_var(h);
  u64 reuse = 0ULL;
  if (nv < h->cur_vars && h->cur_level > 0ULL) {
    u32 *fdec = (u32 *)h->frame_dec;
    if (h->stable != 0ULL) {
      u64 *sc = (u64 *)h->score; u64 lim = sc[nv];
      while (reuse < h->cur_level) {
        u32 dv = fdec[reuse + 1ULL] >> 1;
        if ((u64)dv >= h->cur_vars || sc[dv] <= lim) { break; }
        reuse = reuse + 1ULL;
      }
    } else {
      u32 *qs = (u32 *)h->q_stamp; u32 lim = qs[nv];
      while (reuse < h->cur_level) {
        u32 dv = fdec[reuse + 1ULL] >> 1;
        if ((u64)dv >= h->cur_vars || qs[dv] <= lim) { break; }
        reuse = reuse + 1ULL;
      }
    }
  }
  full_backtrack(h, reuse);
}

bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other) {
  if (h->extend_len + 2ULL > h->extend_cap) { return false; }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = blk_lit | EXT_BLK_FLAG;
  ext[p + 1ULL] = other & PW_LIT_MASK;
  h->extend_len = p + 2ULL;
  return true;
}

bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 sz = ar[(u64)cref + 2ULL];
  if ((u64)cref + 3ULL + (u64)sz > h->arena_len) { return false; }
  if (h->extend_len + (u64)sz + 1ULL > h->extend_cap) { return false; }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = (blk_lit & PW_LIT_MASK) | EXT_BLK_FLAG;
  p = p + 1ULL;
  u32 i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (lit != blk_lit) { ext[p] = lit & PW_LIT_MASK; p = p + 1ULL; }
    i = i + 1u;
  }
  h->extend_len = p;
  return true;
}

void full_extend(FullHdr *h) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ext = (u32 *)h->extend_stk;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ELIM | FL_SUBST)) != 0u || vals[v << 1] == (i8)0) {
      vals[v << 1] = (i8)1; vals[(v << 1) | 1ULL] = (i8)(-1);
    }
    v = v + 1ULL;
  }
  u64 end = h->extend_len;
  while (end > 0ULL) {
    u64 start = end;
    bool sat = false;
    u32 blk = 0xFFFFFFFFu;
    while (start > 0ULL) {
      start = start - 1ULL;
      u32 raw = ext[start];
      u32 lit = raw & PW_LIT_MASK;
      if ((u64)(lit >> 1) < cv && vals[lit] > (i8)0) { sat = true; }
      if ((raw & EXT_BLK_FLAG) != 0u) { blk = lit; break; }
    }
    if (!sat && blk != 0xFFFFFFFFu && (u64)(blk >> 1) < cv) {
      vals[blk] = (i8)1; vals[blk ^ 1u] = (i8)(-1);
    }
    end = start;
  }
}
"

def full2Module : LeanQbe.T.Module :=
  { fns := dimacs_fns ++ full1_fns ++ full2_fns, externs := [], exits := [] }

theorem full_rewatch_arena_wf : Func.Wf full_rewatch_arena_body := by t_wf_reify
theorem full_arena_sweep_wf : Func.Wf full_arena_sweep_body := by t_wf_reify
theorem full_reduce_wf : Func.Wf full_reduce_body := by t_wf_reify
theorem full_analyze_lit_wf : Func.Wf full_analyze_lit_body := by t_wf_reify
theorem full_analyze_rsn_wf : Func.Wf full_analyze_rsn_body := by t_wf_reify
theorem full_clear_ana_wf : Func.Wf full_clear_ana_body := by t_wf_reify
theorem full_bump_analyzed_wf : Func.Wf full_bump_analyzed_body := by t_wf_reify
theorem full_otfs_large_wf : Func.Wf full_otfs_large_body := by t_wf_reify
theorem full_otfs_bin_wf : Func.Wf full_otfs_bin_body := by t_wf_reify
theorem full_otfs_subsume_wf : Func.Wf full_otfs_subsume_body := by t_wf_reify
theorem full_min_mark_wf : Func.Wf full_min_mark_body := by t_wf_reify
theorem full_min_lit_wf : Func.Wf full_min_lit_body := by t_wf_reify
theorem full_tmp_less_wf : Func.Wf full_tmp_less_body := by t_wf_reify
theorem full_sort_tmp_sift_wf : Func.Wf full_sort_tmp_sift_body := by t_wf_reify
theorem full_sort_tmp_wf : Func.Wf full_sort_tmp_body := by t_wf_reify
theorem full_shrink_lower_wf : Func.Wf full_shrink_lower_body := by t_wf_reify
theorem full_shrink_blk_wf : Func.Wf full_shrink_blk_body := by t_wf_reify
theorem full_min_shrink_wf : Func.Wf full_min_shrink_body := by t_wf_reify
theorem full_det_new_level_wf : Func.Wf full_det_new_level_body := by t_wf_reify
theorem full_one_lit_confl_wf : Func.Wf full_one_lit_confl_body := by t_wf_reify
theorem full_deduce_1uip_wf : Func.Wf full_deduce_1uip_body := by t_wf_reify
theorem full_eager_subsume_wf : Func.Wf full_eager_subsume_body := by t_wf_reify
theorem full_learn_clause_wf : Func.Wf full_learn_clause_body := by t_wf_reify
theorem full_analyze_wf : Func.Wf full_analyze_body := by t_wf_reify
theorem full_next_dec_var_wf : Func.Wf full_next_dec_var_body := by t_wf_reify
theorem full_decide_wf : Func.Wf full_decide_body := by t_wf_reify
theorem full_warmup_wf : Func.Wf full_warmup_body := by t_wf_reify
theorem full_walk_collect_wf : Func.Wf full_walk_collect_body := by t_wf_reify
theorem full_walk_cl_sat_wf : Func.Wf full_walk_cl_sat_body := by t_wf_reify
theorem full_walk_pick_lit_wf : Func.Wf full_walk_pick_lit_body := by t_wf_reify
theorem full_walk_wf : Func.Wf full_walk_body := by t_wf_reify
theorem full_rephase_wf : Func.Wf full_rephase_body := by t_wf_reify
theorem full_switch_mode_wf : Func.Wf full_switch_mode_body := by t_wf_reify
theorem full_restart_due_wf : Func.Wf full_restart_due_body := by t_wf_reify
theorem full_restart_wf : Func.Wf full_restart_body := by t_wf_reify
theorem full_extend_push2_wf : Func.Wf full_extend_push2_body := by t_wf_reify
theorem full_extend_push_cl_wf : Func.Wf full_extend_push_cl_body := by t_wf_reify
theorem full_extend_wf : Func.Wf full_extend_body := by t_wf_reify

theorem full2_fns_wf : ∀ f ∈ full2_fns, f.Wf := by
  simp only [full2_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_rewatch_arena_wf, full_arena_sweep_wf, full_reduce_wf, full_analyze_lit_wf,
    full_analyze_rsn_wf, full_clear_ana_wf, full_bump_analyzed_wf, full_otfs_large_wf,
    full_otfs_bin_wf, full_otfs_subsume_wf, full_min_mark_wf, full_min_lit_wf,
    full_tmp_less_wf, full_sort_tmp_sift_wf, full_sort_tmp_wf, full_shrink_lower_wf,
    full_shrink_blk_wf, full_min_shrink_wf, full_det_new_level_wf, full_one_lit_confl_wf,
    full_deduce_1uip_wf, full_eager_subsume_wf, full_learn_clause_wf, full_analyze_wf,
    full_next_dec_var_wf, full_decide_wf, full_warmup_wf, full_walk_collect_wf,
    full_walk_cl_sat_wf, full_walk_pick_lit_wf, full_walk_wf, full_rephase_wf,
    full_switch_mode_wf, full_restart_due_wf, full_restart_wf, full_extend_push2_wf,
    full_extend_push_cl_wf, full_extend_wf⟩

theorem full2_acyclic : full2Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full

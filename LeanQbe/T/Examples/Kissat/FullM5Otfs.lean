/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full M5` OTFS, 2WL Chronological Repair & Backward Unwatch (`FullM5Otfs`)

Drop-in verified C0 upgrades preserving the exact `FullHdr` layout (`0` new or borrowed header
fields) and canonical `FullSpec2` contracts for OOM-safe OTFS and 2WL repair:

1. `full_unwatch_large`: suffix-free backward scan from `end` down to `off + 2`
   (`p = p - 2 + (w >> 31)`), shifting only `[p, end)` down by `2` words.
2. `full_otfs_large`: early `cnt >= 3` Pass-1 exit, headroom pre-check (`wcap - wlen >= 2ULL` +
   `full_wstack_defrag`) and `full_watch_push(nl1, ...)` *before* unwatching `uip` or mutating
   `ar[cref]`, fused compaction + `hp` pass, backward unwatch, and `l0` blocker update.
3. `full_otfs_bin_m5`: binary deduplication on watch slices, headroom pre-check (`wcap - wlen >=
   2ULL` + `full_wstack_defrag`), backward `full_unwatch_large`, and exact `PH_SHRK`-aware
   `full_arena_next(h, cref) - cref` garbage accounting.
4. `full_deduce_1uip_m5`: OTFS (`full_otfs_bin_m5`, `full_otfs_large`) aborting cleanly on
   `h->oom != 0ULL`, plus `h->res_sz = h->min_clr_len` transfer before `full_clear_ana(h)`.
5. `full_one_lit_confl_m5`: top-2 highest-level literal repair for both `pos = 0` (`clvl`) and
   `pos = 1` (`max_{k>=1} lvl`, with headroom pre-check + `full_watch_push` + `full_unwatch_large`
   whenever `hp > 1`) *above* `if (cnt > 1ULL) { return 0ULL; }`.
6. `full_prop_lit_chrono` + `full_prop_lit` + `full_propagate_ignore`: headroom pre-check +
   `full_watch_push` before arena swap + `full_unwatch_large(h, l1, r)` + `ol` blocker update,
   still repairing `[t0 .. h->trail_end)` when `full_prop_lit_raw` hits a non-root conflict.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Otfs

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5Otfs "
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

#define PH_GARB 0x00080000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_backtrack(FullHdr *h, u64 new_lvl);
extern u64 full_det_new_level(FullHdr *h, u64 jump);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern bool full_analyze_lit(FullHdr *h, u32 lit, u32 skip_var);
extern bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var);
extern void full_clear_ana(FullHdr *h);
extern void full_otfs_subsume(
  FullHdr *h, u32 new_confl, u64 old_ctype, u64 old_cref, bool to_bin);
extern bool full_prop_lit_raw(FullHdr *h, u32 lit, u64 ignore_ref);

void full_unwatch_large(FullHdr *h, u32 lit, u32 cref) {
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
      while (p < end) { wstk[q] = wstk[p]; q = q + 1ULL; p = p + 1ULL; }
      wstk[end - 2ULL] = 0xFFFFFFFFu;
      wstk[end - 1ULL] = 0xFFFFFFFFu;
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - 2ULL);
      h->wusable = h->wusable + 2ULL;
      return;
    }
    p = p - 2ULL + (u64)(w >> 31);
  }
}

bool full_otfs_large(FullHdr *h, u32 cref, u32 uip) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u64 cb = (u64)cref + 3ULL;
  u32 l0 = ar[cb]; u32 l1 = ar[cb + 1ULL];
  if (l0 == uip) { l0 = l1; }
  else if (l1 != uip) { return false; }
  u32 old_sz = ar[(u64)cref + 2ULL];
  u32 cnt = 1u; u32 i = 2u;
  while (i < old_sz) {
    if (lvl[ar[cb + (u64)i] >> 1] > 0u) {
      cnt = cnt + 1u;
      if (cnt >= 3u) { break; }
    }
    i = i + 1u;
  }
  if (cnt < 3u) { return false; }
  u32 hl_pre = 0u; u32 nl1_pre = uip;
  i = 2u;
  while (i < old_sz) {
    u32 ot = ar[cb + (u64)i];
    u32 cl = lvl[ot >> 1];
    if (cl > hl_pre) { hl_pre = cl; nl1_pre = ot; }
    i = i + 1u;
  }
  if (h->wcap - h->wlen < 2ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
  }
  if (!full_watch_push(h, nl1_pre, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL; return false;
  }
  ar[cb] = l0; ar[cb + 1ULL] = uip;
  full_unwatch_large(h, uip, cref);
  u32 new_sz = 1u; u32 hp = 1u; u32 hl = 0u;
  i = 2u;
  while (i < old_sz) {
    u32 ot = ar[cb + (u64)i];
    u32 cl = lvl[ot >> 1];
    if (cl > 0u) {
      ar[cb + (u64)new_sz] = ot;
      if (cl > hl) { hl = cl; hp = new_sz; }
      new_sz = new_sz + 1u;
    }
    i = i + 1u;
  }
  u32 hdr = ar[cref];
  ar[(u64)cref + 2ULL] = new_sz; ar[(u64)cref + 1ULL] = 2u;
  if ((hdr & PH_SHRK) == 0u) {
    ar[cref] = hdr | PH_SHRK;
    ar[cb + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
  }
  if (hp != 1u) {
    u32 t = ar[cb + 1ULL]; ar[cb + 1ULL] = ar[cb + (u64)hp];
    ar[cb + (u64)hp] = t;
  }
  u32 nl1 = ar[cb + 1ULL];
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  if ((cref & PW_BIN_FLAG) == 0u) {
    u64 off = (u64)wvec[(u64)l0 << 1];
    u64 sz = (u64)wvec[((u64)l0 << 1) + 1ULL];
    if (sz >= 2ULL) {
      u64 p = off + sz;
      u64 off2 = off + 2ULL;
      while (p >= off2) {
        u32 w = wstk[p - 1ULL];
        if (w == cref) { wstk[p - 2ULL] = nl1 & PW_LIT_MASK; break; }
        p = p - 2ULL + (u64)(w >> 31);
      }
    }
  }
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

bool full_otfs_bin_m5(FullHdr *h, u32 cref, u32 uip) {
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
  bool has_bin = false;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 sa = (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 sb = (u64)wvec[((u64)f1 << 1) + 1ULL];
  u32 src = (sa <= sb) ? f0 : f1;
  u32 tgt = (sa <= sb) ? f1 : f0;
  u64 p = (u64)wvec[(u64)src << 1];
  u64 pend = p + (u64)wvec[((u64)src << 1) + 1ULL];
  while (p < pend) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if ((w0 & PW_LIT_MASK) == tgt) { has_bin = true; break; }
      p = p + 1ULL;
    } else {
      p = p + 2ULL;
    }
  }
  if (!has_bin) {
    if (h->wcap - h->wlen < 2ULL) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
    }
    u32 b0 = (f1 & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (f0 & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, f0, b0, 0u, 1u) ||
        !full_watch_push(h, f1, b1, 0u, 1u)) {
      h->oom = 1ULL; return false;
    }
    h->num_binary = h->num_binary + 1ULL;
  }
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u64 gsz = (u64)full_arena_next(h, cref) - (u64)cref;
  ar[cref] = ar[cref] | PH_GARB;
  h->arena_garbage = h->arena_garbage + gsz;
  h->confl_type = 1ULL; h->confl_lit0 = (u64)f0; h->confl_lit1 = (u64)f1;
  h->confl_ref = 0xFFFFFFFFULL;
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

u64 full_deduce_1uip_m5(FullHdr *h) {
  if (h->oom != 0ULL) { return 0ULL; }
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
          if (full_otfs_bin_m5(h, rsn, p)) {
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len;
            full_clear_ana(h); return 2ULL;
          }
          if (h->oom != 0ULL) { full_clear_ana(h); return 0ULL; }
        } else {
          if (full_otfs_large(h, rsn, p)) {
            h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, rsn, old_ct, old_cr, false);
            }
            h->res_sz = h->min_clr_len;
            full_clear_ana(h); return 2ULL;
          }
          if (h->oom != 0ULL) { full_clear_ana(h); return 0ULL; }
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}

u64 full_one_lit_confl_m5(FullHdr *h) {
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
  u32 pos = 0u;
  while (pos < 2u) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)pos];
    u32 hl = lvl[lit >> 1];
    u32 hp = pos;
    u32 j = pos + 1u;
    while (j < csz) {
      u32 cand = ar[(u64)cref + 3ULL + (u64)j];
      u32 cl = lvl[cand >> 1];
      if (cl > hl) { hl = cl; hp = j; }
      j = j + 1u;
    }
    if (hp != pos) {
      u32 high_lit = ar[(u64)cref + 3ULL + (u64)hp];
      if (hp > 1u) {
        u32 other = ar[(u64)cref + 3ULL + (u64)(pos ^ 1u)];
        if (h->wcap - h->wlen < 2ULL) {
          if (h->wusable > 0ULL) { full_wstack_defrag(h); }
          if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return 2ULL; }
        }
        if (!full_watch_push(h, high_lit, other & PW_LIT_MASK, cref, 2u)) {
          h->oom = 1ULL; return 2ULL;
        }
        ar[(u64)cref + 3ULL + (u64)pos] = high_lit;
        ar[(u64)cref + 3ULL + (u64)hp] = lit;
        full_unwatch_large(h, lit, cref);
      } else {
        ar[(u64)cref + 3ULL + (u64)pos] = high_lit;
        ar[(u64)cref + 3ULL + (u64)hp] = lit;
      }
    }
    pos = pos + 1u;
  }
  if (cnt > 1ULL) { return 0ULL; }
  u64 nlvl = full_det_new_level(h, jlvl);
  full_backtrack(h, nlvl);
  full_assign_lvl(h, forced, cref, (u32)jlvl);
  return 1ULL;
}

bool full_prop_lit_chrono(FullHdr *h, u32 lit, u64 ignore_ref) {
  u64 t0 = h->trail_end;
  bool ok = full_prop_lit_raw(h, lit, ignore_ref);
  if (h->oom != 0ULL) { return false; }
  u64 te = h->trail_end;
  u64 nlits = h->cur_vars << 1;
  if (t0 >= te || (u64)lit >= nlits) { return ok; }
  u32 *lvl = (u32 *)h->level;
  if ((u64)lvl[lit >> 1] >= h->cur_level) { return ok; }
  u32 *trl = (u32 *)h->trail;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 alen = h->arena_len;
  u64 t = t0;
  while (t < te) {
    u32 ol = trl[t];
    t = t + 1ULL;
    if ((u64)ol >= nlits) { continue; }
    u32 r = rsns[ol >> 1];
    if (r == 0xFFFFFFFFu || (r & PW_BIN_FLAG) != 0u) { continue; }
    if ((u64)r + 3ULL > alen) { continue; }
    u32 hdr = ar[r]; u32 csz = ar[(u64)r + 2ULL];
    u64 cb = (u64)r + 3ULL;
    if ((hdr & PH_GARB) != 0u || csz < 3u || cb + (u64)csz > alen) { continue; }
    if (ar[cb] != ol) { continue; }
    u32 l1 = ar[cb + 1ULL];
    if ((u64)l1 >= nlits) { continue; }
    u32 best = lvl[l1 >> 1]; u32 bi = 1u; u32 k = 2u;
    while (k < csz) {
      u32 ck = ar[cb + (u64)k];
      if ((u64)ck < nlits) {
        u32 kl = lvl[ck >> 1];
        if (kl > best) { best = kl; bi = k; }
      }
      k = k + 1u;
    }
    if (bi != 1u) {
      u32 nw = ar[cb + (u64)bi];
      if (h->wcap - h->wlen < 2ULL) {
        if (h->wusable > 0ULL) { full_wstack_defrag(h); }
        if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
      }
      if (!full_watch_push(h, nw, ol & PW_LIT_MASK, r, 2u)) {
        h->oom = 1ULL; return false;
      }
      ar[cb + 1ULL] = nw; ar[cb + (u64)bi] = l1;
      full_unwatch_large(h, l1, r);
      u64 off = (u64)wvec[(u64)ol << 1];
      u64 sz = (u64)wvec[((u64)ol << 1) + 1ULL];
      if (sz >= 2ULL) {
        u64 p = off + sz;
        u64 off2 = off + 2ULL;
        while (p >= off2) {
          u32 w = wstk[p - 1ULL];
          if (w == r) { wstk[p - 2ULL] = nw & PW_LIT_MASK; break; }
          p = p - 2ULL + (u64)(w >> 31);
        }
      }
    }
  }
  return ok;
}

bool full_prop_lit(FullHdr *h, u32 lit, u64 ignore_ref) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)lit < nlits) {
    u32 *lvl = (u32 *)h->level;
    if ((u64)lvl[lit >> 1] < h->cur_level) {
      return full_prop_lit_chrono(h, lit, ignore_ref);
    }
  }
  return full_prop_lit_raw(h, lit, ignore_ref);
}

u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  if (prop >= h->trail_end) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  u32 *trl = (u32 *)h->trail;
  u32 *lvl = (u32 *)h->level;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u64 fuel = h->fuel;
  while (prop < h->trail_end) {
    if (fuel == 0ULL) {
      h->propagated = prop; h->fuel = fuel; return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    prop = prop + 1ULL;
    h->propagated = prop;
    bool ok = true;
    if (clvl != 0ULL && (u64)lit < nlits && (u64)lvl[lit >> 1] < clvl) {
      ok = full_prop_lit_chrono(h, lit, ignore_ref);
    } else {
      ok = full_prop_lit_raw(h, lit, ignore_ref);
    }
    if (!ok) {
      h->fuel = fuel;
      return (h->oom != 0ULL) ? 2ULL : 1ULL;
    }
  }
  h->propagated = prop; h->fuel = fuel;
  return 0ULL;
}
"

/-- External callee signatures referenced by `m5Otfs_fns`. -/
def m5OtfsExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_det_new_level", [i64, i64], [i64]⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool]⟩
  , ⟨"full_clear_ana", [i64], []⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], []⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool]⟩
  ]

/-- Standalone `FullM5Otfs` C0 module (`8` functions, `11` externs, `0` exits). -/
def m5OtfsModule : LeanQbe.T.Module :=
  { fns := m5Otfs_fns, externs := m5OtfsExterns, exits := [] }

theorem full_unwatch_large_wf : Func.Wf full_unwatch_large_body := by t_wf_reify
theorem full_otfs_large_wf : Func.Wf full_otfs_large_body := by t_wf_reify
theorem full_otfs_bin_m5_wf : Func.Wf full_otfs_bin_m5_body := by t_wf_reify
theorem full_deduce_1uip_m5_wf : Func.Wf full_deduce_1uip_m5_body := by t_wf_reify
theorem full_one_lit_confl_m5_wf : Func.Wf full_one_lit_confl_m5_body := by t_wf_reify
theorem full_prop_lit_chrono_wf : Func.Wf full_prop_lit_chrono_body := by t_wf_reify
theorem full_prop_lit_wf : Func.Wf full_prop_lit_body := by t_wf_reify
theorem full_propagate_ignore_wf : Func.Wf full_propagate_ignore_body := by t_wf_reify

theorem m5Otfs_fns_wf : ∀ f ∈ m5Otfs_fns, f.Wf := by
  simp only [m5Otfs_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_unwatch_large_wf, full_otfs_large_wf, full_otfs_bin_m5_wf,
    full_deduce_1uip_m5_wf, full_one_lit_confl_m5_wf, full_prop_lit_chrono_wf,
    full_prop_lit_wf, full_propagate_ignore_wf⟩

theorem m5Otfs_acyclic : m5OtfsModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5Otfs

module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M5 Dense-Mode OOM & BVA Watch Safety (`FullM5DenseSafe`)

Standalone drop-in C0 replacements covering Wave 0 `RC-02`, `RC-03`, and `RC-04` (`0` `FullHdr`
layout churn, `0` edits to landed `Full1..3` / `FullM4*` files), verified against exact canonical
`Full` / `FullFastSched` / `FullFastBveBudgets` / `FullM4Bva` specs for zero-friction `FullM5`
splicing:

1. `full_enter_dense_m5` (`RC-02`): preserves pre-existing `h->oom != 0ULL` (returning `false`
   immediately after level-0 backtrack/propagate); only clears `h->oom = 0ULL` on local dense
   watch-push failure before any clause has been mutated or deleted.
2. `full_subst_rewrite_bins_m5` (`RC-02`, `RC-03`): deduplicates rewritten binaries via `lit_mark`
   bit 1, sets `h->oom = 1ULL` and aborts cleanly (never silently discarding) on `pn >= nlits` or
   `full_add_bin == 2ULL`, and keeps `return false` strictly for genuine `F0.Unsat`.
3. `full_subst_rewrite_ar_m5` (`RC-02`): aborts immediately with `h->oom = 1ULL` on
   `full_add_bin == 2ULL` (`h->oom != 0ULL`) while keeping `return false` strictly for `F0.Unsat`.
4. `full_substitute_m5` (`RC-02`): aborts immediately before `full_propagate`/`full_arena_sweep`
   whenever `h->oom != 0ULL` after `full_subst_rewrite_bins` / `full_subst_rewrite_ar`.
5. `full_fwd_check_cl_m5` (`RC-02`): checks `full_add_bin == 2ULL` before unwatching or
   `PH_GARB`-deleting the strengthened clause, aborting cleanly without dropping clauses or
   falsely returning `false` (which `full_forward_sub` maps to `20ULL` UNSAT).
6. `full_bve_var_m5` (`RC-02`): pre-checks worst-case `watch_stk` headroom over all buffered
   resolvents (calling `full_wstack_defrag` if needed) before `full_bve_weaken` / `FL_ELIM`.
7. `full_bva_commit_m5` (`RC-04`): budgets `2 * wvec[l].sz + 2` copying growth per touched literal
   in `need_w` (defragging if needed) and checks every `full_add_bin` / `full_watch_push` return
   in Phase 1 **before** Phase 2 unwatches/`PH_GARB`-deletes any original clause.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5DenseSafe

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5DenseSafe "
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
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ELIM    2u
#define FL_FACT_P  256u
#define FL_FACT_N  512u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_sweep_bins(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_set_inactive(FullHdr *h, u32 v, u32 bit);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_tarjan_scc(FullHdr *h);
extern bool full_subst_elim_vars(FullHdr *h, u64 ucnt);
extern bool full_subst_rewrite_bins(FullHdr *h);
extern bool full_subst_rewrite_ar(FullHdr *h);
extern u32 full_bve_collect(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern void full_bve_gates(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern bool full_bve_try_bce(FullHdr *h, u32 blk_lit, u32 cr, u32 opp_off, u32 opp_n);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern void full_init_fresh_var(FullHdr *h, u32 fv);

bool full_enter_dense_m5(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return false; }
  if (h->dense_mode != 0ULL) { return true; }
  if (full_propagate(h) == 1ULL) { h->inconsistent = 1ULL; return false; }
  if (h->oom != 0ULL) { return false; }
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
          h->oom = 0ULL; full_arena_sweep(h); return false;
        }
        k = k + 1u;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  h->dense_mode = 1ULL;
  return true;
}

bool full_subst_rewrite_bins_m5(FullHdr *h) {
  if (h->oom != 0ULL) { return true; }
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u8 *lm = (u8 *)h->lit_mark;
  u32 *pa = (u32 *)h->work_stk1; u32 *pb = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    u32 rl = repr[l]; u64 pn = 0ULL; bool ovf = false;
    u64 p = off; u64 q = off; u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) == 0u) {
        if (p < end) { wstk[q] = w0; wstk[q + 1ULL] = wstk[p]; q = q + 2ULL; p = p + 1ULL; }
        continue;
      }
      u32 ot = w0 & PW_LIT_MASK; u32 rot = ((u64)ot < nlits) ? repr[ot] : ot;
      if (rl == (u32)l && rot == ot) {
        if ((lm[ot] & (u8)1) == (u8)0) { lm[ot] = lm[ot] | (u8)1; wstk[q] = w0; q = q + 1ULL; }
        else if (l < (u64)ot && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
      } else {
        if (l < (u64)ot) {
          if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
          if (rl != (rot ^ 1u)) {
            if ((u64)rot < nlits) {
              if ((lm[rot] & (u8)2) == (u8)0) {
                if (pn < nlits) {
                  lm[rot] = lm[rot] | (u8)2; pa[pn] = rl; pb[pn] = rot; pn = pn + 1ULL;
                } else { ovf = true; }
              }
            } else { ovf = true; }
          }
        }
      }
    }
    u64 c = off;
    while (c < q) {
      if ((wstk[c] & PW_BIN_FLAG) != 0u) { lm[wstk[c] & PW_LIT_MASK] = (u8)0; }
      c = c + 1ULL;
    }
    c = 0ULL;
    while (c < pn) { lm[pb[c]] = (u8)0; c = c + 1ULL; }
    c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off); h->wusable = h->wusable + (end - q);
    if (ovf) { h->oom = 1ULL; return true; }
    c = 0ULL;
    while (c < pn) {
      if (pa[c] == pb[c]) { if (!full_add_unit(h, pa[c])) { return false; } }
      else {
        u64 br = full_add_bin(h, pa[c], pb[c]);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
      c = c + 1ULL;
    }
    l = l + 1ULL;
  }
  return true;
}

bool full_subst_rewrite_ar_m5(FullHdr *h) {
  if (h->oom != 0ULL) { return true; }
  u32 *ar = (u32 *)h->arena; u32 *repr = (u32 *)h->repr;
  u8 *lm = (u8 *)h->lit_mark; u64 nlits = h->cur_vars << 1;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) != 0u || sz < 3u) { p = np; continue; }
    bool chg = false; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k];
      if ((u64)l < nlits && repr[l] != l) { chg = true; break; }
      k = k + 1u;
    }
    if (!chg) { p = np; continue; }
    bool taut = false; u32 nsz = 0u; k = 0u;
    while (k < sz) {
      u32 rl = repr[ar[p + 3ULL + (u64)k]];
      if (lm[rl ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rl] == (u8)0) { lm[rl] = (u8)1; ar[p + 3ULL + (u64)nsz] = rl; nsz = nsz + 1u; }
      k = k + 1u;
    }
    k = 0u; while (k < nsz) { lm[ar[p + 3ULL + (u64)k]] = (u8)0; k = k + 1u; }
    if (taut || nsz <= 2u) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
      if (!taut && nsz == 1u && !full_add_unit(h, ar[p + 3ULL])) { return false; }
      if (!taut && nsz == 2u) {
        u64 br = full_add_bin(h, ar[p + 3ULL], ar[p + 4ULL]);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
    } else if (nsz < sz) {
      ar[p + 2ULL] = nsz; ar[p + 1ULL] = 2u;
      if ((hdr & PH_SHRK) == 0u) {
        ar[p] = hdr | PH_SHRK; ar[p + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
      }
    }
    p = np;
  }
  return true;
}

u64 full_substitute_m5(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->num_binary == 0ULL || h->oom != 0ULL) { return 1ULL; }
  u64 round = 0ULL;
  while (round < 4ULL && h->inconsistent == 0ULL && h->oom == 0ULL) {
    u64 before = h->subst_cnt;
    u64 ucnt = full_tarjan_scc(h);
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (!full_subst_elim_vars(h, ucnt)) { return 20ULL; }
    if (h->subst_cnt == before) { break; }
    if (!full_subst_rewrite_bins(h)) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    if (!full_subst_rewrite_ar(h)) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL || h->oom != 0ULL) { return 1ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    round = round + 1ULL;
  }
  return 1ULL;
}

bool full_fwd_check_cl_m5(FullHdr *h, u32 cref) {
  if (h->oom != 0ULL) { return true; }
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 hdr = ar[cref]; u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return true; }
  u32 i = 0u; while (i < sz) { lm[ar[(u64)cref + 3ULL + (u64)i]] = (u8)1; i = i + 1u; }
  bool subsumed = false; u32 drop = 0xFFFFFFFFu; u32 min_l = ar[(u64)cref + 3ULL];
  u32 min_deg = wvec[((u64)min_l << 1) + 1ULL];
  i = 1u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u32 d = wvec[((u64)l << 1) + 1ULL];
    if (d < min_deg) { min_deg = d; min_l = l; }
    i = i + 1u;
  }
  i = 0u;
  while (i < sz && !subsumed && drop == 0xFFFFFFFFu) {
    u32 l = (i == 0u) ? min_l : ar[(u64)cref + 3ULL + (u64)i];
    if (i > 0u && l == min_l) { l = ar[(u64)cref + 3ULL]; }
    u64 off = (u64)wvec[(u64)l << 1]; u64 end = off + (u64)wvec[((u64)l << 1) + 1ULL];
    u64 p = off;
    while (p < end && p - off < 128ULL) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if (lm[ot] != (u8)0) { subsumed = true; break; }
        if ((ot ^ 1u) != l && lm[ot ^ 1u] != (u8)0) { drop = ot ^ 1u; break; }
        continue;
      }
      if (p >= end) { break; }
      u32 cr = wstk[p]; p = p + 1ULL;
      if (cr == cref || (ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
      u32 dsz = ar[(u64)cr + 2ULL];
      if (dsz > sz) { continue; }
      u32 miss = 0u; u32 cand = 0xFFFFFFFFu; u32 j = 0u;
      while (j < dsz) {
        u32 dl = ar[(u64)cr + 3ULL + (u64)j];
        if (lm[dl] == (u8)0 && vals[dl] >= (i8)0) {
          if (lm[dl ^ 1u] != (u8)0 && cand == 0xFFFFFFFFu) { cand = dl ^ 1u; }
          else { miss = 2u; break; }
        }
        j = j + 1u;
      }
      if (miss == 0u && cand == 0xFFFFFFFFu) { subsumed = true; break; }
      if (miss == 0u && cand != 0xFFFFFFFFu) { drop = cand; break; }
    }
    i = i + 1u;
  }
  i = 0u; while (i < sz) { lm[ar[(u64)cref + 3ULL + (u64)i]] = (u8)0; i = i + 1u; }
  if (subsumed) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    h->fwd_sub_cnt = h->fwd_sub_cnt + 1ULL; return true;
  }
  if (drop != 0xFFFFFFFFu) {
    u32 nsz = 0u; u32 l0 = 0u; u32 l1 = 0u; i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      if (l != drop) {
        if (nsz == 0u) { l0 = l; } else if (nsz == 1u) { l1 = l; }
        nsz = nsz + 1u;
      }
      i = i + 1u;
    }
    if (nsz <= 2u) {
      if (nsz == 2u) {
        u64 br = full_add_bin(h, l0, l1);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
      h->fwd_str_cnt = h->fwd_str_cnt + 1ULL; full_unwatch_large(h, drop, cref);
      ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (nsz == 0u) { h->inconsistent = 1ULL; return false; }
      if (nsz == 1u) { return full_add_unit(h, l0); }
      return true;
    }
    h->fwd_str_cnt = h->fwd_str_cnt + 1ULL; full_unwatch_large(h, drop, cref);
    u32 w = 0u; i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      if (l != drop) { ar[(u64)cref + 3ULL + (u64)w] = l; w = w + 1u; }
      i = i + 1u;
    }
    ar[(u64)cref + 2ULL] = w; ar[(u64)cref + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[cref] = hdr | PH_SHRK; ar[(u64)cref + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
    }
  }
  return true;
}

u64 full_bve_var_m5(FullHdr *h, u32 v) {
  if (h->oom != 0ULL) { return 2ULL; }
  if (h->scratch_cap < 512ULL) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 pl = v << 1; u32 nl = pl | 1u;
  u32 np = full_bve_collect(h, pl, scr, 64u);
  u32 nn = full_bve_collect(h, nl, scr + 64, 64u);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  u64 ext_need = full_bve_ext_need(h, 0u, np) + full_bve_ext_need(h, 64u, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, 64u, nn))) { h->oom = 1ULL; return 2ULL; }
    full_set_inactive(h, v, FL_ELIM); h->bve_cnt = h->bve_cnt + 1ULL; return 1ULL;
  }
  u64 r_cnt = 0ULL; u64 rp = 160ULL; u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    full_bve_gates(h, v, np, nn);
    u64 pmask = (u64)scr[128] | ((u64)scr[129] << 32);
    u64 nmask = (u64)scr[130] | ((u64)scr[131] << 32);
    bool gate_found = (pmask != 0ULL || nmask != 0ULL);
    u32 i = 0u;
    while (i < np && fit) {
      u32 j = 0u;
      while (j < nn && fit) {
        bool need_pair = !gate_found ||
          ((((pmask >> (u64)i) | (nmask >> (u64)j)) & 1ULL) != 0ULL);
        if (need_pair && full_bve_resolve_pair(h, v, scr[i], scr[64u + j])) {
          r_cnt = r_cnt + 1ULL;
          if (r_cnt > lim_cls || rp + 1ULL + h->tmp_len > h->scratch_cap) { fit = false; break; }
          scr[rp] = (u32)h->tmp_len; u32 *tmp = (u32 *)h->tmp_lits; u32 k = 0u;
          while ((u64)k < h->tmp_len) { scr[rp + 1ULL + (u64)k] = tmp[k]; k = k + 1u; }
          rp = rp + 1ULL + h->tmp_len;
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
  }
  if (fit && h->arena_len + (rp - 160ULL) + (r_cnt * 2ULL) + 16ULL <= h->arena_cap) {
    u32 *wvec = (u32 *)h->watch_vec;
    u64 w_add = 0ULL; u64 max_sz = 0ULL; u64 wp_p = 160ULL;
    while (wp_p < rp) {
      u32 rsz = scr[wp_p]; wp_p = wp_p + 1ULL;
      if (rsz >= 2u) {
        u64 per = (rsz == 2u) ? 1ULL : 2ULL;
        u32 wk = 0u;
        while (wk < rsz) {
          u32 wl = scr[wp_p + (u64)wk];
          u64 lsz = (u64)wvec[((u64)wl << 1) + 1ULL];
          if (lsz > max_sz) { max_sz = lsz; }
          w_add = w_add + per;
          wk = wk + 1u;
        }
      }
      wp_p = wp_p + (u64)rsz;
    }
    u64 w_need = (w_add << 1) + max_sz + (r_cnt * 4ULL) + 16ULL;
    if (h->wcap < h->wlen || h->wcap - h->wlen < w_need) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    }
    if (h->wcap >= h->wlen && h->wcap - h->wlen >= w_need) {
      if (!full_bve_weaken(h, pl, 0u, np) || !full_bve_weaken(h, nl, 64u, nn)) {
        h->oom = 1ULL; return 2ULL;
      }
      full_set_inactive(h, v, FL_ELIM); h->bve_cnt = h->bve_cnt + 1ULL;
      return full_bve_commit_res(h, 160ULL, rp);
    }
  }
  u32 i = 0u;
  while (i < np) {
    if (full_bve_try_bce(h, pl, scr[i], 64u, nn)) {
      if ((scr[i] & PW_BIN_FLAG) != 0u) {
        if (full_extend_push2(h, pl, scr[i] & PW_LIT_MASK)) {
          full_delete_binary(h, pl, scr[i] & PW_LIT_MASK); h->bce_cnt = h->bce_cnt + 1ULL;
        }
      } else if (full_extend_push_cl(h, pl, scr[i])) {
        u32 *ar = (u32 *)h->arena; u32 ccr = scr[i]; ar[ccr] = ar[ccr] | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)ccr + 2ULL];
        h->bce_cnt = h->bce_cnt + 1ULL;
      }
    }
    i = i + 1u;
  }
  return 1ULL;
}

bool full_bva_commit_m5(FullHdr *h, u32 best_k) {
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
      while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
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
  while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}
"

/-- External callee signatures referenced by `m5DenseSafe_fns`. -/
def m5DenseSafeExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
  , ⟨"full_sweep_bins", [i64], []⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool]⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_set_inactive", [i64, i32, i32], []⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_tarjan_scc", [i64], [i64]⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool]⟩
  , ⟨"full_subst_rewrite_bins", [i64], [.bool]⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool]⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32]⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], []⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64]⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64]⟩
  , ⟨"full_init_fresh_var", [i64, i32], []⟩ ]

/-- Standalone M5 Wave-0B module (`7` upgraded functions + `27` externs, `0` exits). -/
def m5DenseSafeModule : LeanQbe.T.Module :=
  { fns := m5DenseSafe_fns, externs := m5DenseSafeExterns, exits := [] }

/-- Drop-in renamed `Fn` handles matching canonical `FullM4`/`FullM5` splice slots. -/
def m5EnterDenseFn : Fn := ⟨"full_enter_dense", [i64], [.bool], full_enter_dense_m5_body⟩
def m5SubstRewriteBinsFn : Fn :=
  ⟨"full_subst_rewrite_bins", [i64], [.bool], full_subst_rewrite_bins_m5_body⟩
def m5SubstRewriteArFn : Fn :=
  ⟨"full_subst_rewrite_ar", [i64], [.bool], full_subst_rewrite_ar_m5_body⟩
def m5SubstituteFn : Fn := ⟨"full_substitute", [i64], [i64], full_substitute_m5_body⟩
def m5FwdCheckClFn : Fn := ⟨"full_fwd_check_cl", [i64, i32], [.bool], full_fwd_check_cl_m5_body⟩
def m5BveVarFn : Fn := ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_m5_body⟩
def m5BvaCommitFn : Fn := ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_m5_body⟩

theorem full_enter_dense_m5_wf : Func.Wf full_enter_dense_m5_body := by t_wf_reify
theorem full_subst_rewrite_bins_m5_wf : Func.Wf full_subst_rewrite_bins_m5_body := by t_wf_reify
theorem full_subst_rewrite_ar_m5_wf : Func.Wf full_subst_rewrite_ar_m5_body := by t_wf_reify
theorem full_substitute_m5_wf : Func.Wf full_substitute_m5_body := by t_wf_reify
theorem full_fwd_check_cl_m5_wf : Func.Wf full_fwd_check_cl_m5_body := by t_wf_reify
theorem full_bve_var_m5_wf : Func.Wf full_bve_var_m5_body := by t_wf_reify
theorem full_bva_commit_m5_wf : Func.Wf full_bva_commit_m5_body := by t_wf_reify

theorem m5DenseSafe_fns_wf : ∀ f ∈ m5DenseSafe_fns, f.Wf := by
  simp only [m5DenseSafe_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_enter_dense_m5_wf, full_subst_rewrite_bins_m5_wf, full_subst_rewrite_ar_m5_wf,
    full_substitute_m5_wf, full_fwd_check_cl_m5_wf, full_bve_var_m5_wf, full_bva_commit_m5_wf⟩

theorem m5DenseSafe_acyclic : m5DenseSafeModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5DenseSafe

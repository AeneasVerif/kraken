module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M4f Upgrades: Effort-Capped Prefix-Sorted Vivification & Dual-Polarity BCE

Standalone, zero-conflict C0 module off `main @ d8468dce` preserving the frozen `144`-word
`FullHdr` layout (`0` layout churn, `0` edits to existing files):

1. **Vivification `vivifyeffort` tick cap, watch-degree prefix-sorted schedule & trail reuse**:
   - `full_viv_sort_noccs_m4`: sorts `tmp_lits[0 .. sz)` by watch-list occurrence counts
     `watch_vec[(l << 1) + 1]` (including binary clauses; descending degree, tie-break literal ID).
   - `full_viv_has_l0_m4` / `full_viv_l0_simp_m4`: checks whether any literal of `cref` is assigned
     at level `0` and, if so, backtracks to level `0` and runs `full_viv_simplify`.
   - `full_viv_reuse_prefix_m4`: true prefix-preserving trail reuse (no `tmp` reordering) keeping
     the shared decision prefix `frame_dec[1 .. keep_lvl]` (skipping literals already implied
     false at `<= keep_lvl`), guarding `rsns[l >> 1] == cref`, and backtracking only to `keep_lvl`.
   - `full_viv_finish_m4` / `full_viv_clause_m4`: single-clause vivification keeping the
     assumption trail alive across clauses unless a level-0 simplification/strengthening commits
     (unwinding 1 level on conflict).
   - `full_viv_sort_sched_m4` / `full_viv_tier_match_m4` / `full_viv_collect_m4` /
     `full_viv_keys_m4` / `full_viv_clear_tier_m4`: collects candidate clauses into `red_refs`,
     computes top-2 watch-degree literal keys `(k0, k1)`, shell-sorts by watch-degree descending
     with prefix grouping `(deg(k0) desc, k0 asc, deg(k1) desc, k1 asc, cref asc)`, and clears
     `PH_VIV` on tier wrap-around (`0` `tarjan_reach` writes).
   - `full_vivify_m4`: drop-in same-spec replacement (`FullFastBveBudgets.fullVivifyFastSpec`)
     enforcing Kissat 4.0.4's `mineffort` + `vivifyeffort` tick cap (`eff_ref = max(delta, 10M)`,
     `3%` for tier 1/2/irred and `1%` for tier 3 -> `300k/300k/100k/300k` floor, where
     `delta = search_ticks - fwd_sub_cnt`), building the watch-degree prefix-sorted schedule in
     `red_refs`, and clearing `PH_VIV` only on tier wrap-around.

2. **Dual-polarity Blocked Clause Elimination (`l` and `nl`)**:
   - `full_bce_side_m4`: dense-mode single-polarity BCE loop deleting blocked binaries and
     marking blocked arena clauses `PH_GARB` while compacting surviving entries in place.
   - `full_bce_pair_m4`: fixes the positive-only BCE bug by running `full_bce_side_m4` on BOTH
     positive (`pl = v << 1`) and negative (`nl = pl | 1u`) occurrences (passing the compacted
     surviving positive count `rem_p` to the negative pass).
   - `full_bce_var_m4`: dense-mode per-variable BCE driver collecting `pl` and `nl` (`cap = 64`).
   - `full_bce_m4`: standalone sparse-mode BCE pass (`FullSparseInv -> FullSparseInv`,
     UNSAT-sound `20 -> F0.Unsat`) entering dense mode, running dual-polarity BCE on active
     unassigned variables within `budget`, rebuilding 2WL watches, and propagating level-0 units.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4VivBce

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m4VivBce "
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
#define PH_VIV  0x00100000u
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE 1u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref);
extern u64 full_propagate(FullHdr *h);
extern u64 full_viv_simplify(FullHdr *h, u32 cref);
extern u32 full_viv_deduce(FullHdr *h, u32 cref, u32 implied, u32 *out);
extern u64 full_viv_commit(FullHdr *h, u32 cref, u32 *out, u32 olen, bool used_red);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u32 full_bve_collect(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern bool full_bve_try_bce(FullHdr *h, u32 blk_lit, u32 cr, u32 opp_off, u32 opp_n);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);

void full_viv_sort_noccs_m4(FullHdr *h, u32 sz) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 i = 1u;
  while (i < sz) {
    u32 x = tmp[i];
    u32 dx = wvec[((u64)x << 1) + 1ULL];
    u32 j = i;
    while (j > 0u) {
      u32 prev = tmp[j - 1u];
      u32 dp = wvec[((u64)prev << 1) + 1ULL];
      if (dp > dx || (dp == dx && prev < x)) { break; }
      tmp[j] = prev;
      j = j - 1u;
    }
    tmp[j] = x;
    i = i + 1u;
  }
}

bool full_viv_has_l0_m4(FullHdr *h, u32 cref, u32 sz) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[l] != (i8)0 && lvl[l >> 1] == 0u) { return true; }
    i = i + 1u;
  }
  return false;
}

u64 full_viv_l0_simp_m4(FullHdr *h, u32 cref, u32 sz) {
  if (!full_viv_has_l0_m4(h, cref, sz)) { return 0ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 sr = full_viv_simplify(h, cref);
  if (sr != 0ULL) { return (sr == 20ULL) ? 20ULL : 1ULL; }
  return 0ULL;
}

void full_viv_reuse_prefix_m4(FullHdr *h, u32 cref, u32 sz) {
  if (h->cur_level == 0ULL) { return; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u64 clvl = h->cur_level;
  u64 keep_lvl = 0ULL;
  u32 i = 0u;
  while (i < sz && keep_lvl < clvl) {
    u32 l = tmp[i];
    if (l == (fdec[keep_lvl + 1ULL] ^ 1u)) {
      keep_lvl = keep_lvl + 1ULL;
    } else if (!(vals[l] < (i8)0 && (u64)lvl[l >> 1] <= keep_lvl)) {
      break;
    }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < sz && keep_lvl > 0ULL) {
    u32 l = tmp[j];
    if (vals[l] > (i8)0 && rsns[l >> 1] == cref) {
      u64 rl = (u64)lvl[l >> 1];
      if (rl == 0ULL) { keep_lvl = 0ULL; }
      else if (rl - 1ULL < keep_lvl) { keep_lvl = rl - 1ULL; }
    }
    j = j + 1u;
  }
  if (keep_lvl < clvl) { full_backtrack(h, keep_lvl); }
}

u64 full_viv_finish_m4(FullHdr *h, u32 cref, u32 sz, bool confl, u32 implied, bool all_done) {
  u32 *out = (u32 *)h->work_stk2;
  u32 olen = sz;
  h->res_sz = 0ULL;
  if (confl || implied != 0xFFFFFFFFu || all_done) {
    olen = full_viv_deduce(h, cref, confl ? 0xFFFFFFFFu : implied, out);
  }
  bool used_red = (h->res_sz != 0ULL);
  if (olen < sz) {
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    return full_viv_commit(h, cref, out, olen, used_red);
  }
  if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
  if (h->cur_level > 0ULL) {
    u32 *ar = (u32 *)h->arena;
    i8 *vals = (i8 *)h->values;
    u32 *lvl = (u32 *)h->level;
    u32 l0 = ar[(u64)cref + 3ULL];
    u32 l1 = ar[(u64)cref + 4ULL];
    i8 v0 = vals[l0];
    i8 v1 = vals[l1];
    u64 lvl0 = (v0 != (i8)0) ? (u64)lvl[l0 >> 1] : 0ULL;
    u64 lvl1 = (v1 != (i8)0) ? (u64)lvl[l1 >> 1] : 0ULL;
    u64 new_lvl = 0ULL;
    if (v0 < (i8)0) {
      if (v1 < (i8)0) {
        new_lvl = (lvl0 < lvl1) ? lvl0 : lvl1;
      } else {
        if (v1 == (i8)0) { new_lvl = lvl0; }
        else if (lvl0 < lvl1) { new_lvl = lvl0; }
      }
    } else if (v1 < (i8)0) {
      if (v0 == (i8)0) { new_lvl = lvl1; }
      else if (lvl1 < lvl0) { new_lvl = lvl1; }
    }
    if (new_lvl > 0ULL && new_lvl - 1ULL < h->cur_level) {
      full_backtrack(h, new_lvl - 1ULL);
    }
  }
  return 1ULL;
}

u64 full_viv_clause_m4(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((ar[cref] & PH_GARB) != 0u) { return 1ULL; }
  u32 sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u64 l0r = full_viv_l0_simp_m4(h, cref, sz);
  if (l0r != 0ULL) { return l0r; }
  sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u;
  while (i < sz) { tmp[i] = ar[(u64)cref + 3ULL + (u64)i]; i = i + 1u; }
  full_viv_sort_noccs_m4(h, sz);
  full_viv_reuse_prefix_m4(h, cref, sz);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  bool confl = false; u32 implied = 0xFFFFFFFFu;
  i = 0u;
  while (i < sz) {
    u32 lit = tmp[i]; i8 lv = vals[lit];
    if (lv > (i8)0) { implied = lit; break; }
    if (lv == (i8)0) {
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { break; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
      full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
      u64 pr = full_propagate_ignore(h, (u64)cref);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) { confl = true; break; }
    }
    i = i + 1u;
  }
  u64 fr = full_viv_finish_m4(h, cref, sz, confl, implied, i == sz);
  if (fr != 2ULL && (ar[cref] & PH_GARB) == 0u) { ar[cref] = ar[cref] | PH_VIV; }
  return fr;
}

void full_viv_sort_sched_m4(FullHdr *h, u64 bn) {
  u32 *rr = (u32 *)h->red_refs;
  u32 *wvec = (u32 *)h->watch_vec;
  u64 nlits = h->cur_vars << 1;
  u64 gap = bn >> 1;
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < bn) {
      u64 sb = si * 3ULL;
      u32 cr = rr[sb];
      u32 k0 = rr[sb + 1ULL];
      u32 k1 = rr[sb + 2ULL];
      u32 dk0 = ((u64)k0 < nlits) ? wvec[((u64)k0 << 1) + 1ULL] : 0u;
      u32 dk1 = ((u64)k1 < nlits) ? wvec[((u64)k1 << 1) + 1ULL] : 0u;
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u64 pb = pj * 3ULL;
        u32 pcr = rr[pb];
        u32 pk0 = rr[pb + 1ULL];
        u32 pk1 = rr[pb + 2ULL];
        u32 dpk0 = ((u64)pk0 < nlits) ? wvec[((u64)pk0 << 1) + 1ULL] : 0u;
        u32 dpk1 = ((u64)pk1 < nlits) ? wvec[((u64)pk1 << 1) + 1ULL] : 0u;
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
        u64 jb = sj * 3ULL;
        rr[jb] = pcr;
        rr[jb + 1ULL] = pk0;
        rr[jb + 2ULL] = pk1;
        sj = pj;
      }
      u64 fb = sj * 3ULL;
      rr[fb] = cr;
      rr[fb + 1ULL] = k0;
      rr[fb + 2ULL] = k1;
      si = si + 1ULL;
    }
    gap = gap >> 1;
  }
}

bool full_viv_tier_match_m4(FullHdr *h, u32 hdr, u64 tier_mode) {
  bool is_red = ((hdr & PH_RED) != 0u);
  u64 glue = (u64)(hdr & PH_GLUE_MASK);
  if (tier_mode == 0ULL) { return !is_red; }
  if (tier_mode == 1ULL) { return is_red && glue <= h->tier1; }
  if (tier_mode == 2ULL) { return is_red && glue > h->tier1 && glue <= h->tier2; }
  return is_red && glue > h->tier2;
}

u64 full_viv_collect_m4(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = 0ULL;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_VIV)) == 0u) {
      if (full_viv_tier_match_m4(h, hdr, tier_mode) && bn < bmax) {
        rr[bn * 3ULL] = (u32)p;
        bn = bn + 1ULL;
      }
    }
    p = np;
  }
  return bn;
}

void full_viv_keys_m4(FullHdr *h, u64 bn) {
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *rr = (u32 *)h->red_refs;
  u64 nlits = h->cur_vars << 1;
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi * 3ULL];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k0 = 0xFFFFFFFFu; u32 d0 = 0u;
    u32 k1 = 0xFFFFFFFFu; u32 d1 = 0u;
    u32 j = 0u;
    while (j < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)j];
      u32 dl = ((u64)l < nlits) ? wvec[((u64)l << 1) + 1ULL] : 0u;
      if (k0 == 0xFFFFFFFFu || dl > d0 || (dl == d0 && l < k0)) {
        k1 = k0; d1 = d0; k0 = l; d0 = dl;
      } else if (k1 == 0xFFFFFFFFu || dl > d1 || (dl == d1 && l < k1)) {
        k1 = l; d1 = dl;
      }
      j = j + 1u;
    }
    rr[bi * 3ULL + 1ULL] = k0;
    rr[bi * 3ULL + 2ULL] = k1;
    bi = bi + 1ULL;
  }
}

void full_viv_clear_tier_m4(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u64 q = 0ULL;
  while (q < h->arena_len) {
    u32 hdr = ar[q];
    if ((hdr & (PH_GARB | PH_VIV)) == PH_VIV) {
      if (full_viv_tier_match_m4(h, hdr, tier_mode)) { ar[q] = hdr & (~PH_VIV); }
    }
    q = (u64)full_arena_next(h, (u32)q);
  }
}

u64 full_vivify_m4(FullHdr *h, u64 tier_mode, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 start_ticks = h->search_ticks;
  u64 delta = (start_ticks > h->fwd_sub_cnt) ? (start_ticks - h->fwd_sub_cnt) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 base_eff = eff_ref / 100ULL;
  u64 tick_cap = (tier_mode == 3ULL) ? base_eff : (base_eff * 3ULL);
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = full_viv_collect_m4(h, tier_mode);
  full_viv_keys_m4(h, bn);
  full_viv_sort_sched_m4(h, bn);
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         (h->search_ticks - start_ticks) < tick_cap) {
    u32 cr = rr[bi * 3ULL];
    budget = budget - 1ULL;
    u64 vc = full_viv_clause_m4(h, cr);
    if (vc == 20ULL) { res = 20ULL; break; }
    if (vc == 2ULL) { break; }
    if (h->cur_level == 0ULL && full_propagate(h) == 1ULL) { res = 20ULL; break; }
    bi = bi + 1ULL;
  }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (res == 1ULL && bi >= bn && bn < bmax) {
    full_viv_clear_tier_m4(h, tier_mode);
  }
  h->probing = 0ULL;
  return res;
}

u32 full_bce_side_m4(FullHdr *h, u32 blk_lit, u32 cand_off, u32 cand_n,
                     u32 opp_off, u32 opp_n) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 i = 0u;
  u32 rem = 0u;
  while (i < cand_n) {
    u32 w = scr[(u64)cand_off + (u64)i];
    bool deleted = false;
    if (full_bve_try_bce(h, blk_lit, w, opp_off, opp_n)) {
      if ((w & PW_BIN_FLAG) != 0u) {
        if (full_extend_push2(h, blk_lit, w & PW_LIT_MASK)) {
          full_delete_binary(h, blk_lit, w & PW_LIT_MASK);
          h->bce_cnt = h->bce_cnt + 1ULL;
          deleted = true;
        }
      } else {
        u32 *ar = (u32 *)h->arena;
        if ((ar[(u64)w] & PH_GARB) != 0u) {
          deleted = true;
        } else if (full_extend_push_cl(h, blk_lit, w)) {
          ar[(u64)w] = ar[(u64)w] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
          h->bce_cnt = h->bce_cnt + 1ULL;
          deleted = true;
        }
      }
    }
    if (!deleted) {
      scr[(u64)cand_off + (u64)rem] = w;
      rem = rem + 1u;
    }
    i = i + 1u;
  }
  return rem;
}

void full_bce_pair_m4(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 rem_p = full_bce_side_m4(h, pl, 0u, np, 64u, nn);
  full_bce_side_m4(h, nl, 64u, nn, 0u, rem_p);
}

void full_bce_var_m4(FullHdr *h, u32 v) {
  if (h->scratch_cap < 128ULL) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect(h, pl, scr, 64u);
  u32 nn = full_bve_collect(h, nl, scr + 64, 64u);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return; }
  full_bce_pair_m4(h, v, np, nn);
}

u64 full_bce_m4(FullHdr *h, u64 budget) {
  if (budget == 0ULL || h->scratch_cap < 128ULL) { return 1ULL; }
  if (!full_enter_dense(h)) {
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  u64 done = 0ULL;
  while (v < cv && done < budget && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      done = done + 1ULL;
      full_bce_var_m4(h, (u32)v);
    }
    v = v + 1ULL;
  }
  u64 rr = full_rebuild_watches(h);
  if (rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  return 1ULL;
}
"

/-- Canonical external callee signatures referenced by `m4VivBce_fns` (`15` externs). -/
def m4VivBceExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_viv_simplify", [i64, i32], [i64]⟩
  , ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32]⟩
  , ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32]⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool]⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩ ]

/-- Standalone M4f module (`16` new functions + `15` canonical externs, `0` exits). -/
def m4VivBceModule : LeanQbe.T.Module :=
  { fns := m4VivBce_fns, externs := m4VivBceExterns, exits := [] }

theorem full_viv_sort_noccs_m4_wf : Func.Wf full_viv_sort_noccs_m4_body := by t_wf_reify
theorem full_viv_has_l0_m4_wf : Func.Wf full_viv_has_l0_m4_body := by t_wf_reify
theorem full_viv_l0_simp_m4_wf : Func.Wf full_viv_l0_simp_m4_body := by t_wf_reify
theorem full_viv_reuse_prefix_m4_wf : Func.Wf full_viv_reuse_prefix_m4_body := by t_wf_reify
theorem full_viv_finish_m4_wf : Func.Wf full_viv_finish_m4_body := by t_wf_reify
theorem full_viv_clause_m4_wf : Func.Wf full_viv_clause_m4_body := by t_wf_reify
theorem full_viv_sort_sched_m4_wf : Func.Wf full_viv_sort_sched_m4_body := by t_wf_reify
theorem full_viv_tier_match_m4_wf : Func.Wf full_viv_tier_match_m4_body := by t_wf_reify
theorem full_viv_collect_m4_wf : Func.Wf full_viv_collect_m4_body := by t_wf_reify
theorem full_viv_keys_m4_wf : Func.Wf full_viv_keys_m4_body := by t_wf_reify
theorem full_viv_clear_tier_m4_wf : Func.Wf full_viv_clear_tier_m4_body := by t_wf_reify
theorem full_vivify_m4_wf : Func.Wf full_vivify_m4_body := by t_wf_reify
theorem full_bce_side_m4_wf : Func.Wf full_bce_side_m4_body := by t_wf_reify
theorem full_bce_pair_m4_wf : Func.Wf full_bce_pair_m4_body := by t_wf_reify
theorem full_bce_var_m4_wf : Func.Wf full_bce_var_m4_body := by t_wf_reify
theorem full_bce_m4_wf : Func.Wf full_bce_m4_body := by t_wf_reify

theorem m4VivBce_fns_wf : ∀ f ∈ m4VivBce_fns, f.Wf := by
  simp only [m4VivBce_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_viv_sort_noccs_m4_wf, full_viv_has_l0_m4_wf, full_viv_l0_simp_m4_wf,
    full_viv_reuse_prefix_m4_wf, full_viv_finish_m4_wf, full_viv_clause_m4_wf,
    full_viv_sort_sched_m4_wf, full_viv_tier_match_m4_wf, full_viv_collect_m4_wf,
    full_viv_keys_m4_wf, full_viv_clear_tier_m4_wf, full_vivify_m4_wf, full_bce_side_m4_wf,
    full_bce_pair_m4_wf, full_bce_var_m4_wf, full_bce_m4_wf⟩

theorem m4VivBce_acyclic : m4VivBceModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM4VivBce

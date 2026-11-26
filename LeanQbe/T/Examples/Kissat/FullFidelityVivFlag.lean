/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Examples.Kissat.Dimacs

/-!
# Kissat Step-11 `S11-8` Upstream `c->vivify` Flag Semantics (`FullFidelityVivFlag`)

Purely additive C0 layer (`0` edits to Step-10 modules, `0` new memory) aligning `PH_VIV` with
upstream Kissat 4.0.4 `vivify.c:231-316, 1303-1311`:
1. **`full_viv_collect_fid`:** Pushes `PH_VIV == 0` first, then `PH_VIV != 0` last; if `0`
   prioritized clauses were pushed, sets `ar[rr[k]] |= PH_VIV` on all `0 <= k < bn`.
2. **`full_viv_sort2_fid` & `full_viv_sort_fid`:** Sort `PH_VIV != 0` ahead of `PH_VIV == 0`
   (`if (pv0 && !v0) { break; }`) for the forward `do_sort` consumer scan `rr[bi]`.
3. **`full_viv_clause_m6`:** Clears `ar[cref] &= (~PH_VIV)` after trying a candidate when
   `fr != 2ULL && fr != 20ULL && (ar[cref] & PH_GARB) == 0u`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivFlag

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fid11VivFlag "
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

#define PH_GARB               0x00080000u
#define PH_VIV                0x00100000u

extern u32  full_arena_next(FullHdr *h, u32 cref);
extern bool full_viv_tier_match_m6(FullHdr *h, u32 hdr, u64 tier_mode);
extern void full_viv_sort2_fid(FullHdr *h, u64 bn, u64 mode);
extern u64  full_viv_l0_simp_m6(FullHdr *h, u32 cref, u32 sz);
extern void full_viv_sort_counts_m6(FullHdr *h, u32 sz);
extern void full_viv_reuse_prefix_m6(FullHdr *h, u32 cref, u32 sz);
extern u32  full_viv_best_implied_m6(FullHdr *h, u32 sz);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern u64  full_propagate_ignore(FullHdr *h, u64 ignore_ref);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64  full_viv_finish_m6(FullHdr *h, u32 cref, u32 sz,
                               bool confl, u32 implied, bool all_done);

u64 fid11_viv_collect_fid(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = 0ULL;
  bool any_prio = false;
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
          if (pass != 0ULL) { any_prio = true; }
        }
      }
      p = np;
    }
    pass = pass + 1ULL;
  }
  if (!any_prio) {
    u64 k = 0ULL;
    while (k < bn) {
      u32 cref = rr[k];
      ar[cref] = ar[cref] | PH_VIV;
      k = k + 1ULL;
    }
  }
  return bn;
}

void fid11_viv_sort2_fid(FullHdr *h, u64 bn, u64 mode) {
  if (bn <= 1ULL) { return; }
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
  u64 bn3 = bn / 3ULL;
  u64 gap = 1ULL;
  while (gap < bn3) {
    gap = gap * 3ULL + 1ULL;
  }
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
        if (pv0 && !v0) { break; }
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
    gap = gap / 3ULL;
  }
}

void fid11_viv_sort_fid(FullHdr *h, u64 bn) {
  if (bn <= 1ULL) { return; }
  u64 rcap = h->red_cap;
  u64 scap = h->scratch_cap;
  if (bn <= rcap / 3ULL) { full_viv_sort2_fid(h, bn, 1ULL); return; }
  if (bn <= (scap >> 1)) { full_viv_sort2_fid(h, bn, 2ULL); return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  if (bn > (rcap >> 1) && bn > scap) {
    u64 lo = 0ULL;
    u64 hi = bn - 1ULL;
    while (lo < hi) {
      u32 lcr = rr[lo];
      if ((ar[lcr] & PH_VIV) != 0u) {
        lo = lo + 1ULL;
      } else {
        u32 hcr = rr[hi];
        if ((ar[hcr] & PH_VIV) == 0u) {
          hi = hi - 1ULL;
        } else {
          rr[lo] = hcr; rr[hi] = lcr;
          lo = lo + 1ULL;
          hi = hi - 1ULL;
        }
      }
    }
    return;
  }
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 nlits = h->cur_vars << 1;
  u32 *keys1 = (bn <= (rcap >> 1)) ? (rr + bn) : ((u32 *)h->scratch_buf);
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
  u64 bn3 = bn / 3ULL;
  u64 gap = 1ULL;
  while (gap < bn3) {
    gap = gap * 3ULL + 1ULL;
  }
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
        if (pv0 && !v0) { break; }
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
    gap = gap / 3ULL;
  }
}

u64 fid11_viv_clause_m6(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((ar[cref] & PH_GARB) != 0u) { return 1ULL; }
  u32 sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u64 l0r = full_viv_l0_simp_m6(h, cref, sz);
  if (l0r != 0ULL) { return l0r; }
  sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u;
  while (i < sz) { tmp[i] = ar[(u64)cref + 3ULL + (u64)i]; i = i + 1u; }
  full_viv_sort_counts_m6(h, sz);
  full_viv_reuse_prefix_m6(h, cref, sz);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  bool confl = false; u32 implied = 0xFFFFFFFFu;
  i = 0u;
  while (i < sz) {
    u32 lit = tmp[i]; i8 lv = vals[lit];
    if (lv > (i8)0) { implied = full_viv_best_implied_m6(h, sz); break; }
    if (lv == (i8)0) {
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { break; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
      full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
      u64 pr = full_propagate_ignore(h, (u64)cref);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) { confl = true; break; }
      u32 bi = full_viv_best_implied_m6(h, sz);
      if (bi != 0xFFFFFFFFu) { implied = bi; break; }
    }
    i = i + 1u;
  }
  u64 fr = full_viv_finish_m6(h, cref, sz, confl, implied, i == sz);
  if (fr != 2ULL && fr != 20ULL && (ar[cref] & PH_GARB) == 0u) {
    ar[cref] = ar[cref] & (~PH_VIV);
  }
  return fr;
}
"

/-- Replacement `Fn` for `"full_viv_collect_fid"`. -/
def fid11VivCollectFidFn : Fn :=
  ⟨"full_viv_collect_fid", [i64, i64], [i64], fid11_viv_collect_fid_body⟩

/-- Replacement `Fn` for `"full_viv_sort2_fid"`. -/
def fid11VivSort2FidFn : Fn :=
  ⟨"full_viv_sort2_fid", [i64, i64, i64], [], fid11_viv_sort2_fid_body⟩

/-- Replacement `Fn` for `"full_viv_sort_fid"`. -/
def fid11VivSortFidFn : Fn :=
  ⟨"full_viv_sort_fid", [i64, i64], [], fid11_viv_sort_fid_body⟩

/-- Replacement `Fn` for `"full_viv_clause_m6"`. -/
def fid11VivClauseM6Fn : Fn :=
  ⟨"full_viv_clause_m6", [i64, i32], [i64], fid11_viv_clause_m6_body⟩

/-- `S11-8` replacement functions (`4` fns). -/
def fid11VivFlagRepls : List Fn :=
  [ fid11VivCollectFidFn
  , fid11VivSort2FidFn
  , fid11VivSortFidFn
  , fid11VivClauseM6Fn ]

end

public section

theorem fid11_viv_collect_fid_wf : Func.Wf fid11VivCollectFidFn.body := by
  t_wf_reify

theorem fid11_viv_sort2_fid_wf : Func.Wf fid11VivSort2FidFn.body := by
  t_wf_reify

theorem fid11_viv_sort_fid_wf : Func.Wf fid11VivSortFidFn.body := by
  t_wf_reify

theorem fid11_viv_clause_m6_wf : Func.Wf fid11VivClauseM6Fn.body := by
  t_wf_reify

theorem fid11VivFlagRepls_wf : ∀ f ∈ fid11VivFlagRepls, f.Wf := by
  intro f hf
  simp only [fid11VivFlagRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact fid11_viv_collect_fid_wf
  · exact fid11_viv_sort2_fid_wf
  · exact fid11_viv_sort_fid_wf
  · exact fid11_viv_clause_m6_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityVivFlag

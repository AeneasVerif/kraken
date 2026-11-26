/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 10 Audit Defect Closures (`FullFidelityStep10`)

Purely additive C0 layer (`5` replacements + `1` inserted helper = `505` fns, `0` externs,
`0` exits, every function `<= 6` args for SysV x64 & Arm64 ABI) atop Step 9 `fidStep9Module`
(`504` fns), closing all 4 confirmed findings from the 116-function cyber audit plus clean
`unflushed` reset on dense-to-sparse watch rebuild:
1. **`[P1]` Unsorted Vivification Priority Inversion (`full_vivify_tier_m6_hdr`):** Iterate forward
   `rr[bi]` for both sorted and unsorted paths so fresh untried clauses (`rr[0..K-1]`) always run
   before already-vivified clauses (`rr[K..bn-1]`). *(Audited `full_vivify_m6_hdr` `h->probing = 0`
   on `sum == 0`: intentional under C0's per-substage `probing` convention & `m6aVivifySpec`.)*
2. **`[P1]` Emergency `full_reduce(h, true)` Tier Reset (`full_learn_clause_m6` +
   `full_analyze_core_m6`):** Route `full_analyze_core_m6` to `full_learn_clause_m6`, whose
   emergency reduction calls `full_reduce_m6(h, true)` so `M6HdrExt` tiers (`used_0/used_1`),
   `full_log10_q16_m7`, and `M6_WM_REDUCE_{CONFL,TICKS}` watermarks are preserved.
3. **`[P1]` Uncertified 1-Sided Core Gate Flag Leak (`full_bve_def_k6_fid`):** Check the `bool`
   return value of `full_bve_certify_unit_fid(...)`; when `false`, clear `scr[M8_GF_IDX] = 0u`
   and `scr[M8_RG_IDX] = 0u` so `full_bve_var_m7` never runs with an uncertified 1-sided mask.
4. **`[P2]` All-Falsified Vacuous Match (`full_cong_has_clause_k`):** Track `matched_cnt` across
   marked unassigned literals and require `ok && matched_cnt >= k` so all-root-falsified clauses
   cannot vacuously match.
5. **Rebuild `unflushed` Hygiene (`full_rebuild_watches_nosort_fid`):** Clear `h->unflushed = 0ULL`
   after `full_arena_sweep(h)` returns `0ULL` (before `full_propagate(h)`) so pre-sweep root units
   do not force redundant level-0 backtracks in subsequent `full_reduce_m6` calls.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep10

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep10 "
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
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define M8_NEG_OFF            2001u
#define M8_POS_MASK           4002u
#define M8_NEG_MASK           4066u
#define M8_GF_IDX             4130u
#define M8_RG_IDX             4131u
#define FID_K6_TICK_P1        1000000u
#define FID_K6_TICK_P2        10000000u

extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_det_new_level(FullHdr *h, u64 jump);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern void full_eager_subsume(FullHdr *h, u64 new_ref);
extern u64 full_one_lit_confl(FullHdr *h);
extern u64 full_ana_failed_lit_m6_hdr(FullHdr *h);
extern u64 full_deduce_1uip_m6_hdr(FullHdr *h);
extern void full_restore_bump_ana_m6_hdr(FullHdr *h);
extern void full_min_shrink_m6(FullHdr *h);
extern void full_tick_rel(FullHdr *h);
extern void full_ema_update(FullHdr *h, u64 glue);
extern u64 full_viv_collect_fid(FullHdr *h, u64 tier_mode);
extern void full_viv_count_fid(FullHdr *h, u64 bn);
extern void full_viv_sort_fid(FullHdr *h, u64 bn);
extern u64 full_viv_clause_m6(FullHdr *h, u32 cr);
extern u64 full_propagate(FullHdr *h);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_bve_k6_mv_fid(u64 cap);
extern bool full_k6_extract_and_solve_fid(
    FullHdr *h, u32 v, u32 np, u32 nn, bool core_only, u32 tick_lim);
extern bool full_bve_certify_unit_fid(
    FullHdr *h, u32 v, u32 unit, u32 side_off, u32 side_cnt, u32 side_mask);

u64 full_learn_clause_m6(FullHdr *h, u64 glue) {
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
  u64 tlen = h->tmp_len;
  if (tlen > 2ULL) {
    u64 lo = 1ULL;
    u64 hi = tlen - 1ULL;
    while (lo < hi) {
      u32 sw = tmp[lo]; tmp[lo] = tmp[hi]; tmp[hi] = sw;
      lo = lo + 1ULL;
      hi = hi - 1ULL;
    }
    u64 rb = 1ULL;
    while (rb < tlen) {
      u32 rl = lvl[((u64)tmp[rb]) >> 1];
      u64 re = rb + 1ULL;
      while (re < tlen && lvl[((u64)tmp[re]) >> 1] == rl) {
        re = re + 1ULL;
      }
      u64 rl_i = rb;
      u64 rh_i = re - 1ULL;
      while (rl_i < rh_i) {
        u32 sw = tmp[rl_i]; tmp[rl_i] = tmp[rh_i]; tmp[rh_i] = sw;
        rl_i = rl_i + 1ULL;
        rh_i = rh_i - 1ULL;
      }
      rb = re;
    }
  }
  u64 i = 2ULL;
  while (i < tlen) {
    u32 x = tmp[i];
    u32 lx = lvl[((u64)x) >> 1];
    u64 j = i;
    while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] < lx) {
      tmp[j] = tmp[j - 1ULL];
      j = j - 1ULL;
    }
    tmp[j] = x;
    i = i + 1ULL;
  }
  u64 max_lvl = (u64)lvl[((u64)tmp[1]) >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce_m6(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}

u64 full_analyze_core_m6(FullHdr *h) {
  u32 *lvl = (u32 *)h->level; u32 *tmp = (u32 *)h->tmp_lits; u32 *ar = (u32 *)h->arena;
  u64 iter = 0ULL; u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) {
      if (h->probing == 0ULL) { h->conflicts = h->conflicts + 1ULL; }
      return 1ULL;
    }
    if (ol == 2ULL) { return 0ULL; }
    if (h->cur_level == 1ULL) { return full_ana_failed_lit_m6_hdr(h); }
    u64 dst = full_deduce_1uip_m6_hdr(h);
    if (dst == 20ULL) { return 20ULL; }
    if (dst == 0ULL) { return 0ULL; }
    if (dst == 2ULL) {
      h->conflicts = h->conflicts + 1ULL;
      if (h->probing == 0ULL) {
        if (h->cur_vars > 0ULL) {
          if (h->confl_type == 1ULL) { tmp[0] = (u32)h->confl_lit0; h->tmp_len = 1ULL; }
          else if (h->confl_type == 2ULL && h->confl_ref < h->arena_len &&
                   3ULL < h->arena_len - h->confl_ref) {
            tmp[0] = ar[h->confl_ref + 3ULL]; h->tmp_len = 1ULL;
          }
        }
        full_restore_bump_ana_m6_hdr(h);
      }
      continue;
    }
    full_min_shrink_m6(h);
    if (h->probing == 0ULL) { full_restore_bump_ana_m6_hdr(h); full_tick_rel(h); }
    u64 glue = 0ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    if (h->probing == 0ULL) { full_ema_update(h, glue); }
    return full_learn_clause_m6(h, glue);
  }
  return 0ULL;
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = full_viv_collect_fid(h, tier_mode);
  bool do_sort = (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant);
  if (do_sort) {
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

u64 full_rebuild_watches_nosort_fid(FullHdr *h) {
  h->dense_mode = 0ULL;
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (sr == 0ULL) { h->unflushed = 0ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    if (sr == 0ULL) { break; }
  }
  return 1ULL;
}

bool full_cong_has_clause_k(FullHdr *h, u32 k) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *lm = (u8 *)h->lit_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 nlits = h->cur_vars << 1;
  if (k < 3u || k > 5u || (u64)k > h->cur_vars) { return false; }
  u32 min_l = tmp[0]; u32 min_d = wvec[((u64)min_l << 1) + 1ULL];
  u32 i = 0u;
  while (i < k) {
    u32 tl = tmp[i];
    lm[tl] = (u8)(i + 1u);
    u32 d = wvec[((u64)tl << 1) + 1ULL];
    if (d < min_d) { min_d = d; min_l = tl; }
    i = i + 1u;
  }
  bool res = false;
  u64 off = (u64)wvec[(u64)min_l << 1];
  u64 end = off + (u64)wvec[((u64)min_l << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        i8 ov = vals[ot];
        if (ov < (i8)0 || (ov == (i8)0 && lm[ot] != (u8)0)) { res = true; break; }
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u) { continue; }
    bool ok = true; u32 matched_cnt = 0u; u32 j = 0u;
    while (j < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)j];
      i8 cv = vals[cl];
      if (cv > (i8)0) { ok = false; break; }
      if (cv == (i8)0) {
        if (lm[cl] == (u8)0) { ok = false; break; }
        matched_cnt = matched_cnt + 1u;
      }
      j = j + 1u;
    }
    if (ok && matched_cnt >= k) { res = true; break; }
  }
  i = 0u;
  while (i < k) { lm[tmp[i]] = (u8)0; i = i + 1u; }
  return res;
}

void full_bve_def_k6_fid(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 mv = (u32)full_bve_k6_mv_fid(h->scratch_cap);
  if (mv == 0u || np == 0u || nn == 0u || np + nn > (mv << 1)) { return; }
  if (!full_k6_extract_and_solve_fid(h, v, np, nn, false, FID_K6_TICK_P1)) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  if (!full_k6_extract_and_solve_fid(h, v, np, nn, true, FID_K6_TICK_P2)) {
    scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    return;
  }
  bool has_pos = false; bool has_neg = false; u32 mi = 0u;
  while (mi < 64u) {
    if (scr[M8_POS_MASK + mi] != 0u) { has_pos = true; }
    if (scr[M8_NEG_MASK + mi] != 0u) { has_neg = true; }
    mi = mi + 1u;
  }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (!has_pos && has_neg) {
    if (!full_bve_certify_unit_fid(h, v, nl, M8_NEG_OFF, nn, M8_NEG_MASK)) {
      scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    }
  } else if (has_pos && !has_neg) {
    if (!full_bve_certify_unit_fid(h, v, pl, 0u, np, M8_POS_MASK)) {
      scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    }
  }
}
"

/-! ## 1. Canonical `Fn` Handles, Replacement / Insertion Lists & Module (`505` fns) -/

def fidStep10LearnClauseM6Fn : Fn :=
  ⟨"full_learn_clause_m6", [i64, i64], [i64], full_learn_clause_m6_body⟩

def fidStep10AnalyzeCoreM6Fn : Fn :=
  ⟨"full_analyze_core_m6", [i64], [i64], full_analyze_core_m6_body⟩

def fidStep10VivifyTierM6HdrFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_body⟩

def fidStep10RebuildWatchesNosortFn : Fn :=
  ⟨"full_rebuild_watches_nosort_fid", [i64], [i64], full_rebuild_watches_nosort_fid_body⟩

def fidStep10CongHasClauseKFn : Fn :=
  ⟨"full_cong_has_clause_k", [i64, i32], [.bool], full_cong_has_clause_k_body⟩

def fidStep10BveDefK6Fn : Fn :=
  ⟨"full_bve_def_k6_fid", [i64, i32, i32, i32], [], full_bve_def_k6_fid_body⟩

/-- Exact `5`-function Step-10 replacement list over `fidStep9Fns`. -/
def fidStep10Repls : List Fn :=
  [ fidStep10AnalyzeCoreM6Fn
  , fidStep10VivifyTierM6HdrFn
  , fidStep10RebuildWatchesNosortFn
  , fidStep10CongHasClauseKFn
  , fidStep10BveDefK6Fn ]

/-- Ordered helper insertion (`+1` helper `full_learn_clause_m6`, net `504 -> 505` functions). -/
def fidStep10Befores : List (Sym × List Fn) :=
  [ ("full_analyze_core_m6", [fidStep10LearnClauseM6Fn]) ]

/-- Ordered `505`-fn Step-10 `KissatFidelity` function list (`patchFns` over `fidStep9Fns`). -/
def fidStep10ModuleFns : List Fn :=
  patchFns fidStep10Repls fidStep10Befores fidStep9Fns

/-- Closed `505`-function Gate-1 Step-10 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep10Module : LeanQbe.T.Module :=
  { fidStep9Module with fns := fidStep10ModuleFns }

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Exit-Freedom -/

public section

theorem fidStep10ModuleFns_eq : fidStep10Module.fns = fidStep10ModuleFns :=
  rfl

theorem full_learn_clause_m6_step10_wf : Func.Wf fidStep10LearnClauseM6Fn.body := by t_wf_reify
theorem full_analyze_core_m6_step10_wf : Func.Wf fidStep10AnalyzeCoreM6Fn.body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_step10_wf :
    Func.Wf fidStep10VivifyTierM6HdrFn.body := by
  t_wf_reify
theorem full_rebuild_watches_nosort_step10_wf :
    Func.Wf fidStep10RebuildWatchesNosortFn.body := by
  t_wf_reify
theorem full_cong_has_clause_k_step10_wf : Func.Wf fidStep10CongHasClauseKFn.body := by t_wf_reify
theorem full_bve_def_k6_fid_step10_wf : Func.Wf fidStep10BveDefK6Fn.body := by t_wf_reify

theorem fidStep10Befores_wf : ∀ h ∈ fidStep10Befores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep10Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_singleton] at hh
  subst hh
  exact full_learn_clause_m6_step10_wf

theorem fidStep10Repls_wf : ∀ f ∈ fidStep10Repls, f.Wf := by
  intro f hf
  simp only [fidStep10Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_analyze_core_m6_step10_wf
  · exact full_vivify_tier_m6_hdr_step10_wf
  · exact full_rebuild_watches_nosort_step10_wf
  · exact full_cong_has_clause_k_step10_wf
  · exact full_bve_def_k6_fid_step10_wf

theorem fidStep10Module_wf : ∀ f ∈ fidStep10Module.fns, f.Wf :=
  patchFns_wf fidStep9Module_wf fidStep10Repls_wf fidStep10Befores_wf

theorem fidStep10_noExit : fidStep10Module.exits = [] :=
  fidStep9_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep10

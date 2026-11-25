/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullM7HotTernary
public import LeanQbe.T.Examples.Kissat.FullM7HotHop1
public import LeanQbe.T.Examples.Kissat.PatchModule
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM8CoreParity
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7HotTernary
import all LeanQbe.T.Examples.Kissat.FullM7HotHop1
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0
public meta import LeanQbe.T.Examples.Kissat.PatchModule
public meta import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public meta import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public meta import LeanQbe.T.Examples.Kissat.FullM7HotTernary
public meta import LeanQbe.T.Examples.Kissat.FullM7HotHop1

/-!
# Purified Upstream-Faithful `FullFidelityBase` Module Assembly (`KissatFidelity`)

Strictly additive assembly (`0` edits to existing `FullM6*`/`FullM7*`/`FullM8*` files) purifying
the `FullM8SweepV2` (`m8FidV123t2Module`) + `CoreParity` base to exact upstream Kissat 4.0.4
heuristics, plus wiring bit-identical `FullM7HotTernary` and `FullM7HotHop1` (`0` `XorGauss`, `0`
`Prelearn`, `0` `WaveACore`, `0` `SbvaTie`):
1. `full_bve_gates_fid`: omits `D-11` syntactic XOR matcher `full_bve_find_xor_m8` (`gates.c:44-55`
   order: equivalence -> AND -> ITE -> K6 definition).
2. `full_bve_var_m7_fid` & `full_bve_var_fid`: omits `D-22` opportunistic BCE
   `full_bve_bce_side_m8` on `!fit`, returning `1ULL` directly (`eliminate.c:385-414`).
3. `full_m6_sweep_vars_fid`: restores exact `1x` Kitten ticks `spent = (u64)k[K6H_TICKS]`
   (`sweep.c:1673`), dropping `D-19` `((ticks << 2) + 512ULL)`.
4. `full_vivify_tier_m6_hdr_fid`: exact `vivify.c:1269` candidate-sort guard
   `if (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant)` with zero Wave-A delay
   overrides.
5. `fidBaseModule` (`469` functions = `449` base + `3` Min helpers + `17` purified BVE helpers)
   via `PatchModule.splice_module!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBase

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7HotTernary
open LeanQbe.T.Examples.Kissat.FullM7HotHop1
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Purified Upstream-Faithful C0 Replacements -/

kissat_c0! fidBase "
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

#define FL_ACTIVE             1u
#define FL_ELIM               2u
#define FL_SWEEP              1024u

#define M8_OCC_LIM            2001u
#define M8_NEG_OFF            2001u
#define M8_POS_MASK           4002u
#define M8_NEG_MASK           4066u
#define M8_GF_IDX             4130u
#define M8_RG_IDX             4131u
#define M8_RES_OFF            4192u

#define K6H_TICKS             11u

extern bool full_bve_find_equiv_m8(FullHdr *h, u32 np, u32 nn);
extern bool full_bve_find_and_m8(FullHdr *h, u32 pl, u32 np, u32 nn);
extern bool full_bve_find_ite_m8(FullHdr *h, u32 v, u32 np, u32 nn);
extern void full_bve_def_k6_m8(FullHdr *h, u32 v, u32 np, u32 nn);

extern void full_wstack_defrag(FullHdr *h);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern u64 full_bve_var_m7(FullHdr *h, u32 v);

extern u64 full_m6_max_v(u64 cap);
extern bool full_m6_dense_prop(FullHdr *h);
extern u32 full_m6_collect_cands(FullHdr *h);
extern u64 full_m6_sweep_var(FullHdr *h, u32 v, u64 tick_lim);

extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_viv_collect_m6(FullHdr *h, u64 tier_mode);
extern void full_viv_count_m6(FullHdr *h, u64 bn);
extern void full_viv_keys_m6(FullHdr *h, u64 bn);
extern void full_viv_sort_sched_m6(FullHdr *h, u64 bn);
extern u64 full_viv_clause_m6(FullHdr *h, u32 cref);
extern u64 full_propagate(FullHdr *h);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);

void full_bve_gates_fid(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 130u) { scr[M8_POS_MASK + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m8(h, np, nn)) { return; }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (full_bve_find_and_m8(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m8(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m8(h, v, np, nn)) { return; }
  full_bve_def_k6_m8(h, v, np, nn);
}

u64 full_bve_var_m7_fid(FullHdr *h, u32 v) {
  if (h->scratch_cap < 2048ULL) { return 1ULL; }
  bool use_m8 = (h->scratch_cap >= 16384ULL);
  u32 occ_lim = use_m8 ? M8_OCC_LIM : 512u;
  u32 neg_off = use_m8 ? M8_NEG_OFF : 512u;
  u32 pos_mask = use_m8 ? M8_POS_MASK : 1024u;
  u32 neg_mask = use_m8 ? M8_NEG_MASK : 1040u;
  u32 gf_idx = use_m8 ? M8_GF_IDX : 1056u;
  u32 rg_idx = use_m8 ? M8_RG_IDX : 1057u;
  u64 r_off = use_m8 ? (u64)M8_RES_OFF : 1088ULL;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m7(h, pl, scr, occ_lim);
  u32 nn = full_bve_collect_m7(h, nl, scr + neg_off, occ_lim);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  u64 ext_need = full_bve_ext_need(h, 0u, np) + full_bve_ext_need(h, neg_off, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, neg_off, nn))) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    return 1ULL;
  }
  u64 rp = r_off;
  u64 r_cnt = 0ULL;
  u64 w_est = 0ULL;
  u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    if (use_m8) { full_bve_gates_fid(h, v, np, nn); }
    else { full_bve_gates_m7(h, v, np, nn); }
    bool gf = (scr[gf_idx] != 0u);
    bool rg = (scr[rg_idx] != 0u);
    u32 *wvec = (u32 *)h->watch_vec;
    u32 i = 0u;
    while (i < np && fit) {
      bool pi = ((scr[pos_mask + (i >> 5)] >> (i & 31u)) & 1u) != 0u;
      u32 j = 0u;
      while (j < nn && fit) {
        bool nj = ((scr[neg_mask + (j >> 5)] >> (j & 31u)) & 1u) != 0u;
        bool need_pair = !gf || (rg ? (pi || nj) : (pi != nj));
        if (need_pair && full_bve_resolve_pair(h, v, scr[i], scr[neg_off + j])) {
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
    if (!full_bve_weaken(h, pl, 0u, np) || !full_bve_weaken(h, nl, neg_off, nn)) {
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
  return 1ULL;
}

u64 full_bve_var_fid(FullHdr *h, u32 v) {
  return full_bve_var_m7(h, v);
}

u64 full_m6_sweep_vars_fid(FullHdr *h, u64 budget, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (!full_m6_dense_prop(h)) { return 20ULL; }
  u32 nc = full_m6_collect_cands(h);
  if (nc == 0u) { return 1ULL; }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 per_v = 16384ULL;
  u32 ci = 0u; u64 rem_b = budget;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci]; ci = ci + 1u;
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); rem_b = rem_b - 1ULL;
      u64 vlim = (rem_ticks > per_v) ? per_v : rem_ticks;
      if (full_m6_sweep_var(h, v, vlim) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
      u64 spent = (u64)k[K6H_TICKS];
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_vivify_tier_m6_hdr_fid(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = full_viv_collect_m6(h, tier_mode);
  if (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant) {
    full_viv_count_m6(h, bn);
    full_viv_keys_m6(h, bn);
    full_viv_sort_sched_m6(h, bn);
  }
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         h->search_ticks < tick_lim) {
    u32 cr = rr[bi * 3ULL];
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
  h->probing = 0ULL;
  return res;
}
"

/-! ## 2. Canonical `Fn` Handles, Purified Helper Lists, and `fidBaseModule` Splice -/

def fidBveGatesFn : Fn :=
  ⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], full_bve_gates_fid_body⟩

def fidBveVarM7Fn : Fn :=
  ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_fid_body⟩

def fidBveVarFn : Fn :=
  ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_fid_body⟩

def fidSweepVarsFn : Fn :=
  ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_fid_body⟩

def fidVivifyTierFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_fid_body⟩

/-- Purified `17`-function BVE helper list (`m8BveHelpers` without `full_bve_find_xor_m8` and
`full_bve_bce_side_m8`, replacing `full_bve_gates_m8` with `fidBveGatesFn`). -/
def fidBveHelpers : List Fn :=
  [ m8BveFindEquivFn, m8BveFindAndFn, m8BveMatchTernFn, m8BveFindIteSideFn
  , m8BveFindIteFn, m8K6WatchFn, m8K6AssignFn, m8K6MtfFn
  , m8K6BacktrackFn, m8K6PropFn, m8K6AnaClFn, m8K6AnalyzeFn, m8K6SolveFn
  , m8K6CoreFn, m8K6ExtractSolveFn, m8BveDefK6Fn, fidBveGatesFn ]

/-- Insertion pairs (`3` Min helpers + `17` purified BVE helpers = `20` helpers). -/
def fidBaseBefores : List (Sym × List Fn) :=
  [ ("full_min_shrink_m6", m8MinHelpers)
  , ("full_bve_var_m7", fidBveHelpers) ]

/-- Canonical `12` replacements over `m8FidV123t2Module` (`449` -> `469` functions). -/
def fidBaseRepls : List Fn :=
  [ m8MinShrinkM6Fn, fidBveVarM7Fn, fidBveVarFn, m8BveVarKeyM7Fn
  , m8ProbeDticksM6HdrFn, m8ProbeM6Fn, m8SearchM6Fn
  , fidSweepVarsFn, fidVivifyTierFn
  , m7HasTernaryFn, m7Hop1Fn, m7Hop2Fn ]

theorem full_bve_gates_fid_wf : Func.Wf full_bve_gates_fid_body := by t_wf_reify
theorem full_bve_var_m7_fid_wf : Func.Wf full_bve_var_m7_fid_body := by t_wf_reify
theorem full_bve_var_fid_wf : Func.Wf full_bve_var_fid_body := by t_wf_reify
theorem full_m6_sweep_vars_fid_wf : Func.Wf full_m6_sweep_vars_fid_body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_fid_wf : Func.Wf full_vivify_tier_m6_hdr_fid_body := by t_wf_reify

theorem fidBaseRepls_wf : ∀ r ∈ fidBaseRepls, r.Wf := by
  intro r hr
  simp only [fidBaseRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_min_shrink_m6_m8_wf
  · exact full_bve_var_m7_fid_wf
  · exact full_bve_var_fid_wf
  · exact full_bve_var_key_m7_m8_wf
  · exact full_probe_dticks_m6_hdr_m8_wf
  · exact full_probe_m6_m8_wf
  · exact full_search_m6_m8_wf
  · exact full_m6_sweep_vars_fid_wf
  · exact full_vivify_tier_m6_hdr_fid_wf
  · exact m7HasTernaryFn_wf
  · exact m7Hop1Fn_wf
  · exact m7Hop2Fn_wf

theorem fidBveHelpers_wf : ∀ h ∈ fidBveHelpers, h.Wf := by
  intro h hh
  simp only [fidBveHelpers, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · exact full_bve_find_equiv_m8_wf
  · exact full_bve_find_and_m8_wf
  · exact full_bve_match_tern_m8_wf
  · exact full_bve_find_ite_side_m8_wf
  · exact full_bve_find_ite_m8_wf
  · exact full_k6_watch_m8_wf
  · exact full_k6_assign_m8_wf
  · exact full_k6_mtf_m8_wf
  · exact full_k6_backtrack_m8_wf
  · exact full_k6_prop_m8_wf
  · exact full_k6_ana_cl_m8_wf
  · exact full_k6_analyze_m8_wf
  · exact full_k6_solve_m8_wf
  · exact full_k6_core_m8_wf
  · exact full_k6_extract_and_solve_m8_wf
  · exact full_bve_def_k6_m8_wf
  · exact full_bve_gates_fid_wf

theorem fidBaseBefores_wf : ∀ h ∈ fidBaseBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  rw [List.mem_flatMap] at hh
  rcases hh with ⟨p, hp, hmem⟩
  simp only [fidBaseBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact m8CoreParityBefores_wf ("full_min_shrink_m6", m8MinHelpers)
      (by simp [m8CoreParityBefores]) h hmem
  · exact fidBveHelpers_wf h hmem

private theorem m8FidV123t2Fns_wf_local : ∀ f ∈ m8FidV123t2Fns, f.Wf := by
  have hm8V12Wf : ∀ f ∈ m8FidV12Fns, f.Wf := by
    intro f hf
    dsimp only [m8FidV12Fns, FullM7Splice.spliceFns] at hf
    rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
    cases hfind : m8FidV12Repls.find? (·.name == g.name) with
    | none => exact m7FidelityFns_wf g hg
    | some r => exact m8FidV12Repls_wf r (List.mem_of_find?_eq_some hfind)
  have hSwB_wf : ∀ p ∈ m8FidV123t2Befores, ∀ h ∈ p.2, h.Wf := by
    intro p hp h hh
    simp only [m8FidV123t2Befores, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact m8SweepV2Helpers_wf h hh
  exact FullM7Splice.patchFns_wf hm8V12Wf m8SweepV2Repls_wf hSwB_wf

/-- Canonical `469`-function purified `KissatFidelity` base function list. -/
def fidBaseFns : List Fn :=
  PatchModule.patchFns fidBaseRepls fidBaseBefores m8FidV123t2Fns

/-- Canonical `469`-function purified `KissatFidelity` base module (`0` externs, `0` exits). -/
def fidBaseModule : LeanQbe.T.Module :=
  PatchModule.patchModule m8FidV123t2Module fidBaseRepls fidBaseBefores

theorem fidBaseFns_wf : ∀ f ∈ fidBaseFns, f.Wf :=
  PatchModule.patchFns_wf m8FidV123t2Fns_wf_local fidBaseRepls_wf fidBaseBefores_wf

theorem fidBase_noExit : fidBaseModule.exits = [] := FullM8SweepV2.m8FidV123t2_noExit

/-- The `5` newly authored purified C0 functions in `FullFidelityBase`. -/
def fidBaseNewFns : List Fn :=
  [ fidBveGatesFn, fidBveVarM7Fn, fidBveVarFn, fidSweepVarsFn, fidVivifyTierFn ]

/-! ## 3. Standalone Legalization & Multi-ISA Executable Verification -/

#guard fidBaseFns.length == 469
#guard (fidBaseFns.map Fn.name).eraseDups.length == 469
#guard fidBaseModule.checkAcyclic
#guard !(fidBaseFns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidBaseFns.map Fn.name).contains "full_bve_bce_side_m8"
#guard (fidBaseFns.map Fn.name).contains "full_bve_gates_fid"
#guard (fidBaseFns.map Fn.name).contains "full_has_ternary"
#guard (fidBaseFns.map Fn.name).contains "full_bva_hop1"
#guard (fidBaseFns.map Fn.name).contains "full_bva_hop2"

#guard (PrintCpp.ppModule (fidBaseNewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidBaseNewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidBaseNewFns.map (Fn.legal .x64AVX512))).isOk
#guard (PrintCpp.ppModule (fidBaseNewFns.map (Fn.legal .x64AVX2))).isOk

#guard fidBaseNewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidBaseNewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidBaseNewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard fidBaseNewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbe.T.Examples.Kissat.FullFidelityBase

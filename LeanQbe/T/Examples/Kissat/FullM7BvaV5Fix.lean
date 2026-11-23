module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M7 Purely Additive `V5_BVA` Parity + `P1-3` Fixes (`FullM7BvaV5Fix`)

Strictly additive drop-in C0 replacements over unchanged `FullHdr` implementing the `V5_BVA`
parity and `P1-3` fixes without modifying `Full1.lean`, `FullM6Orch.lean`, `FullM7.lean`, or
`FullM7BveGates.lean`:

1. `full_calc_max_v_m7v5`: raises `bva_cap` candidate from `(mv >> 1) + 16ULL` to `4096ULL`
   (bounded by remaining `max_bva` work memory per `Full1.lean:758-771`).
2. `full_probe_m7v5`: exact `FullM6Orch.full_probe_m6` logic with `(initial || h->num_irred <=
   4096ULL || h->eliminations > 0ULL) && full_enter_dense(h)` and `fbud = full_min_u64(initial ?
   (h->cur_vars * 4ULL + 1024ULL) : (128ULL + (dticks >> 8)), 8192ULL)` (unchanged `ilog10`).
3. `full_forward_sub_m7v5`: `P1-3` — runs `FL_SUBSUME` cleanup/re-arming on `rr[i..ncand)` and
   `PH_SUBSUME` arena flags even when `i < ncand` exits early on budget.
4. `full_eliminate_m7v5`: fixes `NLOG2N` (`500ULL * h->eliminations * loge * loge`) while keeping
   `h->elim_bound` save/zero/restore around `full_factor` (`V_win_optimal`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7BvaV5Fix "
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

#define PH_GARB             0x00080000u
#define PH_SUBSUME          0x01000000u
#define FL_SUBSUME          8u
#define FL_ELIM_C           16u

#define M6_DELAY_CONGRUENCE 1ULL
#define M6_DELAY_SWEEP      2ULL
#define M6_WM_PROBE_TICKS   0ULL

extern u64 full_fixed_bytes(u64 mv);

extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_ilog10(u64 x);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern bool full_enter_dense(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_rebuild_watches(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern u64 full_probe_tail_m6(FullHdr *h, u64 dticks);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_factor(FullHdr *h, u64 budget);

extern bool full_fwd_dedup_bins(FullHdr *h);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u64 full_fwd_collect_sort_m7(FullHdr *h);
extern void full_fwd_flush_large_m7(FullHdr *h);
extern bool full_fwd_check_cl_m7(FullHdr *h, u32 cref);
extern void full_fwd_connect_subsumer_m7(FullHdr *h, u32 cref);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_fwd_reconnect_irred_m7(FullHdr *h);

extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_elim_bve_m7(FullHdr *h, u64 bve_lim);

u64 full_calc_max_v_m7v5(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = 4096ULL;
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 fixed = full_fixed_bytes(max_v);
  if (avail < fixed || avail - fixed < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_probe_m7v5(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 logp = full_ilog10(h->probings + 9ULL);
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, 100ULL * h->probings * logp);
  }
  u64 round = 0ULL;
  while (round < 2ULL) {
    u64 before_unass = h->unassigned;
    if (full_enter_dense(h)) {
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if ((h->cong_cnt > cb) && (h->cong_cnt - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
      }
      if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
        u64 sb = h->sweep_cnt;
        if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if ((h->sweep_cnt > sb) && (h->sweep_cnt - sb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
        }
      }
      if (full_rebuild_watches(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    } else if (h->inconsistent != 0ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->unassigned >= before_unass) { break; }
    round = round + 1ULL;
  }
  if (!initial) {
    if (full_probe_tail_m6(h, dticks) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, dticks * 4ULL + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  }
  if ((initial || h->num_irred <= 4096ULL || h->eliminations > 0ULL) &&
      full_enter_dense(h)) {
    u64 fbud = full_min_u64(
      initial ? (h->cur_vars * 4ULL + 1024ULL) : (128ULL + (dticks >> 8)),
      8192ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}

u64 full_forward_sub_m7v5(FullHdr *h, u64 budget) {
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
  if (h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 *fl = (u32 *)h->flags;
    u64 cv = h->cur_vars;
    u64 v = 0ULL;
    while (v < cv) { fl[v] = fl[v] & (~FL_SUBSUME); v = v + 1ULL; }
    u64 ri = i;
    while (ri < ncand) {
      u32 rcr = rr[ri];
      u32 rhdr = ar[rcr];
      if ((rhdr & PH_GARB) == 0u) {
        u32 rsz = ar[(u64)rcr + 2ULL];
        u32 rk = 0u;
        while (rk < rsz) {
          u32 rlv = ar[(u64)rcr + 3ULL + (u64)rk] >> 1;
          if ((u64)rlv < cv) { fl[rlv] = fl[rlv] | FL_SUBSUME; }
          rk = rk + 1u;
        }
      }
      ri = ri + 1ULL;
    }
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

u64 full_eliminate_m7v5(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge0 = full_ilog10(h->eliminations + 9ULL);
    u64 loge = (loge0 > 1ULL) ? (loge0 - 1ULL) : 1ULL;
    u64 delta = full_scale_delta(h, 500ULL * h->eliminations * loge * loge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub_m7v5(h, fbud);
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

/-- External callee signatures referenced by `m7BvaV5Fix_fns`. -/
def m7BvaV5FixExterns : List Extern :=
  [ ⟨"full_fixed_bytes", [i64], [i64]⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64]⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], []⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], []⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64]⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool]⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool]⟩
  , ⟨"full_fwd_collect_sort_m7", [i64], [i64]⟩
  , ⟨"full_fwd_flush_large_m7", [i64], []⟩
  , ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool]⟩
  , ⟨"full_fwd_connect_subsumer_m7", [i64, i32], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_fwd_reconnect_irred_m7", [i64], []⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64]⟩ ]

/-- Standalone M7 `V5_BVA` + `P1-3` fix module (`4` functions + `28` externs, `0` exits). -/
def m7BvaV5FixModule : LeanQbe.T.Module :=
  { fns := m7BvaV5Fix_fns, externs := m7BvaV5FixExterns, exits := [] }

/-- Drop-in renamed `Fn` handles matching canonical `Full1` / `FullM6Orch` / `FullM7` slots. -/
def m7v5CalcMaxVFn : Fn :=
  ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], full_calc_max_v_m7v5_body⟩
def m7v5ProbeFn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m7v5_body⟩
def m7v5ForwardSubFn : Fn :=
  ⟨"full_forward_sub", [i64, i64], [i64], full_forward_sub_m7v5_body⟩
def m7v5EliminateFn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m7v5_body⟩

theorem full_calc_max_v_m7v5_wf : Func.Wf full_calc_max_v_m7v5_body := by t_wf_reify
theorem full_probe_m7v5_wf : Func.Wf full_probe_m7v5_body := by t_wf_reify
theorem full_forward_sub_m7v5_wf : Func.Wf full_forward_sub_m7v5_body := by t_wf_reify
theorem full_eliminate_m7v5_wf : Func.Wf full_eliminate_m7v5_body := by t_wf_reify

theorem m7BvaV5Fix_fns_wf : ∀ f ∈ m7BvaV5Fix_fns, f.Wf := by
  simp only [m7BvaV5Fix_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_calc_max_v_m7v5_wf, full_probe_m7v5_wf,
    full_forward_sub_m7v5_wf, full_eliminate_m7v5_wf⟩

theorem m7BvaV5Fix_acyclic : m7BvaV5FixModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix

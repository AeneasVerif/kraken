module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M7 Parity BVA Tie-Break + `bb20` Overrides (`FullM7ParityBvaTie`)

Purely additive drop-in C0 overrides over unchanged `FullHdr` for Target B (`FullM7Plus`),
preserving exact `m7SpecTable` specifications with zero spec edits:

1. `full_bva_pick_cand_bt`: clones `FullM6BvaNoHops.full_bva_pick_cand_no_hops` with the 1-line
   canonical symmetry-preserving tie-break `|| (deg == best_deg && clit < best_lit)`.
2. `full_probe_tail_bt`: clones `FullM6Orch.full_probe_tail_m6` with `backboneeffort = 20` per
   mille (`(dticks / 50ULL) + 65536ULL` instead of `dticks * 4ULL + 65536ULL`).
3. `full_probe_bt`: adapts `FullM7BvaV5Fix.full_probe_m7v5` with `(dticks / 50ULL) + 65536ULL`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7ParityBvaTie "
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

#define M6_DELAY_CONGRUENCE 1ULL
#define M6_DELAY_SWEEP      2ULL
#define M6_WM_PROBE_TICKS   0ULL

extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_vivify_m6_hdr(FullHdr *h);

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
extern u64 full_factor(FullHdr *h, u64 budget);

u32 full_bva_pick_cand_bt(FullHdr *h, u32 ncntd, u32 f0) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *cnt = (u32 *)h->wsort;
  u32 *cntd = (u32 *)h->work_stk1;
  u32 best_c = 0u;
  u32 best_deg = 0u;
  u32 best_lit = 0xFFFFFFFFu;
  u32 ci = 0u;
  while (ci < ncntd) {
    u32 clit = cntd[ci];
    u32 cc = cnt[clit];
    if (cc >= 2u) {
      if (cc > best_c) {
        best_c = cc;
        best_deg = wvec[((u64)clit << 1) + 1ULL];
        best_lit = clit;
      } else if (cc == best_c) {
        u32 deg = wvec[((u64)clit << 1) + 1ULL];
        if (deg > best_deg || (deg == best_deg && clit < best_lit)) {
          best_deg = deg;
          best_lit = clit;
        }
      }
    }
    ci = ci + 1u;
  }
  ci = 0u;
  while (ci < ncntd) {
    cnt[cntd[ci]] = 0u;
    ci = ci + 1u;
  }
  return (best_c < 2u) ? 0xFFFFFFFFu : best_lit;
}

u64 full_probe_tail_bt(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL &&
      full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
    return 20ULL;
  }
  u64 tr_lim = (dticks / 50ULL) + 100000ULL;
  if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) { return 20ULL; }
  u64 pbud = full_min_u64(8ULL + (dticks >> 10), 64ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  if (full_vivify_m6_hdr(h) == 20ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_bt(FullHdr *h, bool initial) {
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
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
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
"

/-- External callee signatures referenced by `m7ParityBvaTie_fns` (`19` externs). -/
def m7ParityBvaTieExterns : List Extern :=
  [ ⟨"full_backbone_m6", [i64, i64], [i64]⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_probe_run", [i64, i64], [i64]⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64]⟩
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
  , ⟨"full_factor", [i64, i64], [i64]⟩ ]

/-- Standalone M7 BVA tie-break + `bb20` module (`3` functions + `19` externs, `0` exits). -/
def m7ParityBvaTieModule : LeanQbe.T.Module :=
  { fns := m7ParityBvaTie_fns, externs := m7ParityBvaTieExterns, exits := [] }

/-- Drop-in `Fn` handles matching canonical `FullM7.m7Module` slots for `FullM7Splice.patchFns`. -/
def m7btBvaPickCandFn : Fn :=
  ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], full_bva_pick_cand_bt_body⟩

def m7btProbeTailFn : Fn :=
  ⟨"full_probe_tail_m6", [i64, i64], [i64], full_probe_tail_bt_body⟩

def m7btProbeFn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_bt_body⟩

/-- `FullM7Splice.patchFns`-ready `3`-function replacement list for Target B (`FullM7Plus`). -/
def m7ParityBvaTiePatchFns : List Fn :=
  [m7btBvaPickCandFn, m7btProbeTailFn, m7btProbeFn]

theorem full_bva_pick_cand_bt_wf : Func.Wf full_bva_pick_cand_bt_body := by t_wf_reify
theorem full_probe_tail_bt_wf : Func.Wf full_probe_tail_bt_body := by t_wf_reify
theorem full_probe_bt_wf : Func.Wf full_probe_bt_body := by t_wf_reify

theorem m7ParityBvaTie_fns_wf : ∀ f ∈ m7ParityBvaTie_fns, f.Wf := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact full_bva_pick_cand_bt_wf
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact full_probe_tail_bt_wf
    · rcases List.mem_singleton.mp hf with rfl
      exact full_probe_bt_wf

theorem m7ParityBvaTiePatchFns_wf : ∀ f ∈ m7ParityBvaTiePatchFns, f.Wf := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact full_bva_pick_cand_bt_wf
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact full_probe_tail_bt_wf
    · rcases List.mem_singleton.mp hf with rfl
      exact full_probe_bt_wf

theorem m7ParityBvaTie_acyclic : m7ParityBvaTieModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie

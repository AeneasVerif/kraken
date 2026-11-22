module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M6 Tier-A: Zero-Hop BVA Candidate Picker (`FullM6BvaNoHops`)

Purely additive drop-in replacement for `FullM4Bva.full_bva_pick_cand` matching upstream
Kissat 4.0.4 (`factor.c:next_factor`) under default `--factorstructural=0` (`hops = 0`):
- Single-pass scan over `cntd[0..ncntd)` picking the first literal maximizing `(cnt[lit], deg)`
  where `deg = wvec[(lit << 1) + 1]` (watch-list degree), skipping `wvec` loads whenever
  `cnt[lit] < 2` or `cnt[lit] < best_c`.
- Clears `cnt[cntd[0..ncntd)] = 0u` exactly as `FullM4Bva.full_bva_pick_cand`.
- Returns `(best_c < 2u) ? 0xFFFFFFFFu : best_lit`.
- Zero calls to `full_bva_hop1`/`hop2`/`hop3` (`0` callees, `0` externs, `0` exits).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6BvaNoHops

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6BvaNoHops "
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

u32 full_bva_pick_cand_no_hops(FullHdr *h, u32 ncntd, u32 f0) {
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
        if (deg > best_deg) {
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
"

/-- Drop-in Wave-3 `Fn` handle preserving the canonical `"full_bva_pick_cand"` symbol name. -/
def m6BvaPickCandFn : Fn :=
  ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], full_bva_pick_cand_no_hops_body⟩

/-- Standalone drop-in function list (`1` fn, `0` callees). -/
def m6BvaNoHopsFns : List Fn := [m6BvaPickCandFn]

/-- Standalone closed module (`1` fn, `0` externs, `0` exits). -/
def m6BvaNoHopsModule : LeanQbe.T.Module :=
  { fns := m6BvaNoHopsFns, externs := [], exits := [] }

end LeanQbe.T.Examples.Kissat.FullM6BvaNoHops

end

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BvaNoHops

open LeanQbe.T

theorem full_bva_pick_cand_no_hops_wf : Func.Wf full_bva_pick_cand_no_hops_body := by
  t_wf_reify

theorem m6BvaPickCandFn_wf : m6BvaPickCandFn.Wf :=
  full_bva_pick_cand_no_hops_wf

theorem m6BvaNoHops_fns_wf : ∀ f ∈ m6BvaNoHops_fns, f.Wf := by
  intro f hf
  simp only [m6BvaNoHops_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf; exact full_bva_pick_cand_no_hops_wf

theorem m6BvaNoHopsFns_wf : ∀ f ∈ m6BvaNoHopsFns, f.Wf := by
  intro f hf
  simp only [m6BvaNoHopsFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf; exact full_bva_pick_cand_no_hops_wf

theorem m6BvaNoHops_acyclic : m6BvaNoHopsModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6BvaNoHops

end

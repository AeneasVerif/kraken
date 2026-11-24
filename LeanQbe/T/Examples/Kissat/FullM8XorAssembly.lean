/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorGauss
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `M8XorGauss` Additive Splice Assembly (`FullM8XorAssembly`)

Purely additive `Class S` splice wrapper over `FullM7Fidelity.m7FidelityFns` (`413` → `433`
functions, `0` modifications to `FullM7*`, `FullM6*`, or existing `Kissat*` files):
- Inserts the `19` `FullM8XorGauss.m8XorGaussFns` functions plus `full_probe_m7_inner`
  (`FullM7FidelitySchedFix.full_probe_fid2_body`) immediately before `"full_probe_m6"`.
- Replaces `"full_probe_m6"` with the thin wrapper calling `full_xor_gauss` (with guarded
  `full_substitute` cascade), `full_probe_m7_inner`, and a post-congruence `full_xor_gauss` pass.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorAssembly

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
open LeanQbe.T.Examples.Kissat.FullM8XorGauss

kissat_c0! m8ProbeWrap "
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

extern u64 full_xor_gauss(FullHdr *h);
extern u64 full_substitute(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_probe_m7_inner(FullHdr *h, bool initial);

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 te0 = h->trail_end;
  u64 nb0 = h->num_binary;
  u64 xr = full_xor_gauss(h);
  if (xr == 20ULL) {
    m6_hdr_set_watermark(h, 0ULL, h->search_ticks);
    return 20ULL;
  }
  if (h->trail_end != te0 || h->num_binary != nb0) {
    u64 sr = full_substitute(h);
    if (sr == 20ULL) {
      m6_hdr_set_watermark(h, 0ULL, h->search_ticks);
      return 20ULL;
    }
  }
  u64 pr = full_probe_m7_inner(h, initial);
  if (pr == 20ULL) {
    return 20ULL;
  }
  u64 te1 = h->trail_end;
  u64 nb1 = h->num_binary;
  xr = full_xor_gauss(h);
  if (xr == 20ULL) {
    m6_hdr_set_watermark(h, 0ULL, h->search_ticks);
    return 20ULL;
  }
  if (h->trail_end != te1 || h->num_binary != nb1) {
    u64 sr2 = full_substitute(h);
    if (sr2 == 20ULL) {
      m6_hdr_set_watermark(h, 0ULL, h->search_ticks);
      return 20ULL;
    }
  }
  return 1ULL;
}
"

def fullProbeM7InnerFn : Fn :=
  { name := "full_probe_m7_inner"
  , as := [i64, .bool]
  , rs := [i64]
  , body := full_probe_fid2_body }

def m8ProbeWrapFn : Fn :=
  { name := "full_probe_m6"
  , as := [i64, .bool]
  , rs := [i64]
  , body := full_probe_m6_body }

def m8XorFidelityFns : List Fn :=
  patchFns [m8ProbeWrapFn]
    [("full_probe_m6", m8XorGaussFns ++ [fullProbeM7InnerFn])]
    m7FidelityFns

def m8XorFidelityModule : LeanQbe.T.Module :=
  { fns := m8XorFidelityFns, externs := [], exits := [] }

theorem fullProbeM7InnerFn_wf : fullProbeM7InnerFn.Wf := full_probe_fid2_wf

theorem m8ProbeWrapFn_wf : m8ProbeWrapFn.Wf := by
  change Func.Wf full_probe_m6_body
  t_wf_reify

theorem m8XorFidelityFns_wf : ∀ f ∈ m8XorFidelityFns, f.Wf := by
  refine patchFns_wf m7FidelityFns_wf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact m8ProbeWrapFn_wf) ?_
  intro p hp h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  rcases List.mem_append.mp hh with h1 | h2
  · exact m8XorGaussFns_wf _ h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    subst h2; exact fullProbeM7InnerFn_wf

end LeanQbe.T.Examples.Kissat.FullM8XorAssembly

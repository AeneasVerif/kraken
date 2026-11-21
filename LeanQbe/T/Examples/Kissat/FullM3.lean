module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullFastCore
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
public import LeanQbe.T.Examples.Kissat.FullFastSched
public import LeanQbe.T.Examples.Kissat.FullKitten
public import LeanQbe.T.Examples.Kissat.FullDefSweep
public import LeanQbe.T.Examples.Kissat.FullBvaHeap
public import LeanQbe.T.Examples.Kissat.FullFast
public import LeanQbe.T.Examples.Kissat.FullM3Backbone
public import LeanQbe.T.Examples.Kissat.FullM3VivChrono
public import LeanQbe.T.Examples.Kissat.FullM3CongBva
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` Unified M3 Solver (`FullM3`, `204` Functions)

Splices ALL THREE M3 upgrades (M3a + M3b + M3c) onto `FullFast.fastFns` (`196` → `204` functions)
in strict topological call order (`externs := []`, `exits := []`):
- **M3a (`FullM3VivChrono`)**: chrono/rephase-aware `full_tick_rel`, `full_analyze_rsn`,
  `full_prop_lit` (`propLitRawFn` + `m3PropLitFn`), and 4-tier `full_vivify`.
- **M3b (`FullM3CongBva`)**: worklist congruence `m3MarkTrailFn..m3CongruenceDenseFn` (`6` fns),
  neighbor-rearming BVE `m3ElimCollectNbrsFn` + `m3ElimBveFn`, `m3EliminateFn`, `m3PreprocessFn`.
- **M3c (`FullM3Backbone`)**: cursor `full_probe_run`, `full_backbone_lit`, and `full_backbone`.
- **Merged orchestrators (`m3Orch`)**:
  1. `full_probe_tail`: M3c `full_backbone` + M3c `pbud` + M3a Tier-3 `full_vivify(h, 3ULL, v0)`.
  2. `full_probe`: M3b pure-3-CNF dense gate (`initial || num_binary * 3 >= num_irred`) + M3c
     `if (initial) { backbone; transitive; probe_run; } else { full_probe_tail; }`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m3Orch "
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

extern u64 full_ilog10(u64 x);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_backbone(FullHdr *h, u64 tick_lim);
extern u64 full_transitive(FullHdr *h, u64 tick_lim);
extern u64 full_vivify(FullHdr *h, u64 tier_mode, u64 budget);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_probe_dticks(FullHdr *h, bool initial);

u64 full_probe_tail(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL && full_backbone(h, dticks * 4ULL + 65536ULL) == 20ULL) {
    return 20ULL;
  }
  if (h->num_binary > 0ULL && full_transitive(h, dticks * 2ULL + 20000ULL) == 20ULL) {
    return 20ULL;
  }
  u64 pbud = full_min_u64(16ULL + (dticks >> 9), 128ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  u64 v1 = full_min_u64(32ULL + (dticks >> 7), 1024ULL);
  u64 v0 = full_min_u64(16ULL + (dticks >> 8), 512ULL);
  if (full_vivify(h, 1ULL, v1) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 2ULL, v1) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 3ULL, v0) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 0ULL, v0) == 20ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 logp = full_ilog10(h->probings + 9ULL);
    h->probe_limit = h->conflicts + full_scale_delta(h, 120ULL * h->probings * logp);
  }
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
  bool do_dense = (initial || h->num_binary * 3ULL >= h->num_irred);
  if (do_dense) {
    if (full_enter_dense(h)) {
      u64 sweep_bud = full_min_u64(8ULL + (dticks >> 11), 32ULL);
      if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
        full_rebuild_watches(h); return 20ULL;
      }
      if (full_sweep_dense(h, sweep_bud, dticks + 4096ULL) == 20ULL) {
        full_rebuild_watches(h); return 20ULL;
      }
      if (full_rebuild_watches(h) == 20ULL) { return 20ULL; }
    } else if (h->inconsistent != 0ULL) { return 20ULL; }
  }
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
  if (initial) {
    if (h->num_binary > 0ULL && full_backbone(h, dticks * 4ULL + 65536ULL) == 20ULL) {
      return 20ULL;
    }
    if (h->num_binary > 0ULL && full_transitive(h, dticks * 2ULL + 20000ULL) == 20ULL) {
      return 20ULL;
    }
    u64 pbud0 = full_min_u64(16ULL + (dticks >> 10), 64ULL);
    if (h->num_binary > 0ULL && full_probe_run(h, pbud0) == 20ULL) { return 20ULL; }
  } else {
    if (full_probe_tail(h, dticks) == 20ULL) { return 20ULL; }
  }
  h->fwd_sub_cnt = h->search_ticks;
  return 1ULL;
}
"

theorem full_probe_tail_wf : Func.Wf full_probe_tail_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify

theorem m3Orch_fns_wf : ∀ f ∈ m3Orch_fns, f.Wf := by
  simp only [m3Orch_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_probe_tail_wf, full_probe_wf⟩

/-! ## Unified `204`-Function Splicing Layout (`m3Fns` / `m3Module`) -/

def m3PropLitRawFn : Fn :=
  ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], FastCore.full_prop_lit_body⟩

def m3ProbeRunFn : Fn :=
  ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.full_probe_run_body⟩

def m3BackboneLitFn : Fn :=
  ⟨"full_backbone_lit", [i64, i32], [i64], FullM3Backbone.full_backbone_lit_body⟩

def m3BackboneFn : Fn :=
  ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.full_backbone_body⟩

def m3ProbeTailFn : Fn := ⟨"full_probe_tail", [i64, i64], [i64], full_probe_tail_body⟩
def m3ProbeFn : Fn := ⟨"full_probe", [i64, .bool], [i64], full_probe_body⟩

theorem m3PropLitRaw_wf : m3PropLitRawFn.Wf := FastCore.full_prop_lit_wf
theorem m3ProbeRun_wf : m3ProbeRunFn.Wf := FullM3Backbone.full_probe_run_wf
theorem m3BackboneLit_wf : m3BackboneLitFn.Wf := FullM3Backbone.full_backbone_lit_wf
theorem m3Backbone_wf : m3BackboneFn.Wf := FullM3Backbone.full_backbone_wf
theorem m3ProbeTail_wf : m3ProbeTailFn.Wf := full_probe_tail_wf
theorem m3Probe_wf : m3ProbeFn.Wf := full_probe_wf

/-- Unified M3 prefix `[0, 129)` (`129` fns): preserves `[0, 47)` alignment with `Full.fullFns`
except M3a `full_tick_rel` (`25`), splits `full_prop_lit` into `full_prop_lit_raw` (`47`) + M3a
`full_prop_lit` (`48`), and replaces `full_analyze_rsn` (`64`), M3c `full_probe_run` (`112`),
and M3a `full_vivify` (`120`). -/
def m3FnsPrefix : List Fn :=
  Full.fullFns.take 25 ++
  [FullM3VivChrono.m3TickRelFn] ++
  (Full.fullFns.drop 26).take 10 ++
  FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  (Full.fullFns.drop 37).take 10 ++
  [m3PropLitRawFn, FullM3VivChrono.m3PropLitFn] ++
  FastCore.fastCore_fns.drop 1 ++
  (Full.fullFns.drop 50).take 7 ++
  FullFastSched.sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 5 ++
  [FullM3VivChrono.m3AnalyzeRsnFn] ++
  (Full.fullFns.drop 64).take 47 ++
  [m3ProbeRunFn] ++
  (Full.fullFns.drop 112).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
  (Full.fullFns.drop 114).take 5 ++
  [FullM3VivChrono.m3VivifyFn] ++
  (Full.fullFns.drop 120).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
  (Full.fullFns.drop 122).take 3 ++
  (FullFastSched.sched_fns.drop 1).take 2 ++
  (Full.fullFns.drop 127).take 1

/-- Unified M3 suffix `[129, 204)` (`75` fns): `FullKitten` (`15`), congruence + M3b `6` fns,
sweeping (`4`), BVE helpers + `full_bve_var`, `FullBvaHeap` (`13`), schedulers, M3c
`full_backbone_lit` + `full_backbone`, merged `full_probe_tail` + `full_probe`, M3b
BVE/elim/preproc, `full_simplify`, `full_search`, and `Full.kissat_solve_bytes`. -/
def m3FnsSuffix : List Fn :=
  Full.fullKitten_fns ++
  (Full.fullFns.drop 128).take 7 ++
  (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
  [ FullM3CongBva.m3MarkTrailFn
  , FullM3CongBva.m3UnitFoldFn
  , FullM3CongBva.m3EquivFoldFn
  , FullM3CongBva.m3AndMatchFn
  , FullM3CongBva.m3CongWorkStepFn
  , FullM3CongBva.m3CongruenceDenseFn ] ++
  FullDefSweep.full_def_sweep_fns.drop 5 ++
  (Full.fullFns.drop 145).take 2 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
  (Full.fullFns.drop 148).take 1 ++
  FullDefSweep.full_def_sweep_fns.take 3 ++
  (Full.fullFns.drop 151).take 5 ++
  FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
  FullBvaHeap.bvaHeap_fns ++
  (FullFastSched.sched_fns.drop 3).take 4 ++
  [m3BackboneLitFn, m3BackboneFn, m3ProbeTailFn, m3ProbeFn] ++
  (FullFastSched.sched_fns.drop 9).take 1 ++
  [ FullM3CongBva.m3ElimCollectNbrsFn
  , FullM3CongBva.m3ElimBveFn
  , FullM3CongBva.m3EliminateFn
  , FullM3CongBva.m3PreprocessFn ] ++
  FullFastSched.sched_fns.drop 13 ++
  Full.fullFns.drop 165

/-- Unified M3 function list (`204` functions in strict topological call order). -/
def m3Fns : List Fn := m3FnsPrefix ++ m3FnsSuffix

/-- Closed Unified M3 compilation module (`externs := []`, `exits := []`). -/
def m3Module : LeanQbe.T.Module :=
  { fns := m3Fns, externs := [], exits := [] }

/-- Name-directed splice combinator transforming `FullFast.fastFns` (`196`) into `m3Fns` (`204`). -/
def m3Splice (f : Fn) : List Fn :=
  if f.name = "full_tick_rel" then [FullM3VivChrono.m3TickRelFn]
  else if f.name = "full_prop_lit" then
    [FullM3VivChrono.propLitRawFn f, FullM3VivChrono.m3PropLitFn]
  else if f.name = "full_analyze_rsn" then [FullM3VivChrono.m3AnalyzeRsnFn]
  else if f.name = "full_probe_run" then [m3ProbeRunFn]
  else if f.name = "full_vivify" then [FullM3VivChrono.m3VivifyFn]
  else if f.name = "full_cong_hash_step" then
    [ FullM3CongBva.m3MarkTrailFn
    , FullM3CongBva.m3UnitFoldFn
    , FullM3CongBva.m3EquivFoldFn
    , FullM3CongBva.m3AndMatchFn
    , FullM3CongBva.m3CongWorkStepFn ]
  else if f.name = "full_congruence_dense" then [FullM3CongBva.m3CongruenceDenseFn]
  else if f.name = "full_probe_tail" then [m3BackboneLitFn, m3BackboneFn, m3ProbeTailFn]
  else if f.name = "full_probe" then [m3ProbeFn]
  else if f.name = "full_elim_bve" then
    [FullM3CongBva.m3ElimCollectNbrsFn, FullM3CongBva.m3ElimBveFn]
  else if f.name = "full_eliminate" then [FullM3CongBva.m3EliminateFn]
  else if f.name = "full_preprocess" then [FullM3CongBva.m3PreprocessFn]
  else [f]

theorem m3Fns_eq_flatMap_sigs :
    m3Fns.map (fun f => (f.name, f.as, f.rs)) =
      (FullFast.fastFns.flatMap m3Splice).map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

private theorem fullFns_len : Full.fullFns.length = 166 := by t_kernel_rfl
private theorem fastCore_len : FastCore.fastCore_fns.length = 3 := by t_kernel_rfl
private theorem bveBudgets_len : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by
  t_kernel_rfl
private theorem sched_len : FullFastSched.sched_fns.length = 15 := by t_kernel_rfl
private theorem kitten_len : Full.fullKitten_fns.length = 15 := by t_kernel_rfl
private theorem defSweep_len : FullDefSweep.full_def_sweep_fns.length = 9 := by t_kernel_rfl
private theorem bvaHeap_len : FullBvaHeap.bvaHeap_fns.length = 13 := by t_kernel_rfl

theorem m3FnsPrefix_wf : ∀ f ∈ m3FnsPrefix, f.Wf := by
  intro f hf
  simp only [m3FnsPrefix, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (((((((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) |
    h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact Full.fullFns_wf f (List.mem_of_mem_take h)
  · subst h; exact FullM3VivChrono.full_tick_rel_wf
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · rcases h with rfl | rfl
    · exact m3PropLitRaw_wf
    · exact FullM3VivChrono.full_prop_lit_wf
  · exact FastCore.fastCore_fns_wf f (List.mem_of_mem_drop h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · subst h; exact FullM3VivChrono.full_analyze_rsn_wf
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · subst h; exact m3ProbeRun_wf
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · subst h; exact FullM3VivChrono.full_vivify_wf
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))

theorem m3FnsSuffix_wf : ∀ f ∈ m3FnsSuffix, f.Wf := by
  intro f hf
  simp only [m3FnsSuffix, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) |
    h) | h) | h) | h) | h)
  · exact Full.fullKitten_fns_wf f h
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullDefSweep.full_def_sweep_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact FullM3CongBva.full_cong_mark_trail_wf
    · exact FullM3CongBva.full_cong_unit_fold_wf
    · exact FullM3CongBva.full_cong_equiv_fold_wf
    · exact FullM3CongBva.full_cong_and_match_wf
    · exact FullM3CongBva.full_cong_work_step_wf
    · exact FullM3CongBva.full_congruence_dense_wf
  · exact FullDefSweep.full_def_sweep_fns_wf f (List.mem_of_mem_drop h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullDefSweep.full_def_sweep_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop h)
  · exact FullBvaHeap.bvaHeap_fns_wf f h
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · rcases h with rfl | rfl | rfl | rfl
    · exact m3BackboneLit_wf
    · exact m3Backbone_wf
    · exact m3ProbeTail_wf
    · exact m3Probe_wf
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · rcases h with rfl | rfl | rfl | rfl
    · exact FullM3CongBva.full_elim_collect_nbrs_wf
    · exact FullM3CongBva.full_elim_bve_wf
    · exact FullM3CongBva.full_eliminate_wf
    · exact FullM3CongBva.full_preprocess_wf
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop h)

theorem m3Fns_wf : ∀ f ∈ m3Fns, f.Wf := by
  intro f hf
  simp only [m3Fns, List.mem_append] at hf
  rcases hf with h | h
  · exact m3FnsPrefix_wf f h
  · exact m3FnsSuffix_wf f h

theorem m3_acyclic : m3Module.checkAcyclic = true := by
  t_kernel_rfl

theorem m3FnsPrefix_length : m3FnsPrefix.length = 129 := by
  simp [m3FnsPrefix, fullFns_len, fastCore_len, bveBudgets_len, sched_len]

theorem m3FnsSuffix_length : m3FnsSuffix.length = 75 := by
  simp [m3FnsSuffix, fullFns_len, kitten_len, defSweep_len, bveBudgets_len, bvaHeap_len, sched_len]

theorem m3Fns_length : m3Fns.length = 204 := by
  rw [m3Fns, List.length_append, m3FnsPrefix_length, m3FnsSuffix_length]

end LeanQbe.T.Examples.Kissat.FullM3

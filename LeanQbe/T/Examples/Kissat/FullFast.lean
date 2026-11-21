module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullFastCore
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
public import LeanQbe.T.Examples.Kissat.FullFastSched
public import LeanQbe.T.Examples.Kissat.FullKitten
public import LeanQbe.T.Examples.Kissat.FullDefSweep
public import LeanQbe.T.Examples.Kissat.FullBvaHeap
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M2 Unified Fast Solver (`FullFast`)

Splices all `6` M2 upgrades onto the `134` unchanged `Full.fullFns` functions in strict
topological call order (`196` total functions, `externs := []`, `exits := []`, `0` edits to
`Full{,1..3}.lean` or `FullFastSched.lean`):
1. **`FastCore` (`3` fns, `[47..49]`)**: hot-loop inline BCP (`full_prop_lit`,
   `full_propagate_ignore`, `full_propagate`).
2. **`FastBveBudgets` (`7` fns, `{36, 111, 113, 119, 121, 159, 169}`)**: tuned `full_init_hdr`,
   budgeted `full_probe_run` / `full_transitive` / `full_vivify` / `full_forward_sub`,
   `TmkZero`-clean `full_tarjan_scc`, and `64`-occ `P_ng × N_ng` `full_bve_var`.
3. **`FullKitten` (`15` fns, `[128..142]`)**: scratch-resident `kitten` mini-CDCL sub-solver.
4. **`FullDefSweep` (`9` fns, `{150, 152..156, 161..163}`)**: semantic gate mining
   (`full_bve_mark_and`, `full_find_definition`, `full_bve_gates`), ticks-bounded dense congruence
   (`full_cong_extract`, `full_congruence_dense`), and `kitten`-backed dense cone sweeping
   (`full_sweep_cone`, `full_sweep_refine_kitten`, `full_sweep_var`, `full_sweep_dense`).
5. **`FullBvaHeap` (`13` fns, `[170..182]`)**: 3-hop complement-overlap BVA & max-degree binary
   heap factoring (`full_init_fresh_var` .. `full_factor`).
6. **`FullFastSched` (`12` reused fns) + `3` unified M2 orchestrators (`full_probe_tail`,
   `full_probe`, `full_eliminate`, bridging budgeted/dense/heap callee signatures and zeroing
   `tarjan_mark` before `full_elim_bve`) + `Full.kissat_solve_bytes` (`195`)**.

Index alignment with `Full.fullFns` is preserved 1-to-1 across `[0, 128)`, including exact slice
reuse of `[0, 36)` (first `9` chunks of `KissatFullCert1`), `[67, 88)` (`KissatFullCert3`), and
`[88, 111)` (`KissatFullCert4`) for `LinkedCert.append`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFast

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fastOrch "
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
extern u64 full_transitive(FullHdr *h, u64 tick_lim);
extern u64 full_vivify(FullHdr *h, u64 tier_mode, u64 budget);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_probe_dticks(FullHdr *h, bool initial);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_elim_bve(FullHdr *h, u64 bve_lim);

u64 full_probe_tail(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL && full_transitive(h, dticks * 2ULL + 20000ULL) == 20ULL) {
    return 20ULL;
  }
  u64 pbud = full_min_u64(8ULL + (dticks >> 10), 64ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  u64 v1 = full_min_u64(32ULL + (dticks >> 7), 1024ULL);
  u64 v0 = full_min_u64(16ULL + (dticks >> 8), 512ULL);
  if (full_vivify(h, 1ULL, v1) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 2ULL, v1) == 20ULL) { return 20ULL; }
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
  bool do_dense = (h->num_binary >= 4ULL && (initial || h->num_binary * 3ULL >= h->num_irred));
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
  if (!initial && full_probe_tail(h, dticks) == 20ULL) { return 20ULL; }
  h->fwd_sub_cnt = h->search_ticks;
  return 1ULL;
}

u64 full_eliminate(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    h->elim_limit = h->conflicts + full_scale_delta(h, 250ULL * h->eliminations * loge);
    if (h->eliminations >= 2ULL && h->elim_bound < 8ULL) {
      h->elim_bound = h->elim_bound + 2ULL;
    }
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) { full_rebuild_watches(h); return 20ULL; }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = full_min_u64(initial ? (cv + 256ULL) : (64ULL + (dticks >> 7)), cv);
  u64 res = full_elim_bve(h, bve_lim);
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 1024ULL)) {
    u64 fact_bud = full_min_u64(initial ? 128ULL : (16ULL + (dticks >> 10)), 256ULL);
    full_factor(h, fact_bud);
  }
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}
"

theorem full_probe_tail_wf : Func.Wf full_probe_tail_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify

theorem fastOrch_fns_wf : ∀ f ∈ fastOrch_fns, f.Wf := by
  simp only [fastOrch_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_probe_tail_wf, full_probe_wf, full_eliminate_wf⟩

/-! ## Unified `196`-Function Splicing Layout (`fastFns` / `fastModule`) -/

/-- Prefix `[0, 128)` matching `Full.fullFns[0..128)` index-for-index, splicing `FastBveBudgets`
`{36, 111, 113, 119, 121}`, `FastCore` `[47..49]`, and `FullFastSched` `{57, 125, 126}`. -/
def fastFnsPrefix : List Fn :=
  Full.fullFns.take 36 ++
  FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  (Full.fullFns.drop 37).take 10 ++
  FastCore.fastCore_fns ++
  (Full.fullFns.drop 50).take 7 ++
  FullFastSched.sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 53 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
  (Full.fullFns.drop 112).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
  (Full.fullFns.drop 114).take 5 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
  (Full.fullFns.drop 120).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
  (Full.fullFns.drop 122).take 3 ++
  (FullFastSched.sched_fns.drop 1).take 2 ++
  (Full.fullFns.drop 127).take 1

/-- Suffix `[128, 196)` (`68` fns): `FullKitten` (`15`), congruence/sweep (`14`, `DefSweep`),
forward/BVE (`13`, `FastBveBudgets` + `DefSweep`), `FullBvaHeap` (`13`), unified schedulers
(`12`), and `Full.kissat_solve_bytes` (`1`). -/
def fastFnsSuffix : List Fn :=
  Full.fullKitten_fns ++
  (Full.fullFns.drop 128).take 7 ++
  (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
  (Full.fullFns.drop 136).take 1 ++
  FullDefSweep.full_def_sweep_fns.drop 4 ++
  (Full.fullFns.drop 145).take 2 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
  (Full.fullFns.drop 148).take 1 ++
  FullDefSweep.full_def_sweep_fns.take 3 ++
  (Full.fullFns.drop 151).take 5 ++
  FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
  FullBvaHeap.bvaHeap_fns ++
  (FullFastSched.sched_fns.drop 3).take 4 ++
  fastOrch_fns.take 2 ++
  (FullFastSched.sched_fns.drop 9).take 2 ++
  fastOrch_fns.drop 2 ++
  FullFastSched.sched_fns.drop 12 ++
  Full.fullFns.drop 165

/-- Unified M2 `FullFast` function list (`196` functions in strict topological call order). -/
def fastFns : List Fn :=
  fastFnsPrefix ++ fastFnsSuffix

/-- Closed M2 `FullFast` compilation module (`externs := []`, `exits := []`). -/
def fastModule : LeanQbe.T.Module :=
  { fns := fastFns, externs := [], exits := [] }

theorem fastFnsPrefix_wf : ∀ f ∈ fastFnsPrefix, f.Wf := by
  intro f hf
  simp only [fastFnsPrefix, List.mem_append] at hf
  rcases hf with ((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) |
    h) | h) | h) | h)
  · exact Full.fullFns_wf f (List.mem_of_mem_take h)
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FastCore.fastCore_fns_wf f h
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))

theorem fastFnsSuffix_wf : ∀ f ∈ fastFnsSuffix, f.Wf := by
  intro f hf
  simp only [fastFnsSuffix, List.mem_append] at hf
  rcases hf with (((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) |
    h) | h) | h) | h) | h)
  · exact Full.fullKitten_fns_wf f h
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullDefSweep.full_def_sweep_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullDefSweep.full_def_sweep_fns_wf f (List.mem_of_mem_drop h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullDefSweep.full_def_sweep_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullFastBveBudgets.fastBveBudgets_fns_wf f (List.mem_of_mem_drop h)
  · exact FullBvaHeap.bvaHeap_fns_wf f h
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact fastOrch_fns_wf f (List.mem_of_mem_take h)
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact fastOrch_fns_wf f (List.mem_of_mem_drop h)
  · exact FullFastSched.sched_fns_wf f (List.mem_of_mem_drop h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop h)

theorem fastFns_wf : ∀ f ∈ fastFns, f.Wf := by
  intro f hf
  simp only [fastFns, List.mem_append] at hf
  rcases hf with h | h
  · exact fastFnsPrefix_wf f h
  · exact fastFnsSuffix_wf f h

theorem fast_acyclic : fastModule.checkAcyclic = true := by
  t_kernel_rfl

/-! ## Prefix & Unchanged-Slice Alignment Lemmas for `LinkedCert.append` Reuse -/

private theorem fullFns_len : Full.fullFns.length = 166 := by t_kernel_rfl
private theorem fastCore_len : FastCore.fastCore_fns.length = 3 := by t_kernel_rfl
private theorem bveBudgets_len : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by t_kernel_rfl
private theorem sched_len : FullFastSched.sched_fns.length = 15 := by t_kernel_rfl
private theorem kitten_len : Full.fullKitten_fns.length = 15 := by t_kernel_rfl
private theorem defSweep_len : FullDefSweep.full_def_sweep_fns.length = 9 := by t_kernel_rfl
private theorem bvaHeap_len : FullBvaHeap.bvaHeap_fns.length = 13 := by t_kernel_rfl
private theorem fastOrch_len : fastOrch_fns.length = 3 := by t_kernel_rfl

theorem fastFnsPrefix_length : fastFnsPrefix.length = 128 := by
  simp [fastFnsPrefix, fullFns_len, fastCore_len, bveBudgets_len, sched_len]

theorem fastFnsSuffix_length : fastFnsSuffix.length = 68 := by
  simp [fastFnsSuffix, fullFns_len, kitten_len, defSweep_len, bveBudgets_len, bvaHeap_len,
    sched_len, fastOrch_len]

theorem fastFns_length : fastFns.length = 196 := by
  rw [fastFns, List.length_append, fastFnsPrefix_length, fastFnsSuffix_length]

private theorem drop_append_left {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  subst h; simp

private theorem take_append_left {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).take n = xs := by
  subst h; simp

/-- Unchanged prefix `[0, 36)` matching `Full.fullFns.take 36` (first `9` chunks of
`KissatFullCert1`). -/
theorem fastFns_take_36 : fastFns.take 36 = Full.fullFns.take 36 := by
  have heq : fastFns = Full.fullFns.take 36 ++
      (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
       (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
       (Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1 ++
       (Full.fullFns.drop 58).take 53 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
       (Full.fullFns.drop 112).take 1 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
       (Full.fullFns.drop 114).take 5 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
       (Full.fullFns.drop 120).take 1 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
       (Full.fullFns.drop 122).take 3 ++
       (FullFastSched.sched_fns.drop 1).take 2 ++
       (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  rw [heq, take_append_left (by simp [fullFns_len])]

/-- Unchanged slice `[37, 47)` (`10` fns). -/
theorem fastFns_slice_37_47 : (fastFns.drop 37).take 10 = (Full.fullFns.drop 37).take 10 := by
  have h37 : (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1).length = 37 :=
    by simp [fullFns_len, bveBudgets_len]
  have heq : fastFns =
      (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1) ++
      ((Full.fullFns.drop 37).take 10 ++
       (FastCore.fastCore_fns ++ (Full.fullFns.drop 50).take 7 ++
        FullFastSched.sched_fns.take 1 ++ (Full.fullFns.drop 58).take 53 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
        (Full.fullFns.drop 112).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
        (Full.fullFns.drop 114).take 5 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
        (Full.fullFns.drop 120).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
        (Full.fullFns.drop 122).take 3 ++
        (FullFastSched.sched_fns.drop 1).take 2 ++
        (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix)) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  rw [heq, drop_append_left h37, take_append_left (by simp [fullFns_len])]

/-- Unchanged slice `[50, 57)` (`7` fns). -/
theorem fastFns_slice_50_57 : (fastFns.drop 50).take 7 = (Full.fullFns.drop 50).take 7 := by
  have h50 : (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
      (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns).length = 50 := by
    simp [fullFns_len, bveBudgets_len, fastCore_len]
  have heq : fastFns =
      (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
        (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns) ++
      ((Full.fullFns.drop 50).take 7 ++
       (FullFastSched.sched_fns.take 1 ++ (Full.fullFns.drop 58).take 53 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
        (Full.fullFns.drop 112).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
        (Full.fullFns.drop 114).take 5 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
        (Full.fullFns.drop 120).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
        (Full.fullFns.drop 122).take 3 ++
        (FullFastSched.sched_fns.drop 1).take 2 ++
        (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix)) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  rw [heq, drop_append_left h50, take_append_left (by simp [fullFns_len])]

/-- Unchanged slice `[58, 111)` (`53` fns, covering `KissatFullCert3` & `KissatFullCert4`). -/
theorem fastFns_slice_58_111 : (fastFns.drop 58).take 53 = (Full.fullFns.drop 58).take 53 := by
  have h58 : (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
      (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
      (Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1).length = 58 := by
    simp [fullFns_len, bveBudgets_len, fastCore_len, sched_len]
  have heq : fastFns =
      (Full.fullFns.take 36 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
        (Full.fullFns.drop 37).take 10 ++ FastCore.fastCore_fns ++
        (Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1) ++
      ((Full.fullFns.drop 58).take 53 ++
       ((FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
        (Full.fullFns.drop 112).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
        (Full.fullFns.drop 114).take 5 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
        (Full.fullFns.drop 120).take 1 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
        (Full.fullFns.drop 122).take 3 ++
        (FullFastSched.sched_fns.drop 1).take 2 ++
        (Full.fullFns.drop 127).take 1 ++ fastFnsSuffix)) := by
    simp only [fastFns, fastFnsPrefix, List.append_assoc]
  rw [heq, drop_append_left h58, take_append_left (by simp [fullFns_len])]

/-- Exact slice `[67, 88)` matching `KissatFullCert3` (`21` unchanged functions). -/
theorem fastFns_slice_67_88 : (fastFns.drop 67).take 21 = (Full.fullFns.drop 67).take 21 := by
  have h1 := congrArg (fun xs => (xs.drop 9).take 21) fastFns_slice_58_111
  simpa [List.drop_take, List.drop_drop, List.take_take] using h1

/-- Exact slice `[88, 111)` matching `KissatFullCert4` (`23` unchanged functions). -/
theorem fastFns_slice_88_111 : (fastFns.drop 88).take 23 = (Full.fullFns.drop 88).take 23 := by
  have h1 := congrArg (fun xs => (xs.drop 30).take 23) fastFns_slice_58_111
  simpa [List.drop_take, List.drop_drop, List.take_take] using h1

/-- Exact `FullKitten` slice `[128, 143)` (`15` functions). -/
theorem fastFns_slice_128_143 : (fastFns.drop 128).take 15 = Full.fullKitten_fns := by
  rw [fastFns, drop_append_left fastFnsPrefix_length]
  have heq : fastFnsSuffix = Full.fullKitten_fns ++
      ((Full.fullFns.drop 128).take 7 ++
       (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
       (Full.fullFns.drop 136).take 1 ++ FullDefSweep.full_def_sweep_fns.drop 4 ++
       (Full.fullFns.drop 145).take 2 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
       (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
       (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
       FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
       fastOrch_fns.take 2 ++ (FullFastSched.sched_fns.drop 9).take 2 ++
       fastOrch_fns.drop 2 ++ FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165) := by
    simp only [fastFnsSuffix, List.append_assoc]
  rw [heq, take_append_left kitten_len]

/-- Exact `FullBvaHeap` slice `[170, 183)` (`13` functions). -/
theorem fastFns_slice_170_183 : (fastFns.drop 170).take 13 = FullBvaHeap.bvaHeap_fns := by
  have h42 : (Full.fullKitten_fns ++ (Full.fullFns.drop 128).take 7 ++
      (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++ (Full.fullFns.drop 136).take 1 ++
      FullDefSweep.full_def_sweep_fns.drop 4 ++ (Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++ (Full.fullFns.drop 148).take 1 ++
      FullDefSweep.full_def_sweep_fns.take 3 ++ (Full.fullFns.drop 151).take 5 ++
      FullFastBveBudgets.fastBveBudgets_fns.drop 6).length = 42 := by
    simp [fullFns_len, kitten_len, defSweep_len, bveBudgets_len]
  have heq : fastFnsSuffix =
      (Full.fullKitten_fns ++ (Full.fullFns.drop 128).take 7 ++
        (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++ (Full.fullFns.drop 136).take 1 ++
        FullDefSweep.full_def_sweep_fns.drop 4 ++ (Full.fullFns.drop 145).take 2 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++ (Full.fullFns.drop 148).take 1 ++
        FullDefSweep.full_def_sweep_fns.take 3 ++ (Full.fullFns.drop 151).take 5 ++
        FullFastBveBudgets.fastBveBudgets_fns.drop 6) ++
      (FullBvaHeap.bvaHeap_fns ++
       ((FullFastSched.sched_fns.drop 3).take 4 ++ fastOrch_fns.take 2 ++
        (FullFastSched.sched_fns.drop 9).take 2 ++ fastOrch_fns.drop 2 ++
        FullFastSched.sched_fns.drop 12 ++ Full.fullFns.drop 165)) := by
    simp only [fastFnsSuffix, List.append_assoc]
  rw [fastFns, show 170 = 128 + 42 from rfl, ← List.drop_drop,
    drop_append_left fastFnsPrefix_length, heq, drop_append_left h42, take_append_left bvaHeap_len]

/-- Tail entry `[195]` is unchanged `Full.kissat_solve_bytes` (`Full.fullFns[165]`). -/
theorem fastFns_drop_195 : fastFns.drop 195 = Full.fullFns.drop 165 := by
  have h67 : (Full.fullKitten_fns ++ (Full.fullFns.drop 128).take 7 ++
      (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++ (Full.fullFns.drop 136).take 1 ++
      FullDefSweep.full_def_sweep_fns.drop 4 ++ (Full.fullFns.drop 145).take 2 ++
      (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++ (Full.fullFns.drop 148).take 1 ++
      FullDefSweep.full_def_sweep_fns.take 3 ++ (Full.fullFns.drop 151).take 5 ++
      FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++ FullBvaHeap.bvaHeap_fns ++
      (FullFastSched.sched_fns.drop 3).take 4 ++ fastOrch_fns.take 2 ++
      (FullFastSched.sched_fns.drop 9).take 2 ++ fastOrch_fns.drop 2 ++
      FullFastSched.sched_fns.drop 12).length = 67 := by
    simp [fullFns_len, kitten_len, defSweep_len, bveBudgets_len, bvaHeap_len, sched_len,
      fastOrch_len]
  have heq : fastFnsSuffix =
      (Full.fullKitten_fns ++ (Full.fullFns.drop 128).take 7 ++
        (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++ (Full.fullFns.drop 136).take 1 ++
        FullDefSweep.full_def_sweep_fns.drop 4 ++ (Full.fullFns.drop 145).take 2 ++
        (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++ (Full.fullFns.drop 148).take 1 ++
        FullDefSweep.full_def_sweep_fns.take 3 ++ (Full.fullFns.drop 151).take 5 ++
        FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++ FullBvaHeap.bvaHeap_fns ++
        (FullFastSched.sched_fns.drop 3).take 4 ++ fastOrch_fns.take 2 ++
        (FullFastSched.sched_fns.drop 9).take 2 ++ fastOrch_fns.drop 2 ++
        FullFastSched.sched_fns.drop 12) ++
      Full.fullFns.drop 165 := by
    simp only [fastFnsSuffix, List.append_assoc]
  rw [fastFns, show 195 = 128 + 67 from rfl, ← List.drop_drop,
    drop_append_left fastFnsPrefix_length, heq, drop_append_left h67]

end LeanQbe.T.Examples.Kissat.FullFast

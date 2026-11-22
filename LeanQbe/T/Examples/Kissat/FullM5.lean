module

public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.Examples.Kissat.FullM4VivBce
public import LeanQbe.T.Examples.Kissat.FullM4Sweep
public import LeanQbe.T.Examples.Kissat.FullM4InprocHot
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullM5ProbeProp
public import LeanQbe.T.Examples.Kissat.FullM5Sched
public import LeanQbe.T.Examples.Kissat.FullM5CongBins
public import LeanQbe.T.Examples.Kissat.FullM5CongFix
public import LeanQbe.T.Examples.Kissat.FullM5Hbr
public import LeanQbe.T.Examples.Kissat.FullM5Orch
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` Unified M5 Solver (`FullM5`)

Splices all Wave 0 (`W0A` `FullM4Compact`, `W0B` `FullM5DenseSafe`, `W0C` `FullM5Otfs`,
`W0D` `FullM4Sweep` + `FullM4VivBce` + `FullM5KittenDefFix`) and Wave 1 (`W1A` `FullM5HeurCore`,
`W1B` `FullM4Bcp` + `FullM5ProbeProp`, `W1C` `FullM5Sched`, `W1D` `FullM4Bva` + `FullM4InprocHot` +
`FullM5CongBins` + `FullM5CongFix`, `W1E` `FullM5Hbr` + `FullM5Orch`) upgrades in strict
topological call order (`externs := []`, `exits := []`):
- Unifies `W1A` `full_analyze_m5` with `W0C` `full_deduce_1uip_m5` + `full_one_lit_confl_m5`.
- Wires BOTH `[38] full_calc_ext_cap_m5` (`4M`) and `[39] full_calc_scr_cap_m5` (`1M`) into
  `full_init_state_m5` (fixing `extend_cap` witness overflow).
- Uses `W1E` `full_vivify_m5` + `full_vivify_tier_m5` (uncapped `0xFFFFFFFFu`, rolling cumulative
  `tick_cap`, delegating per-clause to `FullM4VivBce`) and `W0D` `full_bce_m4`.
- Drops regressive `full_promote_reasons`, `full_reorder_heap`, `full_tumble_*`, and
  `full_ternary*`.
- Exposes canonical external entrypoints (`full_init_state`, `full_reduce`, `full_preprocess`,
  `full_search`, `kissat_solve_bytes`) forwarding directly to their `_m5` implementations.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5Fwd "
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

extern bool full_init_state_m5(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel);
extern u64 full_reduce_m5(FullHdr *h, bool force);
extern u64 full_preprocess_m5(FullHdr *h);
extern u64 full_search_m5(FullHdr *h);
extern u64 kissat_solve_bytes_m5(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel);

bool full_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  return full_init_state_m5(cnf_ptr, cnf_end, hdr_addr, avail, fuel);
}

u64 full_reduce(FullHdr *h, bool force) {
  return full_reduce_m5(h, force);
}

u64 full_preprocess(FullHdr *h) {
  return full_preprocess_m5(h);
}

u64 full_search(FullHdr *h) {
  return full_search_m5(h);
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  return kissat_solve_bytes_m5(cnf_ptr, cnf_len, work_ptr, work_cap, fuel);
}
"

theorem full_init_state_wf : Func.Wf full_init_state_body := by t_wf_reify
theorem full_reduce_wf : Func.Wf full_reduce_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify
theorem full_search_wf : Func.Wf full_search_body := by t_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

theorem m5Fwd_fns_wf : ∀ f ∈ m5Fwd_fns, f.Wf := by
  simp only [m5Fwd_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_init_state_wf, full_reduce_wf, full_preprocess_wf, full_search_wf,
    kissat_solve_bytes_wf⟩

kissat_c0! m5AddBin "
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

#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_delete_bin_side(FullHdr *h, u32 lit, u32 other);

u64 full_add_bin(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == (b ^ 1u)) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  if (vals[a] > (i8)0 || vals[b] > (i8)0) { return 0ULL; }
  if (vals[a] < (i8)0 && vals[b] < (i8)0) { h->inconsistent = 1ULL; return 20ULL; }
  if (vals[a] < (i8)0 || a == b) { full_assign_lvl(h, b, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (vals[b] < (i8)0) { full_assign_lvl(h, a, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (full_has_bin(h, a, b)) { return 0ULL; }
  u32 b0 = (b & PW_LIT_MASK) | PW_BIN_FLAG;
  u32 b1 = (a & PW_LIT_MASK) | PW_BIN_FLAG;
  if (!full_watch_push(h, a, b0, 0u, 1u)) { h->oom = 1ULL; return 2ULL; }
  if (!full_watch_push(h, b, b1, 0u, 1u)) {
    full_delete_bin_side(h, a, b);
    h->oom = 1ULL; return 2ULL;
  }
  h->num_binary = h->num_binary + 1ULL;
  return 1ULL;
}
"

theorem full_add_bin_wf : Func.Wf full_add_bin_body := by t_wf_reify

def m5AddBinFn : Fn := ⟨"full_add_bin", [i64, i32, i32], [i64], full_add_bin_body⟩

/-! ## Canonical `Fn` Handles & Unified `m5Fns` Splicing Layout -/

def m5OneLitConflFn : Fn :=
  ⟨"full_one_lit_confl", [i64], [i64], FullM5Otfs.full_one_lit_confl_m5_body⟩

def m5Deduce1uipFn : Fn :=
  ⟨"full_deduce_1uip", [i64], [i64], FullM5Otfs.full_deduce_1uip_m5_body⟩

def m5HbrDomFn : Fn :=
  ⟨"full_hbr_dom", [i64, i32, i32], [i32], FullM5Hbr.full_hbr_dom_m5_body⟩

def m5ProbePropLitFn : Fn :=
  ⟨"full_probe_prop_lit", [i64, i32], [.bool], FullM5ProbeProp.full_probe_prop_lit_m5_body⟩

def m5FindDefinitionFn : Fn :=
  ⟨"full_find_definition", [i64, i32, i32, i32], [],
    FullM5KittenDefFix.full_find_definition_m5_body⟩

def m5InitStateFwdFn : Fn :=
  ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], full_init_state_body⟩

def m5ReduceFwdFn : Fn := ⟨"full_reduce", [i64, .bool], [i64], full_reduce_body⟩
def m5PreprocessFwdFn : Fn := ⟨"full_preprocess", [i64], [i64], full_preprocess_body⟩
def m5SearchFwdFn : Fn := ⟨"full_search", [i64], [i64], full_search_body⟩
def m5SolveBytesFwdFn : Fn :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], kissat_solve_bytes_body⟩

def m5BvaFns : List Fn :=
  FullBvaHeap.bvaHeap_fns.take 1 ++
  [FullM4Bva.m4Hop1Fn, FullM4Bva.m4Hop2Fn, FullM4Bva.m4Hop3Fn] ++
  (FullBvaHeap.bvaHeap_fns.drop 4).take 2 ++
  [FullM4Bva.m4PickCandFn, FullM4Bva.m4FilterRowFn, FullM5DenseSafe.m5BvaCommitFn,
   FullM4Bva.m4TryLitFn] ++
  (FullBvaHeap.bvaHeap_fns.drop 10).take 2 ++
  [FullM4Bva.m4FactorFn]

/-- Unified M5 prefix (parser, heap, scheduling, BCP/OTFS, CDCL analyze, walk, probing/vivify,
dense substitution) in strict topological call order. -/
def m5FnsPrefix : List Fn :=
  Full.fullFns.take 14 ++
  [FullM4InprocHot.m4WstackDefragFn] ++
  (Full.fullFns.drop 15).take 6 ++
  [FullM4Bump.m4BumpVarFn] ++
  (Full.fullFns.drop 22).take 3 ++
  [FullM3VivChrono.m3TickRelFn] ++
  FullM5Sched.m5Sched_fns.take 3 ++
  (Full.fullFns.drop 27).take 2 ++
  [ FullM5HeurCore.m5SaveTargetBestFn
  , FullM5HeurCore.m5BacktrackRawFn
  , FullM5HeurCore.m5BacktrackFn ] ++
  (Full.fullFns.drop 31).take 5 ++
  FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  (Full.fullFns.drop 37).take 1 ++
  FullM5Orch.m5Orch_fns.take 2 ++
  (Full.fullFns.drop 40).take 1 ++
  (FullM5Orch.m5Orch_fns.drop 2).take 1 ++
  [m5InitStateFwdFn] ++
  (Full.fullFns.drop 42).take 5 ++
  FullM5Otfs.m5Otfs_fns.take 1 ++
  [FullM4.m4PropLitRawFn] ++
  FullM5Otfs.m5Otfs_fns.drop 5 ++
  FastCore.fastCore_fns.drop 2 ++
  (Full.fullFns.drop 50).take 6 ++
  FullFastSched.sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 3 ++
  (FullM5Orch.m5Orch_fns.drop 11).take 1 ++
  [m5ReduceFwdFn] ++
  (Full.fullFns.drop 62).take 1 ++
  [FullM5HeurCore.m5AnalyzeRsnFn] ++
  (Full.fullFns.drop 64).take 1 ++
  [FullM5HeurCore.m5BumpAnalyzedFn, FullM5HeurCore.m5RestoreBumpAnaFn] ++
  (FullM5Otfs.m5Otfs_fns.drop 1).take 2 ++
  [FullM5HeurCore.m5OtfsSubsumeFn] ++
  (Full.fullFns.drop 69).take 9 ++
  [ m5OneLitConflFn, m5Deduce1uipFn
  , FullM5HeurCore.m5EagerSubsumeFn
  , FullM5HeurCore.m5LearnClauseFn
  , FullM5HeurCore.m5AnalyzeFn ] ++
  (Full.fullFns.drop 83).take 2 ++
  [FullM5HeurCore.m5WarmupFn] ++
  (Full.fullFns.drop 86).take 4 ++
  FullM5Sched.m5Sched_fns.drop 3 ++
  (Full.fullFns.drop 93).take 3 ++
  [FullM4.m4ExtendFn] ++
  (Full.fullFns.drop 97).take 1 ++
  (Full.fullFns.drop 99).take 1 ++
  [m5AddBinFn] ++
  (Full.fullFns.drop 100).take 6 ++
  [m5HbrDomFn, m5ProbePropLitFn] ++
  (Full.fullFns.drop 108).take 3 ++
  [FullM3.m3ProbeRunFn] ++
  (FullM5Orch.m5Orch_fns.drop 5).take 2 ++
  (Full.fullFns.drop 114).take 4 ++
  FullM4VivBce.m4VivBce_fns.take 11 ++
  (FullM5Orch.m5Orch_fns.drop 7).take 2 ++
  (Full.fullFns.drop 120).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
  (Full.fullFns.drop 122).take 1 ++
  [ FullM5DenseSafe.m5SubstRewriteBinsFn
  , FullM5DenseSafe.m5SubstRewriteArFn
  , FullM5DenseSafe.m5SubstituteFn
  , FullM5DenseSafe.m5EnterDenseFn ] ++
  (Full.fullFns.drop 127).take 1

/-- Unified M5 suffix (kitten, congruence, sweep, forward/BVE, BVA, compact, reorder, BCE,
probe, eliminate, preprocess, simplify, search, top-level solve) in strict topological order. -/
def m5FnsSuffix : List Fn :=
  [FullM4InprocHot.m4KittenInitFn] ++
  Full.fullKitten_fns.drop 1 ++
  (Full.fullFns.drop 128).take 1 ++
  FullM5CongFix.m5CongFix_fns.take 1 ++
  [FullM4InprocHot.m4HasTernaryFn] ++
  (Full.fullFns.drop 131).take 1 ++
  (FullM5CongFix.m5CongFix_fns.drop 1).take 4 ++
  [FullM3CongBva.m3MarkTrailFn, FullM3CongBva.m3UnitFoldFn, FullM3CongBva.m3EquivFoldFn] ++
  FullM5CongFix.m5CongFix_fns.drop 5 ++
  FullM5CongBins.m5CongBins_fns ++
  FullM4Sweep.fullM4Sweep_fns.take 22 ++
  (FullM5Orch.m5Orch_fns.drop 9).take 1 ++
  (Full.fullFns.drop 145).take 1 ++
  [FullM5DenseSafe.m5FwdCheckClFn] ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
  (Full.fullFns.drop 148).take 1 ++
  FullDefSweep.full_def_sweep_fns.take 1 ++
  FullM5KittenDefFix.m5KittenDefFix_fns.take 5 ++
  [m5FindDefinitionFn] ++
  (FullDefSweep.full_def_sweep_fns.drop 2).take 1 ++
  (Full.fullFns.drop 151).take 5 ++
  [FullM5DenseSafe.m5BveVarFn] ++
  m5BvaFns ++
  FullM4Compact.compact_fns ++
  (FullM4Ternary.full_m4_ternary_fns.drop 3).take 2 ++
  (FullM5Orch.m5Orch_fns.drop 12).take 1 ++
  FullM4VivBce.m4VivBce_fns.drop 12 ++
  (FullFastSched.sched_fns.drop 4).take 2 ++
  (FullM5Orch.m5Orch_fns.drop 3).take 1 ++
  [FullM3.m3BackboneLitFn, FullM3.m3BackboneFn] ++
  (FullM5Orch.m5Orch_fns.drop 10).take 1 ++
  (FullM5Orch.m5Orch_fns.drop 13).take 1 ++
  (FullM5Orch.m5Orch_fns.drop 4).take 1 ++
  [FullM3CongBva.m3ElimCollectNbrsFn, FullM3CongBva.m3ElimBveFn] ++
  (FullM5Orch.m5Orch_fns.drop 14).take 2 ++
  [m5PreprocessFwdFn] ++
  (FullM5Orch.m5Orch_fns.drop 16).take 2 ++
  [m5SearchFwdFn] ++
  FullM5Orch.m5Orch_fns.drop 18 ++
  [m5SolveBytesFwdFn]

/-- Complete Unified M5 function list in strict topological call order. -/
def m5Fns : List Fn := m5FnsPrefix ++ m5FnsSuffix

/-- Closed Unified M5 compilation module (`externs := []`, `exits := []`). -/
def m5Module : LeanQbe.T.Module :=
  { fns := m5Fns, externs := [], exits := [] }

private theorem wf_app {a b : List Fn} (ha : ∀ f ∈ a, f.Wf) (hb : ∀ f ∈ b, f.Wf) :
    ∀ f ∈ a ++ b, f.Wf :=
  fun f h => (List.mem_append.mp h).elim (ha f) (hb f)

private theorem wf_take {n : Nat} {a : List Fn} (ha : ∀ f ∈ a, f.Wf) :
    ∀ f ∈ a.take n, f.Wf :=
  fun f h => ha f (List.mem_of_mem_take h)

private theorem wf_drop {n : Nat} {a : List Fn} (ha : ∀ f ∈ a, f.Wf) :
    ∀ f ∈ a.drop n, f.Wf :=
  fun f h => ha f (List.mem_of_mem_drop h)

private theorem wf_cons {x : Fn} {a : List Fn} (hx : x.Wf) (ha : ∀ f ∈ a, f.Wf) :
    ∀ f ∈ x :: a, f.Wf :=
  fun f h => (List.mem_cons.mp h).elim (fun e => e ▸ hx) (ha f)

private theorem wf_nil : ∀ f ∈ ([] : List Fn), f.Wf :=
  fun _ h => nomatch h

private theorem wf_one {x : Fn} (hx : x.Wf) : ∀ f ∈ [x], f.Wf :=
  wf_cons hx wf_nil

theorem m5OneLitConfl_wf : m5OneLitConflFn.Wf := FullM5Otfs.full_one_lit_confl_m5_wf
theorem m5Deduce1uip_wf : m5Deduce1uipFn.Wf := FullM5Otfs.full_deduce_1uip_m5_wf
theorem m5HbrDom_wf : m5HbrDomFn.Wf := FullM5Hbr.full_hbr_dom_m5_wf
theorem m5ProbePropLit_wf : m5ProbePropLitFn.Wf := FullM5ProbeProp.full_probe_prop_lit_m5_wf
theorem m5FindDefinition_wf : m5FindDefinitionFn.Wf := FullM5KittenDefFix.full_find_definition_m5_wf

theorem m5FnsPrefix_wf : ∀ f ∈ m5FnsPrefix, f.Wf := by
  unfold m5FnsPrefix
  repeat' apply wf_app
  · exact wf_take Full.fullFns_wf
  · exact wf_one FullM4InprocHot.full_wstack_defrag_m4_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM4Bump.full_bump_var_m4_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM3VivChrono.full_tick_rel_wf
  · exact wf_take FullM5Sched.m5Sched_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_cons FullM5HeurCore.full_save_target_best_m5_wf
      (wf_cons FullM5HeurCore.full_backtrack_raw_m5_wf
        (wf_one FullM5HeurCore.full_backtrack_m5_wf))
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullFastBveBudgets.fastBveBudgets_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullM5Orch.m5Orch_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_one full_init_state_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullM5Otfs.m5Otfs_fns_wf
  · exact wf_one FullM4.m4PropLitRaw_wf
  · exact wf_drop FullM5Otfs.m5Otfs_fns_wf
  · exact wf_drop FastCore.fastCore_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullFastSched.sched_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_one full_reduce_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM5HeurCore.full_analyze_rsn_m5_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_cons FullM5HeurCore.full_bump_analyzed_m5_wf
      (wf_one FullM5HeurCore.full_restore_bump_ana_m5_wf)
  · exact wf_take (wf_drop FullM5Otfs.m5Otfs_fns_wf)
  · exact wf_one FullM5HeurCore.full_otfs_subsume_m5_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_cons m5OneLitConfl_wf (wf_cons m5Deduce1uip_wf
      (wf_cons FullM5HeurCore.full_eager_subsume_m5_wf
        (wf_cons FullM5HeurCore.full_learn_clause_m5_wf
          (wf_one FullM5HeurCore.full_analyze_m5_wf))))
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM5HeurCore.full_warmup_m5_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_drop FullM5Sched.m5Sched_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM4.full_extend_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one full_add_bin_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_cons m5HbrDom_wf (wf_one m5ProbePropLit_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM3.m3ProbeRun_wf
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullM4VivBce.m4VivBce_fns_wf
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullFastBveBudgets.fastBveBudgets_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_cons FullM5DenseSafe.full_subst_rewrite_bins_m5_wf
      (wf_cons FullM5DenseSafe.full_subst_rewrite_ar_m5_wf
        (wf_cons FullM5DenseSafe.full_substitute_m5_wf
          (wf_one FullM5DenseSafe.full_enter_dense_m5_wf)))
  · exact wf_take (wf_drop Full.fullFns_wf)

theorem m5BvaFns_wf : ∀ f ∈ m5BvaFns, f.Wf := by
  unfold m5BvaFns
  repeat' apply wf_app
  · exact wf_take FullBvaHeap.bvaHeap_fns_wf
  · exact wf_cons FullM4Bva.full_bva_hop1_wf
      (wf_cons FullM4Bva.full_bva_hop2_wf (wf_one FullM4Bva.full_bva_hop3_wf))
  · exact wf_take (wf_drop FullBvaHeap.bvaHeap_fns_wf)
  · exact wf_cons FullM4Bva.full_bva_pick_cand_wf
      (wf_cons FullM4Bva.full_bva_filter_row_wf
        (wf_cons FullM5DenseSafe.full_bva_commit_m5_wf (wf_one FullM4Bva.full_bva_try_lit_wf)))
  · exact wf_take (wf_drop FullBvaHeap.bvaHeap_fns_wf)
  · exact wf_one FullM4Bva.full_factor_wf

private theorem wf_m5Kitten_all : ∀ f ∈ FullM5KittenDefFix.m5KittenDefFix_fns, f.Wf := by
  intro f hf
  simp only [FullM5KittenDefFix.m5KittenDefFix_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact FullM5KittenDefFix.full_kitten_add_clause_m5_wf
  · exact FullM5KittenDefFix.full_kitten_ana_clause_m5_wf
  · exact FullM5KittenDefFix.full_kitten_build_failing_m5_wf
  · exact FullM5KittenDefFix.full_kitten_solve_m5_wf
  · exact FullM5KittenDefFix.full_kitten_core_m5_wf
  · exact FullM5KittenDefFix.full_find_definition_m5_wf

theorem m5FnsSuffix_wf : ∀ f ∈ m5FnsSuffix, f.Wf := by
  unfold m5FnsSuffix
  repeat' (first
    | exact m5BvaFns_wf
    | exact FullM4Compact.compact_fns_wf
    | exact FullM5CongBins.m5CongBins_fns_wf
    | apply wf_app)
  · exact wf_one FullM4InprocHot.full_kitten_init_m4_wf
  · exact wf_drop Full.fullKitten_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullM5CongFix.m5CongFix_fns_wf
  · exact wf_one FullM4InprocHot.full_has_ternary_m4_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullM5CongFix.m5CongFix_fns_wf)
  · exact wf_cons FullM3CongBva.full_cong_mark_trail_wf
      (wf_cons FullM3CongBva.full_cong_unit_fold_wf
        (wf_one FullM3CongBva.full_cong_equiv_fold_wf))
  · exact wf_drop FullM5CongFix.m5CongFix_fns_wf
  · exact wf_take FullM4Sweep.fullM4Sweep_fns_wf
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM5DenseSafe.full_fwd_check_cl_m5_wf
  · exact wf_take (wf_drop FullFastBveBudgets.fastBveBudgets_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullDefSweep.full_def_sweep_fns_wf
  · exact wf_take wf_m5Kitten_all
  · exact wf_one m5FindDefinition_wf
  · exact wf_take (wf_drop FullDefSweep.full_def_sweep_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM5DenseSafe.full_bve_var_m5_wf
  · exact wf_take (wf_drop FullM4Ternary.full_m4_ternary_fns_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_drop FullM4VivBce.m4VivBce_fns_wf
  · exact wf_take (wf_drop FullFastSched.sched_fns_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_cons FullM3.m3BackboneLit_wf (wf_one FullM3.m3Backbone_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_cons FullM3CongBva.full_elim_collect_nbrs_wf
      (wf_one FullM3CongBva.full_elim_bve_wf)
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_one full_preprocess_wf
  · exact wf_take (wf_drop FullM5Orch.m5Orch_fns_wf)
  · exact wf_one full_search_wf
  · exact wf_drop FullM5Orch.m5Orch_fns_wf
  · exact wf_one kissat_solve_bytes_wf

theorem m5Fns_wf : ∀ f ∈ m5Fns, f.Wf :=
  wf_app m5FnsPrefix_wf m5FnsSuffix_wf

theorem m5Fns_length : m5Fns.length = 270 := by
  t_kernel_rfl

theorem m5_acyclic : m5Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5

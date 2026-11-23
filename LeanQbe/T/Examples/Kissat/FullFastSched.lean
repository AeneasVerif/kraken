module

public import LeanQbe.T.Examples.Kissat.Full

set_option autoImplicit false

@[expose] public section

/-!
# Kissat `D-Full` M2 Fast-Scheduler C0 Upgrades (`FullFastSched`)

Self-contained C0 scheduler upgrades over unchanged `FullHdr` (`144` `u64` words =
`4` `KissatDimacs` + `140` tail words), preserving `FullCfg`, `FullState`, `FullMem`,
and `FullInv`:
1. **Level-0 Binary-Sweep Completeness Fix**:
   - `full_sweep_bins`: guards falsified-literal binary deletion by `h->propagated >= h->trail_end`
     (always keeping unsatisfied binaries while level-0 propagation is pending) and preserves
     `0xFFFFFFFFu` sentinel fill for `WatchStackLayout`.
   - `full_substitute`: early-skips when `h->num_binary == 0ULL` (after level-0 backtrack) and
     propagates newly derived level-0 units before `full_arena_sweep`.
   - `full_enter_dense`: propagates pending level-0 units before `full_sweep_bins` and marks
     `h->inconsistent = 1ULL` on level-0 conflict.
2. **Ticks-Gated Inprocessing Schedulers**:
   - Stores `last_probe_ticks` / `last_elim_ticks` inside `FullHdr`'s unconstrained stat slots
     `fwd_sub_cnt` / `fwd_str_cnt` (saving/restoring `fwd_sub_cnt` across `full_forward_sub`).
   - Adds `full_scale_delta`, `full_min_u64`, `full_max_u64`, `full_probe_dticks`,
     `full_probe_tail`, `full_elim_dticks`, `full_elim_bve`, plus upgraded `full_probe`,
     `full_eliminate`, `full_preprocess`, `full_simplify` (with lazy `full_reduce(h, false)`),
     and `full_search`.
3. **Standalone Spliced Module (`schedModule`)**:
   - Reuses all `158` unchanged functions from `Full.fullFns`, splicing in the `3` completeness
     fixes and `12` ticks-gated scheduler functions (`173` total functions), with `Func.Wf` and
     `schedModule.checkAcyclic = true`.
-/

namespace LeanQbe.T.Examples.Kissat.FullFastSched

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

kissat_c0! sched "
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

#define PH_GARB 0x00080000u
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_ELIM_C  16u

extern u64 full_ilog10(u64 x);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_reduce(FullHdr *h, bool force);
extern u64 full_analyze(FullHdr *h);
extern u64 full_decide(FullHdr *h);
extern void full_warmup(FullHdr *h);
extern void full_rephase(FullHdr *h);
extern void full_switch_mode(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern u64 full_lucky(FullHdr *h);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_transitive(FullHdr *h);
extern u64 full_vivify(FullHdr *h, u64 tier_mode);
extern u64 full_tarjan_scc(FullHdr *h);
extern bool full_subst_elim_vars(FullHdr *h, u64 ucnt);
extern bool full_subst_rewrite_bins(FullHdr *h);
extern bool full_subst_rewrite_ar(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_congruence(FullHdr *h);
extern u64 full_sweep_sat(FullHdr *h);
extern u64 full_forward_sub(FullHdr *h);
extern u64 full_bve_var(FullHdr *h, u32 v);
extern u64 full_factor(FullHdr *h);

void full_sweep_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  bool prop_done = (h->propagated >= h->trail_end);
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    bool lsat = (lvl[l >> 1] == 0u && vals[l] > (i8)0);
    bool lfix = lsat || (prop_done && lvl[l >> 1] == 0u && vals[l] < (i8)0);
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        bool osat = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] > (i8)0);
        bool ofix = osat ||
          (prop_done && (u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] < (i8)0);
        if (lfix || ofix) {
          if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
        } else {
          wstk[q] = w0; q = q + 1ULL;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off);
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  full_wstack_defrag(h);
}

u64 full_substitute(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->num_binary == 0ULL) { return 1ULL; }
  u64 round = 0ULL;
  while (round < 4ULL && h->inconsistent == 0ULL && h->oom == 0ULL) {
    u64 before = h->subst_cnt;
    u64 ucnt = full_tarjan_scc(h);
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (!full_subst_elim_vars(h, ucnt)) { return 20ULL; }
    if (h->subst_cnt == before) { break; }
    if (!full_subst_rewrite_bins(h)) { return 20ULL; }
    if (!full_subst_rewrite_ar(h)) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    round = round + 1ULL;
  }
  return 1ULL;
}

bool full_enter_dense(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->dense_mode != 0ULL) { return true; }
  if (full_propagate(h) == 1ULL) { h->inconsistent = 1ULL; return false; }
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
          h->oom = 0ULL; full_arena_sweep(h); return false;
        }
        k = k + 1u;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  h->dense_mode = 1ULL;
  return true;
}

u64 full_scale_delta(FullHdr *h, u64 delta) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 lg = full_ilog10(clauses + 1ULL);
  u64 diff = (lg > 5ULL) ? (lg - 5ULL) : (5ULL - lg);
  u64 scale = ((diff * diff * 45ULL) / 10ULL) + 25ULL;
  return delta * scale;
}

u64 full_min_u64(u64 a, u64 b) { return (a < b) ? a : b; }

u64 full_max_u64(u64 a, u64 b) { return (a > b) ? a : b; }

u64 full_probe_dticks(FullHdr *h, bool initial) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 raw = (h->search_ticks > h->fwd_sub_cnt) ? (h->search_ticks - h->fwd_sub_cnt) : 0ULL;
  u64 dticks = initial ? ((h->cur_vars + clauses) * 8ULL) : raw;
  return full_max_u64(dticks, 4000ULL);
}

u64 full_probe_tail(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL && full_transitive(h) == 20ULL) { return 20ULL; }
  u64 pbud = full_min_u64(8ULL + (dticks >> 10), 64ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 1ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 2ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 0ULL) == 20ULL) { return 20ULL; }
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
    if (full_congruence(h) == 20ULL) { return 20ULL; }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
    if (full_sweep_sat(h) == 20ULL) { return 20ULL; }
  }
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
  if (!initial && full_probe_tail(h, dticks) == 20ULL) { return 20ULL; }
  h->fwd_sub_cnt = h->search_ticks;
  return 1ULL;
}

u64 full_elim_dticks(FullHdr *h, bool initial) {
  if (initial) { return (h->cur_vars + h->num_irred + h->num_binary) * 12ULL; }
  return (h->search_ticks > h->fwd_str_cnt) ? (h->search_ticks - h->fwd_str_cnt) : 0ULL;
}

u64 full_elim_bve(FullHdr *h, u64 bve_lim) {
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u64 cv = h->cur_vars;
  u64 v = 0ULL; u64 tried = 0ULL; u64 res = 1ULL;
  while (v < cv && tried < bve_lim && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_ELIM_C); tried = tried + 1ULL;
      u64 br = full_bve_var(h, (u32)v);
      if (br == 20ULL) { res = 20ULL; break; }
      if (br == 2ULL) { break; }
    }
    v = v + 1ULL;
  }
  return res;
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
  u64 fs = full_forward_sub(h);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) { full_rebuild_watches(h); return 20ULL; }
  u64 bve_lim =
    full_min_u64(initial ? (h->cur_vars + 256ULL) : (64ULL + (dticks >> 7)), h->cur_vars);
  u64 res = full_elim_bve(h, bve_lim);
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 1024ULL)) {
    full_factor(h);
  }
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_preprocess(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_scale_delta(h, 120ULL);
  if (h->num_binary == 0ULL && h->cur_vars >= 48ULL && h->arena_len == h->num_irred * 6ULL) {
    return 1ULL;
  }
  if (full_probe(h, true) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_scale_delta(h, 120ULL);
  return 1ULL;
}

u64 full_simplify(FullHdr *h, bool do_probe, bool do_elim) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (full_reduce(h, false) == 20ULL) { return 20ULL; }
  if (do_probe && full_probe(h, false) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (do_elim && full_eliminate(h, false) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  return 1ULL;
}

u64 full_search(FullHdr *h) {
  u64 lk = full_lucky(h);
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  full_warmup(h);
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
      full_switch_mode(h);
      if (h->conflicts >= h->rephase_limit) { full_rephase(h); }
      if (h->conflicts >= h->reduce_limit) {
        u64 rr = full_reduce(h, false);
        if (rr == 20ULL) { return 20ULL; }
        if (rr != 1ULL) { return 0ULL; }
      }
      bool due_p = (h->conflicts >= h->probe_limit);
      bool due_e = (h->conflicts >= h->elim_limit);
      if (due_p || due_e) {
        u64 sr = full_simplify(h, due_p, due_e);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      } else if (full_restart_due(h) != 0ULL) { full_restart(h); }
    } else {
      if (h->unassigned == 0ULL) { return 10ULL; }
      if (full_decide(h) == 0ULL) { return (h->unassigned == 0ULL) ? 10ULL : 0ULL; }
    }
  }
}
"

theorem full_sweep_bins_wf : Func.Wf full_sweep_bins_body := by t_wf_reify
theorem full_substitute_wf : Func.Wf full_substitute_body := by t_wf_reify
theorem full_enter_dense_wf : Func.Wf full_enter_dense_body := by t_wf_reify
theorem full_scale_delta_wf : Func.Wf full_scale_delta_body := by t_wf_reify
theorem full_min_u64_wf : Func.Wf full_min_u64_body := by t_wf_reify
theorem full_max_u64_wf : Func.Wf full_max_u64_body := by t_wf_reify
theorem full_probe_dticks_wf : Func.Wf full_probe_dticks_body := by t_wf_reify
theorem full_probe_tail_wf : Func.Wf full_probe_tail_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify
theorem full_elim_dticks_wf : Func.Wf full_elim_dticks_body := by t_wf_reify
theorem full_elim_bve_wf : Func.Wf full_elim_bve_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify
theorem full_simplify_wf : Func.Wf full_simplify_body := by t_wf_reify
theorem full_search_wf : Func.Wf full_search_body := by t_wf_reify

theorem sched_fns_wf : ∀ f ∈ sched_fns, f.Wf := by
  simp only [sched_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_sweep_bins_wf, full_substitute_wf, full_enter_dense_wf, full_scale_delta_wf,
    full_min_u64_wf, full_max_u64_wf, full_probe_dticks_wf, full_probe_tail_wf, full_probe_wf,
    full_elim_dticks_wf, full_elim_bve_wf, full_eliminate_wf, full_preprocess_wf,
    full_simplify_wf, full_search_wf⟩

/-- Standalone spliced function list reusing all `158` unchanged `Full.fullFns` functions,
replacing `full_sweep_bins`, `full_substitute`, `full_enter_dense`, and the `5` top schedulers
with the `15` M2 fast-scheduler functions (`173` total functions in strict acyclic order). -/
def schedSplicedFns : List Fn :=
  Full.fullFns.take 57 ++ sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 67 ++ (sched_fns.drop 1).take 2 ++
  (Full.fullFns.drop 127).take 33 ++ sched_fns.drop 3 ++ Full.fullFns.drop 165

/-- Standalone spliced `LeanQbe.T.Module` directly testable against `bench/kissat/run_full.sh`. -/
def schedModule : LeanQbe.T.Module :=
  { fns := schedSplicedFns, externs := [], exits := [] }

theorem schedSplicedFns_wf : ∀ f ∈ schedSplicedFns, f.Wf := by
  intro f hf
  simp only [schedSplicedFns, List.mem_append] at hf
  rcases hf with (((((h | h) | h) | h) | h) | h) | h
  · exact Full.fullFns_wf f (List.mem_of_mem_take h)
  · exact sched_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact sched_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact sched_fns_wf f (List.mem_of_mem_drop h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop h)

theorem sched_acyclic : schedModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullFastSched

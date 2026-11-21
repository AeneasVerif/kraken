module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M3c Upgrades: Binary-Implication Backbone & Persistent `probe_run` Cursor

Strictly standalone new C0 definitions (zero edits to `Full*` or `FullFast*`, zero layout churn on
the frozen `144`-word `FullHdr` geometry):
1. **`full_probe_run(h, budget)`**: persistent wrap-around variable cursor stored in `FullScratch`'s
   unused `h->iterating` slot (initialized to `0ULL` by `full_init_hdr`), eliminating the `0..64`
   reset cliff so variables `>= 64` are probed across rounds without starving tail variables.
2. **`full_backbone_lit(h, cand)` & `full_backbone(h, tick_lim)`**: Kissat 4.0 `backbone.c`
   binary-implication unit discovery using `FL_BONE0` / `FL_BONE1` flags, tick-budgeted BIG BFS
   over binary watches (`PW_BIN_FLAG`), clean trail unwind, entailed level-0 unit assertion via
   `full_add_unit` + `full_propagate`, multi-round cascading (up to `4` sweeps when new units are
   derived), and persistent `backbone_units` telemetry in unused `h->delayed_len`.
3. **Spliced Closed Modules (`externs := []`, `exits := []`)**:
   - `m3BackboneLocalModule` (`5` upgraded/new fns + `14` externs): focused M3c compilation unit.
   - `m3BackboneFastModule` (`198` fns): splices all `5` M3c upgrades (`full_probe_run`,
     `full_backbone_lit`, `full_backbone`, `full_probe_tail`, `full_probe`) onto
     `FullFast.fastFns` in strict topological call order.
   - `m3BackboneFullModule` (`168` fns): splices `full_probe_run`, `full_backbone_lit`,
     `full_backbone`, and 1-arg `FullProbeFull.full_probe` onto `Full.fullFns` for unconditional
     `168/168` closed-module `ModuleOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3Backbone

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m3Backbone "
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

#define FL_ACTIVE  1u
#define FL_BONE0   128u
#define FL_BONE1   256u

extern u64 full_ilog10(u64 x);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_probe_assume_pair(FullHdr *h, u32 lit);
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

u64 full_probe_run(FullHdr *h, u64 budget) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  if (budget == 0ULL || h->num_binary == 0ULL || cv == 0ULL) {
    h->probing = 0ULL; return 1ULL;
  }
  h->probing = 1ULL;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 v = h->iterating;
  if (v >= cv) { v = 0ULL; }
  u64 scanned = 0ULL;
  u64 done = 0ULL;
  u64 res = 1ULL;
  while (scanned < cv && done < budget && h->fuel > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u64 st = full_probe_assume_pair(h, (u32)(v << 1));
      done = done + 1ULL;
      if (st == 20ULL) { res = 20ULL; break; }
      if (st == 2ULL) { break; }
    }
    v = v + 1ULL;
    if (v >= cv) { v = 0ULL; }
    scanned = scanned + 1ULL;
  }
  h->iterating = v;
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 0ULL;
  return res;
}

u64 full_backbone_lit(FullHdr *h, u32 cand) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)cand >= nlits) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  if (vals[cand] != (i8)0) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u64 csz = (u64)wvec[((u64)cand << 1) + 1ULL];
  if (csz == 0ULL) { return 0ULL; }
  u64 ticks = h->ant_sz;
  if (ticks == 0ULL) { return 0ULL; }
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *trl = (u32 *)h->trail;
  u32 not_cand = cand ^ 1u;
  u64 saved = h->trail_end;
  u64 prop = saved;
  bool failed = false;
  vals[not_cand] = (i8)1;
  vals[cand] = (i8)(-1);
  trl[saved] = not_cand;
  h->trail_end = saved + 1ULL;
  while (!failed && prop < h->trail_end && ticks > 0ULL) {
    u32 lit = trl[prop];
    prop = prop + 1ULL;
    u32 nl = lit ^ 1u;
    u64 loff = (u64)wvec[(u64)nl << 1];
    u64 lend = loff + (u64)wvec[((u64)nl << 1) + 1ULL];
    u64 q = loff;
    while (q < lend && ticks > 0ULL) {
      u32 qw = wstk[q];
      ticks = ticks - 1ULL;
      if ((qw & PW_BIN_FLAG) == 0u) { q = q + 2ULL; continue; }
      u32 ot = qw & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        if (vals[ot] < (i8)0) { failed = true; break; }
        if (vals[ot] == (i8)0 && h->trail_end < h->max_vars) {
          vals[ot] = (i8)1;
          vals[ot ^ 1u] = (i8)(-1);
          trl[h->trail_end] = ot;
          h->trail_end = h->trail_end + 1ULL;
        }
      }
      q = q + 1ULL;
    }
  }
  while (h->trail_end > saved) {
    h->trail_end = h->trail_end - 1ULL;
    u32 ul = trl[h->trail_end];
    vals[ul] = (i8)0;
    vals[ul ^ 1u] = (i8)0;
  }
  h->ant_sz = ticks;
  if (failed) {
    if (!full_add_unit(h, cand)) { return 20ULL; }
    return 1ULL;
  }
  return 0ULL;
}

u64 full_backbone(FullHdr *h, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  if (h->num_binary == 0ULL || tick_lim == 0ULL || cv == 0ULL) {
    h->probing = 0ULL; return 1ULL;
  }
  h->probing = 1ULL;
  u64 pr0 = full_propagate(h);
  if (pr0 == 1ULL) { h->probing = 0ULL; return 20ULL; }
  if (pr0 == 2ULL) { h->probing = 0ULL; return 1ULL; }
  h->ant_sz = tick_lim;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 res = 1ULL;
  u64 round = 0ULL;
  while (round < 4ULL && h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u64 found = 0ULL;
    u64 v = 0ULL;
    while (v < cv && h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        if ((fl[v] & FL_BONE0) != 0u) {
          u64 br0 = full_backbone_lit(h, (u32)(v << 1));
          if (br0 == 20ULL) { res = 20ULL; break; }
          if (h->ant_sz > 0ULL) { fl[v] = fl[v] & (~FL_BONE0); }
          if (br0 == 1ULL) {
            found = found + 1ULL;
            h->delayed_len = h->delayed_len + 1ULL;
            u64 p0 = full_propagate(h);
            if (p0 == 1ULL) { res = 20ULL; break; }
            if (p0 == 2ULL) { break; }
          }
        }
        if (vals[v << 1] == (i8)0 && (fl[v] & FL_BONE1) != 0u &&
            h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
          u64 br1 = full_backbone_lit(h, (u32)((v << 1) | 1ULL));
          if (br1 == 20ULL) { res = 20ULL; break; }
          if (h->ant_sz > 0ULL) { fl[v] = fl[v] & (~FL_BONE1); }
          if (br1 == 1ULL) {
            found = found + 1ULL;
            h->delayed_len = h->delayed_len + 1ULL;
            u64 p1 = full_propagate(h);
            if (p1 == 1ULL) { res = 20ULL; break; }
            if (p1 == 2ULL) { break; }
          }
        }
      }
      v = v + 1ULL;
    }
    if (res == 20ULL || h->oom != 0ULL || h->fuel == 0ULL) { break; }
    if (v >= cv && h->ant_sz > 0ULL) {
      u64 r = 0ULL;
      while (r < cv) {
        if ((fl[r] & FL_ACTIVE) != 0u && vals[r << 1] == (i8)0) {
          fl[r] = fl[r] | FL_BONE0 | FL_BONE1;
        }
        r = r + 1ULL;
      }
    }
    if (found == 0ULL) { break; }
    round = round + 1ULL;
  }
  h->probing = 0ULL;
  return res;
}

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

namespace FullProbeFull

kissat_c0! fullProbeM3 "
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

extern u64 full_isqrt(u64 x);
extern u64 full_substitute(FullHdr *h);
extern u64 full_congruence(FullHdr *h);
extern u64 full_sweep_sat(FullHdr *h);
extern u64 full_transitive(FullHdr *h);
extern u64 full_backbone(FullHdr *h, u64 tick_lim);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_vivify(FullHdr *h, u64 tier_mode);

u64 full_probe(FullHdr *h) {
  h->probings = h->probings + 1ULL;
  h->probe_limit = h->conflicts + 500ULL * full_isqrt(h->probings);
  if (full_substitute(h) == 20ULL) { return 20ULL; }
  if (full_congruence(h) == 20ULL) { return 20ULL; }
  if (full_substitute(h) == 20ULL) { return 20ULL; }
  if (full_sweep_sat(h) == 20ULL) { return 20ULL; }
  if (full_backbone(h, 200000ULL) == 20ULL) { return 20ULL; }
  if (full_transitive(h) == 20ULL) { return 20ULL; }
  if (full_probe_run(h, 64ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 1ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 2ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 0ULL) == 20ULL) { return 20ULL; }
  return 1ULL;
}
"

theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify

theorem fullProbeM3_fns_wf : ∀ f ∈ fullProbeM3_fns, f.Wf := by
  simp only [fullProbeM3_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact full_probe_wf

end FullProbeFull

/-! ## `Func.Wf` Proofs & Spliced Modules -/

theorem full_probe_run_wf : Func.Wf full_probe_run_body := by t_wf_reify
theorem full_backbone_lit_wf : Func.Wf full_backbone_lit_body := by t_wf_reify
theorem full_backbone_wf : Func.Wf full_backbone_body := by t_wf_reify
theorem full_probe_tail_wf : Func.Wf full_probe_tail_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify

theorem m3Backbone_fns_wf : ∀ f ∈ m3Backbone_fns, f.Wf := by
  simp only [m3Backbone_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_probe_run_wf, full_backbone_lit_wf, full_backbone_wf,
    full_probe_tail_wf, full_probe_wf⟩

/-- Extern signature list for the standalone `5`-function M3c compilation unit. -/
def m3BackboneExterns : List Extern :=
  [ ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_probe_assume_pair", [i64, i32], [i64]⟩
  , ⟨"full_transitive", [i64, i64], [i64]⟩
  , ⟨"full_vivify", [i64, i64, i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64]⟩ ]

/-- Standalone `5`-function M3c module with explicit `FullFast` externs. -/
def m3BackboneLocalModule : LeanQbe.T.Module :=
  { fns := m3Backbone_fns, externs := m3BackboneExterns, exits := [] }

theorem m3BackboneLocal_acyclic : m3BackboneLocalModule.checkAcyclic = true := by
  t_kernel_rfl

/-- Unified M3c + M2 `FullFast` function list (`198` functions in strict topological call order):
replaces `full_probe_run` (`[111]`), `full_probe_tail`, and `full_probe` (`[187..188]`), inserting
`full_backbone_lit` and `full_backbone` directly ahead of `full_probe_tail`. -/
def m3BackboneFastFns : List Fn :=
  FullFast.fastFns.take 111 ++
  m3Backbone_fns.take 1 ++
  (FullFast.fastFns.drop 112).take 75 ++
  m3Backbone_fns.drop 1 ++
  FullFast.fastFns.drop 189

/-- Closed M3c + M2 `FullFast` compilation module (`externs := []`, `exits := []`). -/
def m3BackboneFastModule : LeanQbe.T.Module :=
  { fns := m3BackboneFastFns, externs := [], exits := [] }

theorem m3BackboneFastFns_wf : ∀ f ∈ m3BackboneFastFns, f.Wf := by
  intro f hf
  simp only [m3BackboneFastFns, List.mem_append] at hf
  rcases hf with (((h | h) | h) | h) | h
  · exact FullFast.fastFns_wf f (List.mem_of_mem_take h)
  · exact m3Backbone_fns_wf f (List.mem_of_mem_take h)
  · exact FullFast.fastFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact m3Backbone_fns_wf f (List.mem_of_mem_drop h)
  · exact FullFast.fastFns_wf f (List.mem_of_mem_drop h)

theorem m3BackboneFast_acyclic : m3BackboneFastModule.checkAcyclic = true := by
  t_kernel_rfl

/-- Closed M3c + `D-Full` function list (`168` functions in strict topological call order):
splices wrap-around `full_probe_run`, `full_backbone_lit`, `full_backbone`, and
`FullProbeFull.full_probe` onto `Full.fullFns` for unconditional `168/168` `ModuleOk`. -/
def m3BackboneFullFns : List Fn :=
  Full.fullFns.take 111 ++
  m3Backbone_fns.take 1 ++
  (Full.fullFns.drop 112).take 2 ++
  (m3Backbone_fns.drop 1).take 2 ++
  (Full.fullFns.drop 114).take 46 ++
  FullProbeFull.fullProbeM3_fns ++
  Full.fullFns.drop 161

/-- Closed M3c + `D-Full` compilation module (`externs := []`, `exits := []`). -/
def m3BackboneFullModule : LeanQbe.T.Module :=
  { fns := m3BackboneFullFns, externs := [], exits := [] }

theorem m3BackboneFullFns_wf : ∀ f ∈ m3BackboneFullFns, f.Wf := by
  intro f hf
  simp only [m3BackboneFullFns, List.mem_append] at hf
  rcases hf with (((((h | h) | h) | h) | h) | h) | h
  · exact Full.fullFns_wf f (List.mem_of_mem_take h)
  · exact m3Backbone_fns_wf f (List.mem_of_mem_take h)
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact m3Backbone_fns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Full.fullFns_wf f (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact FullProbeFull.fullProbeM3_fns_wf f h
  · exact Full.fullFns_wf f (List.mem_of_mem_drop h)

theorem m3BackboneFull_acyclic : m3BackboneFullModule.checkAcyclic = true := by
  t_kernel_rfl

private theorem m3Backbone_len : m3Backbone_fns.length = 5 := by t_kernel_rfl
private theorem fullProbeM3_len : FullProbeFull.fullProbeM3_fns.length = 1 := by t_kernel_rfl
private theorem fullFns_len : Full.fullFns.length = 166 := by t_kernel_rfl

theorem m3BackboneFastFns_length : m3BackboneFastFns.length = 198 := by
  simp [m3BackboneFastFns, FullFast.fastFns_length, m3Backbone_len]

theorem m3BackboneFullFns_length : m3BackboneFullFns.length = 168 := by
  simp [m3BackboneFullFns, fullFns_len, m3Backbone_len, fullProbeM3_len]

end LeanQbe.T.Examples.Kissat.FullM3Backbone

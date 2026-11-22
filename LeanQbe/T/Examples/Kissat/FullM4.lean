module

public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Examples.Kissat.FullM4Compact
public import LeanQbe.T.Examples.Kissat.FullM4Ternary
public import LeanQbe.T.Examples.Kissat.FullM4Bva
public import LeanQbe.T.Examples.Kissat.FullM4Bcp
public import LeanQbe.T.Examples.Kissat.FullM4Bump
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` Unified M4 Solver (`FullM4`, `231` Functions)

Splices the verified zero-regression M4 slices (`M4a`, `M4c`, `M4d`, `M4e`, `M4g`)
onto `FullM3` in strict topological call order (`externs := []`, `exits := []`):
- **M4a (`FullM4Compact`)**: dead-variable compaction + arena sweep in `full_preprocess`/`simplify`,
  with `d.mv`/`bva_cap` rebase in `full_preprocess`/`full_simplify`, restore in
  `kissat_solve_bytes` after `full_extend`, and `EXT_COMPACT_FLAG` + `[0..max_vars)` decoding.
- **M4d (`FullM4Bva`)**: `256 x 32` BVA, pre-BVE `full_factor` only (post-BVE factor skipped per
  Tier-1 ablation), capped `elim_limit`.
- **M4c (`FullM4Ternary`)**: trail reason promotion on periodic `full_reduce(h, false)` (`!force`
  preserving `work_stk2` on `full_learn_clause`'s `full_reduce(h, true)`), hyper-ternary in
  `full_probe`, and variable/clause reorder in `full_simplify` gated by `conflicts >= 10000`.
- **M4e (`FullM4Bcp`)**: sentinel-tail `full_prop_lit_m4` spliced as `full_prop_lit_raw` under
  M3a chrono wrapper `FullM3VivChrono.m3PropLitFn`.
- **M4g (`FullM4Bump`)**: focused-mode `full_heap_up` elision in `full_bump_var`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m4Orch "
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

#define PH_GLUE_MASK     0x7FFFFu
#define PH_GARB          0x00080000u
#define PH_RSN           0x00200000u
#define PH_RED           0x00400000u
#define PW_LIT_MASK      0x7FFFFFFFu
#define FL_ELIM          2u
#define FL_SUBST         4u
#define EXT_BLK_FLAG     0x80000000u
#define EXT_COMPACT_FLAG 0x40000000u
#define EXT_CNT_MASK     0x3FFFFFFFu

extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d, i8 *vals, u64 mv_max);
extern u64 full_isqrt(u64 x);
extern u64 full_ilog10(u64 x);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel);
extern u64 full_parse_body(FullHdr *h, u64 cnf_end);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_promote_reasons(FullHdr *h);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_backbone(FullHdr *h, u64 tick_lim);
extern u64 full_transitive(FullHdr *h, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_ternary(FullHdr *h, u64 rounds, u64 budget);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_probe_dticks(FullHdr *h, bool initial);
extern u64 full_probe_tail(FullHdr *h, u64 dticks);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_elim_bve(FullHdr *h, u64 bve_lim);
extern u64 full_factor(FullHdr *h, u64 budget);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);
extern u64 full_reorder(FullHdr *h, u64 budget);
extern u64 full_search(FullHdr *h);

u64 full_reduce(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + 1000ULL * full_isqrt(h->reductions);
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  if (!force && h->cur_level > 0ULL) { full_promote_reasons(h); }
  full_recompute_tiers(h);
  full_mark_reasons(h, true);
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 rc = 0ULL; u64 p = 0ULL;
  u64 t1 = h->tier1; u64 t2 = h->tier2;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 n = full_arena_next(h, (u32)p);
    if ((hdr & PH_RED) != 0u && (hdr & PH_GARB) == 0u) {
      u32 old_u = (hdr >> 27) & 31u;
      if (old_u > 0u) { ar[p] = (hdr & 0x07FFFFFFu) | ((old_u - 1u) << 27); }
      if ((hdr & PH_RSN) == 0u) {
        u64 glue = (u64)(hdr & PH_GLUE_MASK);
        bool keep = (glue <= t1 && old_u > 0u) || (glue <= t2 && old_u >= 30u);
        if (!keep && rc < h->red_cap) { rr[rc] = (u32)p; rc = rc + 1ULL; }
      }
    }
    p = (u64)n;
  }
  if (rc > 0ULL) {
    full_sort_reds(h, rc);
    u64 logv = full_ilog10(h->reductions + 9ULL);
    u64 target = (rc * (900ULL - (400ULL / logv))) / 1000ULL;
    u64 i = 0ULL;
    while (i < target && i < rc) {
      u64 cref = (u64)rr[i]; u32 hdr = ar[cref];
      if ((hdr & PH_GARB) == 0u) {
        ar[cref] = hdr | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[cref + 2ULL];
      }
      i = i + 1ULL;
    }
  }
  if (force || (h->unflushed == 0ULL &&
      (h->arena_garbage * 4ULL >= h->arena_len ||
       h->arena_len * 5ULL >= h->arena_cap * 4ULL))) {
    while (true) {
      u64 sr = full_arena_sweep(h);
      if (sr == 2ULL) { return 20ULL; }
      if (sr == 3ULL) { return 0ULL; }
      if (sr == 0ULL) { break; }
      u64 pr = full_propagate(h);
      if (pr == 1ULL) { return 20ULL; }
      if (pr != 0ULL) { return 0ULL; }
      h->unflushed = 0ULL;
    }
  } else { full_mark_reasons(h, false); }
  return 1ULL;
}

void full_extend(FullHdr *h) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ext = (u32 *)h->extend_stk;
  u64 mx = h->max_vars;
  u64 v = 0ULL;
  while (v < mx) {
    if ((fl[v] & (FL_ELIM | FL_SUBST)) != 0u || vals[v << 1] == (i8)0) {
      vals[v << 1] = (i8)1; vals[(v << 1) | 1ULL] = (i8)(-1);
    }
    v = v + 1ULL;
  }
  u64 end = h->extend_len;
  while (end > 0ULL) {
    u64 start = end;
    while (start > 0ULL) {
      start = start - 1ULL;
      if ((ext[start] & EXT_BLK_FLAG) != 0u) { break; }
    }
    u32 head = ext[start];
    if ((head & EXT_COMPACT_FLAG) != 0u) {
      u64 ncv = (u64)(head & EXT_CNT_MASK);
      if (start + 1ULL + ncv <= end && ncv <= mx) {
        u64 k = ncv;
        while (k > 0ULL) {
          k = k - 1ULL;
          u32 ov = ext[start + 1ULL + k];
          if ((u64)ov < mx) {
            i8 pv = vals[k << 1];
            i8 nv = vals[(k << 1) | 1ULL];
            vals[(u64)ov << 1] = pv;
            vals[((u64)ov << 1) | 1ULL] = nv;
          }
        }
        u64 j = 0ULL;
        u64 g = 0ULL;
        while (g < mx) {
          u64 nxt = (j < ncv) ? (u64)ext[start + 1ULL + j] : mx;
          if (g == nxt) { j = j + 1ULL; }
          else { vals[g << 1] = (i8)1; vals[(g << 1) | 1ULL] = (i8)(-1); }
          g = g + 1ULL;
        }
      }
    } else {
      bool sat = false;
      u64 p = start;
      while (p < end) {
        u32 lit = ext[p] & PW_LIT_MASK;
        if ((u64)(lit >> 1) < mx && vals[lit] > (i8)0) { sat = true; break; }
        p = p + 1ULL;
      }
      u32 blk = head & PW_LIT_MASK;
      if (!sat && (u64)(blk >> 1) < mx) {
        vals[blk] = (i8)1; vals[blk ^ 1u] = (i8)(-1);
      }
    }
    end = start;
  }
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
  if (h->num_irred > 0ULL && full_ternary(h, 2ULL, 4096ULL) == 20ULL) { return 20ULL; }
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

u64 full_eliminate(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    u64 d_scale = full_scale_delta(h, 250ULL * h->eliminations * loge);
    u64 d_cap = 4000ULL * full_isqrt(h->eliminations) * loge;
    h->elim_limit = h->conflicts + full_min_u64(d_scale, d_cap);
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
  u64 fact_bud = full_min_u64(initial ? 512ULL : (64ULL + (dticks >> 9)), 1024ULL);
  if (h->num_binary > 0ULL || h->num_irred <= 4096ULL) {
    full_factor(h, fact_bud);
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = initial ? (cv * 4ULL + 256ULL) : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve(h, bve_lim);
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
  h->elim_limit = full_min_u64(full_scale_delta(h, 120ULL), 6000ULL);
  if (full_probe(h, true) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_min_u64(full_scale_delta(h, 120ULL), 6000ULL);
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
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->conflicts >= 10000ULL) { full_reorder(h, 256ULL); }
  return 1ULL;
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + (u64)sizeof(FullHdr)) { return 0ULL; }
  u64 hdr_addr = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  if (!full_init_state(cnf_ptr, cnf_end, hdr_addr, avail, fuel)) { return 0ULL; }
  FullHdr *h = (FullHdr *)hdr_addr;
  u64 pb = full_parse_body(h, cnf_end);
  if (pb != 1ULL) { return pb; }
  u64 orig_mv = h->d.mv;
  u64 pp = full_preprocess(h);
  if (pp == 20ULL) { return 20ULL; }
  u64 r = (pp == 10ULL) ? 10ULL : ((pp == 0ULL) ? 0ULL : full_search(h));
  if (r == 10ULL) {
    full_extend(h);
    h->d.mv = orig_mv;
    h->bva_cap = h->max_vars - orig_mv;
    u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, orig_mv);
    return (ok == 1ULL) ? 10ULL : 0ULL;
  }
  return r;
}
"

theorem full_reduce_wf : Func.Wf full_reduce_body := by t_wf_reify
theorem full_extend_wf : Func.Wf full_extend_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify
theorem full_simplify_wf : Func.Wf full_simplify_body := by t_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

theorem m4Orch_fns_wf : ∀ f ∈ m4Orch_fns, f.Wf := by
  simp only [m4Orch_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_reduce_wf, full_extend_wf, full_probe_wf, full_eliminate_wf,
    full_preprocess_wf, full_simplify_wf, kissat_solve_bytes_wf⟩

/-! ## Named `Fn` Handles & Unified `231`-Function `m4Fns` Splicing Layout -/

def m4PropLitRawFn : Fn :=
  ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], FullM4Bcp.full_prop_lit_m4_body⟩

def m4ReduceFn : Fn := ⟨"full_reduce", [i64, .bool], [i64], full_reduce_body⟩
def m4ExtendFn : Fn := ⟨"full_extend", [i64], [], full_extend_body⟩
def m4ProbeFn : Fn := ⟨"full_probe", [i64, .bool], [i64], full_probe_body⟩
def m4EliminateFn : Fn := ⟨"full_eliminate", [i64, .bool], [i64], full_eliminate_body⟩
def m4PreprocessFn : Fn := ⟨"full_preprocess", [i64], [i64], full_preprocess_body⟩
def m4SimplifyFn : Fn := ⟨"full_simplify", [i64, .bool, .bool], [i64], full_simplify_body⟩
def m4SolveBytesFn : Fn :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], kissat_solve_bytes_body⟩

theorem m4PropLitRaw_wf : m4PropLitRawFn.Wf := FullM4Bcp.full_prop_lit_m4_wf

def m4PromoteFns : List Fn := FullM4Ternary.full_m4_ternary_fns.take 3
def m4ReorderTernaryFns : List Fn := FullM4Ternary.full_m4_ternary_fns.drop 3

def m4BvaFns : List Fn :=
  FullBvaHeap.bvaHeap_fns.take 1 ++
  [FullM4Bva.m4Hop1Fn, FullM4Bva.m4Hop2Fn, FullM4Bva.m4Hop3Fn] ++
  (FullBvaHeap.bvaHeap_fns.drop 4).take 2 ++
  [FullM4Bva.m4PickCandFn, FullM4Bva.m4FilterRowFn, FullM4Bva.m4CommitFn,
   FullM4Bva.m4TryLitFn] ++
  (FullBvaHeap.bvaHeap_fns.drop 10).take 2 ++
  [FullM4Bva.m4FactorFn]

/-- Unified M4 prefix `[0..132)` in strict topological call order. -/
def m4FnsPrefix : List Fn :=
  Full.fullFns.take 21 ++
  [FullM4Bump.m4BumpVarFn] ++
  (Full.fullFns.drop 22).take 3 ++
  [FullM3VivChrono.m3TickRelFn] ++
  (Full.fullFns.drop 26).take 10 ++
  FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  (Full.fullFns.drop 37).take 10 ++
  [m4PropLitRawFn, FullM3VivChrono.m3PropLitFn] ++
  FastCore.fastCore_fns.drop 1 ++
  (Full.fullFns.drop 50).take 7 ++
  FullFastSched.sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 3 ++
  m4PromoteFns ++
  [m4ReduceFn] ++
  (Full.fullFns.drop 62).take 1 ++
  [FullM3VivChrono.m3AnalyzeRsnFn] ++
  (Full.fullFns.drop 64).take 32 ++
  [m4ExtendFn] ++
  (Full.fullFns.drop 97).take 14 ++
  [FullM3.m3ProbeRunFn] ++
  (Full.fullFns.drop 112).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
  (Full.fullFns.drop 114).take 5 ++
  [FullM3VivChrono.m3VivifyFn] ++
  (Full.fullFns.drop 120).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
  (Full.fullFns.drop 122).take 3 ++
  (FullFastSched.sched_fns.drop 1).take 2 ++
  (Full.fullFns.drop 127).take 1

/-- Unified M4 suffix `[132..231)` in strict topological call order. -/
def m4FnsSuffix : List Fn :=
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
  m4BvaFns ++
  FullM4Compact.compact_fns ++
  m4ReorderTernaryFns ++
  (FullFastSched.sched_fns.drop 3).take 4 ++
  [FullM3.m3BackboneLitFn, FullM3.m3BackboneFn, FullM3.m3ProbeTailFn, m4ProbeFn] ++
  (FullFastSched.sched_fns.drop 9).take 1 ++
  [ FullM3CongBva.m3ElimCollectNbrsFn
  , FullM3CongBva.m3ElimBveFn
  , m4EliminateFn
  , m4PreprocessFn
  , m4SimplifyFn ] ++
  FullFastSched.sched_fns.drop 14 ++
  [m4SolveBytesFn]

/-- Complete Unified M4 function list (`231` functions in strict topological call order). -/
def m4Fns : List Fn := m4FnsPrefix ++ m4FnsSuffix

/-- Closed Unified M4 compilation module (`externs := []`, `exits := []`). -/
def m4Module : LeanQbe.T.Module :=
  { fns := m4Fns, externs := [], exits := [] }

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

theorem m4FnsPrefix_wf : ∀ f ∈ m4FnsPrefix, f.Wf := by
  unfold m4FnsPrefix m4PromoteFns
  repeat' apply wf_app
  · exact wf_take Full.fullFns_wf
  · exact wf_one FullM4Bump.full_bump_var_m4_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM3VivChrono.full_tick_rel_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullFastBveBudgets.fastBveBudgets_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_cons m4PropLitRaw_wf (wf_one FullM3VivChrono.full_prop_lit_wf)
  · exact wf_drop FastCore.fastCore_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullFastSched.sched_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullM4Ternary.full_m4_ternary_fns_wf
  · exact wf_one full_reduce_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM3VivChrono.full_analyze_rsn_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one full_extend_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM3.m3ProbeRun_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullFastBveBudgets.fastBveBudgets_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_one FullM3VivChrono.full_vivify_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullFastBveBudgets.fastBveBudgets_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullFastSched.sched_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)

theorem m4BvaFns_wf : ∀ f ∈ m4BvaFns, f.Wf := by
  unfold m4BvaFns
  repeat' apply wf_app
  · exact wf_take FullBvaHeap.bvaHeap_fns_wf
  · exact wf_cons FullM4Bva.full_bva_hop1_wf
      (wf_cons FullM4Bva.full_bva_hop2_wf (wf_one FullM4Bva.full_bva_hop3_wf))
  · exact wf_take (wf_drop FullBvaHeap.bvaHeap_fns_wf)
  · exact wf_cons FullM4Bva.full_bva_pick_cand_wf
      (wf_cons FullM4Bva.full_bva_filter_row_wf
        (wf_cons FullM4Bva.full_bva_commit_wf (wf_one FullM4Bva.full_bva_try_lit_wf)))
  · exact wf_take (wf_drop FullBvaHeap.bvaHeap_fns_wf)
  · exact wf_one FullM4Bva.full_factor_wf

theorem m4FnsSuffix_wf : ∀ f ∈ m4FnsSuffix, f.Wf := by
  unfold m4FnsSuffix m4ReorderTernaryFns
  repeat' (first
    | exact m4BvaFns_wf
    | exact FullM4Compact.compact_fns_wf
    | apply wf_app)
  · exact Full.fullKitten_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullDefSweep.full_def_sweep_fns_wf)
  · exact wf_cons FullM3CongBva.full_cong_mark_trail_wf
      (wf_cons FullM3CongBva.full_cong_unit_fold_wf
        (wf_cons FullM3CongBva.full_cong_equiv_fold_wf
          (wf_cons FullM3CongBva.full_cong_and_match_wf
            (wf_cons FullM3CongBva.full_cong_work_step_wf
              (wf_one FullM3CongBva.full_congruence_dense_wf)))))
  · exact wf_drop FullDefSweep.full_def_sweep_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take (wf_drop FullFastBveBudgets.fastBveBudgets_fns_wf)
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_take FullDefSweep.full_def_sweep_fns_wf
  · exact wf_take (wf_drop Full.fullFns_wf)
  · exact wf_drop FullFastBveBudgets.fastBveBudgets_fns_wf
  · exact wf_drop FullM4Ternary.full_m4_ternary_fns_wf
  · exact wf_take (wf_drop FullFastSched.sched_fns_wf)
  · exact wf_cons FullM3.m3BackboneLit_wf
      (wf_cons FullM3.m3Backbone_wf (wf_cons FullM3.m3ProbeTail_wf (wf_one full_probe_wf)))
  · exact wf_take (wf_drop FullFastSched.sched_fns_wf)
  · exact wf_cons FullM3CongBva.full_elim_collect_nbrs_wf
      (wf_cons FullM3CongBva.full_elim_bve_wf
        (wf_cons full_eliminate_wf (wf_cons full_preprocess_wf (wf_one full_simplify_wf))))
  · exact wf_drop FullFastSched.sched_fns_wf
  · exact wf_one kissat_solve_bytes_wf

theorem m4Fns_wf : ∀ f ∈ m4Fns, f.Wf :=
  wf_app m4FnsPrefix_wf m4FnsSuffix_wf

theorem m4Fns_length : m4Fns.length = 231 := by
  t_kernel_rfl

theorem m4_acyclic : m4Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM4

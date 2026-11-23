/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 High-Fidelity Search Loop, Randec & Bumping (`FullM7FidelitySearch`)

Purely additive Target A (`FullM7Fidelity`) C0 overrides (`0` edits to existing modules)
matching upstream Kissat 4.0.4 (`src/mode.c`, `src/decide.c`, `src/bump.c`, `src/search.c`),
exporting `FullM7Splice.patchFns`-ready handles with `0` spec-table changes:

1. `full_bump_analyzed_fid` (`"full_bump_analyzed_m6_hdr"`, `m6aBumpAnalyzedSpec`): splits
   bumping by mode (`h->stable == 0ULL`: sort + `full_queue_mtf` only; `h->stable != 0ULL`:
   `full_bump_var` + `full_bump_decay` only).
2. `full_switch_mode_fid` (`"full_switch_mode_m7"`, `m7SwitchModeSpec`): resets `randec` slots
   `glue_used[56..63]` (`M7_GU_RANDEC_{REM,LIM,SEQ,CFL}`) on switching to focused mode.
3. `m6_hdr_decide_fid` (`"m6_hdr_decide_fid"`, `m6HdrDecideSpec`): calls `full_decide_m7`
   (preserving `randec` and phase alternation) while maintaining `M6W_DR_STATE`.
4. `full_search_fid` (`"full_search_m6"`, `fullM6SearchSpec`): upstream `src/search.c:195-223`
   loop placing `reduce`/`mode`/`restart`/`reorder`/`rephase`/`probe`/`eliminate` in the
   `pr == 0ULL` `else` branch with `h->fuel` decrements on rare events and `m6_hdr_decide_fid`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySearch

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fid_search "
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

#define PW_BIN_FLAG       0x80000000u
#define PW_LIT_MASK       0x7FFFFFFFu
#define FL_ACTIVE         1u

#define M6_EXT_BYTES      2304ULL
#define M6W_DR_STATE      1ULL

#define M7_GU_RANDEC_REM  56ULL
#define M7_GU_RANDEC_LIM  58ULL
#define M7_GU_RANDEC_SEQ  60ULL
#define M7_GU_RANDEC_CFL  62ULL

extern bool m6_hdr_dr_allow(FullHdr *h);
extern void full_sort_ana_qs_m6(FullHdr *h, u64 cnt);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_bump_var(FullHdr *h, u32 v);
extern void full_bump_decay(FullHdr *h);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);
extern void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m);
extern u64 full_ilog10(u64 x);
extern void full_heap_down(FullHdr *h, u32 v);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_decide_m7(FullHdr *h);
extern void m6_hdr_dr_init(FullHdr *h);
extern u64 full_lucky_late_m7(FullHdr *h);
extern u64 full_propagate(FullHdr *h);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern void full_switch_mode_m7(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern u64 full_reorder_m6(FullHdr *h, u64 budget);
extern void full_rephase(FullHdr *h);
extern u64 full_simplify_m6(FullHdr *h, bool do_probe, bool do_elim);

void full_bump_analyzed_fid(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  if (m6_hdr_dr_allow(h)) {
    u64 lim = saved * 10ULL;
    u64 i = 0ULL;
    u64 tlen = h->tmp_len;
    if (tlen > cv) { tlen = cv; }
    while (i < tlen && h->min_clr_len <= lim) {
      u32 uv = tmp[i] >> 1;
      u32 rsn = ((u64)uv < cv) ? rsns[uv] : 0xFFFFFFFFu;
      if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) != 0u) {
        u32 ov = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
          mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
          h->min_clr_len = h->min_clr_len + 1ULL;
        }
      } else if (rsn != 0xFFFFFFFFu && (u64)rsn + 3ULL <= h->arena_len) {
        u32 sz = ar[(u64)rsn + 2ULL];
        if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len) {
          u32 j = 0u;
          while (j < sz && h->min_clr_len <= lim) {
            u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
            if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
              mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
              h->min_clr_len = h->min_clr_len + 1ULL;
            }
            j = j + 1u;
          }
        }
      }
      i = i + 1ULL;
    }
    if (h->min_clr_len > lim) {
      while (h->min_clr_len > saved) {
        h->min_clr_len = h->min_clr_len - 1ULL;
        u32 rv = ana[h->min_clr_len];
        if ((u64)rv < cv) { mrk[rv] = (u8)0; }
      }
    }
  }
  u64 cnt = h->min_clr_len;
  if (h->stable == 0ULL) {
    if (cnt <= cv) { full_sort_ana_qs_m6(h, cnt); }
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_queue_mtf(h, bv);
      }
      k = k + 1ULL;
    }
  } else {
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_bump_var(h, bv);
      }
      k = k + 1ULL;
    }
    full_bump_decay(h);
  }
}

void full_switch_mode_fid(FullHdr *h) {
  u64 old_m = 0ULL;
  u64 new_m = 1ULL;
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    old_m = 0ULL;
    new_m = 1ULL;
    h->stable = 1ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 rp = h->rel_period;
    if (h->rel_limit > 0ULL && rp > h->rel_limit) { rp = h->rel_limit; }
    h->rel_wait = rp;
    h->rel_u = 1ULL;
    h->rel_v = 1ULL;
    h->rel_trigger = 0ULL;
    u64 cv = h->cur_vars;
    u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap;
    u32 *ps = (u32 *)h->pos;
    u64 n = 0ULL;
    u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u) {
        hp[n] = (u32)v;
        ps[v] = (u32)n;
        n = n + 1ULL;
      } else {
        ps[v] = 0xFFFFFFFFu;
      }
      v = v + 1ULL;
    }
    h->heap_len = n;
    u64 s = n >> 1;
    while (s > 0ULL) { s = s - 1ULL; full_heap_down(h, hp[s]); }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    old_m = 1ULL;
    new_m = 0ULL;
    h->stable = 0ULL;
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 cc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
    u64 q = full_log10_q16_m7(cc + 9ULL);
    u64 l2 = (q * q) >> 16;
    u64 l4 = (l2 * l2) >> 16;
    u64 scaled = 0ULL;
    if (cnt <= 1000000ULL) {
      scaled = (1000ULL * cnt * l4) >> 16;
    } else {
      u64 clim = (cnt > 100000000ULL) ? 100000000ULL : cnt;
      scaled = ((1000ULL * clim) >> 16) * l4;
    }
    h->mode_confl_lim = h->conflicts + scaled;
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < h->cur_vars) {
      u32 *qs = (u32 *)h->q_stamp;
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  full_ema_swap_m7(h, old_m, new_m);
  if (h->stable == 0ULL) {
    u64 delta = 1ULL;
    u64 rst = h->restarts;
    if (rst > 0ULL) {
      u64 rc = (rst < 1000000000000ULL) ? rst : 1000000000000ULL;
      u64 d10 = full_ilog10(rc + 9ULL);
      delta = (d10 > 1ULL) ? (d10 - 1ULL) : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
    full_m7_set64(h, M7_GU_RANDEC_REM, 0ULL);
    full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + 500ULL);
    full_m7_set64(h, M7_GU_RANDEC_SEQ, 0ULL);
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
  }
}

u64 m6_hdr_decide_fid(FullHdr *h) {
  if (full_decide_m7(h) == 0ULL) { return 0ULL; }
  m6_hdr_dr_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 hi = st & (~mask56);
  u64 decs = st & mask56;
  if (decs < mask56) { e[M6W_DR_STATE] = hi | (decs + 1ULL); }
  return 1ULL;
}

u64 full_search_fid(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  u64 reordered = 0ULL;
  u64 last_reduce_cfl = 0xFFFFFFFFFFFFFFFFULL;
  u64 lkr = full_lucky_late_m7(h);
  if (lkr == 10ULL || lkr == 20ULL) { return lkr; }
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
    } else if (h->unassigned == 0ULL) {
      return 10ULL;
    } else if (h->fuel == 0ULL) {
      return 0ULL;
    } else if (h->conflicts >= h->reduce_limit) {
      last_reduce_cfl = h->conflicts;
      h->fuel = h->fuel - 1ULL;
      u64 rr = full_reduce_m6(h, false);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
    } else if ((h->stable == 0ULL) ? (h->conflicts >= h->mode_confl_lim)
                                   : (h->search_ticks >= h->mode_tick_lim)) {
      h->fuel = h->fuel - 1ULL;
      full_switch_mode_m7(h);
    } else if (full_restart_due(h) != 0ULL) {
      h->fuel = h->fuel - 1ULL;
      full_restart(h);
    } else if (h->cur_level == 0ULL && h->conflicts >= reorder_limit) {
      reordered = reordered + 1ULL;
      reorder_limit = h->conflicts + 10000ULL * reordered;
      h->fuel = h->fuel - 1ULL;
      full_reorder_m6(h, 256ULL);
    } else if (h->stable != 0ULL && h->conflicts >= h->rephase_limit) {
      h->fuel = h->fuel - 1ULL;
      full_rephase(h);
    } else if (h->conflicts != last_reduce_cfl && h->conflicts >= h->probe_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, true, false);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else if (h->conflicts != last_reduce_cfl && h->conflicts >= h->elim_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, false, true);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else {
      if (m6_hdr_decide_fid(h) == 0ULL) {
        return (h->unassigned == 0ULL) ? 10ULL : 0ULL;
      }
    }
  }
}
"

/-- Canonical external callee signatures referenced by `fidSearchFns` (`22` externs). -/
def fidSearchExterns : List Extern :=
  [ ⟨"m6_hdr_dr_allow", [i64], [.bool]⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], []⟩
  , ⟨"full_queue_mtf", [i64, i32], []⟩
  , ⟨"full_bump_var", [i64, i32], []⟩
  , ⟨"full_bump_decay", [i64], []⟩
  , ⟨"full_m7_set64", [i64, i64, i64], []⟩
  , ⟨"full_ema_swap_m7", [i64, i64, i64], []⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_heap_down", [i64, i32], []⟩
  , ⟨"full_log10_q16_m7", [i64], [i64]⟩
  , ⟨"full_decide_m7", [i64], [i64]⟩
  , ⟨"m6_hdr_dr_init", [i64], []⟩
  , ⟨"full_lucky_late_m7", [i64], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_analyze_m6_hdr", [i64], [i64]⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64]⟩
  , ⟨"full_switch_mode_m7", [i64], []⟩
  , ⟨"full_restart_due", [i64], [i64]⟩
  , ⟨"full_restart", [i64], []⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64]⟩
  , ⟨"full_rephase", [i64], []⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64]⟩ ]

/-- Standalone Target A (`FullM7Fidelity`) search/mode/decide/bump function list (`4` fns). -/
def fidSearchFns : List Fn := fid_search_fns

/-- Standalone Target A (`FullM7Fidelity`) module (`4` functions + `22` externs, `0` exits). -/
def fidSearchModule : LeanQbe.T.Module :=
  { fns := fidSearchFns, externs := fidSearchExterns, exits := [] }

/-- Drop-in canonical `Fn` handles matching `FullM7.m7Module` splice slots. -/
def fidBumpAnalyzedFn : Fn :=
  ⟨"full_bump_analyzed_m6_hdr", [i64], [], full_bump_analyzed_fid_body⟩
def fidSwitchModeFn : Fn :=
  ⟨"full_switch_mode_m7", [i64], [], full_switch_mode_fid_body⟩
def fidHdrDecideFn : Fn :=
  ⟨"m6_hdr_decide_fid", [i64], [i64], m6_hdr_decide_fid_body⟩
def fidSearchM6Fn : Fn :=
  ⟨"full_search_m6", [i64], [i64], full_search_fid_body⟩

/-- `FullM7Splice.patchFns` in-place replacement list for `FullM7.m7Fns` (`3` fns). -/
def fidSearchPatchRepls : List Fn :=
  [fidBumpAnalyzedFn, fidSwitchModeFn, fidSearchM6Fn]

/-- `FullM7Splice.patchFns` anchor-insertion list inserting `m6_hdr_decide_fid` immediately
before `full_search_m6` (after `full_decide_m7` in `m7Fns`). -/
def fidSearchPatchBefores : List (Sym × List Fn) :=
  [("full_search_m6", [fidHdrDecideFn])]

/-- Local `@[expose]` anchor-insertion helper matching `FullM7Splice.patchInsAt`. -/
def fidPatchInsAt (befores : List (Sym × List Fn)) (f : Fn) : List Fn :=
  (befores.filterMap fun (a, hs) => if a == f.name then some hs else none).flatten

/-- Local `@[expose]` splice helper matching `FullM7Splice.patchFns`. -/
def fidPatchFns (repls : List Fn) (befores : List (Sym × List Fn)) (fs : List Fn) : List Fn :=
  fs.flatMap fun f => fidPatchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f]

/-- `4`-fn ordered patch list (canonically keyed by `FullM7.m7Module` names + helper). -/
def fidSearchPatchFns : List Fn :=
  [fidBumpAnalyzedFn, fidSwitchModeFn, fidHdrDecideFn, fidSearchM6Fn]

theorem full_bump_analyzed_fid_wf : Func.Wf full_bump_analyzed_fid_body := by t_wf_reify
theorem full_switch_mode_fid_wf : Func.Wf full_switch_mode_fid_body := by t_wf_reify
theorem m6_hdr_decide_fid_wf : Func.Wf m6_hdr_decide_fid_body := by t_wf_reify
theorem full_search_fid_wf : Func.Wf full_search_fid_body := by t_wf_reify

theorem fidSearch_fns_wf : ∀ f ∈ fidSearchFns, f.Wf := by
  simp only [fidSearchFns, fid_search_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_bump_analyzed_fid_wf, full_switch_mode_fid_wf,
    m6_hdr_decide_fid_wf, full_search_fid_wf⟩

theorem fidSearchPatchRepls_wf : ∀ f ∈ fidSearchPatchRepls, f.Wf := by
  simp only [fidSearchPatchRepls, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_bump_analyzed_fid_wf, full_switch_mode_fid_wf, full_search_fid_wf⟩

theorem fidSearchPatchBefores_wf :
    ∀ p ∈ fidSearchPatchBefores, ∀ h ∈ p.2, h.Wf := by
  intro p hp h hh
  simp only [fidSearchPatchBefores, List.mem_singleton] at hp
  subst hp
  simp only [List.mem_singleton] at hh
  subst hh
  exact m6_hdr_decide_fid_wf

theorem fidSearch_acyclic : fidSearchModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7FidelitySearch

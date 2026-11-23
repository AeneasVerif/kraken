module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 High-Fidelity Upstream C 4.0.4 Schedule & Preprocessing (`FullM7FidelitySched`)

Purely additive C0 overrides (`0` edits to existing modules) for Target A (`FullM7Fidelity`),
matching upstream C Kissat 4.0.4 (`src/kimits.c`, `src/reduce.c`, `src/probe.c`,
`src/eliminate.c`, `src/factor.c`, `src/preprocess.c`):
1. `full_ilog10_fid`: upstream `kissat_log10(x)` (`P1-4` fix: returns `1` for `0 <= x < 100`
   and `floor(log10(x))` capped at `19` for `x >= 100`, avoiding the `+1` inflation in
   `Full1.full_ilog10`).
2. `full_nlogpown_fid`: overflow-safe upstream `NLOGN`/`NLOG2N`/`NLOG3N` scaling
   (`base * count * ilog10(count + 9)^exp` for `exp <= 3`).
3. `full_calc_max_v_fid`: removes the `(mv >> 1) + 16` clamp in `Full1.full_calc_max_v`, raising
   the dynamic BVA variable cap to `min(4096, max_bva)` bounded by remaining work memory.
4. `full_reduce_fid`: `M6Hdr` reduce using `full_ilog10_fid` (`50%` first-reduce drop vs `70%`).
5. `full_probe_fid`: uses `full_nlogpown_fid(100, h->probings, 1)` (`NLOGN`), removes the
   `num_irred <= 4096 || eliminations > 0` gate before `full_factor`, and raises initial BVA
   budget to `min(cur_vars * 4 + 1024, 8192)`.
6. `full_eliminate_fid`: uses `full_nlogpown_fid(500, h->eliminations, 2)` (`NLOG2N`, restoring
   missing `* h->eliminations`), calls `full_forward_sub_m7` (`P1-3`) & `full_elim_bve_m7`, and
   preserves `h->elim_bound` across `full_factor` without forcing `h->elim_bound = 0ULL`.
7. `full_preprocess_fid`: runs `full_probe_fid(h, true)` followed by `full_eliminate_fid(h, true)`
   with upstream `inconsistent`/`oom`/`fuel`/compaction checks matching `preprocess.c`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySched

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fid_sched "
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

#define PH_GLUE_MASK          0x7FFFFu
#define PH_GARB               0x00080000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL

#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL

extern u64 full_fixed_bytes(u64 mv);
extern u64 full_isqrt(u64 x);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_arena_sweep(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern bool full_enter_dense(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 kind);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_rebuild_watches(FullHdr *h);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 kind);
extern void m6_hdr_bump_delay(FullHdr *h, u64 kind);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern u64 full_probe_tail_m6(FullHdr *h, u64 dticks);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_forward_sub_m7(FullHdr *h, u64 budget);
extern u64 full_elim_bve_m7(FullHdr *h, u64 budget);
extern u64 full_lucky(FullHdr *h);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);

u64 full_ilog10_fid(u64 x) {
  u64 r = 1ULL;
  u64 p = 10ULL;
  while (x / 10ULL >= p && r < 19ULL) {
    r = r + 1ULL;
    p = p * 10ULL;
  }
  return r;
}

u64 full_nlogpown_fid(u64 base, u64 count, u64 exp) {
  u64 arg = (count > (~0ULL) - 9ULL) ? (~0ULL) : (count + 9ULL);
  u64 lg = full_ilog10_fid(arg);
  u64 cc = (count > 100000000ULL) ? 100000000ULL : count;
  u64 bc = (base > 10000ULL) ? 10000ULL : base;
  u64 e = (exp > 3ULL) ? 3ULL : exp;
  u64 p = 1ULL;
  u64 i = 0ULL;
  while (i < e) {
    p = p * lg;
    i = i + 1ULL;
  }
  return bc * cc * p;
}

u64 full_calc_max_v_fid(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = 4096ULL;
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 fixed = full_fixed_bytes(max_v);
  if (avail < fixed || avail - fixed < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_reduce_fid(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + 1000ULL * full_isqrt(h->reductions);
  u64 ret = 1ULL;
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { ret = 20ULL; }
    else if (pr != 0ULL) { ret = 0ULL; }
    else { h->unflushed = 0ULL; }
  }
  if (ret == 1ULL) {
    m6_hdr_recompute_tiers(h);
    full_mark_reasons(h, true);
    u32 *ar = (u32 *)h->arena;
    u32 *rr = (u32 *)h->red_refs;
    u64 rc = 0ULL;
    u64 p = 0ULL;
    u64 t1 = h->tier1;
    u64 t2 = h->tier2;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 n = full_arena_next(h, (u32)p);
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
      u64 arg = (h->reductions > (~0ULL) - 9ULL) ? (~0ULL) : (h->reductions + 9ULL);
      u64 logv = full_ilog10_fid(arg);
      u64 target = (rc * (900ULL - (400ULL / logv))) / 1000ULL;
      u64 i = 0ULL;
      while (i < target && i < rc) {
        u64 cref = (u64)rr[i];
        u32 hdr = ar[cref];
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
        if (sr == 2ULL) { ret = 20ULL; break; }
        if (sr == 3ULL) { ret = 0ULL; break; }
        if (sr == 0ULL) { break; }
        u64 pr = full_propagate(h);
        if (pr == 1ULL) { ret = 20ULL; break; }
        if (pr != 0ULL) { ret = 0ULL; break; }
        h->unflushed = 0ULL;
      }
    } else {
      full_mark_reasons(h, false);
    }
  }
  m6_hdr_set_watermark(h, M6_WM_REDUCE_CONFL, h->conflicts);
  m6_hdr_set_watermark(h, M6_WM_REDUCE_TICKS, h->search_ticks);
  return ret;
}

u64 full_probe_fid(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 nlogp = full_nlogpown_fid(100ULL, h->probings, 1ULL);
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
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
        full_backbone_m6(h, dticks * 4ULL + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  }
  if (full_enter_dense(h)) {
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

u64 full_eliminate_fid(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 nloge = full_nlogpown_fid(500ULL, h->eliminations, 2ULL);
    u64 delta = full_scale_delta(h, nloge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub_m7(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) {
    full_rebuild_watches(h);
    return 20ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = initial ? (cv * 4ULL + 256ULL) : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve_m7(h, bve_lim);
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 1024ULL)) {
    u64 fact_bud = full_min_u64(initial ? 128ULL : (16ULL + (dticks >> 10)), 256ULL);
    u64 saved_eb = h->elim_bound;
    full_factor(h, fact_bud);
    h->elim_bound = saved_eb;
  }
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_preprocess_fid(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  u64 lk = full_lucky(h);
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  if (full_probe_fid(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate_fid(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  return 1ULL;
}
"

/-- Canonical external callee signatures referenced by `fidSchedFns` (`31` externs). -/
def fidSchedExterns : List Extern :=
  [ ⟨"full_fixed_bytes", [i64], [i64]⟩
  , ⟨"full_isqrt", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], []⟩
  , ⟨"full_mark_reasons", [i64, .bool], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_sort_reds", [i64, i64], []⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64]⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], []⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], []⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64]⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64]⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64]⟩
  , ⟨"full_lucky", [i64], [i64]⟩
  , ⟨"full_compact_needed", [i64], [.bool]⟩
  , ⟨"full_compact", [i64], [i64]⟩ ]

/-- Standalone Target A (`FullM7Fidelity`) schedule & preprocessing function list (`7` fns). -/
def fidSchedFns : List Fn := fid_sched_fns

/-- Standalone Target A (`FullM7Fidelity`) module (`7` functions + `31` externs, `0` exits). -/
def fidSchedModule : LeanQbe.T.Module :=
  { fns := fidSchedFns, externs := fidSchedExterns, exits := [] }

/-- Individual `fidSched` function handles matching canonical Kissat C0 symbol names. -/
def fidIlog10Fn : Fn := ⟨"full_ilog10", [i64], [i64], full_ilog10_fid_body⟩
def fidNlogpownFn : Fn := ⟨"full_nlogpown", [i64, i64, i64], [i64], full_nlogpown_fid_body⟩
def fidCalcMaxVFn : Fn :=
  ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], full_calc_max_v_fid_body⟩
def fidReduceFn : Fn := ⟨"full_reduce", [i64, .bool], [i64], full_reduce_fid_body⟩
def fidReduceM6Fn : Fn := ⟨"full_reduce_m6", [i64, .bool], [i64], full_reduce_fid_body⟩
def fidProbeFn : Fn := ⟨"full_probe", [i64, .bool], [i64], full_probe_fid_body⟩
def fidProbeM6Fn : Fn := ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_fid_body⟩
def fidEliminateFn : Fn := ⟨"full_eliminate", [i64, .bool], [i64], full_eliminate_fid_body⟩
def fidEliminateM7Fn : Fn := ⟨"full_eliminate_m7", [i64, .bool], [i64], full_eliminate_fid_body⟩
def fidPreprocessFn : Fn := ⟨"full_preprocess", [i64], [i64], full_preprocess_fid_body⟩
def fidPreprocessM6Fn : Fn := ⟨"full_preprocess_m6", [i64], [i64], full_preprocess_fid_body⟩

theorem full_ilog10_fid_wf : Func.Wf full_ilog10_fid_body := by t_wf_reify
theorem full_nlogpown_fid_wf : Func.Wf full_nlogpown_fid_body := by t_wf_reify
theorem full_calc_max_v_fid_wf : Func.Wf full_calc_max_v_fid_body := by t_wf_reify
theorem full_reduce_fid_wf : Func.Wf full_reduce_fid_body := by t_wf_reify
theorem full_probe_fid_wf : Func.Wf full_probe_fid_body := by t_wf_reify
theorem full_eliminate_fid_wf : Func.Wf full_eliminate_fid_body := by t_wf_reify
theorem full_preprocess_fid_wf : Func.Wf full_preprocess_fid_body := by t_wf_reify

theorem fidSched_fns_wf : ∀ f ∈ fidSchedFns, f.Wf := by
  simp only [fidSchedFns, fid_sched_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_ilog10_fid_wf, full_nlogpown_fid_wf, full_calc_max_v_fid_wf,
    full_reduce_fid_wf, full_probe_fid_wf, full_eliminate_fid_wf, full_preprocess_fid_wf⟩

theorem fidSched_acyclic : fidSchedModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7FidelitySched

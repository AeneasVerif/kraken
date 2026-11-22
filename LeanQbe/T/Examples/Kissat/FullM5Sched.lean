module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Stage-3 M5 Scheduler Parity v2 C0 Upgrades (`FullM5Sched`)

Drop-in verified C0 replacements targeting Kissat 4.0.4 (`C1`) scheduler, EMA, mode-switching,
rephase, and limit-scaling parity (`PR-W1C`, `RC-13`) while preserving the exact `FullHdr` layout
(`0` new or borrowed header fields) and unchanged `Full` / `FullFastSched` contracts:

- `full_log10_q16`: pure Q16 fixed-point `log10(x)` via Q32 repeated squaring (`u64`-safe).
- `full_scale_delta_m5`: continuous `Q16` `log10(clauses + 10)` limit scaling (`kimits.c:39-57`).
- `full_ema_update`: `Q32` focused glue EMAs (auto-promoting `Q24` init from `Full1`, no-op when
  `stable != 0`), eliminating `/ 100000` slow-EMA deadband.
- `full_rephase`: focused `stable == 0` guard above `full_backtrack(h, 0ULL)` (`rephase.c:32-38`)
  and `1000 * n * log10(n + 9)^3` interval.
- `full_switch_mode`: `1000 * cnt * log10(cnt + 9)^4` focused conflict interval (`mode.c:91`),
  no artificial `dticks < 1000ULL` floor, `rel_*` reset on focused -> stable, and `Q32` EMA reset.
- `full_restart_due`: checks `conflicts < restart_limit` before `stable`, exact un-truncated `Q32`
  ratio comparison (`(fb << 16) / fd` vs `(sb << 16) / sd`), and passes `restarts + 1`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Sched

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5Sched "
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

#define FL_ACTIVE 1u

extern u64 full_ilog10(u64 x);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_walk(FullHdr *h);

u64 full_log10_q16(u64 x) {
  if (x <= 1ULL) { return 0ULL; }
  u64 d = 0ULL;
  u64 pow10 = 1ULL;
  while (x / 10ULL >= pow10 && d < 19ULL) {
    d = d + 1ULL;
    pow10 = pow10 * 10ULL;
  }
  u64 xm = x;
  u64 pm = pow10;
  if (pm > 100000000ULL) {
    u64 sc = pm / 100000000ULL;
    xm = xm / sc;
    pm = 100000000ULL;
  }
  u64 m = (xm << 32) / pm;
  u64 lim10 = 10ULL << 32;
  u64 frac = 0ULL;
  u64 i = 0ULL;
  while (i < 16ULL) {
    u64 m_hi = m >> 16;
    u64 m_lo = m & 0xFFFFULL;
    u64 q = (m_lo * m_lo) >> 16;
    u64 mid = (2ULL * m_hi * m_lo) + q;
    m = (m_hi * m_hi) + (mid >> 16);
    frac = frac << 1;
    if (m >= lim10) {
      m = m / 10ULL;
      frac = frac + 1ULL;
    }
    i = i + 1ULL;
  }
  return (d << 16) + frac;
}

u64 full_scale_delta_m5(FullHdr *h, u64 delta) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 cx = (clauses < 1000000000000000000ULL) ? clauses : 1000000000000000000ULL;
  u64 q = full_log10_q16(cx + 10ULL);
  u64 five = 5ULL << 16;
  u64 diff = (q >= five) ? (q - five) : (five - q);
  u64 ff_q32 = diff * diff;
  u64 fff_q16 = (((ff_q32 * 45ULL) / 10ULL) >> 16) + (25ULL << 16);
  if (delta <= (1ULL << 36)) {
    return (delta * fff_q16) >> 16;
  }
  return (delta >> 16) * fff_q16;
}

void full_ema_update(FullHdr *h, u64 glue) {
  if (h->stable != 0ULL) { return; }
  u64 g = (glue > 16383ULL) ? 16383ULL : glue;
  u64 ys = g << 32;
  u64 fb = h->ema_fast_biased;
  u64 fe = h->ema_fast_exp;
  u64 sb = h->ema_slow_biased;
  u64 se = h->ema_slow_exp;
  if (fe == (1ULL << 24) && se == (1ULL << 24) && fb == 0ULL && sb == 0ULL) {
    fe = 1ULL << 32;
    se = 1ULL << 32;
  }
  if (ys >= fb) { fb = fb + ((ys - fb) / 33ULL); }
  else { fb = fb - ((fb - ys) / 33ULL); }
  h->ema_fast_biased = fb;
  if (fe > 0ULL) {
    u64 df = fe / 33ULL;
    h->ema_fast_exp = (df == 0ULL) ? 0ULL : (fe - df);
  }
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  h->ema_slow_biased = sb;
  if (se > 0ULL) {
    u64 ds = se / 100000ULL;
    h->ema_slow_exp = (ds == 0ULL) ? 0ULL : (se - ds);
  }
}

void full_rephase(FullHdr *h) {
  if (h->stable == 0ULL) {
    h->rephase_limit = h->mode_confl_lim;
    return;
  }
  full_backtrack(h, 0ULL);
  h->rephased = h->rephased + 1ULL;
  u64 sel = (h->rephased - 1ULL) % 6ULL;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  u64 k = 0ULL;
  if (sel == 0ULL || sel == 3ULL) {
    while (k < cv) { if (pbst[k] != (i8)0) { ph[k] = pbst[k]; } k = k + 1ULL; }
    h->best_assigned = 0ULL;
  } else if (sel == 1ULL || sel == 4ULL) {
    full_walk(h);
  } else if (sel == 2ULL) {
    while (k < cv) { ph[k] = (i8)(-1); k = k + 1ULL; }
  } else {
    while (k < cv) { ph[k] = (i8)1; k = k + 1ULL; }
  }
  k = 0ULL;
  while (k < cv) { ptgt[k] = ph[k]; k = k + 1ULL; }
  h->target_assigned = 0ULL;
  u64 n = h->rephased;
  u64 nc = (n < 1000000000000ULL) ? n : 1000000000000ULL;
  u64 q = full_log10_q16(nc + 9ULL);
  u64 l2 = (q * q) >> 16;
  u64 l3 = (l2 * q) >> 16;
  u64 scaled = 0ULL;
  if (n <= 1000000ULL) {
    scaled = (1000ULL * n * l3) >> 16;
  } else {
    u64 nlim = (n > 100000000ULL) ? 100000000ULL : n;
    scaled = ((1000ULL * nlim) >> 16) * l3;
  }
  h->rephase_limit = h->conflicts + scaled;
}

void full_switch_mode(FullHdr *h) {
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    h->stable = 1ULL;
    u64 dticks = h->search_ticks - h->mode_saved_ticks;
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 rp = h->rel_period;
    if (h->rel_limit > 0ULL && rp > h->rel_limit) { rp = h->rel_limit; }
    h->rel_wait = rp;
    h->rel_u = 1ULL;
    h->rel_v = 1ULL;
    h->rel_trigger = 0ULL;
    u64 cv = h->cur_vars;
    i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap; u32 *ps = (u32 *)h->pos;
    u64 n = 0ULL; u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        hp[n] = (u32)v; ps[v] = (u32)n; n = n + 1ULL;
      } else { ps[v] = 0xFFFFFFFFu; }
      v = v + 1ULL;
    }
    h->heap_len = n;
    u64 s = n >> 1;
    while (s > 0ULL) { s = s - 1ULL; full_heap_down(h, hp[s]); }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    h->stable = 0ULL;
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 cc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
    u64 q = full_log10_q16(cc + 9ULL);
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
      u32 *qs = (u32 *)h->q_stamp; h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  h->ema_fast_biased = 0ULL;
  h->ema_fast_exp = 1ULL << 32;
  h->ema_slow_biased = 0ULL;
  h->ema_slow_exp = 1ULL << 32;
  if (h->stable == 0ULL) {
    u64 delta = 1ULL;
    u64 rst = h->restarts;
    if (rst > 0ULL) {
      u64 rc = (rst < 1000000000000ULL) ? rst : 1000000000000ULL;
      u64 d10 = full_ilog10(rc + 9ULL);
      delta = (d10 > 1ULL) ? (d10 - 1ULL) : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
  }
}

u64 full_restart_due(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  if (h->conflicts < h->restart_limit) { return 0ULL; }
  if (h->stable != 0ULL) {
    if (h->rel_trigger != 0ULL) { h->rel_trigger = 0ULL; return 1ULL; }
    return 0ULL;
  }
  u64 scale = 1ULL << 32;
  u64 fe = h->ema_fast_exp;
  u64 se = h->ema_slow_exp;
  if (fe >= scale || se >= scale) { return 0ULL; }
  u64 fd = scale - fe;
  u64 sd = scale - se;
  if (fd == 0ULL || sd == 0ULL) { return 0ULL; }
  u64 fb = h->ema_fast_biased;
  u64 sb = h->ema_slow_biased;
  u64 fbc = (fb > (16384ULL << 32)) ? (16384ULL << 32) : fb;
  u64 sbc = (sb > (16384ULL << 32)) ? (16384ULL << 32) : sb;
  u64 fval = (fbc << 16) / fd;
  u64 sval = (sbc << 16) / sd;
  if (fval > (1ULL << 32)) { fval = 1ULL << 32; }
  if (sval > (1ULL << 32)) { sval = 1ULL << 32; }
  if (fval * 100ULL > sval * 110ULL) {
    u64 rst = (h->restarts < 1000000000000ULL) ? (h->restarts + 1ULL) : 1000000000000ULL;
    u64 d10 = full_ilog10(rst + 9ULL);
    u64 delta = (d10 > 1ULL) ? (d10 - 1ULL) : 1ULL;
    h->restart_limit = h->conflicts + delta;
    return 1ULL;
  }
  return 0ULL;
}
"

/-- External callee signatures referenced by `m5Sched_fns`. -/
def m5SchedExterns : List Extern :=
  [ ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_heap_down", [i64, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_walk", [i64], []⟩
  ]

def m5SchedModule : LeanQbe.T.Module :=
  { fns := m5Sched_fns, externs := m5SchedExterns, exits := [] }

theorem full_log10_q16_wf : Func.Wf full_log10_q16_body := by t_wf_reify
theorem full_scale_delta_m5_wf : Func.Wf full_scale_delta_m5_body := by t_wf_reify
theorem full_ema_update_wf : Func.Wf full_ema_update_body := by t_wf_reify
theorem full_rephase_wf : Func.Wf full_rephase_body := by t_wf_reify
theorem full_switch_mode_wf : Func.Wf full_switch_mode_body := by t_wf_reify
theorem full_restart_due_wf : Func.Wf full_restart_due_body := by t_wf_reify

theorem m5Sched_fns_wf : ∀ f ∈ m5Sched_fns, f.Wf := by
  simp only [m5Sched_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_log10_q16_wf, full_scale_delta_m5_wf, full_ema_update_wf,
    full_rephase_wf, full_switch_mode_wf, full_restart_due_wf⟩

theorem m5Sched_acyclic : m5SchedModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5Sched

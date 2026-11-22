module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M5 Orchestration & Budget Upgrades (`PR-W1E`, `RC-14` & `RC-15`)

Standalone pre-staged `PR-W1E` (`FullM5Orch`) C0 module covering all `19` orchestration,
initialization-cap, and effort/budget upgrades against the frozen `144`-word `FullHdr`:
1. **`RC-15` Caps & Init (`3` fns):** `full_calc_ext_cap_m5` (`4M`), `full_calc_scr_cap_m5` (`1M`),
   and `full_init_state_m5` wiring both `[38]` & `[39]`.
2. **`RC-15` Effort & Budgets (`7` fns):** `full_probe_dticks_m5` & `full_elim_dticks_m5`
   (`10_000_000ULL` `mineffort` floor), `full_trans_lit_m5` (`dst > src` + `ant_sz` inside BFS) &
   `full_transitive_m5`, `full_vivify_tier_m5` & `full_vivify_m5` (no `1024/512` cap via
   `0xFFFFFFFFULL`, rolling cumulative 3:3:1:3 `tick_cap`, 100% tier 0 when `num_redundant == 0`,
   delegating to `FullM4VivBce.full_viv_*_m4`), `full_sweep_dense_m5` (no `16384/32` clamps,
   `eff_ref`-scaled `kitten_ticks`, delegating to `FullM4Sweep.full_m4_sweep_var`), and
   `full_probe_tail_m5`.
3. **`RC-14` Orchestration Parity (`9` fns):** `full_reduce_m5` (no `full_promote_reasons`),
   `full_reorder_m5` (queue-only, no heap reorder / clause tumble), `full_probe_m5` (drop dense
   gate & `full_ternary`, `<= 2` rounds `congruence -> sweep -> substitute`), `full_eliminate_m5`
   (wire `full_bce_m4`, drop BVA `num_binary == 0 && num_irred > 4096` skip, uncapped
   `elim_limit`), `full_preprocess_m5` (`full_lucky`, no eager confl-0 eliminate, initial compact,
   `full_scale_delta_m5` limits), `full_simplify_m5` (no double reduce), `full_search_m5`
   (`search.c:195-224` dispatch, no startup warmup, linear `10k` reorder cadence), and
   `kissat_solve_bytes_m5`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Orch

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5Orch "
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
#define PW_BIN_FLAG      0x80000000u
#define PW_LIT_MASK      0x7FFFFFFFu

#define FL_ACTIVE        1u
#define FL_ELIM          2u
#define FL_SUBST         4u
#define FL_TRANS         512u
#define FL_SWEEP         1024u

#define EXT_BLK_FLAG     0x80000000u
#define EXT_COMPACT_FLAG 0x40000000u
#define EXT_CNT_MASK     0x3FFFFFFFu

#define K512_BASE        2304u
#define K512_MIN_SCR     24576ULL
#define K5H_TICKS        11u

extern bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d);
extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d, i8 *vals, u64 mv_max);
extern u64 full_isqrt(u64 x);
extern u64 full_ilog10(u64 x);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_max_u64(u64 a, u64 b);
extern u64 full_fixed_bytes(u64 max_v);
extern u64 full_calc_max_v(u64 avail, u64 mv, u64 nc, u64 f0);
extern void full_init_arenas(FullHdr *h, u64 hdr_addr, u64 max_v, u64 avail_dyn);
extern void full_init_hdr(FullHdr *h, u64 mv, u64 max_v, u64 fuel);
extern void full_zero_tables1(FullHdr *h);
extern void full_zero_tables2(FullHdr *h);
extern u64 full_parse_body(FullHdr *h, u64 cnf_end);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern void full_switch_mode(FullHdr *h);
extern void full_rephase(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_arena_sweep(FullHdr *h);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_analyze(FullHdr *h);
extern u64 full_decide(FullHdr *h);
extern void full_restart(FullHdr *h);
extern void full_extend(FullHdr *h);
extern u64 full_lucky(FullHdr *h);
extern void full_delete_bin_side(FullHdr *h, u32 lit, u32 dst);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_m4_sweep_var(FullHdr *h, u32 root_v, u64 tick_lim);
extern u64 full_backbone(FullHdr *h, u64 tick_lim);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_viv_collect_m4(FullHdr *h, u64 tier_mode);
extern void full_viv_keys_m4(FullHdr *h, u64 bn);
extern void full_viv_sort_sched_m4(FullHdr *h, u64 bn);
extern u64 full_viv_clause_m4(FullHdr *h, u32 cref);
extern void full_viv_clear_tier_m4(FullHdr *h, u64 tier_mode);
extern u64 full_reorder_queue(FullHdr *h);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_elim_bve(FullHdr *h, u64 bve_lim);
extern u64 full_bce_m4(FullHdr *h, u64 budget);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);

u64 full_calc_ext_cap_m5(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = rem >> 5;
  if (c > 4194304ULL) { c = 4194304ULL; }
  return c & (~1ULL);
}

u64 full_calc_scr_cap_m5(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = (rem >= 16384ULL) ? (rem >> 4) : (rem >> 5);
  if (c > 1048576ULL) { c = 1048576ULL; }
  return c & (~1ULL);
}

bool full_init_state_m5(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  FullHdr *h = (FullHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) { return false; }
  u64 mv = h->d.mv; u64 nc = h->d.nc; u64 f0 = full_fixed_bytes(mv);
  if (avail < f0 || avail - f0 < nc * 40ULL + 136ULL) { return false; }
  u64 max_v = full_calc_max_v(avail, mv, nc, f0);
  u64 rem = avail - full_fixed_bytes(max_v);
  u64 del_cap = (rem >= 524288ULL) ? 4096ULL : 8ULL;
  u64 del_bytes = del_cap * 12ULL;
  u64 ext_cap = full_calc_ext_cap_m5(rem);
  u64 scr_cap = full_calc_scr_cap_m5(rem);
  u64 dyn = del_bytes + (ext_cap << 2) + (scr_cap << 2);
  if (rem < dyn + nc * 40ULL + 136ULL) { ext_cap = 0ULL; scr_cap = 0ULL; dyn = del_bytes; }
  h->delayed_cap = del_cap; h->extend_cap = ext_cap; h->scratch_cap = scr_cap;
  full_init_arenas(h, hdr_addr, max_v, rem - dyn);
  full_init_hdr(h, mv, max_v, fuel);
  full_zero_tables1(h);
  full_zero_tables2(h);
  return true;
}

u64 full_probe_dticks_m5(FullHdr *h, bool initial) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 raw = (h->search_ticks > h->fwd_sub_cnt) ? (h->search_ticks - h->fwd_sub_cnt) : 0ULL;
  u64 dticks = initial ? ((h->cur_vars + clauses) * 8ULL) : raw;
  return full_max_u64(dticks, 10000000ULL);
}

u64 full_elim_dticks_m5(FullHdr *h, bool initial) {
  u64 raw = (h->search_ticks > h->fwd_str_cnt) ? (h->search_ticks - h->fwd_str_cnt) : 0ULL;
  u64 dticks = initial ? ((h->cur_vars + h->num_irred + h->num_binary) * 12ULL) : raw;
  return full_max_u64(dticks, 10000000ULL);
}

bool full_trans_lit_m5(FullHdr *h, u32 src) {
  i8 *vals = (i8 *)h->values;
  if (vals[src] != (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *trl = (u32 *)h->trail; u64 nlits = h->cur_vars << 1;
  u64 off = (u64)wvec[(u64)src << 1]; u64 sz = (u64)wvec[((u64)src << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u32 not_src = src ^ 1u; bool failed = false; u64 reduced = 0ULL;
  u64 p = off; u64 end = off + sz;
  while (p < end && !failed && h->ant_sz > 0ULL) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
    u32 dst = w0 & PW_LIT_MASK;
    if ((u64)dst >= nlits || dst <= src || vals[dst] != (i8)0) { p = p + 1ULL; continue; }
    u64 saved = h->trail_end; u64 prop = saved; bool trans = false;
    vals[not_src] = (i8)1; vals[src] = (i8)(-1); trl[h->trail_end] = not_src;
    h->trail_end = h->trail_end + 1ULL;
    while (!trans && !failed && prop < h->trail_end && h->ant_sz > 0ULL) {
      h->ant_sz = h->ant_sz - 1ULL;
      u32 lit = trl[prop]; prop = prop + 1ULL; u32 nl = lit ^ 1u;
      u64 loff = (u64)wvec[(u64)nl << 1]; u64 lend = loff + (u64)wvec[((u64)nl << 1) + 1ULL];
      u64 q = loff;
      while (q < lend && h->ant_sz > 0ULL) {
        h->ant_sz = h->ant_sz - 1ULL;
        u32 qw = wstk[q];
        if ((qw & PW_BIN_FLAG) == 0u) { q = q + 2ULL; continue; }
        if (nl == src && q == p) { q = q + 1ULL; continue; }
        u32 ot = qw & PW_LIT_MASK;
        if (ot == dst) { trans = true; break; }
        if ((u64)ot < nlits) {
          if (vals[ot] < (i8)0) { failed = true; break; }
          if (vals[ot] == (i8)0 && h->trail_end < h->max_vars) {
            vals[ot] = (i8)1; vals[ot ^ 1u] = (i8)(-1);
            trl[h->trail_end] = ot; h->trail_end = h->trail_end + 1ULL;
          }
        }
        q = q + 1ULL;
      }
    }
    while (h->trail_end > saved) {
      h->trail_end = h->trail_end - 1ULL; u32 ul = trl[h->trail_end];
      vals[ul] = (i8)0; vals[ul ^ 1u] = (i8)0;
    }
    if (trans) {
      full_delete_bin_side(h, dst, src);
      wstk[p] = 0xFFFFFFFFu; reduced = reduced + 1ULL;
      h->trans_cnt = h->trans_cnt + 1ULL;
    }
    p = p + 1ULL;
  }
  if (reduced > 0ULL) {
    u64 q = off; p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if (w0 == 0xFFFFFFFFu) { p = p + 1ULL; }
      else if ((w0 & PW_BIN_FLAG) != 0u) { wstk[q] = w0; q = q + 1ULL; p = p + 1ULL; }
      else if (p + 1ULL < end) {
        wstk[q] = w0; wstk[q + 1ULL] = wstk[p + 1ULL]; q = q + 2ULL; p = p + 2ULL;
      } else { p = p + 1ULL; }
    }
    while (q < end) { wstk[q] = 0xFFFFFFFFu; q = q + 1ULL; }
    wvec[((u64)src << 1) + 1ULL] = (u32)((end - off) - reduced);
    h->wusable = h->wusable + reduced;
    if (h->num_binary >= reduced) { h->num_binary = h->num_binary - reduced; }
  }
  if (failed) { h->trans_cnt = h->trans_cnt + 1ULL; return full_add_unit(h, src); }
  return true;
}

u64 full_transitive_m5(FullHdr *h, u64 tick_lim) {
  if (h->num_binary == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *fl = (u32 *)h->flags; u64 cv = h->cur_vars;
  h->ant_sz = tick_lim; u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && h->ant_sz > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_TRANS)) == (FL_ACTIVE | FL_TRANS)) {
      fl[v] = fl[v] & (~FL_TRANS);
      if (!full_trans_lit_m5(h, (u32)(v << 1))) { res = 20ULL; break; }
      if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
      if (!full_trans_lit_m5(h, (u32)((v << 1) | 1ULL))) { res = 20ULL; break; }
      if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
    }
    v = v + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_tier_m5(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = full_viv_collect_m4(h, tier_mode);
  full_viv_keys_m4(h, bn);
  full_viv_sort_sched_m4(h, bn);
  u64 res = 1ULL;
  u64 bi = 0ULL;
  u64 spent = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         spent < tick_lim) {
    u32 cr = rr[bi * 3ULL];
    u32 sz = ar[(u64)cr + 2ULL];
    spent = spent + 512ULL + ((u64)sz << 5);
    budget = budget - 1ULL;
    u64 vc = full_viv_clause_m4(h, cr);
    if (vc == 20ULL) { res = 20ULL; break; }
    if (vc == 2ULL) { break; }
    if (h->cur_level == 0ULL && full_propagate(h) == 1ULL) { res = 20ULL; break; }
    bi = bi + 1ULL;
  }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (res == 1ULL && bi >= bn && bn < bmax) {
    full_viv_clear_tier_m4(h, tier_mode);
  }
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_m5(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 start = h->search_ticks;
  u64 delta = (start > h->fwd_sub_cnt) ? (start - h->fwd_sub_cnt) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  if (h->num_redundant == 0ULL) {
    return full_vivify_tier_m5(h, 0ULL, 0xFFFFFFFFULL, total);
  }
  if (full_vivify_tier_m5(h, 1ULL, 0xFFFFFFFFULL, (total * 3ULL) / 10ULL) == 20ULL) {
    return 20ULL;
  }
  if (full_vivify_tier_m5(h, 2ULL, 0xFFFFFFFFULL, (total * 3ULL) / 10ULL) == 20ULL) {
    return 20ULL;
  }
  if (full_vivify_tier_m5(h, 3ULL, 0xFFFFFFFFULL, total / 10ULL) == 20ULL) {
    return 20ULL;
  }
  return full_vivify_tier_m5(h, 0ULL, 0xFFFFFFFFULL, (total * 3ULL) / 10ULL);
}

u64 full_sweep_dense_m5(FullHdr *h, u64 budget, u64 tick_lim) {
  if (h->scratch_cap < K512_MIN_SCR || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  u32 *tmk = (u32 *)h->tarjan_mark; u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u64 cv = h->cur_vars; u64 i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  u64 rem_ticks = tick_lim;
  u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && budget > 0ULL && rem_ticks > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); budget = budget - 1ULL;
      if (full_m4_sweep_var(h, (u32)v, rem_ticks) == 20ULL) { res = 20ULL; break; }
      u64 spent = (u64)k[K5H_TICKS] + 64ULL;
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
    v = v + 1ULL;
  }
  return (res == 20ULL || h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_probe_tail_m5(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL && full_backbone(h, dticks * 4ULL + 65536ULL) == 20ULL) {
    return 20ULL;
  }
  u64 tr_lim = (dticks / 50ULL) + 100000ULL;
  if (h->num_binary > 0ULL && full_transitive_m5(h, tr_lim) == 20ULL) { return 20ULL; }
  u64 pbud = full_min_u64(8ULL + (dticks >> 10), 64ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  if (full_vivify_m5(h) == 20ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_reduce_m5(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + 1000ULL * full_isqrt(h->reductions);
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
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

u64 full_reorder_m5(FullHdr *h, u64 budget) {
  return full_reorder_queue(h);
}

u64 full_probe_m5(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m5(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 logp = full_ilog10(h->probings + 9ULL);
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, 100ULL * h->probings * logp);
  }
  u64 round = 0ULL;
  while (round < 2ULL) {
    u64 before_unass = h->unassigned;
    if (full_enter_dense(h)) {
      if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
        full_rebuild_watches(h); return 20ULL;
      }
      if (full_sweep_dense_m5(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
        full_rebuild_watches(h); return 20ULL;
      }
      if (full_rebuild_watches(h) == 20ULL) { return 20ULL; }
    } else if (h->inconsistent != 0ULL) { return 20ULL; }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
    if (h->unassigned >= before_unass) { break; }
    round = round + 1ULL;
  }
  if (!initial) {
    if (full_probe_tail_m5(h, dticks) == 20ULL) { return 20ULL; }
  } else {
    if (h->num_binary > 0ULL &&
        full_backbone(h, dticks * 4ULL + 65536ULL) == 20ULL) {
      return 20ULL;
    }
  }
  if ((h->num_irred <= 4096ULL || h->eliminations > 0ULL) &&
      full_enter_dense(h)) {
    u64 fbud = full_min_u64(initial ? 512ULL : (64ULL + (dticks >> 9)), 1024ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches(h) == 20ULL) { return 20ULL; }
  } else if (h->inconsistent != 0ULL) { return 20ULL; }
  h->fwd_sub_cnt = h->search_ticks;
  return 1ULL;
}

u64 full_eliminate_m5(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks_m5(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    u64 ec = (h->eliminations < 100000000ULL) ? h->eliminations : 100000000ULL;
    h->elim_limit = h->conflicts + full_scale_delta_m5(h, 500ULL * ec * loge * loge);
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
  full_factor(h, fact_bud);
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = initial ? (cv * 4ULL + 256ULL) : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve(h, bve_lim);
  u64 rr = full_rebuild_watches(h);
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) {
    h->fwd_str_cnt = h->search_ticks;
    return 20ULL;
  }
  if (h->oom == 0ULL && h->fuel > 0ULL) {
    u64 bce_bud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 7)), cv * 4ULL + 256ULL);
    if (full_bce_m4(h, bce_bud) == 20ULL) {
      h->fwd_str_cnt = h->search_ticks;
      return 20ULL;
    }
  }
  h->fwd_str_cnt = h->search_ticks;
  return 1ULL;
}

u64 full_preprocess_m5(FullHdr *h) {
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
  if (full_probe_m5(h, true) == 20ULL) { return 20ULL; }
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

u64 full_simplify_m5(FullHdr *h, bool do_probe, bool do_elim) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (do_probe && full_probe_m5(h, false) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (do_elim && full_eliminate_m5(h, false) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  return 1ULL;
}

u64 full_search_m5(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
      bool mode_due = (h->stable == 0ULL)
        ? (h->conflicts >= h->mode_confl_lim)
        : (h->search_ticks >= h->mode_tick_lim);
      if (h->conflicts >= h->reduce_limit) {
        u64 rr = full_reduce_m5(h, false);
        if (rr == 20ULL) { return 20ULL; }
        if (rr != 1ULL) { return 0ULL; }
      } else if (mode_due) {
        full_switch_mode(h);
      } else if (full_restart_due(h) != 0ULL) {
        full_restart(h);
      } else if (h->conflicts >= reorder_limit) {
        reorder_limit = h->conflicts + 10000ULL;
        full_reorder_m5(h, 256ULL);
      } else if (h->conflicts >= h->rephase_limit) {
        full_rephase(h);
      } else if (h->conflicts >= h->probe_limit) {
        u64 sr = full_simplify_m5(h, true, false);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      } else if (h->conflicts >= h->elim_limit) {
        u64 sr = full_simplify_m5(h, false, true);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      }
    } else {
      if (h->unassigned == 0ULL) { return 10ULL; }
      if (full_decide(h) == 0ULL) { return (h->unassigned == 0ULL) ? 10ULL : 0ULL; }
    }
  }
}

u64 kissat_solve_bytes_m5(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + (u64)sizeof(FullHdr)) { return 0ULL; }
  u64 hdr_addr = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  if (!full_init_state_m5(cnf_ptr, cnf_end, hdr_addr, avail, fuel)) { return 0ULL; }
  FullHdr *h = (FullHdr *)hdr_addr;
  u64 pb = full_parse_body(h, cnf_end);
  if (pb != 1ULL) { return pb; }
  u64 orig_mv = h->d.mv;
  u64 pp = full_preprocess_m5(h);
  if (pp == 20ULL) { return 20ULL; }
  u64 r = (pp == 10ULL) ? 10ULL : ((pp == 0ULL) ? 0ULL : full_search_m5(h));
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

/-- External callee signatures referenced by `m5Orch_fns`. -/
def m5OrchExterns : List Extern :=
  [ ⟨"kissat_parse_header", [i64, i64, i64], [.bool]⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64]⟩
  , ⟨"full_isqrt", [i64], [i64]⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_max_u64", [i64, i64], [i64]⟩
  , ⟨"full_fixed_bytes", [i64], [i64]⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64]⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], []⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], []⟩
  , ⟨"full_zero_tables1", [i64], []⟩
  , ⟨"full_zero_tables2", [i64], []⟩
  , ⟨"full_parse_body", [i64, i64], [i64]⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_switch_mode", [i64], []⟩
  , ⟨"full_rephase", [i64], []⟩
  , ⟨"full_restart_due", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_recompute_tiers", [i64], []⟩
  , ⟨"full_mark_reasons", [i64, .bool], []⟩
  , ⟨"full_sort_reds", [i64, i64], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_analyze", [i64], [i64]⟩
  , ⟨"full_decide", [i64], [i64]⟩
  , ⟨"full_restart", [i64], []⟩
  , ⟨"full_extend", [i64], []⟩
  , ⟨"full_lucky", [i64], [i64]⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], []⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"full_m4_sweep_var", [i64, i32, i64], [i64]⟩
  , ⟨"full_backbone", [i64, i64], [i64]⟩
  , ⟨"full_probe_run", [i64, i64], [i64]⟩
  , ⟨"full_viv_collect_m4", [i64, i64], [i64]⟩
  , ⟨"full_viv_keys_m4", [i64, i64], []⟩
  , ⟨"full_viv_sort_sched_m4", [i64, i64], []⟩
  , ⟨"full_viv_clause_m4", [i64, i32], [i64]⟩
  , ⟨"full_viv_clear_tier_m4", [i64, i64], []⟩
  , ⟨"full_reorder_queue", [i64], [i64]⟩
  , ⟨"full_forward_sub", [i64, i64], [i64]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_elim_bve", [i64, i64], [i64]⟩
  , ⟨"full_bce_m4", [i64, i64], [i64]⟩
  , ⟨"full_compact_needed", [i64], [.bool]⟩
  , ⟨"full_compact", [i64], [i64]⟩
  ]

def m5OrchModule : LeanQbe.T.Module :=
  { fns := m5Orch_fns, externs := m5OrchExterns, exits := [] }

theorem full_calc_ext_cap_m5_wf : Func.Wf full_calc_ext_cap_m5_body := by t_wf_reify
theorem full_calc_scr_cap_m5_wf : Func.Wf full_calc_scr_cap_m5_body := by t_wf_reify
theorem full_init_state_m5_wf : Func.Wf full_init_state_m5_body := by t_wf_reify
theorem full_probe_dticks_m5_wf : Func.Wf full_probe_dticks_m5_body := by t_wf_reify
theorem full_elim_dticks_m5_wf : Func.Wf full_elim_dticks_m5_body := by t_wf_reify
theorem full_trans_lit_m5_wf : Func.Wf full_trans_lit_m5_body := by t_wf_reify
theorem full_transitive_m5_wf : Func.Wf full_transitive_m5_body := by t_wf_reify
theorem full_vivify_tier_m5_wf : Func.Wf full_vivify_tier_m5_body := by t_wf_reify
theorem full_vivify_m5_wf : Func.Wf full_vivify_m5_body := by t_wf_reify
theorem full_sweep_dense_m5_wf : Func.Wf full_sweep_dense_m5_body := by t_wf_reify
theorem full_probe_tail_m5_wf : Func.Wf full_probe_tail_m5_body := by t_wf_reify
theorem full_reduce_m5_wf : Func.Wf full_reduce_m5_body := by t_wf_reify
theorem full_reorder_m5_wf : Func.Wf full_reorder_m5_body := by t_wf_reify
theorem full_probe_m5_wf : Func.Wf full_probe_m5_body := by t_wf_reify
theorem full_eliminate_m5_wf : Func.Wf full_eliminate_m5_body := by t_wf_reify
theorem full_preprocess_m5_wf : Func.Wf full_preprocess_m5_body := by t_wf_reify
theorem full_simplify_m5_wf : Func.Wf full_simplify_m5_body := by t_wf_reify
theorem full_search_m5_wf : Func.Wf full_search_m5_body := by t_wf_reify
theorem kissat_solve_bytes_m5_wf : Func.Wf kissat_solve_bytes_m5_body := by t_wf_reify

theorem m5Orch_fns_wf : ∀ f ∈ m5Orch_fns, f.Wf := by
  simp only [m5Orch_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_calc_ext_cap_m5_wf, full_calc_scr_cap_m5_wf, full_init_state_m5_wf,
    full_probe_dticks_m5_wf, full_elim_dticks_m5_wf, full_trans_lit_m5_wf, full_transitive_m5_wf,
    full_vivify_tier_m5_wf, full_vivify_m5_wf, full_sweep_dense_m5_wf, full_probe_tail_m5_wf,
    full_reduce_m5_wf, full_reorder_m5_wf, full_probe_m5_wf, full_eliminate_m5_wf,
    full_preprocess_m5_wf, full_simplify_m5_wf, full_search_m5_wf, kissat_solve_bytes_m5_wf⟩

theorem m5Orch_acyclic : m5OrchModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5Orch

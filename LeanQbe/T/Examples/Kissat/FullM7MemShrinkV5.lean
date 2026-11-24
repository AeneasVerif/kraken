/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Memory-Shrink V5 Wiring (`FullM7MemShrinkV5`)

Clean C0 wiring of `FullM7MemShrink` (`151 -> 90 B/var` resident prefix + `58 B/var` dynamic
transient pool `t_base`, `-40.4%` resident footprint) onto `FullM7Plus` / `FullM7Fidelity`:
1. **V5 BVA Parity (`full_calc_max_v_m7v5`)**: Fixes Cause B (`m7CalcMaxVFn` regression) by
   using `u64 cand = 4096ULL;` while retaining `full_fixed_bytes(max_v) + full_trans_bytes_m7(max_v)`
   budget accounting (100% 35-key telemetry parity with `FullM7Plus` and `FullM7Fidelity`).
2. **Walk-Best Aliasing Guard (`full_compact_vars_m7ms`)**: Fixes Cause C by removing the
   dead `walk_best` copy during variable compaction (`walk_best` aliases `sim_sig` at
   `t_base + 6 * u64b` and is unconditionally re-initialized at the start of `full_walk_m7`).
3. **Canonical Names & `mfPatchFns` Compatibility (`Cause D`)**: Calls canonical `Full1`/`M5`
   symbols directly so only `2` new helpers (`full_fill_u64_m7`, `full_trans_bytes_m7`) are
   inserted via `mfPatchFns` alongside `12` in-place canonical replacements — zero duplicate
   helper bodies and native `bench/kissat/extract_c0_direct.py` compatibility.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7ms "
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

#define FL_ACTIVE  1u
#define FL_SUBSUME 8u
#define FL_ELIM_C  16u
#define FL_FACT_P  32u
#define FL_FACT_N  64u
#define FL_BONE0   128u
#define FL_BONE1   256u
#define FL_TRANS   512u
#define FL_SWEEP   1024u

extern bool kissat_parse_header(u64 p, u64 cend, KissatDimacs *d);
extern u64 full_fixed_bytes(u64 max_v);
extern void full_init_ptrs(FullHdr *h, u64 hdr_addr, u64 max_v);
extern void full_init_hdr(FullHdr *h, u64 mv, u64 max_v, u64 fuel);
extern u64 full_calc_max_v(u64 avail, u64 mv, u64 nc, u64 f0);
extern u64 full_calc_ext_cap_m5(u64 rem);
extern u64 full_calc_scr_cap_m5(u64 rem);
extern void full_init_arenas(FullHdr *h, u64 hdr_addr, u64 max_v, u64 avail_dyn);
extern void full_zero_tables1(FullHdr *h);
extern void full_zero_tables2(FullHdr *h);
extern bool full_init_state_m5(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel);

void full_fill_u64_m7(u64 *dst, u64 n, u64 val) {
  u64 i = 0ULL;
  while (i + 4ULL <= n) {
    dst[i] = val;
    dst[i + 1ULL] = val;
    dst[i + 2ULL] = val;
    dst[i + 3ULL] = val;
    i = i + 4ULL;
  }
  while (i < n) {
    dst[i] = val;
    i = i + 1ULL;
  }
}

void full_zero_tables1_m7ms(FullHdr *h) {
  u64 nlits = h->max_vars << 1;
  u64 n_v64 = ((nlits + 7ULL) & (~7ULL)) >> 3;
  full_fill_u64_m7((u64 *)h->values, n_v64, 0ULL);
  full_fill_u64_m7((u64 *)h->lit_mark, n_v64, 0ULL);
  full_fill_u64_m7((u64 *)h->watch_vec, nlits, 0ULL);
  if (h->wcap > 0ULL) {
    u32 *wstk = (u32 *)h->watch_stk;
    wstk[0] = 0u;
  }
  full_fill_u64_m7((u64 *)h->min_stk, h->min_depth, 0ULL);
  full_fill_u64_m7((u64 *)h->glue_used, 32ULL, 0ULL);
  full_fill_u64_m7((u64 *)h->last_learned, 8ULL, 0xFFFFFFFFFFFFFFFFULL);
}

void full_zero_tables2_m7ms(FullHdr *h) {
  u64 mv = h->d.mv;
  u64 mx = h->max_vars;
  u64 mb_words = ((mx + 7ULL) & (~7ULL)) >> 3;
  u64 ub_words = ((((mx + 1ULL) << 2) + 7ULL) & (~7ULL)) >> 3;
  full_fill_u64_m7((u64 *)h->mark, mb_words, 0ULL);
  full_fill_u64_m7((u64 *)h->phases_target, mb_words, 0ULL);
  full_fill_u64_m7((u64 *)h->phases_best, mb_words, 0ULL);
  full_fill_u64_m7((u64 *)h->phases, mb_words, 0x0101010101010101ULL);
  full_fill_u64_m7((u64 *)h->level, ub_words, 0ULL);
  full_fill_u64_m7((u64 *)h->frame_trail, ub_words, 0ULL);
  full_fill_u64_m7((u64 *)h->reason, ub_words, 0xFFFFFFFFFFFFFFFFULL);
  full_fill_u64_m7((u64 *)h->frame_dec, ub_words, 0xFFFFFFFFFFFFFFFFULL);
  full_fill_u64_m7((u64 *)h->score, mx, 0ULL);
  u32 *fl = (u32 *)h->flags;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 all_c = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_FACT_P | FL_FACT_N |
              FL_BONE0 | FL_BONE1 | FL_TRANS | FL_SWEEP;
  u64 v = 0ULL;
  while (v < mv) {
    fl[v] = all_c;
    hp[v] = (u32)v;
    ps[v] = (u32)v;
    qs[v] = (u32)(v + 1ULL);
    qp[v] = (v == 0ULL) ? 0xFFFFFFFFu : (u32)(v - 1ULL);
    qn[v] = (v + 1ULL >= mv) ? 0xFFFFFFFFu : (u32)(v + 1ULL);
    v = v + 1ULL;
  }
  while (v < mx) {
    fl[v] = 0u;
    hp[v] = 0u;
    ps[v] = 0xFFFFFFFFu;
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    qs[v] = 0u;
    v = v + 1ULL;
  }
}

u64 full_fixed_bytes_m7ms(u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vals_b = (nlits + 7ULL) & (~7ULL);
  u64 mark_b = (max_v + 7ULL) & (~7ULL);
  u64 u32_b = (((max_v + 1ULL) << 2) + 7ULL) & (~7ULL);
  u64 mdepth = (max_v + 1ULL < 1000ULL) ? (max_v + 1ULL) : 1000ULL;
  return (u64)sizeof(FullHdr) + 320ULL + vals_b + (mark_b << 2) +
         (u32_b * 15ULL) + (nlits << 3) + (max_v << 3) + (mdepth << 3);
}

u64 full_trans_bytes_m7(u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vals_b = (nlits + 7ULL) & (~7ULL);
  u64 u64b = max_v << 3;
  return (u64b * 7ULL) + vals_b;
}

void full_init_ptrs_m7ms(FullHdr *h, u64 hdr_addr, u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vb = (nlits + 7ULL) & (~7ULL);
  u64 mb = (max_v + 7ULL) & (~7ULL);
  u64 ub = (((max_v + 1ULL) << 2) + 7ULL) & (~7ULL);
  u64 u64b = max_v << 3;
  u64 mdepth = (max_v + 1ULL < 1000ULL) ? (max_v + 1ULL) : 1000ULL;
  u64 base = hdr_addr + (u64)sizeof(FullHdr);
  h->values = base; base = base + vb;
  h->mark = base; base = base + mb;
  h->phases = base; base = base + mb;
  h->phases_target = base; base = base + mb;
  h->phases_best = base; base = base + mb;
  h->flags = base; base = base + ub;
  h->level = base; base = base + ub;
  h->reason = base; base = base + ub;
  h->trail = base; base = base + ub;
  h->trail_pos = base; base = base + ub;
  h->tmp_lits = base; base = base + ub;
  h->heap = base; base = base + ub;
  h->pos = base; base = base + ub;
  h->min_clr = base; base = base + ub;
  h->shrink_stk = base; base = base + ub;
  h->q_prev = base; base = base + ub;
  h->q_next = base; base = base + ub;
  h->q_stamp = base; base = base + ub;
  h->frame_trail = base; base = base + ub;
  h->frame_dec = base; base = base + ub;
  h->watch_vec = base; base = base + (nlits << 3);
  h->score = base; base = base + u64b;
  h->min_stk = base; base = base + (mdepth << 3);
  h->glue_used = base; base = base + 256ULL;
  h->last_learned = base; base = base + 64ULL;
  h->arena = base;
  h->min_depth = mdepth;
}

void full_init_hdr_m7ms(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
  h->max_vars = max_v; h->cur_vars = mv; h->bva_cap = max_v - mv;
  h->unassigned = mv;
  h->delayed_len = 0ULL; h->arena_len = 0ULL; h->wlen = 1ULL; h->wusable = 0ULL;
  h->arena_garbage = 0ULL; h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL; h->num_redundant = 0ULL; h->num_binary = 0ULL;
  h->unflushed = 0ULL; h->probing = 0ULL; h->trail_end = 0ULL; h->propagated = 0ULL;
  h->cur_level = 0ULL; h->fuel = fuel; h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL; h->confl_lit0 = 0ULL; h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL; h->heap_len = mv; h->scinc = 1ULL << 28;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  h->rel_period = 1024ULL; h->rel_limit = 1048576ULL; h->rel_wait = 1024ULL;
  h->rel_u = 1ULL; h->rel_v = 1ULL; h->rel_trigger = 0ULL;
  h->conflicts = 0ULL; h->learned_lits = 0ULL; h->min_removed = 0ULL;
  h->stable = 0ULL; h->switched = 0ULL; h->mode_count = 0ULL;
  h->mode_confl_lim = 1000ULL; h->mode_tick_lim = 0ULL;
  h->mode_saved_ticks = 0ULL; h->search_ticks = 0ULL;
  h->q_first = (mv == 0ULL) ? 0xFFFFFFFFULL : 0ULL;
  h->q_last = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_idx = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_stamp = mv; h->q_cur_stamp = mv;
  h->target_assigned = 0ULL; h->best_assigned = 0ULL;
  h->rephase_limit = 1000ULL; h->rephased = 0ULL;
  h->reduce_limit = 1000ULL; h->reductions = 0ULL;
  h->tier1 = 2ULL; h->tier2 = 6ULL;
  h->restarts = 0ULL; h->restart_limit = 1ULL;
  h->ema_fast_biased = 0ULL; h->ema_fast_exp = 1ULL << 24;
  h->ema_slow_biased = 0ULL; h->ema_slow_exp = 1ULL << 24;
  h->oom = 0ULL; h->extend_len = 0ULL;
  h->rng_state = 0x9E3779B97F4A7C15ULL ^ (mv + 1ULL);
  h->chrono_levels = 100ULL; h->otfs_cnt = 0ULL; h->eager_sub_cnt = 0ULL;
  h->probe_limit = 2000ULL; h->probings = 0ULL;
  h->elim_limit = 5000ULL; h->eliminations = 0ULL; h->elim_bound = 0ULL;
  h->dense_mode = 0ULL; h->inconsistent = 0ULL; h->iterating = 0ULL;
  h->hbr_cnt = 0ULL; h->trans_cnt = 0ULL; h->viv_cnt = 0ULL; h->subst_cnt = 0ULL;
  h->cong_cnt = 0ULL; h->sweep_cnt = 0ULL; h->bve_cnt = 0ULL; h->bce_cnt = 0ULL;
  h->bva_cnt = 0ULL; h->walk_cnt_stat = 0ULL; h->fwd_sub_cnt = 0ULL; h->fwd_str_cnt = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
}

u64 full_calc_max_v_m7v5(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = 4096ULL;
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 need = full_fixed_bytes(max_v) + full_trans_bytes_m7(max_v);
  if (avail < need || avail - need < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_calc_ext_cap_m7ms(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = rem >> 5;
  if (c > 4194304ULL) { c = 4194304ULL; }
  return c & (~1ULL);
}

u64 full_calc_scr_cap_m7ms(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = (rem >= 16384ULL) ? (rem >> 4) : (rem >> 5);
  if (c > 1048576ULL) { c = 1048576ULL; }
  return c & (~1ULL);
}

void full_init_arenas_m7ms(FullHdr *h, u64 hdr_addr, u64 max_v, u64 avail_dyn) {
  u64 del_bytes = h->delayed_cap * 12ULL;
  u64 ext_cap = h->extend_cap;
  u64 tp = avail_dyn >> 3;
  u64 ap = (tp * 3ULL) / 5ULL;
  if (ap > 134217727ULL) { ap = 134217727ULL; }
  u64 rp = (ap + 5ULL) / 6ULL;
  u64 wp = tp - ap - rp;
  if (wp > 134217727ULL) { wp = 134217727ULL; }
  full_init_ptrs(h, hdr_addr, max_v);
  u64 base = h->arena + (ap << 3);
  h->watch_stk = base; base = base + (wp << 3);
  h->delayed = base; base = base + del_bytes;
  h->red_refs = base; base = base + (rp << 3);
  h->extend_stk = base; base = base + (ext_cap << 2);
  h->scratch_buf = base; base = base + (h->scratch_cap << 2);
  h->arena_cap = ap << 1; h->wcap = wp << 1; h->red_cap = rp << 1;

  u64 u64b = max_v << 3;
  u64 t_base = base;
  h->wsort = t_base;
  h->work_stk1 = t_base + u64b;
  h->work_stk2 = t_base + (u64b * 2ULL);
  h->tarjan_mark = t_base + (u64b * 3ULL);
  h->tarjan_reach = t_base + (u64b * 4ULL);
  h->repr = t_base + (u64b * 5ULL);
  h->walk_vals = t_base + (u64b * 5ULL);
  h->sim_sig = t_base + (u64b * 6ULL);
  h->walk_best = t_base + (u64b * 6ULL);
  h->lit_mark = t_base + (u64b * 7ULL);
}

bool full_init_state_m7ms(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  FullHdr *h = (FullHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) { return false; }
  u64 mv = h->d.mv; u64 nc = h->d.nc;
  u64 f0 = full_fixed_bytes(mv);
  u64 t0 = full_trans_bytes_m7(mv);
  if (avail < f0 + t0 || avail - (f0 + t0) < nc * 40ULL + 136ULL) { return false; }
  u64 max_v = full_calc_max_v(avail, mv, nc, f0);
  u64 tb = full_trans_bytes_m7(max_v);
  u64 rem = avail - full_fixed_bytes(max_v);
  if (rem < tb + nc * 40ULL + 136ULL) { return false; }
  u64 rem_arenas = rem - tb;
  u64 del_cap = (rem_arenas >= 524288ULL) ? 4096ULL : 8ULL;
  u64 del_bytes = del_cap * 12ULL;
  u64 ext_cap = full_calc_ext_cap_m5(rem_arenas);
  u64 scr_cap = full_calc_scr_cap_m5(rem_arenas);
  u64 dyn = del_bytes + (ext_cap << 2) + (scr_cap << 2);
  if (rem_arenas < dyn + nc * 40ULL + 136ULL) { ext_cap = 0ULL; scr_cap = 0ULL; dyn = del_bytes; }
  h->delayed_cap = del_cap; h->extend_cap = ext_cap; h->scratch_cap = scr_cap;
  full_init_arenas(h, hdr_addr, max_v, rem_arenas - dyn);
  full_init_hdr(h, mv, max_v, fuel);
  full_zero_tables1(h);
  full_zero_tables2(h);
  return true;
}

bool full_init_state_wrap_m7ms(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  return full_init_state_m5(cnf_ptr, cnf_end, hdr_addr, avail, fuel);
}

void full_compact_vars_m7ms(FullHdr *h, u64 old_cv, u64 ncv) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *ps = (u32 *)h->pos;
  u32 *inv = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  u64 nlits = old_cv << 1;
  while (l < nlits) { vals[l] = (i8)0; l = l + 1ULL; }
  u64 tgt_asg = 0ULL;
  u64 bst_asg = 0ULL;
  u64 nv = 0ULL;
  while (nv < ncv) {
    u32 ov = inv[nv];
    fl[nv] = fl[ov];
    ph[nv] = ph[ov];
    i8 tv = ptgt[ov];
    i8 bv = pbst[ov];
    ptgt[nv] = tv;
    pbst[nv] = bv;
    if (tv != (i8)0) { tgt_asg = tgt_asg + 1ULL; }
    if (bv != (i8)0) { bst_asg = bst_asg + 1ULL; }
    sc[nv] = sc[ov];
    qs[nv] = qs[ov];
    lvl[nv] = 0u;
    rsns[nv] = 0xFFFFFFFFu;
    nv = nv + 1ULL;
  }
  u64 v = ncv;
  while (v < old_cv) {
    fl[v] = 0u;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    sc[v] = 0ULL;
    qs[v] = 0u;
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    ps[v] = 0xFFFFFFFFu;
    v = v + 1ULL;
  }
  ftrl[0] = 0u;
  fdec[0] = 0xFFFFFFFFu;
  h->trail_end = 0ULL;
  h->propagated = 0ULL;
  h->cur_level = 0ULL;
  h->unflushed = 0ULL;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  h->target_assigned = tgt_asg;
  h->best_assigned = bst_asg;
  h->cur_vars = ncv;
  h->unassigned = ncv;
  if (ncv < h->d.mv) { h->d.mv = ncv; h->bva_cap = h->max_vars - ncv; }
}
"

/-- Helper #1 inserted before `"full_zero_tables1"`. -/
def m7msFillU64Fn : Fn :=
  ⟨"full_fill_u64_m7", [i64, i64, i64], [], full_fill_u64_m7_body⟩

/-- Helper #2 inserted before `"full_calc_max_v"`. -/
def m7msTransBytesFn : Fn :=
  ⟨"full_trans_bytes_m7", [i64], [i64], full_trans_bytes_m7_body⟩

/-- Ordered helper insertions compatible with `FullM7Fidelity.mfPatchFns` and `extract_c0_direct.py`. -/
def m7msBefores : List (Sym × List Fn) :=
  [ ("full_zero_tables1", [m7msFillU64Fn])
  , ("full_calc_max_v", [m7msTransBytesFn]) ]

def m7msZeroTables1Fn : Fn :=
  ⟨"full_zero_tables1", [i64], [], full_zero_tables1_m7ms_body⟩

def m7msZeroTables2Fn : Fn :=
  ⟨"full_zero_tables2", [i64], [], full_zero_tables2_m7ms_body⟩

def m7msFixedBytesFn : Fn :=
  ⟨"full_fixed_bytes", [i64], [i64], full_fixed_bytes_m7ms_body⟩

def m7msInitPtrsFn : Fn :=
  ⟨"full_init_ptrs", [i64, i64, i64], [], full_init_ptrs_m7ms_body⟩

def m7msInitHdrFn : Fn :=
  ⟨"full_init_hdr", [i64, i64, i64, i64], [], full_init_hdr_m7ms_body⟩

def m7msCalcMaxVFn : Fn :=
  ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], full_calc_max_v_m7v5_body⟩

def m7msCalcExtCapM5Fn : Fn :=
  ⟨"full_calc_ext_cap_m5", [i64], [i64], full_calc_ext_cap_m7ms_body⟩

def m7msCalcScrCapM5Fn : Fn :=
  ⟨"full_calc_scr_cap_m5", [i64], [i64], full_calc_scr_cap_m7ms_body⟩

def m7msInitArenasFn : Fn :=
  ⟨"full_init_arenas", [i64, i64, i64, i64], [], full_init_arenas_m7ms_body⟩

def m7msInitStateM5Fn : Fn :=
  ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], full_init_state_m7ms_body⟩

def m7msInitStateFn : Fn :=
  ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], full_init_state_wrap_m7ms_body⟩

def m7msCompactVarsFn : Fn :=
  ⟨"full_compact_vars", [i64, i64, i64], [], full_compact_vars_m7ms_body⟩

/-- All `12` disjoint canonical replacements wiring MemShrink + V5 BVA + compact cleanup. -/
def m7msRepls : List Fn :=
  [ m7msZeroTables1Fn
  , m7msZeroTables2Fn
  , m7msFixedBytesFn
  , m7msInitPtrsFn
  , m7msInitHdrFn
  , m7msCalcMaxVFn
  , m7msCalcExtCapM5Fn
  , m7msCalcScrCapM5Fn
  , m7msInitArenasFn
  , m7msInitStateM5Fn
  , m7msInitStateFn
  , m7msCompactVarsFn ]

/-- Standalone canonical-named `14`-fn MemShrink V5 module (`1` extern: `kissat_parse_header`, `0` exits). -/
def m7msStandaloneFns : List Fn :=
  [ m7msFillU64Fn
  , m7msZeroTables1Fn
  , m7msZeroTables2Fn
  , m7msFixedBytesFn
  , m7msInitPtrsFn
  , m7msInitHdrFn
  , m7msTransBytesFn
  , m7msCalcMaxVFn
  , m7msCalcExtCapM5Fn
  , m7msCalcScrCapM5Fn
  , m7msInitArenasFn
  , m7msInitStateM5Fn
  , m7msInitStateFn
  , m7msCompactVarsFn ]

def m7msStandaloneExterns : List Extern :=
  [⟨"kissat_parse_header", [i64, i64, i64], [.bool]⟩]

def m7msStandaloneModule : LeanQbe.T.Module :=
  { fns := m7msStandaloneFns, externs := m7msStandaloneExterns, exits := [] }

theorem full_fill_u64_m7_wf : Func.Wf full_fill_u64_m7_body := by t_wf_reify
theorem full_zero_tables1_m7ms_wf : Func.Wf full_zero_tables1_m7ms_body := by t_wf_reify
theorem full_zero_tables2_m7ms_wf : Func.Wf full_zero_tables2_m7ms_body := by t_wf_reify
theorem full_fixed_bytes_m7ms_wf : Func.Wf full_fixed_bytes_m7ms_body := by t_wf_reify
theorem full_trans_bytes_m7_wf : Func.Wf full_trans_bytes_m7_body := by t_wf_reify
theorem full_init_ptrs_m7ms_wf : Func.Wf full_init_ptrs_m7ms_body := by t_wf_reify
theorem full_init_hdr_m7ms_wf : Func.Wf full_init_hdr_m7ms_body := by t_wf_reify
theorem full_calc_max_v_m7v5_wf : Func.Wf full_calc_max_v_m7v5_body := by t_wf_reify
theorem full_calc_ext_cap_m7ms_wf : Func.Wf full_calc_ext_cap_m7ms_body := by t_wf_reify
theorem full_calc_scr_cap_m7ms_wf : Func.Wf full_calc_scr_cap_m7ms_body := by t_wf_reify
theorem full_init_arenas_m7ms_wf : Func.Wf full_init_arenas_m7ms_body := by t_wf_reify
theorem full_init_state_m7ms_wf : Func.Wf full_init_state_m7ms_body := by t_wf_reify
theorem full_init_state_wrap_m7ms_wf : Func.Wf full_init_state_wrap_m7ms_body := by t_wf_reify
theorem full_compact_vars_m7ms_wf : Func.Wf full_compact_vars_m7ms_body := by t_wf_reify

theorem m7msBefores_wf : ∀ p ∈ m7msBefores, ∀ h ∈ p.2, h.Wf := by
  intro p hp h hh
  simp only [m7msBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [List.mem_singleton] at hh; subst hh; exact full_fill_u64_m7_wf
  · simp only [List.mem_singleton] at hh; subst hh; exact full_trans_bytes_m7_wf

theorem m7msRepls_wf : ∀ r ∈ m7msRepls, r.Wf := by
  intro r hr
  simp only [m7msRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_zero_tables1_m7ms_wf
  · exact full_zero_tables2_m7ms_wf
  · exact full_fixed_bytes_m7ms_wf
  · exact full_init_ptrs_m7ms_wf
  · exact full_init_hdr_m7ms_wf
  · exact full_calc_max_v_m7v5_wf
  · exact full_calc_ext_cap_m7ms_wf
  · exact full_calc_scr_cap_m7ms_wf
  · exact full_init_arenas_m7ms_wf
  · exact full_init_state_m7ms_wf
  · exact full_init_state_wrap_m7ms_wf
  · exact full_compact_vars_m7ms_wf

theorem m7msStandaloneFns_wf : ∀ f ∈ m7msStandaloneFns, f.Wf := by
  intro f hf
  simp only [m7msStandaloneFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_fill_u64_m7_wf
  · exact full_zero_tables1_m7ms_wf
  · exact full_zero_tables2_m7ms_wf
  · exact full_fixed_bytes_m7ms_wf
  · exact full_init_ptrs_m7ms_wf
  · exact full_init_hdr_m7ms_wf
  · exact full_trans_bytes_m7_wf
  · exact full_calc_max_v_m7v5_wf
  · exact full_calc_ext_cap_m7ms_wf
  · exact full_calc_scr_cap_m7ms_wf
  · exact full_init_arenas_m7ms_wf
  · exact full_init_state_m7ms_wf
  · exact full_init_state_wrap_m7ms_wf
  · exact full_compact_vars_m7ms_wf

theorem m7msStandalone_acyclic : m7msStandaloneModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5

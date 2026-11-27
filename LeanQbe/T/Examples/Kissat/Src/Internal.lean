/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Solver Workspace Initialization, Flags & Fresh Variables (`Src/Internal.lean`)

Mirrors upstream `kissat/src/internal.c, flags.c, resize.c` (`15` live functions, DAG level `L1`):
- `full_zero_tables1` (R4: `kissat_zero_tables_part1`)
- `full_zero_tables2` (R4: `kissat_zero_tables_part2`)
- `full_fixed_bytes` (R4: `kissat_fixed_bytes`)
- `full_init_ptrs` (R4: `kissat_init_ptrs`)
- `full_init_hdr` (R4: `kissat_init_header`)
- `full_calc_max_v` (R4: `kissat_calc_max_vars`)
- `full_calc_ext_cap_m5` (R4: `kissat_calc_extend_cap`)
- `full_calc_scr_cap_m5` (R4: `kissat_calc_scratch_cap`)
- `full_init_arenas` (R4: `kissat_init_arenas`)
- `full_init_state_m5` (R4: `kissat_init_state_impl`)
- `full_init_state` (R4: `kissat_init_state`)
- `full_m6_mem_init` (R4: `kissat_init_workspace`)
- `full_set_inactive` (R4: `kissat_deactivate_variable`)
- `full_init_fresh_var` (R4: `kissat_init_fresh_variable`)
- `full_update_classify_fid`-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Internal

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! internal "
#include \"kissat_internal.h\"

extern bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d);
extern void m6_hdr_init(FullHdr *h);
extern void full_heap_up(FullHdr *h, u32 v);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_heap_push(FullHdr *h, u32 v);
extern u64 m6_wm4_get(FullHdr *h);
extern void m6_wm4_set(FullHdr *h, u64 v);

void full_zero_tables1(FullHdr *h) {
  u64 mx = h->max_vars;
  u64 nlits = mx << 1;
  i8 *vals = (i8 *)h->values;
  i8 *wvals = (i8 *)h->walk_vals;
  u8 *lmrk = (u8 *)h->lit_mark;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach;
  u64 i = 0ULL;
  while (i < nlits) {
    vals[i] = (i8)0; wvals[i] = (i8)0; lmrk[i] = (u8)0;
    wvec[i << 1] = 0u; wvec[(i << 1) + 1ULL] = 0u;
    repr[i] = (u32)i; tmk[i] = 0u; trc[i] = 0u;
    i = i + 1ULL;
  }
  u32 *wstk = (u32 *)h->watch_stk;
  if (h->wcap > 0ULL) { wstk[0] = 0u; }
  u32 *mstk = (u32 *)h->min_stk;
  u64 mcnt = h->min_depth << 1;
  u64 k = 0ULL;
  while (k < mcnt) { mstk[k] = 0u; k = k + 1ULL; }
  u32 *gu = (u32 *)h->glue_used;
  k = 0ULL;
  while (k < 64ULL) { gu[k] = 0u; k = k + 1ULL; }
  u32 *ll = (u32 *)h->last_learned;
  k = 0ULL;
  while (k < 16ULL) { ll[k] = 0xFFFFFFFFu; k = k + 1ULL; }
}

void full_zero_tables2(FullHdr *h) {
  u64 mx = h->max_vars;
  u8 *mrk = (u8 *)h->mark;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  u64 *sc = (u64 *)h->score;
  u64 *sig = (u64 *)h->sim_sig;
  u64 v = 0ULL;
  while (v < mx) {
    mrk[v] = (u8)0; ph[v] = (i8)0; ptgt[v] = (i8)0; pbst[v] = (i8)0; wbst[v] = (i8)1;
    lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
    ftrl[v] = 0u; fdec[v] = 0xFFFFFFFFu; sc[v] = 0ULL; sig[v] = 0ULL;
    fl[v] = 0u; hp[v] = 0u; ps[v] = 0xFFFFFFFFu;
    qp[v] = 0xFFFFFFFFu; qn[v] = 0xFFFFFFFFu; qs[v] = 0u;
    v = v + 1ULL;
  }
  ftrl[mx] = 0u; fdec[mx] = 0xFFFFFFFFu;
}

u64 full_fixed_bytes(u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vals_b = (nlits + 7ULL) & (~7ULL);
  u64 mark_b = (max_v + 7ULL) & (~7ULL);
  u64 u32_b = (((max_v + 1ULL) << 2) + 7ULL) & (~7ULL);
  u64 mdepth = (max_v + 1ULL < 1000ULL) ? (max_v + 1ULL) : 1000ULL;
  return (u64)sizeof(FullHdr) + 320ULL + (vals_b * 3ULL) + (mark_b * 5ULL) +
         (u32_b * 15ULL) + (nlits << 3) + (max_v << 6) + (mdepth << 3);
}

void full_init_ptrs(FullHdr *h, u64 hdr_addr, u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vb = (nlits + 7ULL) & (~7ULL);
  u64 mb = (max_v + 7ULL) & (~7ULL);
  u64 ub = (((max_v + 1ULL) << 2) + 7ULL) & (~7ULL);
  u64 u64b = max_v << 3;
  u64 mdepth = (max_v + 1ULL < 1000ULL) ? (max_v + 1ULL) : 1000ULL;
  u64 base = hdr_addr + (u64)sizeof(FullHdr);
  h->values = base; base = base + vb;
  h->walk_vals = base; base = base + vb;
  h->lit_mark = base; base = base + vb;
  h->mark = base; base = base + mb;
  h->phases = base; base = base + mb;
  h->phases_target = base; base = base + mb;
  h->phases_best = base; base = base + mb;
  h->walk_best = base; base = base + mb;
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
  h->repr = base; base = base + u64b;
  h->wsort = base; base = base + u64b;
  h->work_stk1 = base; base = base + u64b;
  h->work_stk2 = base; base = base + u64b;
  h->tarjan_mark = base; base = base + u64b;
  h->tarjan_reach = base; base = base + u64b;
  h->score = base; base = base + u64b;
  h->sim_sig = base; base = base + u64b;
  h->min_stk = base; base = base + (mdepth << 3);
  h->glue_used = base; base = base + 256ULL;
  h->last_learned = base; base = base + 64ULL;
  h->arena = base;
  h->min_depth = mdepth;
}

void full_init_hdr(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
  h->max_vars = max_v; h->cur_vars = mv; h->bva_cap = max_v - mv;
  h->unassigned = 0ULL;
  h->delayed_len = 0ULL; h->arena_len = 0ULL; h->wlen = 1ULL; h->wusable = 0ULL;
  h->arena_garbage = 0ULL; h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL; h->num_redundant = 0ULL; h->num_binary = 0ULL;
  h->unflushed = 0ULL; h->probing = 0ULL; h->trail_end = 0ULL; h->propagated = 0ULL;
  h->cur_level = 0ULL; h->fuel = fuel; h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL; h->confl_lit0 = 0ULL; h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL; h->heap_len = 0ULL; h->scinc = 0x3FF0000000000000ULL;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  h->rel_period = 1024ULL; h->rel_limit = 1048576ULL; h->rel_wait = 1024ULL;
  h->rel_u = 1ULL; h->rel_v = 1ULL; h->rel_trigger = 0ULL;
  h->conflicts = 0ULL; h->learned_lits = 0ULL; h->min_removed = 0ULL;
  h->stable = 0ULL; h->switched = 0ULL; h->mode_count = 0ULL;
  h->mode_confl_lim = 1000ULL; h->mode_tick_lim = 0ULL;
  h->mode_saved_ticks = 0ULL; h->search_ticks = 0ULL;
  h->q_first = 0xFFFFFFFFULL;
  h->q_last = 0xFFFFFFFFULL;
  h->q_search_idx = 0xFFFFFFFFULL;
  h->q_search_stamp = 0ULL; h->q_cur_stamp = 0ULL;
  h->target_assigned = 0ULL; h->best_assigned = 0ULL;
  h->rephase_limit = 1000ULL; h->rephased = 0ULL;
  h->reduce_limit = 1000ULL; h->reductions = 0ULL;
  h->tier1 = 2ULL; h->tier2 = 6ULL;
  h->restarts = 0ULL; h->restart_limit = 1ULL;
  h->ema_fast_biased = 0ULL; h->ema_fast_exp = 0x3FF0000000000000ULL;
  h->ema_slow_biased = 0ULL; h->ema_slow_exp = 0x3FF0000000000000ULL;
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

u64 full_calc_max_v(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = 32768ULL;
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 fixed = full_fixed_bytes(max_v);
  if (avail < fixed || avail - fixed < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_calc_ext_cap_m5(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = rem >> 5;
  if (c > 4194304ULL) { c = 4194304ULL; }
  return c & (~1ULL);
}

u64 full_calc_scr_cap_m5(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = (rem >= 16384ULL) ? (rem >> 4) : (rem >> 5);
  if (c > 8388608ULL) { c = 8388608ULL; }
  return c & (~1ULL);
}

void full_init_arenas(FullHdr *h, u64 hdr_addr, u64 max_v, u64 avail_dyn) {
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
  h->scratch_buf = base;
  h->arena_cap = ap << 1; h->wcap = wp << 1; h->red_cap = rp << 1;
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

bool full_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  return full_init_state_m5(cnf_ptr, cnf_end, hdr_addr, avail, fuel);
}

u64 full_m6_mem_init(u64 cnf_ptr, u64 cnf_end, u64 work_base, u64 avail, u64 fuel) {
  if (avail < M6_HDR_TOTAL_BYTES || work_base > 0xFFFFFFFFFFFFFFFFULL - avail) {
    return 0ULL;
  }
  u64 hdr_addr = work_base + M6_EXT_BYTES;
  if (!full_init_state(cnf_ptr, cnf_end, hdr_addr, avail - M6_EXT_BYTES, fuel)) {
    return 0ULL;
  }
  m6_hdr_init((FullHdr *)hdr_addr);
  return hdr_addr;
}

void full_set_inactive(FullHdr *h, u32 v, u32 flag) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  bool was_active = ((fl[v] & FL_ACTIVE) != 0u);
  if (was_active && vals[(u64)v << 1] == (i8)0 && h->unassigned > 0ULL) {
    h->unassigned = h->unassigned - 1ULL;
  }
  fl[v] = (fl[v] & (~FL_ACTIVE)) | flag;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 pv = qp[v];
  u32 nv = qn[v];
  if ((u64)pv < cv || (u64)nv < cv || h->q_first == (u64)v || h->q_last == (u64)v) {
    if (h->q_search_idx == (u64)v) {
      u32 srch = nv;
      if ((u64)srch >= cv) { srch = pv; }
      if ((u64)srch >= cv) {
        h->q_search_idx = 0xFFFFFFFFULL;
        h->q_search_stamp = 0ULL;
      } else {
        h->q_search_idx = (u64)srch;
        h->q_search_stamp = (u64)qs[srch];
      }
    }
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    if ((u64)pv >= cv) { h->q_first = (u64)nv; } else { qn[pv] = nv; }
    if ((u64)nv >= cv) { h->q_last = (u64)pv; } else { qp[nv] = pv; }
  }
  u32 *ps = (u32 *)h->pos;
  u32 *hp = (u32 *)h->heap;
  u64 n__ = h->heap_len;
  u32 p__ = ps[v];
  if (n__ > 0ULL && n__ <= cv && (u64)p__ < n__ && hp[p__] == v) {
    u32 last__ = hp[n__ - 1ULL];
    h->heap_len = n__ - 1ULL;
    ps[v] = 0xFFFFFFFFu;
    if (last__ != v && (u64)last__ < cv) {
      hp[p__] = last__;
      ps[last__] = p__;
      full_heap_up(h, last__);
      full_heap_down(h, last__);
    }
  }
}

void full_init_fresh_var(FullHdr *h, u32 fv) {
  i8 *vals = (i8 *)h->values; u8 *mrk = (u8 *)h->mark; u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason; u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev; u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u32 *wvec = (u32 *)h->watch_vec; u64 *sc = (u64 *)h->score;
  wvec[(u64)fv << 2] = 0u; wvec[((u64)fv << 2) + 1ULL] = 0u;
  wvec[((u64)fv << 2) + 2ULL] = 0u; wvec[((u64)fv << 2) + 3ULL] = 0u;
  vals[(u64)fv << 1] = (i8)0; vals[((u64)fv << 1) | 1ULL] = (i8)0;
  mrk[fv] = (u8)0; ph[fv] = (i8)0;
  ptgt[fv] = (i8)0; pbst[fv] = (i8)0; wbst[fv] = (i8)1;
  lvl[fv] = 0u; rsns[fv] = 0xFFFFFFFFu; ps[fv] = 0xFFFFFFFFu; sc[fv] = 0ULL;
  fl[fv] = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP |
           FL_FACT_P | FL_FACT_N | FL_BONE0 | FL_BONE1 | FL_TRANS;
  u32 old_first = (u32)h->q_first;
  qp[fv] = 0xFFFFFFFFu;
  if ((u64)old_first < h->cur_vars) { qn[fv] = old_first; qp[old_first] = fv; }
  else { qn[fv] = 0xFFFFFFFFu; h->q_last = (u64)fv; }
  h->q_first = (u64)fv; qs[fv] = 0u;
  if (h->stable != 0ULL) { full_heap_push(h, fv); }
  h->unassigned = h->unassigned + 1ULL;
}

void full_update_classify_fid(FullHdr *h) {
  u64 clauses = h->num_binary + h->num_irred;
  bool bigbig = false;
  if (clauses > 100000ULL && (h->num_binary * 100000ULL >= clauses * 990ULL)) {
    bigbig = true;
  }
  u64 wm4 = m6_wm4_get(h);
  if (bigbig) { wm4 = wm4 | 2ULL; }
  else { wm4 = wm4 & (~2ULL); }
  m6_wm4_set(h, wm4);
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Internal

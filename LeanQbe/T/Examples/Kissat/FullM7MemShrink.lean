module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Memory-Shrink Prototype A (`FullM7MemShrink`)

Standalone M7 memory-shrink prototype (`151 -> 90 B/var` resident fixed footprint, `-40.4%`)
combining:
1. **Resident/Transient Split (`90 B/var` fixed + `58 B/var` transient pool `t_base`)**:
   - Keeps the `17` hot search arrays resident from `hdr_addr + 1152ULL` (`values`, `mark`,
     `phases`, `phases_target`, `phases_best`, `flags`, `level`, `reason`, `trail`, `trail_pos`,
     `tmp_lits`, `heap`, `pos`, `min_clr`, `shrink_stk`, `q_prev`, `q_next`, `q_stamp`,
     `frame_trail`, `frame_dec`, `watch_vec`, `score`, plus `min_stk`, `glue_used`,
     `last_learned`) = `90 B/var`.
   - Places the `10` transient inprocessing/walk arrays totaling `61 B/var` into a dynamic
     transient region `t_base` immediately after `scratch_buf` (`7 * u64b + vb = 58 B/var`):
     `wsort`, `work_stk1` (full `8 B/var` for M6/M7 `WalkParse`/`CongIte`/`BveGates`),
     `work_stk2`, `tarjan_mark`, `tarjan_reach`, `repr` (shared with `walk_vals`),
     `sim_sig` (shared with `walk_best`), and dedicated non-aliased `lit_mark`.
2. **4x-Unrolled `u64` Bulk Table Fill (`full_fill_u64_m7`)**:
   - Used by `full_zero_tables1_m7` (including `lit_mark` zeroing for `FullLitMarksClear` and
     poisoned-memory safety) and `full_zero_tables2_m7`.
3. **M6/M7-Compatible Init Entrypoints & Drop-In `Fn` Handles**:
   - Standalone `m7MemShrinkFns` (`12` fns) / `m7MemShrinkModule` (`1` extern:
     `kissat_parse_header`, `0` exits) plus canonical drop-in handles matching `Full1` /
     `FullM5Orch`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrink

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7MemShrink "
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

void full_zero_tables1_m7(FullHdr *h) {
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

void full_zero_tables2_m7(FullHdr *h) {
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

u64 full_fixed_bytes_m7(u64 max_v) {
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

void full_init_ptrs_m7(FullHdr *h, u64 hdr_addr, u64 max_v) {
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

void full_init_hdr_m7(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
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

u64 full_calc_max_v_m7(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = (mv >> 1) + 16ULL;
    if (cand > 4096ULL) { cand = 4096ULL; }
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 need = full_fixed_bytes_m7(max_v) + full_trans_bytes_m7(max_v);
  if (avail < need || avail - need < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_calc_ext_cap_m7(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = rem >> 5;
  if (c > 4194304ULL) { c = 4194304ULL; }
  return c & (~1ULL);
}

u64 full_calc_scr_cap_m7(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = (rem >= 16384ULL) ? (rem >> 4) : (rem >> 5);
  if (c > 1048576ULL) { c = 1048576ULL; }
  return c & (~1ULL);
}

void full_init_arenas_m7(FullHdr *h, u64 hdr_addr, u64 max_v, u64 avail_dyn) {
  u64 del_bytes = h->delayed_cap * 12ULL;
  u64 ext_cap = h->extend_cap;
  u64 tp = avail_dyn >> 3;
  u64 ap = (tp * 3ULL) / 5ULL;
  if (ap > 134217727ULL) { ap = 134217727ULL; }
  u64 rp = (ap + 5ULL) / 6ULL;
  u64 wp = tp - ap - rp;
  if (wp > 134217727ULL) { wp = 134217727ULL; }
  full_init_ptrs_m7(h, hdr_addr, max_v);
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

bool full_init_state_m7(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  FullHdr *h = (FullHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) { return false; }
  u64 mv = h->d.mv; u64 nc = h->d.nc;
  u64 f0 = full_fixed_bytes_m7(mv);
  u64 t0 = full_trans_bytes_m7(mv);
  if (avail < f0 + t0 || avail - (f0 + t0) < nc * 40ULL + 136ULL) { return false; }
  u64 max_v = full_calc_max_v_m7(avail, mv, nc, f0);
  u64 tb = full_trans_bytes_m7(max_v);
  u64 rem = avail - full_fixed_bytes_m7(max_v);
  if (rem < tb + nc * 40ULL + 136ULL) { return false; }
  u64 rem_arenas = rem - tb;
  u64 del_cap = (rem_arenas >= 524288ULL) ? 4096ULL : 8ULL;
  u64 del_bytes = del_cap * 12ULL;
  u64 ext_cap = full_calc_ext_cap_m7(rem_arenas);
  u64 scr_cap = full_calc_scr_cap_m7(rem_arenas);
  u64 dyn = del_bytes + (ext_cap << 2) + (scr_cap << 2);
  if (rem_arenas < dyn + nc * 40ULL + 136ULL) { ext_cap = 0ULL; scr_cap = 0ULL; dyn = del_bytes; }
  h->delayed_cap = del_cap; h->extend_cap = ext_cap; h->scratch_cap = scr_cap;
  full_init_arenas_m7(h, hdr_addr, max_v, rem_arenas - dyn);
  full_init_hdr_m7(h, mv, max_v, fuel);
  full_zero_tables1_m7(h);
  full_zero_tables2_m7(h);
  return true;
}
"

/-- Canonical external callee list for `m7MemShrinkModule` (`kissat_parse_header`). -/
def m7MemShrinkExterns : List Extern :=
  [⟨"kissat_parse_header", [i64, i64, i64], [.bool]⟩]

/-- Standalone `m7MemShrink` function list (`12` functions). -/
def m7MemShrinkFns : List Fn := m7MemShrink_fns

/-- Drop-in `Fn` handle preserving `"full_zero_tables1"` (`[i64] -> []`). -/
def m7ZeroTables1Fn : Fn :=
  ⟨"full_zero_tables1", [i64], [], full_zero_tables1_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_zero_tables2"` (`[i64] -> []`). -/
def m7ZeroTables2Fn : Fn :=
  ⟨"full_zero_tables2", [i64], [], full_zero_tables2_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_fixed_bytes"` (`[i64] -> [i64]`). -/
def m7FixedBytesFn : Fn :=
  ⟨"full_fixed_bytes", [i64], [i64], full_fixed_bytes_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_init_ptrs"` (`[i64, i64, i64] -> []`). -/
def m7InitPtrsFn : Fn :=
  ⟨"full_init_ptrs", [i64, i64, i64], [], full_init_ptrs_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_init_hdr"` (`[i64, i64, i64, i64] -> []`). -/
def m7InitHdrFn : Fn :=
  ⟨"full_init_hdr", [i64, i64, i64, i64], [], full_init_hdr_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_calc_max_v"` (`[i64, i64, i64, i64] -> [i64]`). -/
def m7CalcMaxVFn : Fn :=
  ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], full_calc_max_v_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_calc_ext_cap_m5"` (`[i64] -> [i64]`). -/
def m7CalcExtCapM5Fn : Fn :=
  ⟨"full_calc_ext_cap_m5", [i64], [i64], full_calc_ext_cap_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_calc_scr_cap_m5"` (`[i64] -> [i64]`). -/
def m7CalcScrCapM5Fn : Fn :=
  ⟨"full_calc_scr_cap_m5", [i64], [i64], full_calc_scr_cap_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_init_arenas"` (`[i64, i64, i64, i64] -> []`). -/
def m7InitArenasFn : Fn :=
  ⟨"full_init_arenas", [i64, i64, i64, i64], [], full_init_arenas_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_init_state"` (`[i64, i64, i64, i64, i64] -> [.bool]`). -/
def m7InitStateFn : Fn :=
  ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], full_init_state_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_init_state_m5"`. -/
def m7InitStateM5Fn : Fn :=
  ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], full_init_state_m7_body⟩

/-- Standalone M7 Memory-Shrink module (`12` functions, `1` extern, `0` exits). -/
def m7MemShrinkModule : LeanQbe.T.Module :=
  { fns := m7MemShrinkFns, externs := m7MemShrinkExterns, exits := [] }

theorem full_fill_u64_m7_wf : Func.Wf full_fill_u64_m7_body := by t_wf_reify
theorem full_zero_tables1_m7_wf : Func.Wf full_zero_tables1_m7_body := by t_wf_reify
theorem full_zero_tables2_m7_wf : Func.Wf full_zero_tables2_m7_body := by t_wf_reify
theorem full_fixed_bytes_m7_wf : Func.Wf full_fixed_bytes_m7_body := by t_wf_reify
theorem full_trans_bytes_m7_wf : Func.Wf full_trans_bytes_m7_body := by t_wf_reify
theorem full_init_ptrs_m7_wf : Func.Wf full_init_ptrs_m7_body := by t_wf_reify
theorem full_init_hdr_m7_wf : Func.Wf full_init_hdr_m7_body := by t_wf_reify
theorem full_calc_max_v_m7_wf : Func.Wf full_calc_max_v_m7_body := by t_wf_reify
theorem full_calc_ext_cap_m7_wf : Func.Wf full_calc_ext_cap_m7_body := by t_wf_reify
theorem full_calc_scr_cap_m7_wf : Func.Wf full_calc_scr_cap_m7_body := by t_wf_reify
theorem full_init_arenas_m7_wf : Func.Wf full_init_arenas_m7_body := by t_wf_reify
theorem full_init_state_m7_wf : Func.Wf full_init_state_m7_body := by t_wf_reify

theorem m7ZeroTables1Fn_wf : m7ZeroTables1Fn.Wf := full_zero_tables1_m7_wf
theorem m7ZeroTables2Fn_wf : m7ZeroTables2Fn.Wf := full_zero_tables2_m7_wf
theorem m7FixedBytesFn_wf : m7FixedBytesFn.Wf := full_fixed_bytes_m7_wf
theorem m7InitPtrsFn_wf : m7InitPtrsFn.Wf := full_init_ptrs_m7_wf
theorem m7InitHdrFn_wf : m7InitHdrFn.Wf := full_init_hdr_m7_wf
theorem m7CalcMaxVFn_wf : m7CalcMaxVFn.Wf := full_calc_max_v_m7_wf
theorem m7CalcExtCapM5Fn_wf : m7CalcExtCapM5Fn.Wf := full_calc_ext_cap_m7_wf
theorem m7CalcScrCapM5Fn_wf : m7CalcScrCapM5Fn.Wf := full_calc_scr_cap_m7_wf
theorem m7InitArenasFn_wf : m7InitArenasFn.Wf := full_init_arenas_m7_wf
theorem m7InitStateFn_wf : m7InitStateFn.Wf := full_init_state_m7_wf
theorem m7InitStateM5Fn_wf : m7InitStateM5Fn.Wf := full_init_state_m7_wf

theorem m7MemShrinkFns_wf : ∀ f ∈ m7MemShrinkFns, f.Wf := by
  simp only [m7MemShrinkFns, m7MemShrink_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_fill_u64_m7_wf, full_zero_tables1_m7_wf, full_zero_tables2_m7_wf,
    full_fixed_bytes_m7_wf, full_trans_bytes_m7_wf, full_init_ptrs_m7_wf,
    full_init_hdr_m7_wf, full_calc_max_v_m7_wf, full_calc_ext_cap_m7_wf,
    full_calc_scr_cap_m7_wf, full_init_arenas_m7_wf, full_init_state_m7_wf⟩

theorem m7MemShrink_acyclic : m7MemShrinkModule.checkAcyclic = true := by
  t_kernel_rfl

/-! ## `spliceFns` / `FullM7` Compatibility Helpers -/

/-- The `11` internal `_m7` helper functions (`full_fill_u64_m7` .. `full_init_arenas_m7`). -/
def m7MemShrinkHelperFns : List Fn :=
  m7MemShrink_fns.take 11

/-- All `11` canonical drop-in `Fn` handles overriding `FullM7.m7Fns` entries `41..51`. -/
def m7MemShrinkCanonFns : List Fn :=
  [ m7ZeroTables1Fn, m7ZeroTables2Fn, m7FixedBytesFn, m7InitPtrsFn, m7InitHdrFn
  , m7CalcMaxVFn, m7CalcExtCapM5Fn, m7CalcScrCapM5Fn, m7InitArenasFn
  , m7InitStateFn, m7InitStateM5Fn ]

/-- Replace each `Fn` in `fs` matching a name in `repls` (matching `FullM7Splice.spliceFns`). -/
def spliceM7Repls (repls fs : List Fn) : List Fn :=
  fs.map fun f => (repls.find? (·.name == f.name)).getD f

/-- Insert `helpers` immediately before the first function matching `anchor` (if present). -/
def insertHelpersBefore (anchor : Sym) (helpers : List Fn) : List Fn → List Fn
  | [] => []
  | f :: fs =>
    if f.name == anchor then helpers ++ f :: fs
    else f :: insertHelpersBefore anchor helpers fs

/-- Splice all `11` `_m7` helper functions before `"full_zero_tables1"` (if present, else at
head) and apply `spliceM7Repls m7MemShrinkCanonFns` to replace the `11` canonical handles. -/
def spliceM7MemShrinkFns (fs : List Fn) : List Fn :=
  spliceM7Repls m7MemShrinkCanonFns
    (if fs.any (·.name == "full_zero_tables1") then
      insertHelpersBefore "full_zero_tables1" m7MemShrinkHelperFns fs
    else m7MemShrinkHelperFns ++ fs)

/-- Apply `spliceM7MemShrinkFns` to `M.fns`, preserving `externs` and `exits`. -/
def spliceM7MemShrinkModule (M : LeanQbe.T.Module) : LeanQbe.T.Module :=
  { M with fns := spliceM7MemShrinkFns M.fns }

theorem m7MemShrinkHelper_wf : ∀ f ∈ m7MemShrinkHelperFns, f.Wf :=
  fun _ hf => m7MemShrinkFns_wf _ (List.mem_of_mem_take hf)

theorem m7MemShrinkCanon_wf : ∀ f ∈ m7MemShrinkCanonFns, f.Wf := by
  simp only [m7MemShrinkCanonFns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨m7ZeroTables1Fn_wf, m7ZeroTables2Fn_wf, m7FixedBytesFn_wf, m7InitPtrsFn_wf,
    m7InitHdrFn_wf, m7CalcMaxVFn_wf, m7CalcExtCapM5Fn_wf, m7CalcScrCapM5Fn_wf,
    m7InitArenasFn_wf, m7InitStateFn_wf, m7InitStateM5Fn_wf⟩

theorem spliceM7Repls_wf {repls fs : List Fn}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf) :
    ∀ f ∈ spliceM7Repls repls fs, f.Wf := by
  intro f hf
  rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => exact hfs g hg
  | some r => exact hr r (List.mem_of_find?_eq_some h)

theorem insertHelpersBefore_cons (anchor : Sym) (helpers : List Fn) (x : Fn) (xs : List Fn) :
    insertHelpersBefore anchor helpers (x :: xs) =
      if x.name == anchor then helpers ++ x :: xs
      else x :: insertHelpersBefore anchor helpers xs := rfl

private theorem insertHelpersBefore_mem (anchor : Sym) (helpers : List Fn) :
    ∀ {fs : List Fn} {f : Fn},
      f ∈ insertHelpersBefore anchor helpers fs → f ∈ helpers ∨ f ∈ fs
  | [], _, h => False.elim (List.not_mem_nil h)
  | x :: xs, f, h => by
    rw [insertHelpersBefore_cons] at h
    split at h
    · rcases List.mem_append.mp h with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
    · rcases List.mem_cons.mp h with rfl | hx
      · exact Or.inr List.mem_cons_self
      · rcases insertHelpersBefore_mem anchor helpers hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (List.mem_cons_of_mem x hx)

theorem spliceM7MemShrinkFns_wf {fs : List Fn} (hfs : ∀ f ∈ fs, f.Wf) :
    ∀ f ∈ spliceM7MemShrinkFns fs, f.Wf := by
  unfold spliceM7MemShrinkFns
  refine spliceM7Repls_wf (fun f hf => ?_) m7MemShrinkCanon_wf
  split at hf
  · rcases insertHelpersBefore_mem "full_zero_tables1" m7MemShrinkHelperFns hf with hm | hm
    · exact m7MemShrinkHelper_wf f hm
    · exact hfs f hm
  · rcases List.mem_append.mp hf with hm | hm
    · exact m7MemShrinkHelper_wf f hm
    · exact hfs f hm

end LeanQbe.T.Examples.Kissat.FullM7MemShrink

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 11 PR 2: S11-3 Lazy Activation + S11-5 True `tumble` + `LUCKY_EXT`

Pure C0/IR layer (`0` `*Proof*` imports, `0` `import all`, every function `<= 3` args for SysV
x64 & Arm64 ABI) implementing:
1. **`S11-3` Lazy Activation + `1 - 1/k` Initial VSIDS Scores:**
   - `full_zero_tables2_fid` (replaces `full_zero_tables2`): initializes all `0..max_vars-1`
     inactive (`flags = 0`, unlinked VMTF, `pos = 0xFFFFFFFF`, `score = 0`).
   - `full_init_hdr_fid` (replaces `full_init_hdr`): initializes `unassigned = 0`, `heap_len = 0`,
     empty VMTF queue (`q_first = q_last = q_search_idx = 0xFFFFFFFF`, stamps `0`).
   - `full_activate_lit_fid` (helper inserted before `full_ingest_cl`): activates variable `v`
     on first kept occurrence in a non-tautological, non-satisfied clause, increments activation
     counter `k` in `glue_used[31]` (`TUM_GU_ACTIVATED`, disjoint from `SWP_GU_* [28..30]`,
     `M7_GU_EMA [36..55]`, `M7_GU_RANDEC [56..63]`), links onto VMTF tail, sets
     `score[v] = scinc - scinc / k`, and pushes via `full_heap_push`.
2. **`S11-5` True `tumble` Variable Renaming (0 New Memory, 0 `FullWitnessInv` Changes):**
   - `full_ingest_cl_tum` (replaces `full_ingest_cl`): maps external DIMACS variables to internal
     indices on first occurrence using `core.frame_dec` (`imap`) and `scratch.extend_len` (`next`)
     when `extend_cap > d.mv`, then activates kept literals via `full_activate_lit_fid`.
   - `full_tumble_finish_fid` (helper inserted before `full_parse_body_m6`): records the inverse
     permutation block `ext[0] = EXT_BLK_FLAG | EXT_PERM_FLAG | mv`, `ext[1+e] = imap[e]`
     (encoding unmapped entries as `EXT_UNMAPPED = 0x7FFFFFFFu` so bit 31 is clear) and resets
     `frame_dec[0..mv-1] = 0xFFFFFFFFu`.
   - `full_parse_body_tum` (replaces `full_parse_body_m6`): initializes `glue_used[31] = 0` and
     (when `extend_cap > d.mv`) `frame_dec[0..mv-1] = 0xFFFFFFFFu`, `extend_len = 0`, runs the
     exact M6 eager-BCP parse loop, and calls `full_tumble_finish_fid` before returning `1`/`20`.
3. **SAT Unpermutation (`Full.fullExtendSpec` / `fullExtendSlice` Preserved Verbatim):**
   - `full_extend_core_fid` = verbatim `FullM4.full_extend_body` (unmodified; safely skips the
     bottom `EXT_PERM_FLAG` block because `EXT_UNMAPPED` clears bit 31 and `EXT_PERM_FLAG` puts
     `blk >> 1 >= 2^28 > mv`).
   - `full_unperm_fid` (helper inserted before `full_extend`): two-pass even/odd in-place `vals[]`
     unpermutation reading `ext[0..mv]` read-only and mutating ONLY `values[]`, preserving
     `fullExtendSlice` verbatim so `kissat_solve_bytes_m6` needs zero changes.
   - `full_extend_tum` (replaces `full_extend`): calls `full_extend_core_fid` then
     `full_unperm_fid`.
4. **`LUCKY_EXT` External-Order Traversal + Post-Compaction `factor` Extension Vars:**
   - `full_lucky_ord_fid` (helper inserted before `full_lucky_scan`): composes `ext[0..mv]`
     through all subsequent `EXT_COMPACT_FLAG` blocks into `tarjan_reach[0..n)`, then appends
     every remaining `v < cur_vars` (including `factor` extension variables created before or
     after compaction) so `asconhashv12`, `yosys_bmc_alloc80`, `php-016-016`, `bart22` all see
     exact external + fresh-extension order.
   - `full_lucky_scan_tum` (replaces `full_lucky_scan`): walks `ord[0..n)` forward/backward.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep11Tum "
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

#define FL_ACTIVE             1u
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u
#define FL_SWEEP              1024u

#define EXT_BLK_FLAG          0x80000000u
#define EXT_COMPACT_FLAG      0x40000000u
#define EXT_PERM_FLAG         0x20000000u
#define EXT_CNT_MASK          0x3FFFFFFFu
#define EXT_PERM_MASK         0x1FFFFFFFu
#define EXT_UNMAPPED          0x7FFFFFFFu

#define TUM_GU_ACTIVATED      31ULL

extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern u64 kissat_next_lit(u64 cend, KissatDimacs *d);
extern void full_heap_push(FullHdr *h, u32 v);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern bool full_skip_cl(u64 cnf_end, KissatDimacs *d);
extern u64 full_ingest_cl(FullHdr *h, u64 cnf_end);
extern u64 full_propagate(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_analyze(FullHdr *h);
extern void full_extend_core_fid(FullHdr *h);

void full_zero_tables2_fid(FullHdr *h) {
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
    mrk[v] = (u8)0; ph[v] = (i8)1; ptgt[v] = (i8)0; pbst[v] = (i8)0; wbst[v] = (i8)1;
    lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
    ftrl[v] = 0u; fdec[v] = 0xFFFFFFFFu; sc[v] = 0ULL; sig[v] = 0ULL;
    fl[v] = 0u; hp[v] = 0u; ps[v] = 0xFFFFFFFFu;
    qp[v] = 0xFFFFFFFFu; qn[v] = 0xFFFFFFFFu; qs[v] = 0u;
    v = v + 1ULL;
  }
  ftrl[mx] = 0u; fdec[mx] = 0xFFFFFFFFu;
}

void full_init_hdr_fid(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
  h->max_vars = max_v; h->cur_vars = mv; h->bva_cap = max_v - mv;
  h->unassigned = 0ULL;
  h->delayed_len = 0ULL; h->arena_len = 0ULL; h->wlen = 1ULL; h->wusable = 0ULL;
  h->arena_garbage = 0ULL; h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL; h->num_redundant = 0ULL; h->num_binary = 0ULL;
  h->unflushed = 0ULL; h->probing = 0ULL; h->trail_end = 0ULL; h->propagated = 0ULL;
  h->cur_level = 0ULL; h->fuel = fuel; h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL; h->confl_lit0 = 0ULL; h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL; h->heap_len = 0ULL; h->scinc = 1ULL << 28;
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

void full_activate_lit_fid(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *fl = (u32 *)h->flags;
  if ((fl[v] & FL_ACTIVE) != 0u) { return; }
  u32 all_c = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_FACT_P | FL_FACT_N |
              FL_BONE0 | FL_BONE1 | FL_TRANS | FL_SWEEP;
  fl[v] = fl[v] | all_c;
  h->unassigned = h->unassigned + 1ULL;
  u32 *gu = (u32 *)h->glue_used;
  u32 k = gu[TUM_GU_ACTIVATED];
  if (k < 0xFFFFFFFFu) { k = k + 1u; }
  gu[TUM_GU_ACTIVATED] = k;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 old_last = (u32)h->q_last;
  qp[v] = old_last;
  qn[v] = 0xFFFFFFFFu;
  h->q_last = (u64)v;
  if ((u64)old_last >= cv) {
    h->q_first = (u64)v;
  } else {
    qn[old_last] = v;
  }
  h->q_cur_stamp = h->q_cur_stamp + 1ULL;
  qs[v] = (u32)h->q_cur_stamp;
  h->q_search_idx = (u64)v;
  h->q_search_stamp = (u64)qs[v];
  u64 *sc = (u64 *)h->score;
  u64 k64 = (u64)k;
  sc[v] = h->scinc - (h->scinc / k64);
  full_heap_push(h, v);
}

u64 full_ingest_cl_tum(FullHdr *h, u64 cnf_end) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u8 *mrk = (u8 *)h->mark;
  i8 *vals = (i8 *)h->values;
  u32 *fd = (u32 *)h->frame_dec;
  bool tum = (h->extend_cap > h->d.mv);
  u32 tlen = 0u;
  bool taut = false;
  bool err = false;
  while (true) {
    u64 st = kissat_next_lit(cnf_end, &h->d);
    if (st == 0ULL) { err = true; break; }
    if (st == 1ULL) { break; }
    u32 lit = (u32)h->d.val;
    u32 ev = lit >> 1;
    if ((u64)ev >= h->d.mv) { err = true; break; }
    u32 v = ev;
    if (tum) {
      u32 iv = fd[ev];
      if (iv == 0xFFFFFFFFu) {
        u64 nxt = h->extend_len;
        if (nxt >= h->d.mv) { err = true; break; }
        iv = (u32)nxt;
        fd[ev] = iv;
        h->extend_len = nxt + 1ULL;
      }
      v = iv;
      lit = (iv << 1) | (lit & 1u);
    }
    u8 ptag = (u8)((lit & 1u) + 1u);
    u8 m = mrk[v];
    if (m == (u8)0) {
      if ((u64)tlen >= h->d.mv) { err = true; break; }
      mrk[v] = ptag; tmp[tlen] = lit; tlen = tlen + 1u;
    } else if (m != ptag) {
      taut = true;
    }
  }
  u32 k = 0u;
  while (k < tlen) {
    u32 kv = tmp[k] >> 1;
    if ((u64)kv < h->d.mv) { mrk[kv] = (u8)0; }
    k = k + 1u;
  }
  if (err) { return 0ULL; }
  if (taut) { return 1ULL; }
  u32 keep = 0u;
  u32 i = 0u;
  while (i < tlen) {
    u32 l = tmp[i];
    i8 lv = vals[l];
    if (lv > (i8)0) { return 1ULL; }
    if (lv == (i8)0) { tmp[keep] = l; keep = keep + 1u; }
    i = i + 1u;
  }
  u32 a = 0u;
  while (a < keep) {
    full_activate_lit_fid(h, tmp[a] >> 1);
    a = a + 1u;
  }
  if (keep == 0u) { return 2ULL; }
  if (keep == 1u) { full_assign_lvl(h, tmp[0], 0xFFFFFFFFu, 0u); return 1ULL; }
  u64 cid = full_add_clause(h, keep, 0u, false);
  if (cid == 0xFFFFFFFFULL) { return 3ULL; }
  return 1ULL;
}

void full_tumble_finish_fid(FullHdr *h) {
  if (h->extend_cap <= h->d.mv) { return; }
  u32 *fd = (u32 *)h->frame_dec;
  u32 *ext = (u32 *)h->extend_stk;
  u64 mv = h->d.mv;
  u64 e = 0ULL;
  while (e < mv) {
    u32 iv = fd[e];
    ext[e + 1ULL] = (iv == 0xFFFFFFFFu) ? EXT_UNMAPPED : iv;
    fd[e] = 0xFFFFFFFFu;
    e = e + 1ULL;
  }
  ext[0] = EXT_BLK_FLAG | EXT_PERM_FLAG | (u32)mv;
  h->extend_len = mv + 1ULL;
}

u64 full_parse_body_tum(FullHdr *h, u64 cnf_end) {
  u32 *gu = (u32 *)h->glue_used;
  gu[TUM_GU_ACTIVATED] = 0u;
  if (h->extend_cap > h->d.mv) {
    u32 *fd = (u32 *)h->frame_dec;
    u64 mv = h->d.mv;
    u64 e = 0ULL;
    while (e < mv) {
      fd[e] = 0xFFFFFFFFu;
      e = e + 1ULL;
    }
    h->extend_len = 0ULL;
  }
  bool unsat_seen = false;
  bool oom_seen = false;
  bool has_cl = false;
  u64 i = 0ULL;
  while (i < h->d.nc) {
    if (unsat_seen) {
      if (!full_skip_cl(cnf_end, &h->d)) { return 0ULL; }
    } else if (oom_seen) {
      return 0ULL;
    } else {
      u64 old_te = h->trail_end;
      u64 st = full_ingest_cl(h, cnf_end);
      if (st == 0ULL) { return 0ULL; }
      if (st == 2ULL) { unsat_seen = true; }
      else if (st == 3ULL) { oom_seen = true; }
      else {
        if (h->trail_end == old_te) { has_cl = true; }
        if (has_cl && h->propagated < h->trail_end) {
          u64 saved_fuel = h->fuel;
          u64 saved_ticks = h->search_ticks;
          u64 pr = full_propagate(h);
          h->fuel = saved_fuel;
          h->search_ticks = saved_ticks;
          if (pr == 1ULL) { unsat_seen = true; }
          else if (pr == 2ULL) { h->oom = 0ULL; oom_seen = true; }
        }
      }
    }
    i = i + 1ULL;
  }
  if (oom_seen) { return 0ULL; }
  h->d.cur = kissat_skip_ws_comments(h->d.cur, cnf_end);
  if (h->d.cur != cnf_end) { return 0ULL; }
  full_tumble_finish_fid(h);
  if (unsat_seen) { return 20ULL; }
  return 1ULL;
}

void full_unperm_fid(FullHdr *h) {
  u64 len = h->extend_len;
  if (len == 0ULL || len > h->extend_cap) { return; }
  u32 *ext = (u32 *)h->extend_stk;
  u32 head = ext[0];
  if ((head & (EXT_BLK_FLAG | EXT_COMPACT_FLAG | EXT_PERM_FLAG)) !=
      (EXT_BLK_FLAG | EXT_PERM_FLAG)) {
    return;
  }
  u64 mv = (u64)(head & EXT_PERM_MASK);
  u64 mx = h->max_vars;
  if (mv > mx || 1ULL + mv > len) { return; }
  i8 *vals = (i8 *)h->values;
  u64 e = 0ULL;
  while (e < mv) {
    u32 iv = ext[1ULL + e];
    i8 pv = (i8)1;
    if ((u64)iv < mx) {
      i8 vv = vals[(u64)iv << 1];
      if (vv < (i8)0) { pv = (i8)(-1); }
    }
    vals[(e << 1) | 1ULL] = pv;
    e = e + 1ULL;
  }
  e = 0ULL;
  while (e < mv) {
    i8 pv = vals[(e << 1) | 1ULL];
    vals[e << 1] = pv;
    vals[(e << 1) | 1ULL] = (pv > (i8)0) ? (i8)(-1) : (i8)1;
    e = e + 1ULL;
  }
}

void full_extend_tum(FullHdr *h) {
  full_extend_core_fid(h);
  full_unperm_fid(h);
}

u64 full_lucky_ord_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 mx = h->max_vars;
  u32 *ord = (u32 *)h->tarjan_reach;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *ext = (u32 *)h->extend_stk;
  u64 len = h->extend_len;
  bool has_perm = false;
  u64 orig_mv = 0ULL;
  if (len > 0ULL && len <= h->extend_cap) {
    u32 h0 = ext[0];
    if ((h0 & (EXT_BLK_FLAG | EXT_COMPACT_FLAG | EXT_PERM_FLAG)) ==
        (EXT_BLK_FLAG | EXT_PERM_FLAG)) {
      orig_mv = (u64)(h0 & EXT_PERM_MASK);
      if (orig_mv <= mx && 1ULL + orig_mv <= len) {
        has_perm = true;
      }
    }
  }
  if (!has_perm) {
    u64 v = 0ULL;
    while (v < cv) {
      ord[v] = (u32)v;
      v = v + 1ULL;
    }
    return cv;
  }
  u64 e = 0ULL;
  while (e < orig_mv) {
    ord[e] = ext[1ULL + e];
    e = e + 1ULL;
  }
  u64 p = 1ULL + orig_mv;
  while (p < len) {
    u32 head = ext[p];
    if ((head & (EXT_BLK_FLAG | EXT_COMPACT_FLAG)) == (EXT_BLK_FLAG | EXT_COMPACT_FLAG)) {
      u64 ncv = (u64)(head & EXT_CNT_MASK);
      if (ncv <= mx && p + 1ULL + ncv <= len) {
        u64 z = 0ULL;
        while (z < mx) { tmk[z] = EXT_UNMAPPED; z = z + 1ULL; }
        u64 k = 0ULL;
        while (k < ncv) {
          u32 ov = ext[p + 1ULL + k];
          if ((u64)ov < mx) { tmk[ov] = (u32)k; }
          k = k + 1ULL;
        }
        e = 0ULL;
        while (e < orig_mv) {
          u32 cur = ord[e];
          ord[e] = ((u64)cur < mx) ? tmk[cur] : EXT_UNMAPPED;
          e = e + 1ULL;
        }
        p = p + 1ULL + ncv;
      } else {
        p = p + 1ULL;
      }
    } else {
      p = p + 1ULL;
      while (p < len && (ext[p] & EXT_BLK_FLAG) == 0u) {
        p = p + 1ULL;
      }
    }
  }
  u64 z = 0ULL;
  while (z < cv) { tmk[z] = 0u; z = z + 1ULL; }
  u64 n = 0ULL;
  e = 0ULL;
  while (e < orig_mv) {
    u32 iv = ord[e];
    if ((u64)iv < cv && tmk[iv] == 0u && n < cv) {
      tmk[iv] = 1u;
      ord[n] = iv;
      n = n + 1ULL;
    }
    e = e + 1ULL;
  }
  u64 v = 0ULL;
  while (v < cv) {
    if (tmk[v] == 0u && n < cv) {
      ord[n] = (u32)v;
      n = n + 1ULL;
    }
    v = v + 1ULL;
  }
  return n;
}

u64 full_lucky_scan_tum(FullHdr *h, bool pos_mode, bool fwd) {
  u64 cv = h->cur_vars;
  u64 n = full_lucky_ord_fid(h);
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  u32 *ord = (u32 *)h->tarjan_reach;
  u64 i = 0ULL;
  while (i < n) {
    u64 j = fwd ? i : (n - 1ULL - i);
    u64 v = (u64)ord[j];
    if (v < cv && (fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      h->fuel = h->fuel - 1ULL;
      u32 lit = pos_mode ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
      full_assign(h, lit, 0xFFFFFFFFu);
      u64 pr = full_propagate(h);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) {
        if (h->cur_level > 1ULL) {
          full_backtrack(h, h->cur_level - 1ULL);
          if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          h->fuel = h->fuel - 1ULL;
          nlvl = h->cur_level + 1ULL;
          if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
          ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
          full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
          u64 pr2 = full_propagate(h);
          if (pr2 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          if (pr2 == 1ULL) { full_backtrack(h, 0ULL); return 0ULL; }
        } else {
          u64 ast = full_analyze(h);
          if (ast == 20ULL) { return 20ULL; }
          if (ast != 1ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          u64 pr3 = full_propagate(h);
          if (pr3 == 1ULL) { return 20ULL; }
          if (pr3 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
        }
      }
    }
    i = i + 1ULL;
  }
  return 10ULL;
}
"

/-! ## 1. Canonical `Fn` Handles & Replacement / Insertion Lists (`fidStep11Tum*`) -/

def fidStep11ZeroTables2Fn : Fn :=
  ⟨"full_zero_tables2", [i64], [], full_zero_tables2_fid_body⟩

def fidStep11InitHdrFn : Fn :=
  ⟨"full_init_hdr", [i64, i64, i64, i64], [], full_init_hdr_fid_body⟩

def fidStep11ActivateLitFn : Fn :=
  ⟨"full_activate_lit_fid", [i64, i32], [], full_activate_lit_fid_body⟩

def fidStep11IngestClFn : Fn :=
  ⟨"full_ingest_cl", [i64, i64], [i64], full_ingest_cl_tum_body⟩

def fidStep11TumbleFinishFn : Fn :=
  ⟨"full_tumble_finish_fid", [i64], [], full_tumble_finish_fid_body⟩

def fidStep11ParseBodyM6Fn : Fn :=
  ⟨"full_parse_body_m6", [i64, i64], [i64], full_parse_body_tum_body⟩

def fidStep11ExtendCoreFn : Fn :=
  ⟨"full_extend_core_fid", [i64], [], FullM4.full_extend_body⟩

def fidStep11UnpermFn : Fn :=
  ⟨"full_unperm_fid", [i64], [], full_unperm_fid_body⟩

def fidStep11ExtendFn : Fn :=
  ⟨"full_extend", [i64], [], full_extend_tum_body⟩

def fidStep11LuckyOrdFn : Fn :=
  ⟨"full_lucky_ord_fid", [i64], [i64], full_lucky_ord_fid_body⟩

def fidStep11LuckyScanFn : Fn :=
  ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], full_lucky_scan_tum_body⟩

/-- Exact `6`-function Step-11 PR 2 replacement list over `fidStep10Fns`. -/
def fidStep11TumRepls : List Fn :=
  [ fidStep11ZeroTables2Fn
  , fidStep11InitHdrFn
  , fidStep11IngestClFn
  , fidStep11ParseBodyM6Fn
  , fidStep11ExtendFn
  , fidStep11LuckyScanFn ]

/-- Ordered helper insertions (`+5` helpers, strictly acyclic before their callers). -/
def fidStep11TumBefores : List (Sym × List Fn) :=
  [ ("full_ingest_cl", [fidStep11ActivateLitFn])
  , ("full_parse_body_m6", [fidStep11TumbleFinishFn])
  , ("full_extend", [fidStep11ExtendCoreFn, fidStep11UnpermFn])
  , ("full_lucky_scan", [fidStep11LuckyOrdFn]) ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_zero_tables2_fid_wf : Func.Wf fidStep11ZeroTables2Fn.body := by t_wf_reify
theorem full_init_hdr_fid_wf : Func.Wf fidStep11InitHdrFn.body := by t_wf_reify
theorem full_activate_lit_fid_wf : Func.Wf fidStep11ActivateLitFn.body := by t_wf_reify
theorem full_ingest_cl_tum_wf : Func.Wf fidStep11IngestClFn.body := by t_wf_reify
theorem full_tumble_finish_fid_wf : Func.Wf fidStep11TumbleFinishFn.body := by t_wf_reify
theorem full_parse_body_tum_wf : Func.Wf fidStep11ParseBodyM6Fn.body := by t_wf_reify
theorem full_extend_core_fid_wf : Func.Wf fidStep11ExtendCoreFn.body := FullM4.full_extend_wf
theorem full_unperm_fid_wf : Func.Wf fidStep11UnpermFn.body := by t_wf_reify
theorem full_extend_tum_wf : Func.Wf fidStep11ExtendFn.body := by t_wf_reify
theorem full_lucky_ord_fid_wf : Func.Wf fidStep11LuckyOrdFn.body := by t_wf_reify
theorem full_lucky_scan_tum_wf : Func.Wf fidStep11LuckyScanFn.body := by t_wf_reify

theorem fidStep11TumRepls_wf : ∀ f ∈ fidStep11TumRepls, f.Wf := by
  intro f hf
  simp only [fidStep11TumRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_zero_tables2_fid_wf
  · exact full_init_hdr_fid_wf
  · exact full_ingest_cl_tum_wf
  · exact full_parse_body_tum_wf
  · exact full_extend_tum_wf
  · exact full_lucky_scan_tum_wf

theorem fidStep11TumBefores_wf : ∀ h ∈ fidStep11TumBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep11TumBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | (rfl | rfl) | rfl
  · exact full_activate_lit_fid_wf
  · exact full_tumble_finish_fid_wf
  · exact full_extend_core_fid_wf
  · exact full_unperm_fid_wf
  · exact full_lucky_ord_fid_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityTumble

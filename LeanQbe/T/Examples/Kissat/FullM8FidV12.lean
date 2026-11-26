/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M8 Fidelity Core (`V12` — `9` Localized Function Replacements)

Purely additive C0 leaf module implementing Tier A (`V12`, `9` localized edits over
`FullM7Fidelity.m7FidelityModule` (`0` ABI/header changes, `0` overlap with `FullM7V2Robust`):

1. **`V1c`** (`full_ana_failed_lit_m6_hdr`): calls `full_ema_update(h, 0ULL)` when
   `h->probing == 0ULL` before incrementing `h->conflicts` (`analyze.c:503`).
2. **`V1b` + `V1a`** (`full_analyze`, `full_analyze_core_m6`): increments `h->conflicts` on
   1-lit chronological conflict reuse when `h->probing == 0ULL` (`proplit.h:194`), and fixes
   learned glue off-by-1 (`u64 glue = 0ULL`, `learn.c:193`).
3. **`V1d`** (`full_restart_due`, `full_switch_mode_m7`): uses `>=` in focused restart ratio check
   (`restart.c:36`) and `delta = (d10 > 0ULL) ? d10 : 1ULL` (`restart.c:43-45`).
4. **`V2a`** (`full_enter_dense`, `full_preprocess_m6`): sweeps & propagates root-falsified
   clauses after `full_lucky` (`preprocess.c:57`) and on entering dense mode if `unflushed > 0`.
5. **`V2b`** (`full_cong_try_xor_ite`): drops duplicate `O(deg^2)` ITE extraction already handled
   in `O(deg log deg)` by `full_cong_extract_ite_all_m7`.
6. **`V2c`** (`full_congruence_dense`): lifts worklist `occ_bkt` cap from `512` to `8192`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM8FidV12

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Splice

kissat_c0! m8FidV12 "
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
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu
#define FL_ACTIVE             1u

#define M7_GU_RANDEC_REM      56ULL
#define M7_GU_RANDEC_LIM      58ULL
#define M7_GU_RANDEC_SEQ      60ULL
#define M7_GU_RANDEC_CFL      62ULL

extern u64 full_ilog10(u64 x);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_tick_rel(FullHdr *h);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern void full_ema_update(FullHdr *h, u64 glue);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_sweep_bins(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_flush_trail(FullHdr *h);
extern void full_clear_ana(FullHdr *h);
extern void full_bump_analyzed_m6_hdr(FullHdr *h);
extern void full_restore_bump_ana_m6_hdr(FullHdr *h);
extern u64 full_ana_failed_lit_m6_hdr(FullHdr *h);
extern void full_min_shrink_m6(FullHdr *h);
extern void full_min_shrink(FullHdr *h);
extern u64 full_deduce_1uip(FullHdr *h);
extern u64 full_deduce_1uip_m6_hdr(FullHdr *h);
extern u64 full_one_lit_confl(FullHdr *h);
extern u64 full_learn_clause(FullHdr *h, u64 glue);
extern void full_restore_bump_ana_m5(FullHdr *h);
extern u64 full_lucky(FullHdr *h);
extern bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c);
extern u64 full_cong_emit_xor(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2);
extern u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim);
extern u64 full_cong_find_units_equivs(FullHdr *h);
extern u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim);
extern u64 full_cong_worklist(FullHdr *h, u64 g_len, u64 ctrl_off, u64 tick_lim);
extern u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim);
extern u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap, u64 tick_lim);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);
extern void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m);
extern u64 full_probe_m6(FullHdr *h, bool initial);

u64 m8_ana_failed_lit_m6_hdr(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (h->cur_level != 1ULL || cv == 0ULL) { return 0ULL; }
  u32 *fdec = (u32 *)h->frame_dec;
  u32 failed = fdec[1];
  u32 fv = failed >> 1;
  u32 not_failed = failed ^ 1u;
  if ((u64)fv >= cv) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  if (vals[failed] <= (i8)0 || lvl[fv] != 1u || rsns[fv] != 0xFFFFFFFFu) {
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *ar = (u32 *)h->arena;
  u32 *ana = (u32 *)h->work_stk1;
  h->min_clr_len = 0ULL;
  u64 unres = 0ULL;
  u64 ucnt = 0ULL;
  bool done = false;
  if (h->confl_type == 1ULL) {
    u32 c0 = (u32)h->confl_lit0; u32 c1 = (u32)h->confl_lit1;
    if (c0 == not_failed || c1 == not_failed) { done = true; }
    else {
      u32 v0 = c0 >> 1; u32 v1 = c1 >> 1;
      if ((u64)v0 >= cv || (u64)v1 >= cv) { return 0ULL; }
      if (lvl[v0] > 0u && mrk[v0] == (u8)0) {
        mrk[v0] = (u8)1; ana[h->min_clr_len] = v0; h->min_clr_len = h->min_clr_len + 1ULL;
        unres = unres + 1ULL;
      }
      if (lvl[v1] > 0u && mrk[v1] == (u8)0) {
        mrk[v1] = (u8)1; ana[h->min_clr_len] = v1; h->min_clr_len = h->min_clr_len + 1ULL;
        unres = unres + 1ULL;
      }
    }
  } else {
    u32 cr = (u32)h->confl_ref;
    if ((u64)cr + 3ULL > h->arena_len) { return 0ULL; }
    u32 csz = ar[(u64)cr + 2ULL];
    if ((u64)cr + 3ULL + (u64)csz > h->arena_len) { return 0ULL; }
    u32 i = 0u;
    while (i < csz) {
      u32 lit = ar[(u64)cr + 3ULL + (u64)i];
      if (lit == not_failed) { done = true; break; }
      u32 lv = lit >> 1;
      if ((u64)lv >= cv) { full_clear_ana(h); return 0ULL; }
      if (lvl[lv] > 0u && mrk[lv] == (u8)0) {
        mrk[lv] = (u8)1;
        if (h->min_clr_len < cv) {
          ana[h->min_clr_len] = lv; h->min_clr_len = h->min_clr_len + 1ULL;
        }
        unres = unres + 1ULL;
      }
      i = i + 1u;
    }
  }
  u64 t = h->trail_end;
  u32 unit = 0xFFFFFFFFu;
  bool err = false;
  while (!done && !err) {
    u32 lit = 0xFFFFFFFFu;
    while (true) {
      if (t == 0ULL) { err = true; break; }
      t = t - 1ULL;
      u32 tl = trl[t]; u32 tv = tl >> 1;
      if ((u64)tv >= cv) { err = true; break; }
      if (mrk[tv] != (u8)0) { lit = tl; break; }
    }
    if (err || lit == 0xFFFFFFFFu) { err = true; break; }
    if (unres == 1ULL) {
      unit = lit ^ 1u;
      if (ucnt < cv) { tmp[ucnt] = unit; ucnt = ucnt + 1ULL; }
      else { err = true; break; }
    }
    u32 rsn = rsns[lit >> 1];
    if (rsn == 0xFFFFFFFFu) { err = true; break; }
    if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ot = rsn & PW_LIT_MASK;
      if (ot == not_failed) { done = true; break; }
      u32 ov = ot >> 1;
      if ((u64)ov >= cv) { err = true; break; }
      if (lvl[ov] > 0u && mrk[ov] == (u8)0) {
        mrk[ov] = (u8)1;
        if (h->min_clr_len < cv) {
          ana[h->min_clr_len] = ov; h->min_clr_len = h->min_clr_len + 1ULL;
        }
        unres = unres + 1ULL;
      }
    } else {
      if ((u64)rsn + 3ULL > h->arena_len) { err = true; break; }
      u32 rsz = ar[(u64)rsn + 2ULL];
      if (rsz < 3u || (u64)rsn + 3ULL + (u64)rsz > h->arena_len) { err = true; break; }
      u32 j = 0u;
      while (j < rsz) {
        u32 ot = ar[(u64)rsn + 3ULL + (u64)j];
        if (ot != lit) {
          if (ot == not_failed) { done = true; break; }
          u32 ov = ot >> 1;
          if ((u64)ov >= cv) { err = true; break; }
          if (lvl[ov] > 0u && mrk[ov] == (u8)0) {
            mrk[ov] = (u8)1;
            if (h->min_clr_len < cv) {
              ana[h->min_clr_len] = ov; h->min_clr_len = h->min_clr_len + 1ULL;
            }
            unres = unres + 1ULL;
          }
        }
        j = j + 1u;
      }
    }
    if (done || err) { break; }
    if (unres == 0ULL) { err = true; break; }
    unres = unres - 1ULL;
  }
  if (err) { full_clear_ana(h); return 0ULL; }
  if (ucnt >= cv) { full_clear_ana(h); return 0ULL; }
  tmp[ucnt] = not_failed; ucnt = ucnt + 1ULL;
  h->tmp_len = ucnt;
  full_bump_analyzed_m6_hdr(h);
  full_clear_ana(h);
  full_backtrack(h, 0ULL);
  u64 k = 0ULL;
  while (k < ucnt) {
    u32 u = tmp[k];
    if (vals[u] < (i8)0) { return 20ULL; }
    if (vals[u] == (i8)0) { full_assign_lvl(h, u, 0xFFFFFFFFu, 0u); }
    k = k + 1ULL;
  }
  if (h->probing == 0ULL) { full_ema_update(h, 0ULL); }
  h->conflicts = h->conflicts + 1ULL;
  h->learned_lits = h->learned_lits + 1ULL;
  h->iterating = 1ULL;
  return 1ULL;
}

u64 m8_analyze(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u64 iter = 0ULL;
  u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) {
      if (h->probing == 0ULL) { h->conflicts = h->conflicts + 1ULL; }
      return 1ULL;
    }
    if (ol == 2ULL) { return 0ULL; }
    u64 dst = full_deduce_1uip(h);
    if (dst == 20ULL) { return 20ULL; }
    if (dst == 0ULL) { return 0ULL; }
    if (dst == 2ULL) {
      h->conflicts = h->conflicts + 1ULL;
      if (h->probing == 0ULL) {
        if (h->cur_vars > 0ULL) {
          if (h->confl_type == 1ULL) {
            tmp[0] = (u32)h->confl_lit0;
            h->tmp_len = 1ULL;
          } else if (h->confl_type == 2ULL && h->confl_ref < h->arena_len &&
                     3ULL < h->arena_len - h->confl_ref) {
            tmp[0] = ar[h->confl_ref + 3ULL];
            h->tmp_len = 1ULL;
          }
        }
        full_restore_bump_ana_m5(h);
      }
      continue;
    }
    full_min_shrink(h);
    if (h->probing == 0ULL) {
      full_restore_bump_ana_m5(h);
      full_tick_rel(h);
    }
    u64 glue = 0ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    if (h->probing == 0ULL) { full_ema_update(h, glue); }
    return full_learn_clause(h, glue);
  }
  return 0ULL;
}

u64 m8_analyze_core_m6(FullHdr *h) {
  u32 *lvl = (u32 *)h->level; u32 *tmp = (u32 *)h->tmp_lits; u32 *ar = (u32 *)h->arena;
  u64 iter = 0ULL; u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) {
      if (h->probing == 0ULL) { h->conflicts = h->conflicts + 1ULL; }
      return 1ULL;
    }
    if (ol == 2ULL) { return 0ULL; }
    if (h->cur_level == 1ULL) { return full_ana_failed_lit_m6_hdr(h); }
    u64 dst = full_deduce_1uip_m6_hdr(h);
    if (dst == 20ULL) { return 20ULL; }
    if (dst == 0ULL) { return 0ULL; }
    if (dst == 2ULL) {
      h->conflicts = h->conflicts + 1ULL;
      if (h->probing == 0ULL) {
        if (h->cur_vars > 0ULL) {
          if (h->confl_type == 1ULL) { tmp[0] = (u32)h->confl_lit0; h->tmp_len = 1ULL; }
          else if (h->confl_type == 2ULL && h->confl_ref < h->arena_len &&
                   3ULL < h->arena_len - h->confl_ref) {
            tmp[0] = ar[h->confl_ref + 3ULL]; h->tmp_len = 1ULL;
          }
        }
        full_restore_bump_ana_m6_hdr(h);
      }
      continue;
    }
    full_min_shrink_m6(h);
    if (h->probing == 0ULL) { full_restore_bump_ana_m6_hdr(h); full_tick_rel(h); }
    u64 glue = 0ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    if (h->probing == 0ULL) { full_ema_update(h, glue); }
    return full_learn_clause(h, glue);
  }
  return 0ULL;
}

u64 m8_restart_due(FullHdr *h) {
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
  if (fval * 100ULL >= sval * 110ULL) {
    u64 rst = (h->restarts < 1000000000000ULL) ? (h->restarts + 1ULL) : 1000000000000ULL;
    u64 d10 = full_ilog10(rst + 9ULL);
    u64 delta = (d10 > 0ULL) ? d10 : 1ULL;
    h->restart_limit = h->conflicts + delta;
    return 1ULL;
  }
  return 0ULL;
}

bool m8_enter_dense(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return false; }
  if (h->dense_mode != 0ULL) { return true; }
  if (full_flush_trail(h) != 1ULL) { return false; }
  if (h->unflushed > 0ULL) {
    u64 sr_d = full_arena_sweep(h);
    if (sr_d == 2ULL) { h->inconsistent = 1ULL; return false; }
    if (full_propagate(h) == 1ULL) { h->inconsistent = 1ULL; return false; }
    if (full_flush_trail(h) != 1ULL) { return false; }
    h->unflushed = 0ULL;
  }
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
          h->oom = 0ULL; full_arena_sweep(h); return false;
        }
        k = k + 1u;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  h->dense_mode = 1ULL;
  return true;
}

u64 m8_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap) {
  if ((a >> 1) == (b >> 1) || (a >> 1) == (c >> 1) || (b >> 1) == (c >> 1)) { return g_len; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mx = (a > b) ? a : b;
  if (c > mx) { mx = c; }
  if (((a & 1u) == 0u || a == mx) && ((b & 1u) == 0u || b == mx) &&
      ((c & 1u) == 0u || c == mx) &&
      full_has_ternary(h, a, b ^ 1u, c ^ 1u) && full_has_ternary(h, a ^ 1u, b, c ^ 1u) &&
      full_has_ternary(h, a ^ 1u, b ^ 1u, c)) {
    if (g_len + 12ULL <= g_cap) {
      g_len = full_cong_emit_xor(scr, g_len, a, b, c);
      g_len = full_cong_emit_xor(scr, g_len, b, a, c);
      g_len = full_cong_emit_xor(scr, g_len, c, a, b);
    }
    return g_len;
  }
  return g_len;
}

u64 m8_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  h->ant_sz = 0ULL;
  if (full_cong_extract_binaries(h, tick_lim) == 20ULL) { h->ant_sz = 0ULL; return 20ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  if (full_cong_find_units_equivs(h) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  u64 ht_sz = 64ULL;
  while (ht_sz * 8ULL <= h->scratch_cap && ht_sz < 131072ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 occ_bkt = (ht_off >= 262144ULL) ? 8192ULL : ((ht_off >= 65536ULL) ? 2048ULL :
    ((ht_off >= 16384ULL) ? 512ULL : ((ht_off >= 2048ULL) ? 256ULL :
    ((ht_off >= 256ULL) ? 32ULL : 16ULL))));
  u64 bkt_off = ht_off - occ_bkt;
  u64 inq_off = bkt_off - occ_bkt;
  u64 q_off = inq_off - occ_bkt;
  u64 ctrl_off = q_off - 8ULL;
  u64 g_cap = (ctrl_off * 3ULL) >> 2;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = full_cong_extract(h, g_cap, tick_lim);
  if (g_len <= g_cap) {
    g_len = (u64)full_cong_extract_ite_all_m7(h, (u32)g_len, (u32)g_cap, tick_lim);
  }
  if (g_len > 0ULL && g_len <= ctrl_off) {
    i = 0ULL;
    while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    h->res_sz = 0ULL;
    scr[ctrl_off] = (u32)occ_bkt; scr[ctrl_off + 1ULL] = (u32)bkt_off;
    scr[ctrl_off + 2ULL] = (u32)inq_off; scr[ctrl_off + 3ULL] = (u32)q_off;
    scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
    scr[ctrl_off + 6ULL] = (u32)ht_off; scr[ctrl_off + 7ULL] = (u32)ht_sz;
    if (full_cong_worklist(h, g_len, ctrl_off, tick_lim) == 20ULL) {
      i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
      h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
    }
  }
  if (full_cong_fwd_subsume(h, tick_lim) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL; h->ant_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

void m8_switch_mode_m7(FullHdr *h) {
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
      delta = (d10 > 0ULL) ? d10 : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
    full_m7_set64(h, M7_GU_RANDEC_REM, 0ULL);
    full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + 500ULL);
    full_m7_set64(h, M7_GU_RANDEC_SEQ, 0ULL);
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
  }
}

u64 m8_preprocess_m6(FullHdr *h) {
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
  if (h->unflushed > 0ULL || h->trail_end > 0ULL) {
    while (true) {
      u64 sr2 = full_arena_sweep(h);
      if (sr2 == 2ULL) { return 20ULL; }
      if (sr2 == 3ULL || h->oom != 0ULL) { break; }
      u64 pr2 = full_propagate(h);
      if (pr2 == 1ULL) { return 20ULL; }
      if (pr2 == 2ULL) { break; }
      if (sr2 == 0ULL && h->propagated >= h->trail_end) { break; }
    }
    h->unflushed = 0ULL;
  }
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
  if (full_probe_m6(h, true) == 20ULL) { return 20ULL; }
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

/-! ## Canonical `Fn` Wrappers & Spliced `m8FidV12Module` (`413` Fns) -/

def m8AnaFailedLitM6HdrFn : Fn :=
  ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m8_ana_failed_lit_m6_hdr_body⟩
def m8AnalyzeFn : Fn :=
  ⟨"full_analyze", [i64], [i64], m8_analyze_body⟩
def m8AnalyzeCoreM6Fn : Fn :=
  ⟨"full_analyze_core_m6", [i64], [i64], m8_analyze_core_m6_body⟩
def m8RestartDueFn : Fn :=
  ⟨"full_restart_due", [i64], [i64], m8_restart_due_body⟩
def m8EnterDenseFn : Fn :=
  ⟨"full_enter_dense", [i64], [.bool], m8_enter_dense_body⟩
def m8CongTryXorIteFn : Fn :=
  ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], m8_cong_try_xor_ite_body⟩
def m8CongruenceDenseFn : Fn :=
  ⟨"full_congruence_dense", [i64, i64], [i64], m8_congruence_dense_body⟩
def m8SwitchModeM7Fn : Fn :=
  ⟨"full_switch_mode_m7", [i64], [], m8_switch_mode_m7_body⟩
def m8PreprocessM6Fn : Fn :=
  ⟨"full_preprocess_m6", [i64], [i64], m8_preprocess_m6_body⟩

def m8FidV12Repls : List Fn :=
  [ m8AnaFailedLitM6HdrFn
  , m8AnalyzeFn
  , m8AnalyzeCoreM6Fn
  , m8RestartDueFn
  , m8EnterDenseFn
  , m8CongTryXorIteFn
  , m8CongruenceDenseFn
  , m8SwitchModeM7Fn
  , m8PreprocessM6Fn ]

def m8FidV12Fns : List Fn := PatchModule.spliceFns m8FidV12Repls m7FidelityFns

def m8FidV12Module : LeanQbe.T.Module :=
  { m7FidelityModule with fns := m8FidV12Fns }

end LeanQbe.T.Examples.Kissat.FullM8FidV12

end

public section

namespace LeanQbe.T.Examples.Kissat.FullM8FidV12

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Splice

theorem m8_ana_failed_lit_m6_hdr_wf : Func.Wf m8_ana_failed_lit_m6_hdr_body := by t_wf_reify
theorem m8_analyze_wf : Func.Wf m8_analyze_body := by t_wf_reify
theorem m8_analyze_core_m6_wf : Func.Wf m8_analyze_core_m6_body := by t_wf_reify
theorem m8_restart_due_wf : Func.Wf m8_restart_due_body := by t_wf_reify
theorem m8_enter_dense_wf : Func.Wf m8_enter_dense_body := by t_wf_reify
theorem m8_cong_try_xor_ite_wf : Func.Wf m8_cong_try_xor_ite_body := by t_wf_reify
theorem m8_congruence_dense_wf : Func.Wf m8_congruence_dense_body := by t_wf_reify
theorem m8_switch_mode_m7_wf : Func.Wf m8_switch_mode_m7_body := by t_wf_reify
theorem m8_preprocess_m6_wf : Func.Wf m8_preprocess_m6_body := by t_wf_reify

theorem m8FidV12Repls_wf : ∀ r ∈ m8FidV12Repls, r.Wf := by
  intro r hr
  simp only [m8FidV12Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8_ana_failed_lit_m6_hdr_wf
  · exact m8_analyze_wf
  · exact m8_analyze_core_m6_wf
  · exact m8_restart_due_wf
  · exact m8_enter_dense_wf
  · exact m8_cong_try_xor_ite_wf
  · exact m8_congruence_dense_wf
  · exact m8_switch_mode_m7_wf
  · exact m8_preprocess_m6_wf

private theorem fid_sig_of_idx {i : Nat} {s : SigEntry}
    (h : m7FidelityFns[i]?.map Fn.sig = some s) :
    ∃ g, m7FidelityFns[i]? = some g ∧ g.sig = s := by
  cases hg : m7FidelityFns[i]? with
  | none => simp [hg] at h
  | some g => exact ⟨g, rfl, by simpa [hg] using h⟩

private theorem fid_idx_9 : m7FidelityFns[9]?.map Fn.sig =
    some ("full_ilog10", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_11 : m7FidelityFns[11]?.map Fn.sig =
    some ("full_arena_next", [i64, i32], [i32]) := by t_kernel_rfl
private theorem fid_idx_18 : m7FidelityFns[18]?.map Fn.sig =
    some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_20 : m7FidelityFns[20]?.map Fn.sig =
    some ("full_heap_down", [i64, i32], []) := by t_kernel_rfl
private theorem fid_idx_29 : m7FidelityFns[29]?.map Fn.sig =
    some ("full_tick_rel", [i64], []) := by t_kernel_rfl
private theorem fid_idx_31 : m7FidelityFns[31]?.map Fn.sig =
    some ("full_log10_q16_m7", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_32 : m7FidelityFns[32]?.map Fn.sig =
    some ("full_scale_delta_m5", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_33 : m7FidelityFns[33]?.map Fn.sig =
    some ("full_ema_update", [i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_35 : m7FidelityFns[35]?.map Fn.sig =
    some ("full_assign_lvl", [i64, i32, i32, i32], []) := by t_kernel_rfl
private theorem fid_idx_39 : m7FidelityFns[39]?.map Fn.sig =
    some ("full_backtrack", [i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_86 : m7FidelityFns[86]?.map Fn.sig =
    some ("full_propagate", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_96 : m7FidelityFns[96]?.map Fn.sig =
    some ("full_sweep_bins", [i64], []) := by t_kernel_rfl
private theorem fid_idx_104 : m7FidelityFns[104]?.map Fn.sig =
    some ("full_arena_sweep", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_106 : m7FidelityFns[106]?.map Fn.sig =
    some ("full_flush_trail", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_115 : m7FidelityFns[115]?.map Fn.sig =
    some ("full_clear_ana", [i64], []) := by t_kernel_rfl
private theorem fid_idx_118 : m7FidelityFns[118]?.map Fn.sig =
    some ("full_bump_analyzed_m6_hdr", [i64], []) := by t_kernel_rfl
private theorem fid_idx_119 : m7FidelityFns[119]?.map Fn.sig =
    some ("full_restore_bump_ana_m6_hdr", [i64], []) := by t_kernel_rfl
private theorem fid_idx_120 : m7FidelityFns[120]?.map Fn.sig =
    some ("full_ana_failed_lit_m6_hdr", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_135 : m7FidelityFns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := by t_kernel_rfl
private theorem fid_idx_137 : m7FidelityFns[137]?.map Fn.sig =
    some ("full_min_shrink", [i64], []) := by t_kernel_rfl
private theorem fid_idx_138 : m7FidelityFns[138]?.map Fn.sig =
    some ("full_deduce_1uip", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_139 : m7FidelityFns[139]?.map Fn.sig =
    some ("full_deduce_1uip_m6_hdr", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_141 : m7FidelityFns[141]?.map Fn.sig =
    some ("full_one_lit_confl", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_143 : m7FidelityFns[143]?.map Fn.sig =
    some ("full_learn_clause", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_148 : m7FidelityFns[148]?.map Fn.sig =
    some ("full_restore_bump_ana_m5", [i64], []) := by t_kernel_rfl
private theorem fid_idx_149 : m7FidelityFns[149]?.map Fn.sig =
    some ("full_analyze", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_150 : m7FidelityFns[150]?.map Fn.sig =
    some ("full_analyze_core_m6", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_170 : m7FidelityFns[170]?.map Fn.sig =
    some ("full_restart_due", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_184 : m7FidelityFns[184]?.map Fn.sig =
    some ("full_lucky", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_236 : m7FidelityFns[236]?.map Fn.sig =
    some ("full_enter_dense", [i64], [.bool]) := by t_kernel_rfl
private theorem fid_idx_243 : m7FidelityFns[243]?.map Fn.sig =
    some ("full_has_ternary", [i64, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_246 : m7FidelityFns[246]?.map Fn.sig =
    some ("full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64]) := by t_kernel_rfl
private theorem fid_idx_249 : m7FidelityFns[249]?.map Fn.sig =
    some ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_252 : m7FidelityFns[252]?.map Fn.sig =
    some ("full_cong_extract_binaries", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_253 : m7FidelityFns[253]?.map Fn.sig =
    some ("full_cong_find_units_equivs", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_254 : m7FidelityFns[254]?.map Fn.sig =
    some ("full_cong_extract", [i64, i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_260 : m7FidelityFns[260]?.map Fn.sig =
    some ("full_cong_worklist", [i64, i64, i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_261 : m7FidelityFns[261]?.map Fn.sig =
    some ("full_cong_fwd_subsume", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_274 : m7FidelityFns[274]?.map Fn.sig =
    some ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]) := by t_kernel_rfl
private theorem fid_idx_275 : m7FidelityFns[275]?.map Fn.sig =
    some ("full_congruence_dense", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_354 : m7FidelityFns[354]?.map Fn.sig =
    some ("full_compact_needed", [i64], [.bool]) := by t_kernel_rfl
private theorem fid_idx_366 : m7FidelityFns[366]?.map Fn.sig =
    some ("full_compact", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_390 : m7FidelityFns[390]?.map Fn.sig =
    some ("full_m7_set64", [i64, i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_400 : m7FidelityFns[400]?.map Fn.sig =
    some ("full_ema_swap_m7", [i64, i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_401 : m7FidelityFns[401]?.map Fn.sig =
    some ("full_switch_mode_m7", [i64], []) := by t_kernel_rfl
private theorem fid_idx_404 : m7FidelityFns[404]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := by t_kernel_rfl
private theorem fid_idx_405 : m7FidelityFns[405]?.map Fn.sig =
    some ("full_preprocess_m6", [i64], [i64]) := by t_kernel_rfl

theorem m8FidV12Repls_sigs :
    ∀ r ∈ m8FidV12Repls, ∀ f ∈ m7FidelityFns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨f120, hf120, hs120⟩ := fid_sig_of_idx fid_idx_120
  obtain ⟨f149, hf149, hs149⟩ := fid_sig_of_idx fid_idx_149
  obtain ⟨f150, hf150, hs150⟩ := fid_sig_of_idx fid_idx_150
  obtain ⟨f170, hf170, hs170⟩ := fid_sig_of_idx fid_idx_170
  obtain ⟨f236, hf236, hs236⟩ := fid_sig_of_idx fid_idx_236
  obtain ⟨f249, hf249, hs249⟩ := fid_sig_of_idx fid_idx_249
  obtain ⟨f275, hf275, hs275⟩ := fid_sig_of_idx fid_idx_275
  obtain ⟨f401, hf401, hs401⟩ := fid_sig_of_idx fid_idx_401
  obtain ⟨f405, hf405, hs405⟩ := fid_sig_of_idx fid_idx_405
  intro r hr f hf hnm
  simp only [m8FidV12Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf120
      (hnm.symm.trans (congrArg Prod.fst hs120.symm))
    subst hf0; exact hs120.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf149
      (hnm.symm.trans (congrArg Prod.fst hs149.symm))
    subst hf0; exact hs149.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf150
      (hnm.symm.trans (congrArg Prod.fst hs150.symm))
    subst hf0; exact hs150.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf170
      (hnm.symm.trans (congrArg Prod.fst hs170.symm))
    subst hf0; exact hs170.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf236
      (hnm.symm.trans (congrArg Prod.fst hs236.symm))
    subst hf0; exact hs236.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf249
      (hnm.symm.trans (congrArg Prod.fst hs249.symm))
    subst hf0; exact hs249.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf275
      (hnm.symm.trans (congrArg Prod.fst hs275.symm))
    subst hf0; exact hs275.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf401
      (hnm.symm.trans (congrArg Prod.fst hs401.symm))
    subst hf0; exact hs401.symm
  · have hf0 := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf405
      (hnm.symm.trans (congrArg Prod.fst hs405.symm))
    subst hf0; exact hs405.symm

private theorem pm_fn_find_name_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) h)

private theorem pm_spliceFns_sigs {repls fs : List Fn}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (PatchModule.spliceFns repls fs).map Fn.sig = fs.map Fn.sig := by
  unfold PatchModule.spliceFns
  rw [List.map_map]
  apply List.map_congr_left
  intro f hf
  dsimp only [Function.comp_def]
  cases h : repls.find? (fun x => x.name == f.name) with
  | none => rfl
  | some r => exact hsig r (List.mem_of_find?_eq_some h) f hf (pm_fn_find_name_eq h)

private theorem pm_checkFnsCallsOk_splice (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen fs repls : List Fn),
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk ((seen ++ pre).map Fn.sig ++ extSigs) exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig)
      (PatchModule.spliceFns repls fs) = true
  | _, [], _, _, _, _ => rfl
  | seen, f :: rest, repls, hchk, hsig, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    unfold PatchModule.spliceFns
    simp only [List.map_cons, LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk (((seen ++ [f]) ++ pre).map Fn.sig ++ extSigs) exits = true := by
      intro pre g post r hsplit hr hnm
      rw [List.append_assoc]
      exact hrepl (f :: pre) g post r (by rw [hsplit]; rfl) hr hnm
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (pm_fn_find_name_eq h)
    have hhead_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        (seen.map Fn.sig ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => exact hchk.1
      | some r =>
        simpa using hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (pm_fn_find_name_eq h)
    refine ⟨hhead_ok, ?_⟩
    have hchk2 : LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((seen ++ [f]).map Fn.sig) rest =
        true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    rw [hhead_sig, show seen.map Fn.sig ++ [f.sig] = (seen ++ [f]).map Fn.sig by simp]
    exact pm_checkFnsCallsOk_splice exits extSigs (seen ++ [f]) rest repls hchk2
      hsig_rest hrepl_rest

private theorem pm_spliceModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits = true) :
    ({ M with fns := PatchModule.spliceFns repls M.fns } : LeanQbe.T.Module).checkAcyclic =
      true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨?_, ?_⟩
  · have hnames : ({ M with fns := PatchModule.spliceFns repls M.fns } : LeanQbe.T.Module).names =
        M.names := by
      simp only [LeanQbe.T.Module.names]
      have hm := congrArg (List.map Prod.fst) (pm_spliceFns_sigs hsig)
      simp only [List.map_map, Function.comp_def, Fn.sig] at hm
      rw [hm]
    unfold LeanQbe.T.Module.checkNamesNodup
    rw [hnames]
    exact hM.1
  · exact pm_checkFnsCallsOk_splice M.exits (M.externs.map Extern.sig) [] M.fns repls
      hM.2 hsig (fun pre f post r hsplit hr hn => hrepl pre f post r hsplit hr hn)

theorem m8FidV12Fns_length : m8FidV12Fns.length = 413 := by
  rw [m8FidV12Fns, PatchModule.spliceFns, List.length_map]
  exact m7FidelityFns_length

theorem m8FidV12Fns_sigs : m8FidV12Fns.map Fn.sig = m7FidelityFns.map Fn.sig :=
  pm_spliceFns_sigs m8FidV12Repls_sigs

theorem m8FidV12Fns_names_nodup : (m8FidV12Fns.map Fn.name).Nodup := by
  have hs := congrArg (List.map Prod.fst) (pm_spliceFns_sigs m8FidV12Repls_sigs)
  simp only [List.map_map, Function.comp_def, Fn.sig] at hs
  change (m8FidV12Fns.map Fn.name) = m7FidelityFns.map Fn.name at hs
  rw [hs]; exact m7FidelityFns_names_nodup

theorem m8FidV12_acyclic : m8FidV12Module.checkAcyclic = true := by
  obtain ⟨g9, hg9, hsg9⟩ := fid_sig_of_idx fid_idx_9
  obtain ⟨g11, hg11, hsg11⟩ := fid_sig_of_idx fid_idx_11
  obtain ⟨g18, hg18, hsg18⟩ := fid_sig_of_idx fid_idx_18
  obtain ⟨g20, hg20, hsg20⟩ := fid_sig_of_idx fid_idx_20
  obtain ⟨g29, hg29, hsg29⟩ := fid_sig_of_idx fid_idx_29
  obtain ⟨g31, hg31, hsg31⟩ := fid_sig_of_idx fid_idx_31
  obtain ⟨g32, hg32, hsg32⟩ := fid_sig_of_idx fid_idx_32
  obtain ⟨g33, hg33, hsg33⟩ := fid_sig_of_idx fid_idx_33
  obtain ⟨g35, hg35, hsg35⟩ := fid_sig_of_idx fid_idx_35
  obtain ⟨g39, hg39, hsg39⟩ := fid_sig_of_idx fid_idx_39
  obtain ⟨g86, hg86, hsg86⟩ := fid_sig_of_idx fid_idx_86
  obtain ⟨g96, hg96, hsg96⟩ := fid_sig_of_idx fid_idx_96
  obtain ⟨g104, hg104, hsg104⟩ := fid_sig_of_idx fid_idx_104
  obtain ⟨g106, hg106, hsg106⟩ := fid_sig_of_idx fid_idx_106
  obtain ⟨g115, hg115, hsg115⟩ := fid_sig_of_idx fid_idx_115
  obtain ⟨g118, hg118, hsg118⟩ := fid_sig_of_idx fid_idx_118
  obtain ⟨g119, hg119, hsg119⟩ := fid_sig_of_idx fid_idx_119
  obtain ⟨g120, hg120, hsg120⟩ := fid_sig_of_idx fid_idx_120
  obtain ⟨g135, hg135, hsg135⟩ := fid_sig_of_idx fid_idx_135
  obtain ⟨g137, hg137, hsg137⟩ := fid_sig_of_idx fid_idx_137
  obtain ⟨g138, hg138, hsg138⟩ := fid_sig_of_idx fid_idx_138
  obtain ⟨g139, hg139, hsg139⟩ := fid_sig_of_idx fid_idx_139
  obtain ⟨g141, hg141, hsg141⟩ := fid_sig_of_idx fid_idx_141
  obtain ⟨g143, hg143, hsg143⟩ := fid_sig_of_idx fid_idx_143
  obtain ⟨g148, hg148, hsg148⟩ := fid_sig_of_idx fid_idx_148
  obtain ⟨g149, hg149, hsg149⟩ := fid_sig_of_idx fid_idx_149
  obtain ⟨g150, hg150, hsg150⟩ := fid_sig_of_idx fid_idx_150
  obtain ⟨g170, hg170, hsg170⟩ := fid_sig_of_idx fid_idx_170
  obtain ⟨g184, hg184, hsg184⟩ := fid_sig_of_idx fid_idx_184
  obtain ⟨g236, hg236, hsg236⟩ := fid_sig_of_idx fid_idx_236
  obtain ⟨g243, hg243, hsg243⟩ := fid_sig_of_idx fid_idx_243
  obtain ⟨g246, hg246, hsg246⟩ := fid_sig_of_idx fid_idx_246
  obtain ⟨g249, hg249, hsg249⟩ := fid_sig_of_idx fid_idx_249
  obtain ⟨g252, hg252, hsg252⟩ := fid_sig_of_idx fid_idx_252
  obtain ⟨g253, hg253, hsg253⟩ := fid_sig_of_idx fid_idx_253
  obtain ⟨g254, hg254, hsg254⟩ := fid_sig_of_idx fid_idx_254
  obtain ⟨g260, hg260, hsg260⟩ := fid_sig_of_idx fid_idx_260
  obtain ⟨g261, hg261, hsg261⟩ := fid_sig_of_idx fid_idx_261
  obtain ⟨g274, hg274, hsg274⟩ := fid_sig_of_idx fid_idx_274
  obtain ⟨g275, hg275, hsg275⟩ := fid_sig_of_idx fid_idx_275
  obtain ⟨g354, hg354, hsg354⟩ := fid_sig_of_idx fid_idx_354
  obtain ⟨g366, hg366, hsg366⟩ := fid_sig_of_idx fid_idx_366
  obtain ⟨g390, hg390, hsg390⟩ := fid_sig_of_idx fid_idx_390
  obtain ⟨g400, hg400, hsg400⟩ := fid_sig_of_idx fid_idx_400
  obtain ⟨g401, hg401, hsg401⟩ := fid_sig_of_idx fid_idx_401
  obtain ⟨g404, hg404, hsg404⟩ := fid_sig_of_idx fid_idx_404
  obtain ⟨g405, hg405, hsg405⟩ := fid_sig_of_idx fid_idx_405
  refine pm_spliceModule_checkAcyclic (M := m7FidelityModule) m7Fidelity_acyclic
    m8FidV12Repls_sigs ?_
  intro pre f post r hsplit hr hnm
  change m7FidelityFns = pre ++ f :: post at hsplit
  simp only [m7FidelityModule, List.map_nil, List.append_nil] at hsplit ⊢
  simp only [m8FidV12Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hn0 : f.name = g120.name := hnm.symm.trans (congrArg Prod.fst hsg120.symm)
    have hc : m8AnaFailedLitM6HdrFn.checkCallsOk
        [ ("full_clear_ana", [i64], [])
        , ("full_bump_analyzed_m6_hdr", [i64], [])
        , ("full_backtrack", [i64, i64], [])
        , ("full_assign_lvl", [i64, i32, i32, i32], [])
        , ("full_ema_update", [i64, i64], []) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hsg115 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg120 hn0 hg115 (by decide)
    · exact hsg118 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg120 hn0 hg118 (by decide)
    · exact hsg39 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg120 hn0 hg39 (by decide)
    · exact hsg35 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg120 hn0 hg35 (by decide)
    · exact hsg33 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg120 hn0 hg33 (by decide)
  · have hn0 : f.name = g149.name := hnm.symm.trans (congrArg Prod.fst hsg149.symm)
    have hc : m8AnalyzeFn.checkCallsOk
        [ ("full_one_lit_confl", [i64], [i64])
        , ("full_deduce_1uip", [i64], [i64])
        , ("full_restore_bump_ana_m5", [i64], [])
        , ("full_min_shrink", [i64], [])
        , ("full_tick_rel", [i64], [])
        , ("full_ema_update", [i64, i64], [])
        , ("full_learn_clause", [i64, i64], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsg141 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg141 (by decide)
    · exact hsg138 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg138 (by decide)
    · exact hsg148 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg148 (by decide)
    · exact hsg137 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg137 (by decide)
    · exact hsg29 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg29 (by decide)
    · exact hsg33 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg33 (by decide)
    · exact hsg143 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg149 hn0 hg143 (by decide)
  · have hn0 : f.name = g150.name := hnm.symm.trans (congrArg Prod.fst hsg150.symm)
    have hc : m8AnalyzeCoreM6Fn.checkCallsOk
        [ ("full_one_lit_confl", [i64], [i64])
        , ("full_ana_failed_lit_m6_hdr", [i64], [i64])
        , ("full_deduce_1uip_m6_hdr", [i64], [i64])
        , ("full_restore_bump_ana_m6_hdr", [i64], [])
        , ("full_min_shrink_m6", [i64], [])
        , ("full_tick_rel", [i64], [])
        , ("full_ema_update", [i64, i64], [])
        , ("full_learn_clause", [i64, i64], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsg141 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg141 (by decide)
    · exact hsg120 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg120 (by decide)
    · exact hsg139 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg139 (by decide)
    · exact hsg119 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg119 (by decide)
    · exact hsg135 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg135 (by decide)
    · exact hsg29 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg29 (by decide)
    · exact hsg33 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg33 (by decide)
    · exact hsg143 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg150 hn0 hg143 (by decide)
  · have hn0 : f.name = g170.name := hnm.symm.trans (congrArg Prod.fst hsg170.symm)
    have hc : m8RestartDueFn.checkCallsOk [("full_ilog10", [i64], [i64])] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    rcases List.mem_singleton.mp hs with rfl
    exact hsg9 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg170 hn0 hg9 (by decide)
  · have hn0 : f.name = g236.name := hnm.symm.trans (congrArg Prod.fst hsg236.symm)
    have hc : m8EnterDenseFn.checkCallsOk
        [ ("full_backtrack", [i64, i64], [])
        , ("full_flush_trail", [i64], [i64])
        , ("full_arena_sweep", [i64], [i64])
        , ("full_propagate", [i64], [i64])
        , ("full_sweep_bins", [i64], [])
        , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
        , ("full_arena_next", [i64, i32], [i32]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsg39 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg39 (by decide)
    · exact hsg106 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg106 (by decide)
    · exact hsg104 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg104 (by decide)
    · exact hsg86 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg86 (by decide)
    · exact hsg96 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg96 (by decide)
    · exact hsg18 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg18 (by decide)
    · exact hsg11 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg236 hn0 hg11 (by decide)
  · have hn0 : f.name = g249.name := hnm.symm.trans (congrArg Prod.fst hsg249.symm)
    have hc : m8CongTryXorIteFn.checkCallsOk
        [ ("full_has_ternary", [i64, i32, i32, i32], [.bool])
        , ("full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hsg243 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg249 hn0 hg243 (by decide)
    · exact hsg246 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg249 hn0 hg246 (by decide)
  · have hn0 : f.name = g275.name := hnm.symm.trans (congrArg Prod.fst hsg275.symm)
    have hc : m8CongruenceDenseFn.checkCallsOk
        [ ("full_cong_extract_binaries", [i64, i64], [i64])
        , ("full_cong_find_units_equivs", [i64], [i64])
        , ("full_cong_extract", [i64, i64, i64], [i64])
        , ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32])
        , ("full_cong_worklist", [i64, i64, i64, i64], [i64])
        , ("full_cong_fwd_subsume", [i64, i64], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsg252 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg275 hn0 hg252 (by decide)
    · exact hsg253 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg275 hn0 hg253 (by decide)
    · exact hsg254 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg275 hn0 hg254 (by decide)
    · exact hsg274 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg275 hn0 hg274 (by decide)
    · exact hsg260 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg275 hn0 hg260 (by decide)
    · exact hsg261 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg275 hn0 hg261 (by decide)
  · have hn0 : f.name = g401.name := hnm.symm.trans (congrArg Prod.fst hsg401.symm)
    have hc : m8SwitchModeM7Fn.checkCallsOk
        [ ("full_heap_down", [i64, i32], [])
        , ("full_log10_q16_m7", [i64], [i64])
        , ("full_ema_swap_m7", [i64, i64, i64], [])
        , ("full_ilog10", [i64], [i64])
        , ("full_m7_set64", [i64, i64, i64], []) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hsg20 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg401 hn0 hg20 (by decide)
    · exact hsg31 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg401 hn0 hg31 (by decide)
    · exact hsg400 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg401 hn0 hg400 (by decide)
    · exact hsg9 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg401 hn0 hg9 (by decide)
    · exact hsg390 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg401 hn0 hg390 (by decide)
  · have hn0 : f.name = g405.name := hnm.symm.trans (congrArg Prod.fst hsg405.symm)
    have hc : m8PreprocessM6Fn.checkCallsOk
        [ ("full_propagate", [i64], [i64])
        , ("full_arena_sweep", [i64], [i64])
        , ("full_lucky", [i64], [i64])
        , ("full_compact_needed", [i64], [.bool])
        , ("full_compact", [i64], [i64])
        , ("full_scale_delta_m5", [i64, i64], [i64])
        , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsg86 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg86 (by decide)
    · exact hsg104 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg104 (by decide)
    · exact hsg184 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg184 (by decide)
    · exact hsg354 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg354 (by decide)
    · exact hsg366 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg366 (by decide)
    · exact hsg32 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg32 (by decide)
    · exact hsg404 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg405 hn0 hg404 (by decide)

theorem m8FidV12_noExit : m8FidV12Module.exits = [] := by t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM8FidV12

end

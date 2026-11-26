/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 11 PR 1 — Strictly Faithful 4.0.4 Parity (`FullFidelityStep11`)

Purely additive C0 layer (`8` sig-preserving replacements, `0` inserted helpers = `505` fns,
`0` externs, `0` exits, every function `<= 6` args for SysV x64 & Arm64 ABI) atop Step 10
`fidStep10Module` (`505` fns), implementing strictly faithful Kissat 4.0.4 heuristic and counter
parity with zero soundness-invariant changes and zero beyond-upstream heuristics:
1. **`S11-1` (Vivify LIFO revert — `vivify.c:1303`):** Restore `FullFidelityStep7`'s LIFO
   unsorted scan `rr[do_sort ? bi : (bn - 1ULL - bi)]` in `full_vivify_tier_m6_hdr`.
2. **`S11-2` (Probing counter guards — `proplit.h:194`, `proprobe.c`):** Guard
   `h->conflicts++` with `if (h->probing == 0ULL)` in `full_min_shrink_m6`,
   `full_analyze_core_m6` (`dst == 2`), `full_analyze` (`dst == 2`), and
   `full_ana_failed_lit_m6_hdr`; guard `m6_hdr_record_used` in `full_analyze_rsn_m6_hdr`;
   save/restore `h->search_ticks` across `full_lucky` in `full_preprocess_m6`.
3. **`S11-4` (Faithful `randec` mode-switch burst — `mode.c`, `decide.c`, `propsearch.c:56`):**
   On focused re-entry in `full_switch_mode_m7`, apply pending conflict delta to `RANDEC_REM`,
   never reset `RANDEC_SEQ`, and start an immediate burst whenever `RANDEC_REM == 0`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep11 "
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
#define PH_GLUE_MASK          0x7FFFFu
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define M7_GU_RANDEC_REM      56ULL
#define M7_GU_RANDEC_LIM      58ULL
#define M7_GU_RANDEC_SEQ      60ULL
#define M7_GU_RANDEC_CFL      62ULL

extern u64 full_ilog10(u64 x);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_tick_rel(FullHdr *h);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern void full_ema_update(FullHdr *h, u64 glue);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void m6_hdr_record_used(FullHdr *h, u64 glue);
extern u64 full_propagate(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var);
extern void full_clear_ana(FullHdr *h);
extern void full_bump_analyzed_m6_hdr(FullHdr *h);
extern void full_restore_bump_ana_m6_hdr(FullHdr *h);
extern u64 full_ana_failed_lit_m6_hdr(FullHdr *h);
extern void full_min_mark(FullHdr *h, u32 v, u8 tag);
extern void full_sort_tmp(FullHdr *h);
extern bool full_min_lit_dfs_m8(FullHdr *h, u32 root_lit, bool minimizing, bool check_used);
extern bool full_shrink_blk_bool_m8(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr);
extern void full_min_shrink_m6(FullHdr *h);
extern void full_min_shrink(FullHdr *h);
extern u64 full_deduce_1uip(FullHdr *h);
extern u64 full_deduce_1uip_m6_hdr(FullHdr *h);
extern u64 full_one_lit_confl(FullHdr *h);
extern u64 full_learn_clause(FullHdr *h, u64 glue);
extern void full_restore_bump_ana_m5(FullHdr *h);
extern u64 full_learn_clause_m6(FullHdr *h, u64 glue);
extern u64 full_lucky(FullHdr *h);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);
extern u64 full_m7_get64(FullHdr *h, u64 idx);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);
extern void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m);
extern u64 full_probe_m6(FullHdr *h, bool initial);

bool full_analyze_rsn_m6_hdr(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    if (glue > 1ULL) {
      u64 lim = glue - 1ULL;
      u32 *lv = (u32 *)h->level;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL; u64 lo = 0ULL; bool more = true;
      while (more && ng <= lim) {
        u64 best = 0xFFFFFFFFFFFFFFFFULL; u32 k = 0u;
        while (k < sz) {
          u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
          if (kv < cv) {
            u64 kl = (u64)lv[kv];
            if (kl >= lo && kl < best) { best = kl; }
          }
          k = k + 1u;
        }
        if (best == 0xFFFFFFFFFFFFFFFFULL) { more = false; }
        else { ng = ng + 1ULL; lo = best + 1ULL; }
      }
      if (!more && ng > 0ULL && ng < glue) {
        hdr = (hdr & (~PH_GLUE_MASK)) | (u32)ng;
        ar[rsn] = hdr;
        glue = ng;
      }
    }
    if (h->probing == 0ULL) { m6_hdr_record_used(h, glue); }
    u32 old_u = (hdr >> 27) & 31u;
    if (31u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (31u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

u64 full_ana_failed_lit_m6_hdr(FullHdr *h) {
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
  if (h->probing == 0ULL) {
    full_ema_update(h, 0ULL);
    h->conflicts = h->conflicts + 1ULL;
  }
  h->learned_lits = h->learned_lits + 1ULL;
  h->iterating = 1ULL;
  return 1ULL;
}

void full_min_shrink_m6(FullHdr *h) {
  u64 cv = h->cur_vars; u64 orig_tlen = h->tmp_len;
  if (h->probing == 0ULL) { h->conflicts = h->conflicts + 1ULL; }
  if (orig_tlen <= 1ULL || orig_tlen > cv) {
    h->learned_lits = h->learned_lits + orig_tlen; return;
  }
  full_sort_tmp(h);
  u32 *tmp = (u32 *)h->tmp_lits; u32 *lvl = (u32 *)h->level; u32 *tpos = (u32 *)h->trail_pos;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  u64 i = 0ULL;
  while (i < orig_tlen) { full_min_mark(h, tmp[i] >> 1, (u8)2); i = i + 1ULL; }
  u64 tlen = orig_tlen;
  u64 beg = 1ULL;
  while (beg < tlen) {
    u32 blvl = lvl[tmp[beg] >> 1]; u64 max_tr = (u64)tpos[tmp[beg] >> 1];
    u64 end_b = beg + 1ULL;
    while (end_b < tlen && lvl[tmp[end_b] >> 1] == blvl) {
      u64 tp = (u64)tpos[tmp[end_b] >> 1];
      if (tp > max_tr) { max_tr = tp; }
      end_b = end_b + 1ULL;
    }
    if (end_b - beg >= 2ULL) {
      if (!full_shrink_blk_bool_m8(h, beg, end_b, blvl, max_tr)) {
        u64 mk2 = beg;
        while (mk2 < end_b) {
          if (full_min_lit_dfs_m8(h, tmp[mk2], false, false)) { tmp[mk2] = 0xFFFFFFFFu; }
          mk2 = mk2 + 1ULL;
        }
      }
    }
    beg = end_b;
  }
  u64 keep = 1ULL; u64 k = 1ULL;
  while (k < tlen) {
    if (tmp[k] != 0xFFFFFFFFu) { tmp[keep] = tmp[k]; keep = keep + 1ULL; }
    k = k + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  if (h->min_clr_full != 0ULL) {
    u64 v = 0ULL; while (v < cv) { mrk[v] = (u8)0; v = v + 1ULL; }
  } else {
    u32 *mclr = (u32 *)h->min_clr; u64 z = 0ULL;
    while (z < h->min_clr_len) {
      u32 z_v = mclr[z]; if ((u64)z_v < cv) { mrk[z_v] = (u8)0; }
      z = z + 1ULL;
    }
  }
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL; h->tmp_len = keep;
  h->min_removed = h->min_removed + (orig_tlen - keep);
  h->learned_lits = h->learned_lits + keep;
}

u64 full_analyze(FullHdr *h) {
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
      if (h->probing == 0ULL) {
        h->conflicts = h->conflicts + 1ULL;
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

u64 full_analyze_core_m6(FullHdr *h) {
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
      if (h->probing == 0ULL) {
        h->conflicts = h->conflicts + 1ULL;
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
    return full_learn_clause_m6(h, glue);
  }
  return 0ULL;
}

void full_switch_mode_m7(FullHdr *h) {
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
    u64 rem = full_m7_get64(h, M7_GU_RANDEC_REM);
    u64 lc = full_m7_get64(h, M7_GU_RANDEC_CFL);
    if (h->conflicts > lc) {
      u64 dc = h->conflicts - lc;
      rem = (rem > dc) ? (rem - dc) : 0ULL;
      full_m7_set64(h, M7_GU_RANDEC_REM, rem);
    }
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
    if (rem == 0ULL) {
      u64 rseq = full_m7_get64(h, M7_GU_RANDEC_SEQ) + 1ULL;
      full_m7_set64(h, M7_GU_RANDEC_SEQ, rseq);
      u64 qarg = (rseq < 1000000000000ULL) ? (rseq + 9ULL) : 1000000000009ULL;
      u64 lg = full_log10_q16_m7(qarg);
      u64 rlen = (10ULL * lg) >> 16;
      if (rlen < 10ULL) { rlen = 10ULL; }
      u64 rdelta = (500ULL * lg) >> 16;
      full_m7_set64(h, M7_GU_RANDEC_REM, rlen);
      full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + rdelta);
    }
  }
}

u64 full_preprocess_m6(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  u64 saved_lk_ticks = h->search_ticks;
  u64 lk = full_lucky(h);
  h->search_ticks = saved_lk_ticks;
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

/-! ## 1. Canonical `Fn` Handles, Replacement Lists & Module (`505` fns) -/

def fidStep11AnalyzeRsnM6HdrFn : Fn :=
  ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], full_analyze_rsn_m6_hdr_body⟩

def fidStep11AnaFailedLitM6HdrFn : Fn :=
  ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], full_ana_failed_lit_m6_hdr_body⟩

def fidStep11MinShrinkM6Fn : Fn :=
  ⟨"full_min_shrink_m6", [i64], [], full_min_shrink_m6_body⟩

def fidStep11AnalyzeFn : Fn :=
  ⟨"full_analyze", [i64], [i64], full_analyze_body⟩

def fidStep11AnalyzeCoreM6Fn : Fn :=
  ⟨"full_analyze_core_m6", [i64], [i64], full_analyze_core_m6_body⟩

def fidStep11VivifyTierM6HdrFn : Fn :=
  FullFidelityStep7.fidStep7VivifyTierM6HdrFn

def fidStep11SwitchModeM7Fn : Fn :=
  ⟨"full_switch_mode_m7", [i64], [], full_switch_mode_m7_body⟩

def fidStep11PreprocessM6Fn : Fn :=
  ⟨"full_preprocess_m6", [i64], [i64], full_preprocess_m6_body⟩

/-- Exact `8`-function Step-11 PR 1 replacement list over `fidStep10Fns`. -/
def fidStep11Pr1Repls : List Fn :=
  [ fidStep11AnalyzeRsnM6HdrFn
  , fidStep11AnaFailedLitM6HdrFn
  , fidStep11MinShrinkM6Fn
  , fidStep11AnalyzeFn
  , fidStep11AnalyzeCoreM6Fn
  , fidStep11VivifyTierM6HdrFn
  , fidStep11SwitchModeM7Fn
  , fidStep11PreprocessM6Fn ]

/-- Alias for the PR 1 replacement list (`fidStep11Pr1Repls`). -/
def fidStep11Repls : List Fn :=
  fidStep11Pr1Repls

/-- Step-11 PR 1 helper insertions (empty; `505 -> 505` functions). -/
def fidStep11Befores : List (Sym × List Fn) :=
  []

/-- Ordered `505`-fn Step-11 PR 1 `KissatFidelity` function list (`patchFns` over
`fidStep10Fns`). -/
def fidStep11ModuleFns : List Fn :=
  patchFns fidStep11Repls fidStep11Befores fidStep10Fns

/-- Closed `505`-function Gate-1 Step-11 PR 1 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep11Module : LeanQbe.T.Module :=
  { fidStep10Module with fns := fidStep11ModuleFns }

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Exit-Freedom -/

public section

theorem fidStep11ModuleFns_eq : fidStep11Module.fns = fidStep11ModuleFns :=
  rfl

theorem full_analyze_rsn_m6_hdr_step11_wf : Func.Wf fidStep11AnalyzeRsnM6HdrFn.body := by t_wf_reify
theorem full_ana_failed_lit_m6_hdr_step11_wf :
    Func.Wf fidStep11AnaFailedLitM6HdrFn.body := by
  t_wf_reify
theorem full_min_shrink_m6_step11_wf : Func.Wf fidStep11MinShrinkM6Fn.body := by t_wf_reify
theorem full_analyze_step11_wf : Func.Wf fidStep11AnalyzeFn.body := by t_wf_reify
theorem full_analyze_core_m6_step11_wf : Func.Wf fidStep11AnalyzeCoreM6Fn.body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_step11_wf : Func.Wf fidStep11VivifyTierM6HdrFn.body :=
  FullFidelityStep7.full_vivify_tier_m6_hdr_step7_wf
theorem full_switch_mode_m7_step11_wf : Func.Wf fidStep11SwitchModeM7Fn.body := by t_wf_reify
theorem full_preprocess_m6_step11_wf : Func.Wf fidStep11PreprocessM6Fn.body := by t_wf_reify

theorem fidStep11Befores_wf : ∀ h ∈ fidStep11Befores.flatMap Prod.snd, h.Wf := by
  intro h hh
  cases hh

theorem fidStep11Pr1Repls_wf : ∀ f ∈ fidStep11Pr1Repls, f.Wf := by
  intro f hf
  simp only [fidStep11Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_analyze_rsn_m6_hdr_step11_wf
  · exact full_ana_failed_lit_m6_hdr_step11_wf
  · exact full_min_shrink_m6_step11_wf
  · exact full_analyze_step11_wf
  · exact full_analyze_core_m6_step11_wf
  · exact full_vivify_tier_m6_hdr_step11_wf
  · exact full_switch_mode_m7_step11_wf
  · exact full_preprocess_m6_step11_wf

theorem fidStep11Repls_wf : ∀ f ∈ fidStep11Repls, f.Wf :=
  fidStep11Pr1Repls_wf

theorem fidStep11Module_wf : ∀ f ∈ fidStep11Module.fns, f.Wf :=
  patchFns_wf fidStep10Module_wf fidStep11Repls_wf fidStep11Befores_wf

theorem fidStep11_noExit : fidStep11Module.exits = [] :=
  fidStep10_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep11

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 13 Shard S4-B: Conflict Analysis, Shrink & `L6a` Header Hoists

Data-pure C0 module (`0` `*Proof*` imports) defining the `10` S4-B functions (`1` ADD + `9` MOD)
copied verbatim from frozen `step13_v2_frozen_direct.c`:
- **ADD (`1`):** `full_analyze_reasons_fid`.
- **MOD (`9`):** `full_analyze_rsn_m6_hdr`, `full_bump_analyzed_m6_hdr`,
  `full_restore_bump_ana_m6_hdr`, `full_ana_failed_lit_m6_hdr`, `full_min_lit_dfs_m8`,
  `full_shrink_blk_bool_m8`, `full_min_shrink_m6`, `full_analyze_core_m6`,
  `full_analyze_m6_hdr`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S4B "
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
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var);
extern void m6_hdr_record_used(FullHdr *h, u64 glue);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool m6_hdr_dr_allow(FullHdr *h);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void full_bump_analyzed_mode_fid(FullHdr *h, bool allow_reasons);
extern void full_restore_bump_ana_mode_fid(FullHdr *h, bool allow_reasons);
extern void full_clear_ana(FullHdr *h);
extern void full_backtrack_ac_fid(FullHdr *h, u64 target_lvl);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_tick_rel(FullHdr *h);
extern void full_ema_update(FullHdr *h, u64 glue);
extern void full_min_mark(FullHdr *h, u32 v, u8 tag);
extern bool full_shrink_lower_m8(FullHdr *h, u32 ot, u32 ov);
extern void full_sort_tmp(FullHdr *h);
extern u64  full_one_lit_confl(FullHdr *h);
extern u64  full_deduce_1uip_m6_hdr(FullHdr *h);
extern void m6_hdr_update_tier_limits(FullHdr *h);
extern u64  full_learn_clause_m6(FullHdr *h, u64 glue);
extern void m6_hdr_dr_update(FullHdr *h);

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
      u32 *lv = (u32 *)h->level;
      u32 *ftrl = (u32 *)h->frame_trail;
      u32 *mclr = (u32 *)h->min_clr;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL;
      u32 k = 0u;
      while (k < sz) {
        u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
        if (kv < cv) {
          u64 kl = (u64)lv[kv];
          if (kl <= h->cur_level && (ftrl[kl] & 0x80000000u) == 0u) {
            ftrl[kl] = ftrl[kl] | 0x80000000u;
            mclr[ng] = (u32)kl;
            ng = ng + 1ULL;
            if (ng >= glue) { break; }
          }
        }
        k = k + 1u;
      }
      u64 ui = 0ULL;
      while (ui < ng) {
        u32 ml = mclr[ui];
        ftrl[ml] = ftrl[ml] & 0x7FFFFFFFu;
        ui = ui + 1ULL;
      }
      if (ng > 0ULL && ng < glue) {
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

void full_analyze_reasons_fid(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u64 cv = h->cur_vars;
  u64 ana_n = h->res_sz;
  if (ana_n > cv) { ana_n = cv; }
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u64 w = 0ULL;
  u64 k = 0ULL;
  while (k < ana_n) {
    u32 av = ana[k];
    if ((u64)av < cv && mrk[av] == (u8)0) {
      mrk[av] = (u8)1;
      ana[w] = av;
      w = w + 1ULL;
    }
    k = k + 1ULL;
  }
  u64 tlen = h->tmp_len;
  if (tlen <= cv) {
    u64 ti = 0ULL;
    while (ti < tlen) {
      u32 tv = tmp[ti] >> 1;
      if ((u64)tv < cv && lvl[tv] > 0u && mrk[tv] == (u8)0 && w < cv) {
        mrk[tv] = (u8)1;
        ana[w] = tv;
        w = w + 1ULL;
      }
      ti = ti + 1ULL;
    }
  }
  h->min_clr_len = w;
  if (w == 0ULL) { return; }
  u64 saved = w;
  if (!m6_hdr_delaying(h, 0ULL) && m6_hdr_dr_allow(h)) {
    u64 lim = saved * 10ULL;
    u64 i = 0ULL;
    u64 tlen_r = h->tmp_len;
    if (tlen_r > cv) { tlen_r = cv; }
    while (i < tlen_r && h->min_clr_len <= lim) {
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
          h->search_ticks = h->search_ticks + 1ULL;
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
      m6_hdr_bump_delay(h, 0ULL);
    } else {
      m6_hdr_reduce_delay(h, 0ULL);
    }
  }
  u64 ci = 0ULL;
  while (ci < h->min_clr_len) {
    u32 cv_i = ana[ci];
    if ((u64)cv_i < cv) { mrk[cv_i] = (u8)0; }
    ci = ci + 1ULL;
  }
}

void full_bump_analyzed_m6_hdr(FullHdr *h) {
  full_bump_analyzed_mode_fid(h, true);
}

void full_restore_bump_ana_m6_hdr(FullHdr *h) {
  full_restore_bump_ana_mode_fid(h, true);
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
  full_bump_analyzed_mode_fid(h, false);
  full_clear_ana(h);
  full_backtrack_ac_fid(h, 0ULL);
  u64 k = 0ULL;
  while (k < ucnt) {
    u32 u = tmp[k];
    if (vals[u] < (i8)0) { return 20ULL; }
    if (vals[u] == (i8)0) { full_assign_lvl(h, u, 0xFFFFFFFFu, 0u); }
    k = k + 1ULL;
  }
  if (h->probing == 0ULL) {
    full_tick_rel(h);
    full_ema_update(h, 0ULL);
    h->conflicts = h->conflicts + 1ULL;
  }
  h->learned_lits = h->learned_lits + 1ULL;
  h->iterating = 1ULL;
  return 1ULL;
}

bool full_min_lit_dfs_m8(FullHdr *h, u32 root_lit, bool minimizing, bool check_used) {
  u64 cv = h->cur_vars;
  u32 root_v = root_lit >> 1;
  if ((u64)root_v >= cv || h->min_depth == 0ULL) { return false; }
  u32 *rsns = (u32 *)h->reason;
  if (rsns[root_v] == 0xFFFFFFFFu) { return false; }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena; u32 *stk = (u32 *)h->wsort;
  u32 *used = (u32 *)h->shrink_stk;
  u32 rlvl = lvl[root_v];
  if (minimizing && check_used && (u64)rlvl < cv && (u64)rlvl < h->cur_level &&
      used[rlvl] <= 1u) {
    return false;
  }
  u64 mv = h->max_vars;
  u64 alen = h->arena_len;
  u64 clvl = h->cur_level;
  u64 mdepth = h->min_depth;
  stk[0] = root_v; stk[1] = 0u;
  u64 sp = 0ULL; u64 cur_depth = 0ULL; bool ok = false; u64 steps = 0ULL;
  u64 max_steps = (alen + cv) * 4ULL + 64ULL;
  while (steps < max_steps) {
    steps = steps + 1ULL;
    u32 v = stk[sp << 1]; u32 pword = stk[(sp << 1) + 1ULL];
    u32 pos = pword & 0x7FFFFFFFu;
    if ((u64)v >= cv) { break; }
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) { break; }
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    if (is_bin) {
      if (pos == 0u) {
        stk[(sp << 1) + 1ULL] = pword | 1u;
        u32 u = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)u >= cv) { break; }
        u32 ul = lvl[u];
        if (u == v || ul == 0u) { continue; }
        u8 mu = mrk[u];
        if ((mu & (u8)2) != (u8)0) { continue; }
        if ((mu & (u8)4) != (u8)0) { break; }
        if (rsns[u] == 0xFFFFFFFFu) { full_min_mark(h, u, (u8)4); break; }
        if (check_used && (u64)ul < cv && (u64)ul < clvl && used[ul] == 0u) { break; }
        if (sp + 1ULL >= mv) { break; }
        sp = sp + 1ULL; stk[sp << 1] = u; stk[(sp << 1) + 1ULL] = 0u;
        continue;
      }
      if (sp == 0ULL) { ok = true; break; }
      full_min_mark(h, v, (u8)2);
      if ((pword & 0x80000000u) != 0u && cur_depth > 0ULL) { cur_depth = cur_depth - 1ULL; }
      sp = sp - 1ULL;
      continue;
    }
    if ((u64)rsn + 3ULL > alen) { break; }
    u32 sz = ar[(u64)rsn + 2ULL];
    if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > alen) { break; }
    if (pos == 0u) { h->search_ticks = h->search_ticks + 1ULL; }
    if (pos < sz) {
      stk[(sp << 1) + 1ULL] = (pword & 0x80000000u) | (pos + 1u);
      u32 l = ar[(u64)rsn + 3ULL + (u64)pos];
      u32 u = l >> 1;
      if ((u64)u >= cv) { break; }
      u32 ul = lvl[u];
      if (u == v || ul == 0u) { continue; }
      u8 mu = mrk[u];
      if ((mu & (u8)2) != (u8)0) { continue; }
      if ((mu & (u8)4) != (u8)0) { break; }
      if (rsns[u] == 0xFFFFFFFFu) { full_min_mark(h, u, (u8)4); break; }
      if (check_used && (u64)ul < cv && (u64)ul < clvl && used[ul] == 0u) { break; }
      if (cur_depth + 1ULL >= mdepth || sp + 1ULL >= mv) { break; }
      cur_depth = cur_depth + 1ULL;
      sp = sp + 1ULL; stk[sp << 1] = u; stk[(sp << 1) + 1ULL] = 0x80000000u;
      continue;
    }
    if (sp == 0ULL) { ok = true; break; }
    full_min_mark(h, v, (u8)2);
    if ((pword & 0x80000000u) != 0u && cur_depth > 0ULL) { cur_depth = cur_depth - 1ULL; }
    sp = sp - 1ULL;
  }
  if (!ok) {
    u64 j = 1ULL;
    while (j <= sp) { full_min_mark(h, stk[j << 1], (u8)4); j = j + 1ULL; }
    return false;
  }
  return true;
}

bool full_shrink_blk_bool_m8(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *sstk = (u32 *)h->shrink_stk;
  u32 *ar = (u32 *)h->arena; u64 cv = h->cur_vars; u64 alen = h->arena_len;
  u64 open = end_b - beg; u64 slen = 0ULL; u64 k = beg;
  while (k < end_b) {
    u32 v = tmp[k] >> 1; mrk[v] = mrk[v] | (u8)8;
    sstk[slen] = v; slen = slen + 1ULL; k = k + 1ULL;
  }
  bool failed = false; u32 uip = 0xFFFFFFFFu; u64 t = max_tr;
  while (!failed) {
    while (true) {
      if (t >= h->trail_end) { failed = true; break; }
      u32 lit = trl[t];
      if ((mrk[lit >> 1] & (u8)8) != (u8)0) { uip = lit; break; }
      if (t == 0ULL) { failed = true; break; }
      t = t - 1ULL;
    }
    if (failed || open == 1ULL || t == 0ULL) {
      if (open != 1ULL) { failed = true; }
      break;
    }
    t = t - 1ULL;
    u32 rsn = rsns[uip >> 1];
    if (rsn == 0xFFFFFFFFu) { failed = true; break; }
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    u32 csz = 1u;
    if (!is_bin) {
      if ((u64)rsn + 3ULL > alen) { failed = true; break; }
      csz = ar[(u64)rsn + 2ULL];
      if (csz < 3u || (u64)rsn + 3ULL + (u64)csz > alen) { failed = true; break; }
      h->search_ticks = h->search_ticks + 1ULL;
    }
    u32 i = 0u;
    while (i < csz && !failed) {
      u32 ot = is_bin ? (rsn & PW_LIT_MASK) : ar[(u64)rsn + 3ULL + (u64)i];
      u32 ov = ot >> 1;
      if (ot != uip && (u64)ov < cv && lvl[ov] > 0u && (mrk[ov] & (u8)8) == (u8)0) {
        if (lvl[ov] < blvl) {
          if (!full_shrink_lower_m8(h, ot, ov)) { failed = true; }
        } else if (lvl[ov] == blvl && slen < cv) {
          mrk[ov] = mrk[ov] | (u8)8; sstk[slen] = ov;
          slen = slen + 1ULL; open = open + 1ULL;
        } else { failed = true; }
      }
      i = i + 1u;
    }
    if (!failed) { open = open - 1ULL; }
  }
  if (failed || uip == 0xFFFFFFFFu) {
    u64 i = 0ULL;
    while (i < slen) { u32 sv = sstk[i]; mrk[sv] = mrk[sv] & (u8)0xF7; i = i + 1ULL; }
    return false;
  }
  k = beg;
  while (k < end_b) { tmp[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  tmp[beg] = uip ^ 1u;
  u64 i = 0ULL;
  while (i < slen) {
    u32 sv = sstk[i]; mrk[sv] = mrk[sv] & (u8)0xF7;
    full_min_mark(h, sv, (u8)2); i = i + 1ULL;
  }
  return true;
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
      if (full_shrink_blk_bool_m8(h, beg, end_b, blvl, max_tr)) {
        u32 *ana_s = (u32 *)h->work_stk1;
        u32 uip_v = tmp[beg] >> 1;
        if ((u64)uip_v < cv && h->res_sz < cv) {
          ana_s[h->res_sz] = uip_v;
          h->res_sz = h->res_sz + 1ULL;
        }
      } else {
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
  if (keep > 2ULL) {
    u64 lo = 1ULL;
    u64 hi = keep - 1ULL;
    while (lo < hi) {
      u32 sw = tmp[lo]; tmp[lo] = tmp[hi]; tmp[hi] = sw;
      lo = lo + 1ULL; hi = hi - 1ULL;
    }
    u64 rb = 1ULL;
    while (rb < keep) {
      u32 rl = lvl[((u64)tmp[rb]) >> 1];
      u64 re = rb + 1ULL;
      while (re < keep && lvl[((u64)tmp[re]) >> 1] == rl) { re = re + 1ULL; }
      u64 rl_i = rb;
      u64 rh_i = re - 1ULL;
      while (rl_i < rh_i) {
        u32 sw = tmp[rl_i]; tmp[rl_i] = tmp[rh_i]; tmp[rh_i] = sw;
        rl_i = rl_i + 1ULL; rh_i = rh_i - 1ULL;
      }
      rb = re;
    }
  }
  h->min_removed = h->min_removed + (orig_tlen - keep);
  h->learned_lits = h->learned_lits + keep;
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
        m6_hdr_update_tier_limits(h);
        if (h->cur_vars > 0ULL) {
          if (h->confl_type == 1ULL) { tmp[0] = (u32)h->confl_lit0; h->tmp_len = 1ULL; }
          else if (h->confl_type == 2ULL && h->confl_ref < h->arena_len &&
                   3ULL < h->arena_len - h->confl_ref) {
            tmp[0] = ar[h->confl_ref + 3ULL]; h->tmp_len = 1ULL;
          }
        }
        full_restore_bump_ana_mode_fid(h, false);
      }
      continue;
    }
    full_min_shrink_m6(h);
    if (h->probing == 0ULL) { full_analyze_reasons_fid(h); full_tick_rel(h); }
    u64 glue = 0ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    if (h->probing == 0ULL) { full_ema_update(h, glue); }
    u64 lret = full_learn_clause_m6(h, glue);
    if (h->probing == 0ULL && h->min_clr_len > 0ULL) {
      if (lret == 1ULL) { full_bump_analyzed_mode_fid(h, false); }
      full_clear_ana(h);
    }
    return lret;
  }
  return 0ULL;
}

u64 full_analyze_m6_hdr(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  if (h->probing == 0ULL) {
    m6_hdr_dr_update(h);
  }
  return full_analyze_core_m6(h);
}
"

/-! ## 1. Drop-In `Fn` Handles & Replacement List -/

/-- `full_analyze_rsn_m6_hdr` replacement (Step-13 `ftrl` bit-31 O(sz) glue recomputation). -/
def fidStep13S4AnalyzeRsnM6HdrFn : Fn :=
  ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], full_analyze_rsn_m6_hdr_body⟩

/-- `full_analyze_reasons_fid` inserted helper (pre-learn reason collection & delay update). -/
def fidStep13S4AnalyzeReasonsFidFn : Fn :=
  ⟨"full_analyze_reasons_fid", [i64], [], full_analyze_reasons_fid_body⟩

/-- `full_bump_analyzed_m6_hdr` replacement (delegates to `full_bump_analyzed_mode_fid`). -/
def fidStep13S4BumpAnalyzedM6HdrFn : Fn :=
  ⟨"full_bump_analyzed_m6_hdr", [i64], [], full_bump_analyzed_m6_hdr_body⟩

/-- `full_restore_bump_ana_m6_hdr` replacement (delegates to `full_restore_bump_ana_mode_fid`). -/
def fidStep13S4RestoreBumpAnaM6HdrFn : Fn :=
  ⟨"full_restore_bump_ana_m6_hdr", [i64], [], full_restore_bump_ana_m6_hdr_body⟩

/-- `full_ana_failed_lit_m6_hdr` replacement (calls `full_bump_analyzed_mode_fid(h, false)` +
`full_tick_rel`). -/
def fidStep13S4AnaFailedLitM6HdrFn : Fn :=
  ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], full_ana_failed_lit_m6_hdr_body⟩

/-- `full_min_lit_dfs_m8` replacement (`L6a` header-field hoists). -/
def fidStep13S4MinLitDfsM8Fn : Fn :=
  ⟨"full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool], full_min_lit_dfs_m8_body⟩

/-- `full_shrink_blk_bool_m8` replacement (`L6a` `arena_len` hoist). -/
def fidStep13S4ShrinkBlkBoolM8Fn : Fn :=
  ⟨"full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool], full_shrink_blk_bool_m8_body⟩

/-- `full_min_shrink_m6` replacement (Step-13 `ana_s[res_sz++]` + descending block reverse). -/
def fidStep13S4MinShrinkM6Fn : Fn :=
  ⟨"full_min_shrink_m6", [i64], [], full_min_shrink_m6_body⟩

/-- `full_analyze_core_m6` replacement (Step-13 tier update, reason collect & post-learn bump). -/
def fidStep13S4AnalyzeCoreM6Fn : Fn :=
  ⟨"full_analyze_core_m6", [i64], [i64], full_analyze_core_m6_body⟩

/-- `full_analyze_m6_hdr` replacement (tier limit update moved into `full_analyze_core_m6`). -/
def fidStep13S4AnalyzeM6HdrFn : Fn :=
  ⟨"full_analyze_m6_hdr", [i64], [i64], full_analyze_m6_hdr_body⟩

/-- Ordered list of the `9` S4-B replacement functions (`0` ABI changes). -/
def fidStep13S4BRepls : List Fn :=
  [ fidStep13S4AnalyzeRsnM6HdrFn
  , fidStep13S4BumpAnalyzedM6HdrFn
  , fidStep13S4RestoreBumpAnaM6HdrFn
  , fidStep13S4AnaFailedLitM6HdrFn
  , fidStep13S4MinLitDfsM8Fn
  , fidStep13S4ShrinkBlkBoolM8Fn
  , fidStep13S4MinShrinkM6Fn
  , fidStep13S4AnalyzeCoreM6Fn
  , fidStep13S4AnalyzeM6HdrFn ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem fidStep13S4AnalyzeRsnM6Hdr_wf :
    Func.Wf fidStep13S4AnalyzeRsnM6HdrFn.body := by t_wf_reify
theorem fidStep13S4AnalyzeReasonsFid_wf :
    Func.Wf fidStep13S4AnalyzeReasonsFidFn.body := by t_wf_reify
theorem fidStep13S4BumpAnalyzedM6Hdr_wf :
    Func.Wf fidStep13S4BumpAnalyzedM6HdrFn.body := by t_wf_reify
theorem fidStep13S4RestoreBumpAnaM6Hdr_wf :
    Func.Wf fidStep13S4RestoreBumpAnaM6HdrFn.body := by t_wf_reify
theorem fidStep13S4AnaFailedLitM6Hdr_wf :
    Func.Wf fidStep13S4AnaFailedLitM6HdrFn.body := by t_wf_reify
theorem fidStep13S4MinLitDfsM8_wf :
    Func.Wf fidStep13S4MinLitDfsM8Fn.body := by t_wf_reify
theorem fidStep13S4ShrinkBlkBoolM8_wf :
    Func.Wf fidStep13S4ShrinkBlkBoolM8Fn.body := by t_wf_reify
theorem fidStep13S4MinShrinkM6_wf :
    Func.Wf fidStep13S4MinShrinkM6Fn.body := by t_wf_reify
theorem fidStep13S4AnalyzeCoreM6_wf :
    Func.Wf fidStep13S4AnalyzeCoreM6Fn.body := by t_wf_reify
theorem fidStep13S4AnalyzeM6Hdr_wf :
    Func.Wf fidStep13S4AnalyzeM6HdrFn.body := by t_wf_reify

theorem fidStep13S4BRepls_wf : ∀ f ∈ fidStep13S4BRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S4BRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fidStep13S4AnalyzeRsnM6Hdr_wf
  · exact fidStep13S4BumpAnalyzedM6Hdr_wf
  · exact fidStep13S4RestoreBumpAnaM6Hdr_wf
  · exact fidStep13S4AnaFailedLitM6Hdr_wf
  · exact fidStep13S4MinLitDfsM8_wf
  · exact fidStep13S4ShrinkBlkBoolM8_wf
  · exact fidStep13S4MinShrinkM6_wf
  · exact fidStep13S4AnalyzeCoreM6_wf
  · exact fidStep13S4AnalyzeM6Hdr_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

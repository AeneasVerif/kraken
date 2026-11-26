/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M8 Core Upstream Parity Closures (`FullM8CoreParity`)

Purely additive C0 parity layer (`0` `FullHdr` edits, `0` edits to `FullM6*` / `FullM7*` /
`M5Hub.lean` / compiler / cert files) spliced over `FullM7Fidelity.m7FidelityModule` (`413` fns)
into `m8CoreParityModule` (`435` fns), closing Ranks #5, #4, and #8 from `m8_parity_gap/REPORT.md`:

1. **Rank #5 (`minimize` binary-clause depth + `minimizeticks=1`):**
   - `full_min_lit_dfs_m8`: stores DFS frames `(v, pword)` in `h->wsort` (`2 * max_vars` words,
     guarded by `sp + 1ULL < h->max_vars`), charges `min_depth` (`cur_depth`) only across large
     clauses (`!is_bin`, bit 31 tag in `pword`), leaves `cur_depth` unchanged across binary edges,
     and increments `h->search_ticks` per dereferenced large clause (`if (pos == 0u)`).
   - `full_shrink_lower_m8` & `full_shrink_blk_bool_m8`: propagate `minimizeticks=1`
     (`h->search_ticks` incremented per dereferenced large reason clause in shrink) and wire into
     `full_min_shrink_m6`.
   - `full_analyze_core_m6` keeps its exact body untouched (re-verified in `FullM8CoreParityProof`
     against `m8MinShrinkSpec`, preserving `m6HdrAnalyzeSpec` & `work_stk2` unchanged).

2. **Rank #4 (`probe` scheduling & early-skip parity):**
   - `full_probe_dticks_m6_hdr`: returns `10000000ULL` directly when `initial == true` (`limits.h`).
   - `full_probe_m6`: increments `h->probings` unconditionally (including `initial == true`,
     fixing all `49` early-skip collapses vs C1), updates `probe_limit` only when `!initial`, and
     caps `initial` probing at `1` round vs `2` rounds (`src/probe.c:75,95,99`).
   - `full_search_m6`: uses strict `h->conflicts > h->probe_limit` (`src/probe.c:23`).

3. **Rank #8 (`eliminateocclim=2000` & Kitten definition `8192+` ticks + 2-core reversed pass):**
   - `full_bve_var_key_m7`: raises polarity degree cap `1024 -> 2000` (`4004000ULL + pos + neg`).
   - `full_bve_var_m7` (and alias `full_bve_var`): on standard runs (`scratch_cap >= 16384`, which
     always holds for `--work-mb >= 1` / `32768`-word scratch), raises collection cap to `2000`
     (`M8_OCC_LIM = 2001u` with `pos` in `[0..2000]` and `neg` in `[2001..4001]`), extracts gates
     over `[0..2000)` / `[2001..4001)`, runs Kitten (`M8_K6_MV=256`, `M8_K6_MC=1024`,
     `M8_K6_MAX_ORIG=512`, `tick_lim=8192`) + second reversed-order core pass (`tick_lim=81920`),
     and shares `full_bve_bce_side_m8` across polarities; falls back to legacy `512`/`1096` layout
     when `scratch_cap < 16384`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Fidelity

kissat_c0! m8CoreParity "
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
#define FL_ELIM               2u

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_WM_PROBE_TICKS     0ULL

#define M8_OCC_LIM            2001u
#define M8_NEG_OFF            2001u
#define M8_POS_MASK           4002u
#define M8_NEG_MASK           4066u
#define M8_GF_IDX             4130u
#define M8_RG_IDX             4131u
#define M8_ITE_CNT            4132u
#define M8_TMP_OFF            4134u
#define M8_RES_OFF            4192u
#define M8_K6_BASE            4192u

#define M8_K6_MV              256u
#define M8_K6_MC              1024u
#define M8_K6_MAX_ORIG        512u
#define M8_K6_TICK_LIM        8192u
#define K6_BIN_FLAG           0x80000000u
#define K6_LIT_MASK           0x7FFFFFFFu
#define KM_LRN                0x40000000u
#define KM_CORE               0x80000000u

#define M8_KH_NV              4192u
#define M8_KH_NC              4193u
#define M8_KH_ORIG_NC         4194u
#define M8_KH_LVL             4195u
#define M8_KH_PROP            4196u
#define M8_KH_TRL_END         4197u
#define M8_KH_UNASS           4198u
#define M8_KH_INCONS          4199u
#define M8_KH_QFIRST          4200u
#define M8_KH_QLAST           4201u
#define M8_KH_QSEARCH         4202u
#define M8_KH_QSTAMP          4203u
#define M8_KH_TICKS           4204u
#define M8_KH_TICK_LIM        4205u
#define M8_KH_ALEN            4206u
#define M8_KH_ACAP            4207u
#define M8_KH_NANA            4208u
#define M8_KH_NKL             4209u
#define M8_KH_NRES            4210u
#define M8_KH_NUNITS          4211u
#define M8_KH_OPEN            4212u
#define M8_KH_PHASE           4213u

#define M8_KO_LVL             4224u
#define M8_KO_RSN             4480u
#define M8_KO_QPREV           4736u
#define M8_KO_QNEXT           4992u
#define M8_KO_QST             5248u
#define M8_KO_TRL             5504u
#define M8_KO_FLAGS           5760u
#define M8_KO_ANA             6016u
#define M8_KO_KL              6272u
#define M8_KO_VALS            6528u
#define M8_KO_WHEAD           7040u
#define M8_KO_WNEXT           7552u
#define M8_KO_WBLIT           9600u
#define M8_KO_CL_OFF          11648u
#define M8_KO_CL_META         12672u
#define M8_KO_CL_AUX          13696u
#define M8_KO_UNITS           14720u
#define M8_KO_RES             15232u
#define M8_KO_ARENA           15744u

extern void full_min_mark(FullHdr *h, u32 v, u8 val);
extern void full_sort_tmp(FullHdr *h);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern bool m6_hdr_delaying(FullHdr *h, u64 k);
extern void m6_hdr_bump_delay(FullHdr *h, u64 k);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 k);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 k);
extern void m6_hdr_set_watermark(FullHdr *h, u64 k, u64 v);
extern u64 full_propagate(FullHdr *h);
extern u64 full_reduce_m6(FullHdr *h, bool init);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern void full_rephase(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 max_v, u64 tick_lim);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern bool full_bve_get_tern_m7(FullHdr *h, u32 v_lit, u32 cr, u32 out_off);
extern u32 full_bve_xor_pat_m7(FullHdr *h, u32 v_lit, u32 cr, u32 k);
extern void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern bool full_bve_try_bce(FullHdr *h, u32 blk_lit, u32 cr, u32 opp_off, u32 opp_n);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_reorder_m6(FullHdr *h, u64 lim);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_lucky_late_m7(FullHdr *h);
extern void full_switch_mode_m7(FullHdr *h);
extern u64 full_probe_tail_m6(FullHdr *h, u64 dticks);
extern u64 full_simplify_m6(FullHdr *h, bool init, bool elim);
extern u64 m6_hdr_decide_fid(FullHdr *h);

/* === Rank #5: minimize binary-clause depth + minimizeticks=1 === */

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
  stk[0] = root_v; stk[1] = 0u;
  u64 sp = 0ULL; u64 cur_depth = 0ULL; bool ok = false; u64 steps = 0ULL;
  u64 max_steps = (h->arena_len + cv) * 4ULL + 64ULL;
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
        if (check_used && (u64)ul < cv && (u64)ul < h->cur_level && used[ul] == 0u) { break; }
        if (sp + 1ULL >= h->max_vars) { break; }
        sp = sp + 1ULL; stk[sp << 1] = u; stk[(sp << 1) + 1ULL] = 0u;
        continue;
      }
      if (sp == 0ULL) { ok = true; break; }
      full_min_mark(h, v, (u8)2);
      if ((pword & 0x80000000u) != 0u && cur_depth > 0ULL) { cur_depth = cur_depth - 1ULL; }
      sp = sp - 1ULL;
      continue;
    }
    if ((u64)rsn + 3ULL > h->arena_len) { break; }
    u32 sz = ar[(u64)rsn + 2ULL];
    if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { break; }
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
      if (check_used && (u64)ul < cv && (u64)ul < h->cur_level && used[ul] == 0u) { break; }
      if (cur_depth + 1ULL >= h->min_depth || sp + 1ULL >= h->max_vars) { break; }
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

bool full_shrink_lower_m8(FullHdr *h, u32 ot, u32 ov) {
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[ov] & (u8)2) != (u8)0) { return true; }
  if ((mrk[ov] & (u8)4) != (u8)0 || !full_min_lit_dfs_m8(h, ot, false, false)) {
    full_min_mark(h, ov, (u8)4);
    return false;
  }
  full_min_mark(h, ov, (u8)2);
  return true;
}

bool full_shrink_blk_bool_m8(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *sstk = (u32 *)h->shrink_stk;
  u32 *ar = (u32 *)h->arena; u64 cv = h->cur_vars;
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
      if ((u64)rsn + 3ULL > h->arena_len) { failed = true; break; }
      csz = ar[(u64)rsn + 2ULL];
      if (csz < 3u || (u64)rsn + 3ULL + (u64)csz > h->arena_len) { failed = true; break; }
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
  h->conflicts = h->conflicts + 1ULL;
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

/* === Rank #8: eliminateocclim=2000 & Kitten definition 8192+ 2-core reversed === */

bool full_bve_find_equiv_m8(FullHdr *h, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 bin_p = 0u;
  u32 i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) {
      u32 ot = wp & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { lm[ot] = (u8)1; bin_p = bin_p + 1u; }
    }
    i = i + 1u;
  }
  if (bin_p == 0u) { return false; }
  u32 match_lit = 0xFFFFFFFFu;
  u32 match_j = 0u;
  u32 j = 0u;
  while (j < nn) {
    u32 wn = scr[M8_NEG_OFF + j];
    if ((wn & PW_BIN_FLAG) != 0u) {
      u32 ot = wn & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot ^ 1u] != (u8)0) {
        match_lit = ot ^ 1u; match_j = j; break;
      }
    }
    j = j + 1u;
  }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) { lm[wp & PW_LIT_MASK] = (u8)0; }
    i = i + 1u;
  }
  if (match_lit == 0xFFFFFFFFu) { return false; }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u && (wp & PW_LIT_MASK) == match_lit) {
      scr[M8_POS_MASK + (i >> 5)] = 1u << (i & 31u);
      scr[M8_NEG_MASK + (match_j >> 5)] = 1u << (match_j & 31u);
      scr[M8_GF_IDX] = 1u;
      scr[M8_RG_IDX] = 0u;
      return true;
    }
    i = i + 1u;
  }
  return false;
}

bool full_bve_find_and_m8(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n) {
  u32 pol = lit & 1u;
  u32 lit_off = (pol != 0u) ? M8_NEG_OFF : 0u;
  u32 opp_off = (pol != 0u) ? 0u : M8_NEG_OFF;
  u32 lit_mask = (pol != 0u) ? M8_NEG_MASK : M8_POS_MASK;
  u32 opp_mask = (pol != 0u) ? M8_POS_MASK : M8_NEG_MASK;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 marked = 0u;
  u32 j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot] == (u8)0) { lm[ot] = (u8)1; marked = marked + 1u; }
    }
    j = j + 1u;
  }
  if (marked < 2u) {
    j = 0u;
    while (j < opp_n) {
      u32 w = scr[opp_off + j];
      if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
      j = j + 1u;
    }
    return false;
  }
  u32 found_i = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < lit_n) {
    u32 w = scr[lit_off + i];
    if ((w & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true; u32 need = 0u; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        if (l != lit) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if (lm[l ^ 1u] == (u8)0) { ok = false; break; }
            need = need + 1u;
          }
        }
        k = k + 1u;
      }
      if (ok && need >= 1u) { found_i = i; break; }
    }
    i = i + 1u;
  }
  j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
    j = j + 1u;
  }
  if (found_i == 0xFFFFFFFFu) { return false; }
  u32 cr = scr[lit_off + found_i];
  u32 sz = ar[(u64)cr + 2ULL];
  u32 uniq_need = 0u; u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit && vals[l] == (i8)0 && lm[l ^ 1u] == (u8)0) {
      lm[l ^ 1u] = (u8)1; uniq_need = uniq_need + 1u;
    }
    k = k + 1u;
  }
  u32 matched = 0u; j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (lm[ot] == (u8)1) {
        lm[ot] = (u8)0;
        u32 midx = opp_mask + (j >> 5);
        scr[midx] = scr[midx] | (1u << (j & 31u));
        matched = matched + 1u;
      }
    }
    j = j + 1u;
  }
  k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit) { lm[l ^ 1u] = (u8)0; }
    k = k + 1u;
  }
  if (matched == uniq_need && uniq_need >= 1u) {
    scr[lit_mask + (found_i >> 5)] = 1u << (found_i & 31u);
    scr[M8_GF_IDX] = 1u;
    scr[M8_RG_IDX] = 0u;
    return true;
  }
  k = 0u;
  while (k < 64u) { scr[opp_mask + k] = 0u; k = k + 1u; }
  return false;
}

u32 full_bve_match_tern_m8(FullHdr *h, u32 opp_lit, u32 x, u32 y, u32 opp_off, u32 opp_n) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 j = 0u;
  while (j < opp_n && scr[M8_ITE_CNT] < 2000u) {
    scr[M8_ITE_CNT] = scr[M8_ITE_CNT] + 1u;
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (ot == x || ot == y) { return j | 0x80000000u; }
    } else {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true; bool sx = false; bool sy = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        i8 vl = vals[l];
        if (vl > (i8)0) { ok = false; break; }
        if (vl == (i8)0 && l != opp_lit) {
          if (l == x) { sx = true; }
          else if (l == y) { sy = true; }
          else { ok = false; break; }
        }
        k = k + 1u;
      }
      if (ok) {
        if (sx && sy) { return j; }
        if (sx || sy) { return j | 0x80000000u; }
      }
    }
    j = j + 1u;
  }
  return 0xFFFFFFFFu;
}

bool full_bve_find_ite_side_m8(FullHdr *h, u32 v, u32 np, u32 nn, bool neg) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 lit = (v << 1) | (neg ? 1u : 0u);
  u32 opp = lit ^ 1u;
  u32 lit_off = neg ? M8_NEG_OFF : 0u;
  u32 lit_n = neg ? nn : np;
  u32 opp_off = neg ? 0u : M8_NEG_OFF;
  u32 opp_n = neg ? np : nn;
  u32 lit_mask = neg ? M8_NEG_MASK : M8_POS_MASK;
  u32 opp_mask = neg ? M8_POS_MASK : M8_NEG_MASK;
  if (lit_n < 2u || opp_n < 2u) { return false; }
  u64 large_clauses = 0ULL; u32 idx = 0u;
  while (idx < lit_n) {
    if ((scr[lit_off + idx] & PW_BIN_FLAG) == 0u) { large_clauses = large_clauses + 1ULL; }
    idx = idx + 1u;
  }
  if (large_clauses < 2ULL || large_clauses * large_clauses > 2000ULL) { return false; }
  scr[M8_ITE_CNT] = 0u;
  u32 i0 = 0u;
  while (i0 + 1u < lit_n && scr[M8_ITE_CNT] < 2000u) {
    u32 w0 = scr[lit_off + i0];
    if ((w0 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w0, M8_TMP_OFF)) {
      u32 a0 = scr[M8_TMP_OFF]; u32 a1 = scr[M8_TMP_OFF + 1u];
      u32 i1 = i0 + 1u;
      while (i1 < lit_n && scr[M8_ITE_CNT] < 2000u) {
        u32 w1 = scr[lit_off + i1];
        if ((w1 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w1, M8_TMP_OFF + 2u)) {
          u32 b0 = scr[M8_TMP_OFF + 2u]; u32 b1 = scr[M8_TMP_OFF + 3u];
          bool ok = false; u32 cond = 0u; u32 u = 0u; u32 w = 0u;
          if (a0 == (b0 ^ 1u)) { ok = true; cond = a0; u = a1; w = b1; }
          else if (a0 == (b1 ^ 1u)) { ok = true; cond = a0; u = a1; w = b0; }
          else if (a1 == (b0 ^ 1u)) { ok = true; cond = a1; u = a0; w = b1; }
          else if (a1 == (b1 ^ 1u)) { ok = true; cond = a1; u = a0; w = b0; }
          if (ok && (u >> 1) != (w >> 1)) {
            u32 m0 = full_bve_match_tern_m8(h, opp, cond, u ^ 1u, opp_off, opp_n);
            if (m0 != 0xFFFFFFFFu) {
              u32 m1 = full_bve_match_tern_m8(h, opp, cond ^ 1u, w ^ 1u, opp_off, opp_n);
              if (m1 != 0xFFFFFFFFu) {
                u32 j0 = m0 & 0x7FFFFFFFu; u32 j1 = m1 & 0x7FFFFFFFu;
                if (j0 != j1) {
                  scr[lit_mask + (i0 >> 5)] = scr[lit_mask + (i0 >> 5)] | (1u << (i0 & 31u));
                  scr[lit_mask + (i1 >> 5)] = scr[lit_mask + (i1 >> 5)] | (1u << (i1 & 31u));
                  scr[opp_mask + (j0 >> 5)] = scr[opp_mask + (j0 >> 5)] | (1u << (j0 & 31u));
                  scr[opp_mask + (j1 >> 5)] = scr[opp_mask + (j1 >> 5)] | (1u << (j1 & 31u));
                  scr[M8_GF_IDX] = 1u;
                  scr[M8_RG_IDX] = (((m0 | m1) & 0x80000000u) != 0u) ? 1u : 0u;
                  return true;
                }
              }
            }
          }
        }
        i1 = i1 + 1u;
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

bool full_bve_find_ite_m8(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (full_bve_find_ite_side_m8(h, v, np, nn, false)) { return true; }
  return full_bve_find_ite_side_m8(h, v, np, nn, true);
}

bool full_bve_find_xor_m8(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 lp = 0u; u32 ln = 0u; u32 i = 0u;
  while (i < np) { if ((scr[i] & PW_BIN_FLAG) == 0u) { lp = lp + 1u; } i = i + 1u; }
  i = 0u;
  while (i < nn) { if ((scr[M8_NEG_OFF + i] & PW_BIN_FLAG) == 0u) { ln = ln + 1u; } i = i + 1u; }
  if (lp < 2u || ln < 2u || (u64)lp * (u64)ln > 4096ULL) { return false; }
  u32 pl = v << 1; u32 nl = pl | 1u; u32 i0 = 0u;
  u32 tmp_e = M8_TMP_OFF; u32 tmp_o = M8_TMP_OFF + 16u; u32 tmp_l = M8_TMP_OFF + 32u;
  while (i0 < np) {
    u32 w0 = scr[i0];
    if ((w0 & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w0 + 2ULL];
      bool ok = true; u32 k = 0u; u32 u = 0u;
      while (u < sz) {
        u32 l = ar[(u64)w0 + 3ULL + (u64)u];
        if (l != pl) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if ((l >> 1) == v || lm[l] != (u8)0 || k >= 4u) { ok = false; break; }
            lm[l] = (u8)(2u + (k << 1)); lm[l ^ 1u] = (u8)(3u + (k << 1));
            scr[tmp_l + k] = l; k = k + 1u;
          }
        }
        u = u + 1u;
      }
      if (ok && k >= 2u && k <= 4u) {
        u32 etgt = (k == 2u) ? 0x9u : ((k == 3u) ? 0x69u : 0x9669u);
        u32 otgt = (k == 2u) ? 0x6u : ((k == 3u) ? 0x96u : 0x6996u);
        u32 emask = 1u; scr[tmp_e] = i0; u32 p_idx = 0u;
        while (p_idx < np && emask != etgt) {
          u32 w = scr[p_idx];
          if (p_idx != i0 && (w & PW_BIN_FLAG) == 0u) {
            u32 pat = full_bve_xor_pat_m7(h, pl, w, k);
            if (pat < 16u && ((etgt >> pat) & 1u) != 0u && ((emask >> pat) & 1u) == 0u) {
              emask = emask | (1u << pat); scr[tmp_e + pat] = p_idx;
            }
          }
          p_idx = p_idx + 1u;
        }
        u32 omask = 0u;
        if (emask == etgt) {
          u32 n_idx = 0u;
          while (n_idx < nn && omask != otgt) {
            u32 w = scr[M8_NEG_OFF + n_idx];
            if ((w & PW_BIN_FLAG) == 0u) {
              u32 pat = full_bve_xor_pat_m7(h, nl, w, k);
              if (pat < 16u && ((otgt >> pat) & 1u) != 0u && ((omask >> pat) & 1u) == 0u) {
                omask = omask | (1u << pat); scr[tmp_o + pat] = n_idx;
              }
            }
            n_idx = n_idx + 1u;
          }
        }
        u32 c = 0u;
        while (c < k) { u32 l = scr[tmp_l + c]; lm[l] = (u8)0; lm[l ^ 1u] = (u8)0; c = c + 1u; }
        if (emask == etgt && omask == otgt) {
          u32 p = 0u; u32 nlim = 1u << k;
          while (p < nlim) {
            if (((etgt >> p) & 1u) != 0u) {
              u32 pi = scr[tmp_e + p];
              scr[M8_POS_MASK + (pi >> 5)] = scr[M8_POS_MASK + (pi >> 5)] | (1u << (pi & 31u));
            }
            if (((otgt >> p) & 1u) != 0u) {
              u32 ni = scr[tmp_o + p];
              scr[M8_NEG_MASK + (ni >> 5)] = scr[M8_NEG_MASK + (ni >> 5)] | (1u << (ni & 31u));
            }
            p = p + 1u;
          }
          scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 0u; return true;
        }
      } else {
        u32 c = 0u;
        while (c < k) { u32 l = scr[tmp_l + c]; lm[l] = (u8)0; lm[l ^ 1u] = (u8)0; c = c + 1u; }
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

void full_k6_watch_m8(FullHdr *h, u32 cid, u32 l0, u32 l1, u32 sz) {
  if (cid >= M8_K6_MC || l0 >= (M8_K6_MV << 1) || l1 >= (M8_K6_MV << 1)) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 bf = (sz == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  scr[M8_KO_WBLIT + w0] = l1 | bf;
  scr[M8_KO_WNEXT + w0] = scr[M8_KO_WHEAD + l0]; scr[M8_KO_WHEAD + l0] = w0;
  scr[M8_KO_WBLIT + w1] = l0 | bf;
  scr[M8_KO_WNEXT + w1] = scr[M8_KO_WHEAD + l1]; scr[M8_KO_WHEAD + l1] = w1;
}

void full_k6_assign_m8(FullHdr *h, u32 lit, u32 rsn_cid) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 te = scr[M8_KH_TRL_END];
  if (lit >= (M8_K6_MV << 1) || te >= M8_K6_MV) { return; }
  u32 v = lit >> 1;
  scr[M8_KO_VALS + lit] = 1u; scr[M8_KO_VALS + (lit ^ 1u)] = 2u;
  scr[M8_KO_LVL + v] = scr[M8_KH_LVL]; scr[M8_KO_RSN + v] = rsn_cid;
  scr[M8_KO_TRL + te] = lit; scr[M8_KH_TRL_END] = te + 1u;
  if (scr[M8_KH_UNASS] > 0u) { scr[M8_KH_UNASS] = scr[M8_KH_UNASS] - 1u; }
  u32 fl = scr[M8_KO_FLAGS + v];
  scr[M8_KO_FLAGS + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

void full_k6_mtf_m8(FullHdr *h, u32 v) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nv = scr[M8_KH_NV];
  if (v >= nv || nv > M8_K6_MV) { return; }
  u32 ql = scr[M8_KH_QLAST];
  if (v != ql) {
    u32 pv = scr[M8_KO_QPREV + v]; u32 nx = scr[M8_KO_QNEXT + v];
    if (pv < nv) { scr[M8_KO_QNEXT + pv] = nx; } else { scr[M8_KH_QFIRST] = nx; }
    if (nx < nv) { scr[M8_KO_QPREV + nx] = pv; } else { scr[M8_KH_QLAST] = pv; }
    u32 old_last = scr[M8_KH_QLAST];
    scr[M8_KO_QPREV + v] = old_last; scr[M8_KO_QNEXT + v] = 0xFFFFFFFFu;
    if (old_last < nv) { scr[M8_KO_QNEXT + old_last] = v; } else { scr[M8_KH_QFIRST] = v; }
    scr[M8_KH_QLAST] = v;
  }
  u32 st = scr[M8_KH_QSTAMP] + 1u;
  scr[M8_KH_QSTAMP] = st; scr[M8_KO_QST + v] = st; scr[M8_KH_QSEARCH] = v;
}

void full_k6_backtrack_m8(FullHdr *h, u32 target_lvl) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nv = scr[M8_KH_NV];
  if (nv > M8_K6_MV) { return; }
  u32 te = scr[M8_KH_TRL_END];
  if (te > M8_K6_MV) { te = M8_K6_MV; }
  while (te > 0u) {
    u32 lit = scr[M8_KO_TRL + te - 1u]; u32 v = lit >> 1;
    if (v >= nv || scr[M8_KO_LVL + v] <= target_lvl) { break; }
    te = te - 1u;
    scr[M8_KO_VALS + lit] = 0u; scr[M8_KO_VALS + (lit ^ 1u)] = 0u;
    scr[M8_KO_LVL + v] = 0u; scr[M8_KO_RSN + v] = 0xFFFFFFFFu;
    scr[M8_KH_UNASS] = scr[M8_KH_UNASS] + 1u;
  }
  scr[M8_KH_TRL_END] = te; scr[M8_KH_LVL] = target_lvl;
  if (scr[M8_KH_PROP] > te) { scr[M8_KH_PROP] = te; }
}

u32 full_k6_prop_m8(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nv = scr[M8_KH_NV]; u32 nc = scr[M8_KH_NC]; u32 acap = scr[M8_KH_ACAP];
  if (nv > M8_K6_MV || nc > M8_K6_MC) { return 0xFFFFFFFFu; }
  u64 ticks = 0ULL;
  while (scr[M8_KH_PROP] < scr[M8_KH_TRL_END] && scr[M8_KH_PROP] < M8_K6_MV) {
    u32 lit = scr[M8_KO_TRL + scr[M8_KH_PROP]]; scr[M8_KH_PROP] = scr[M8_KH_PROP] + 1u;
    if (lit >= (nv << 1)) { continue; }
    u32 nl = lit ^ 1u; u64 visits = 0ULL; u32 prev = 0xFFFFFFFFu;
    u32 w = scr[M8_KO_WHEAD + nl]; u32 wsteps = 0u;
    while (w < (nc << 1) && wsteps < (M8_K6_MC << 1)) {
      wsteps = wsteps + 1u;
      u32 nxt = scr[M8_KO_WNEXT + w]; visits = visits + 1ULL;
      u32 wb = scr[M8_KO_WBLIT + w]; u32 bv = wb & K6_LIT_MASK;
      if (bv >= (nv << 1)) { prev = w; w = nxt; continue; }
      u32 bvv = scr[M8_KO_VALS + bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          scr[M8_KH_TICKS] = scr[M8_KH_TICKS] + (u32)(ticks + (visits >> 4) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign_m8(h, bv, cid); }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u; u32 off = scr[M8_KO_CL_OFF + cid];
      u32 sz = scr[M8_KO_CL_META + cid] & 0xFFFFu;
      if (sz < 2u || off + sz > acap) { prev = w; w = nxt; continue; }
      u32 other = scr[M8_KO_ARENA + off + (slot ^ 1u)];
      if (other >= (nv << 1)) { prev = w; w = nxt; continue; }
      ticks = ticks + 1ULL;
      if (scr[M8_KO_VALS + other] == 1u) {
        scr[M8_KO_WBLIT + w] = other; prev = w; w = nxt; continue;
      }
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = scr[M8_KO_ARENA + off + r];
        if (cand < (nv << 1) && scr[M8_KO_VALS + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        scr[M8_KO_ARENA + off + slot] = repl; scr[M8_KO_ARENA + off + ri] = nl;
        if (prev >= (nc << 1)) { scr[M8_KO_WHEAD + nl] = nxt; }
        else { scr[M8_KO_WNEXT + prev] = nxt; }
        scr[M8_KO_WBLIT + w] = other;
        scr[M8_KO_WNEXT + w] = scr[M8_KO_WHEAD + repl];
        scr[M8_KO_WHEAD + repl] = w;
        w = nxt; continue;
      }
      scr[M8_KO_WBLIT + w] = other; prev = w; w = nxt;
      u32 ov = scr[M8_KO_VALS + other];
      if (ov == 2u) {
        scr[M8_KH_TICKS] = scr[M8_KH_TICKS] + (u32)(ticks + (visits >> 4) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign_m8(h, other, cid); }
    }
    ticks = ticks + (visits >> 4) + 1ULL;
  }
  scr[M8_KH_TICKS] = scr[M8_KH_TICKS] + (u32)ticks;
  return 0xFFFFFFFFu;
}

void full_k6_ana_cl_m8(FullHdr *h, u32 cid, u32 skip_v) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nc = scr[M8_KH_NC]; u32 nv = scr[M8_KH_NV]; u32 acap = scr[M8_KH_ACAP];
  if (cid >= nc || nc > M8_K6_MC || nv > M8_K6_MV) { return; }
  u32 clvl = scr[M8_KH_LVL]; u32 off = scr[M8_KO_CL_OFF + cid];
  u32 sz = scr[M8_KO_CL_META + cid] & 0xFFFFu;
  if (off + sz > acap) { return; }
  if (scr[M8_KH_NRES] < M8_K6_MAX_ORIG) {
    scr[M8_KO_RES + scr[M8_KH_NRES]] = cid; scr[M8_KH_NRES] = scr[M8_KH_NRES] + 1u;
  } else { scr[M8_KH_NRES] = M8_K6_MAX_ORIG + 1u; }
  u32 i = 0u;
  while (i < sz) {
    u32 l = scr[M8_KO_ARENA + off + i]; u32 v = l >> 1;
    if (v < nv && v != skip_v && (scr[M8_KO_FLAGS + v] & 2u) == 0u) {
      scr[M8_KO_FLAGS + v] = scr[M8_KO_FLAGS + v] | 2u;
      if (scr[M8_KH_NANA] < M8_K6_MV) {
        scr[M8_KO_ANA + scr[M8_KH_NANA]] = v; scr[M8_KH_NANA] = scr[M8_KH_NANA] + 1u;
      }
      u32 vlvl = scr[M8_KO_LVL + v];
      if (vlvl == 0u) {
        u32 r0 = scr[M8_KO_RSN + v];
        if (r0 != 0xFFFFFFFFu) {
          if (scr[M8_KH_NRES] < M8_K6_MAX_ORIG) {
            scr[M8_KO_RES + scr[M8_KH_NRES]] = r0; scr[M8_KH_NRES] = scr[M8_KH_NRES] + 1u;
          } else { scr[M8_KH_NRES] = M8_K6_MAX_ORIG + 1u; }
        }
      } else if (vlvl == clvl) {
        scr[M8_KH_OPEN] = scr[M8_KH_OPEN] + 1u;
      } else if (scr[M8_KH_NKL] < M8_K6_MV) {
        scr[M8_KO_KL + scr[M8_KH_NKL]] = l; scr[M8_KH_NKL] = scr[M8_KH_NKL] + 1u;
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze_m8(FullHdr *h, u32 confl_cid) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nv = scr[M8_KH_NV]; if (nv > M8_K6_MV) { return false; }
  scr[M8_KH_NKL] = 1u; scr[M8_KH_NANA] = 0u; scr[M8_KH_NRES] = 0u; scr[M8_KH_OPEN] = 0u;
  full_k6_ana_cl_m8(h, confl_cid, 0xFFFFFFFFu);
  u32 clvl = scr[M8_KH_LVL]; u32 idx = scr[M8_KH_TRL_END];
  if (idx > M8_K6_MV) { idx = M8_K6_MV; }
  u32 uip = 0xFFFFFFFFu;
  while (scr[M8_KH_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = scr[M8_KO_TRL + idx]; u32 pv = p >> 1;
    if (pv < nv && (scr[M8_KO_FLAGS + pv] & 2u) != 0u && scr[M8_KO_LVL + pv] == clvl) {
      scr[M8_KH_OPEN] = scr[M8_KH_OPEN] - 1u;
      if (scr[M8_KH_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = scr[M8_KO_RSN + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_cl_m8(h, rsn, pv);
    }
  }
  u32 nana = scr[M8_KH_NANA]; if (nana > M8_K6_MV) { nana = M8_K6_MV; }
  u32 ai = 0u;
  while (ai < nana) {
    u32 av = scr[M8_KO_ANA + ai];
    if (av < nv) { scr[M8_KO_FLAGS + av] = scr[M8_KO_FLAGS + av] & (~2u); }
    ai = ai + 1u;
  }
  u32 nres = scr[M8_KH_NRES]; u32 nkl = scr[M8_KH_NKL];
  if (uip == 0xFFFFFFFFu || uip >= (nv << 1) ||
      nres > M8_K6_MAX_ORIG || nkl == 0u || nkl > M8_K6_MV) {
    return false;
  }
  scr[M8_KO_KL] = uip;
  u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 kv = scr[M8_KO_KL + i] >> 1;
    if (kv < nv) { u32 il = scr[M8_KO_LVL + kv]; if (il > jlvl) { jlvl = il; wi = i; } }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = scr[M8_KO_KL + 1u]; scr[M8_KO_KL + 1u] = scr[M8_KO_KL + wi]; scr[M8_KO_KL + wi] = t;
  }
  full_k6_backtrack_m8(h, jlvl);
  ai = 0u; while (ai < nana) { full_k6_mtf_m8(h, scr[M8_KO_ANA + ai]); ai = ai + 1u; }
  u32 nc = scr[M8_KH_NC]; u32 off = scr[M8_KH_ALEN];
  if (nc >= M8_K6_MC || off + nkl + nres > scr[M8_KH_ACAP]) { return false; }
  i = 0u; while (i < nkl) { scr[M8_KO_ARENA + off + i] = scr[M8_KO_KL + i]; i = i + 1u; }
  i = 0u; while (i < nres) { scr[M8_KO_ARENA + off + nkl + i] = scr[M8_KO_RES + i]; i = i + 1u; }
  scr[M8_KH_ALEN] = off + nkl + nres;
  scr[M8_KO_CL_OFF + nc] = off;
  scr[M8_KO_CL_META + nc] = nkl | KM_LRN; scr[M8_KO_CL_AUX + nc] = nres;
  scr[M8_KH_NC] = nc + 1u;
  if (nkl == 1u) { full_k6_assign_m8(h, uip, nc); return true; }
  full_k6_watch_m8(h, nc, scr[M8_KO_KL], scr[M8_KO_KL + 1u], nkl);
  full_k6_assign_m8(h, uip, nc);
  return true;
}

u64 full_k6_solve_m8(FullHdr *h, u32 tick_lim) {
  u32 *scr = (u32 *)h->scratch_buf;
  full_k6_backtrack_m8(h, 0u);
  if (scr[M8_KH_INCONS] != 0xFFFFFFFFu) { return 20ULL; }
  scr[M8_KH_TICK_LIM] = tick_lim; scr[M8_KH_TICKS] = 0u;
  u32 nv = scr[M8_KH_NV]; u32 nc = scr[M8_KH_NC];
  u32 acap = scr[M8_KH_ACAP]; u32 nunits = scr[M8_KH_NUNITS];
  if (nv > M8_K6_MV || nc > M8_K6_MC || nunits > M8_K6_MAX_ORIG) { return 0ULL; }
  u32 ui = 0u;
  while (ui < nunits) {
    u32 ucid = scr[M8_KO_UNITS + ui];
    if (ucid < nc) {
      u32 off = scr[M8_KO_CL_OFF + ucid];
      if (off < acap) {
        u32 ul = scr[M8_KO_ARENA + off];
        if (ul < (nv << 1)) {
          u32 uv = scr[M8_KO_VALS + ul];
          if (uv == 2u) { scr[M8_KH_INCONS] = ucid; return 20ULL; }
          if (uv == 0u) { full_k6_assign_m8(h, ul, ucid); }
        }
      }
    }
    ui = ui + 1u;
  }
  u32 confl = full_k6_prop_m8(h);
  if (confl != 0xFFFFFFFFu) { scr[M8_KH_INCONS] = confl; return 20ULL; }
  while (scr[M8_KH_TICKS] < scr[M8_KH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (scr[M8_KH_LVL] == 0u) { scr[M8_KH_INCONS] = confl; return 20ULL; }
      if (!full_k6_analyze_m8(h, confl)) { return 0ULL; }
      confl = full_k6_prop_m8(h);
      continue;
    }
    if (scr[M8_KH_UNASS] == 0u) { return 10ULL; }
    u32 cur = scr[M8_KH_QSEARCH]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (scr[M8_KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
      cur = scr[M8_KO_QPREV + cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = scr[M8_KH_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (scr[M8_KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = scr[M8_KO_QPREV + cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (scr[M8_KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    scr[M8_KH_QSEARCH] = pick;
    u32 ph = (scr[M8_KO_FLAGS + pick] ^ scr[M8_KH_PHASE]) & 1u;
    scr[M8_KH_LVL] = scr[M8_KH_LVL] + 1u;
    full_k6_assign_m8(h, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_prop_m8(h);
  }
  return 0ULL;
}

void full_k6_core_m8(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 nc = scr[M8_KH_NC]; u32 nv = scr[M8_KH_NV]; u32 acap = scr[M8_KH_ACAP];
  if (nc > M8_K6_MC || nv > M8_K6_MV) { return; }
  u32 i = 0u;
  while (i < nc) { scr[M8_KO_CL_META + i] = scr[M8_KO_CL_META + i] & (~KM_CORE); i = i + 1u; }
  u32 inc = scr[M8_KH_INCONS];
  if (inc < nc) {
    i = 0u; while (i < nv) { scr[M8_KO_FLAGS + i] = scr[M8_KO_FLAGS + i] & (~2u); i = i + 1u; }
    scr[M8_KO_CL_META + inc] = scr[M8_KO_CL_META + inc] | KM_CORE;
    u32 off = scr[M8_KO_CL_OFF + inc]; u32 sz = scr[M8_KO_CL_META + inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 j = 0u;
      while (j < sz) {
        u32 lv = scr[M8_KO_ARENA + off + j] >> 1;
        if (lv < nv) { scr[M8_KO_FLAGS + lv] = scr[M8_KO_FLAGS + lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = scr[M8_KH_TRL_END]; if (ti > M8_K6_MV) { ti = M8_K6_MV; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = scr[M8_KO_TRL + ti] >> 1;
      if (v >= nv || (scr[M8_KO_FLAGS + v] & 2u) == 0u) { continue; }
      scr[M8_KO_FLAGS + v] = scr[M8_KO_FLAGS + v] & (~2u);
      u32 rsn = scr[M8_KO_RSN + v];
      if (rsn >= nc) { continue; }
      scr[M8_KO_CL_META + rsn] = scr[M8_KO_CL_META + rsn] | KM_CORE;
      u32 roff = scr[M8_KO_CL_OFF + rsn]; u32 rsz = scr[M8_KO_CL_META + rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = scr[M8_KO_ARENA + roff + j] >> 1;
          if (lv < nv && lv != v) { scr[M8_KO_FLAGS + lv] = scr[M8_KO_FLAGS + lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u; while (i < nv) { scr[M8_KO_FLAGS + i] = scr[M8_KO_FLAGS + i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u; bool changed = true;
  while (changed && pass < nc) {
    changed = false; pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = scr[M8_KO_CL_META + cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = scr[M8_KO_CL_OFF + cid]; u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = scr[M8_KO_CL_AUX + cid];
          if (off + sz + na <= acap) {
            u32 j = 0u;
            while (j < na) {
              u32 ant = scr[M8_KO_ARENA + off + sz + j];
              if (ant < nc && (scr[M8_KO_CL_META + ant] & KM_CORE) == 0u) {
                scr[M8_KO_CL_META + ant] = scr[M8_KO_CL_META + ant] | KM_CORE; changed = true;
              }
              j = j + 1u;
            }
          }
        } else if (off + sz <= acap) {
          u32 j = 0u;
          while (j < sz) {
            u32 lv = scr[M8_KO_ARENA + off + j] >> 1;
            if (lv < nv && scr[M8_KO_LVL + lv] == 0u) {
              u32 r0 = scr[M8_KO_RSN + lv];
              if (r0 < nc && (scr[M8_KO_CL_META + r0] & KM_CORE) == 0u) {
                scr[M8_KO_CL_META + r0] = scr[M8_KO_CL_META + r0] | KM_CORE; changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
}

bool full_k6_extract_and_solve_m8(
    FullHdr *h, u32 v, u32 np, u32 nn, bool second_pass, u32 tick_lim) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 acap = (u32)(h->scratch_cap - (u64)M8_KO_ARENA);
  u32 max_csz = (h->max_vars < 100ULL) ? (u32)h->max_vars : 100u;
  u32 nv = 0u; u32 nc = 0u; u32 alen = 0u; u32 nunits = 0u;
  u32 trivial_eid = 0xFFFFFFFFu; bool abort_def = false;
  u32 pl = v << 1; u32 nl = pl | 1u;
  u32 s_step = 0u;
  while (s_step < 2u && !abort_def && trivial_eid == 0xFFFFFFFFu) {
    u32 side = second_pass ? (1u - s_step) : s_step;
    u32 cnt = (side == 0u) ? np : nn;
    u32 off_s = (side == 0u) ? 0u : M8_NEG_OFF;
    u32 mb = (side == 0u) ? M8_POS_MASK : M8_NEG_MASK;
    u32 except = (side == 0u) ? pl : nl;
    u32 step = 0u;
    while (step < cnt && !abort_def) {
      u32 idx = second_pass ? (cnt - 1u - step) : step;
      step = step + 1u;
      if (second_pass && ((scr[mb + (idx >> 5)] >> (idx & 31u)) & 1u) == 0u) { continue; }
      u32 w = scr[off_s + idx];
      u32 eid = (side << 11) | idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { trivial_eid = eid; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= M8_K6_MV || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
          if (nc >= M8_K6_MAX_ORIG || alen + 1u > acap) { abort_def = true; break; }
          scr[M8_KO_ARENA + alen] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          scr[M8_KO_CL_OFF + nc] = alen; scr[M8_KO_CL_META + nc] = 1u; scr[M8_KO_CL_AUX + nc] = eid;
          scr[M8_KO_UNITS + nunits] = nc; nunits = nunits + 1u; nc = nc + 1u; alen = alen + 1u;
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= M8_K6_MV || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              if (csz >= max_csz) { abort_def = true; break; }
              tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u); csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_eid = eid; break; }
          if (nc >= M8_K6_MAX_ORIG || alen + csz > acap) { abort_def = true; break; }
          m = 0u; while (m < csz) { scr[M8_KO_ARENA + alen + m] = tmp[m]; m = m + 1u; }
          scr[M8_KO_CL_OFF + nc] = alen; scr[M8_KO_CL_META + nc] = csz;
          scr[M8_KO_CL_AUX + nc] = eid;
          if (csz == 1u) { scr[M8_KO_UNITS + nunits] = nc; nunits = nunits + 1u; }
          nc = nc + 1u; alen = alen + csz;
        }
      }
    }
    s_step = s_step + 1u;
  }
  u32 ci = 0u;
  while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_eid != 0xFFFFFFFFu) {
    u32 idx = trivial_eid & 0x7FFu;
    u32 mbase = ((trivial_eid >> 11) == 0u) ? M8_POS_MASK : M8_NEG_MASK;
    u32 z = 0u; while (z < 128u) { scr[M8_POS_MASK + z] = 0u; z = z + 1u; }
    scr[mbase + (idx >> 5)] = 1u << (idx & 31u);
    scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 1u;
    return true;
  }
  if (abort_def || nv == 0u || nc < 2u) { return false; }
  scr[M8_KH_NV] = nv; scr[M8_KH_NC] = nc; scr[M8_KH_ORIG_NC] = nc;
  scr[M8_KH_LVL] = 0u; scr[M8_KH_PROP] = 0u; scr[M8_KH_TRL_END] = 0u; scr[M8_KH_UNASS] = nv;
  scr[M8_KH_INCONS] = 0xFFFFFFFFu;
  scr[M8_KH_QFIRST] = 0u; scr[M8_KH_QLAST] = nv - 1u;
  scr[M8_KH_QSEARCH] = nv - 1u; scr[M8_KH_QSTAMP] = nv;
  scr[M8_KH_TICKS] = 0u; scr[M8_KH_TICK_LIM] = tick_lim;
  scr[M8_KH_ALEN] = alen; scr[M8_KH_ACAP] = acap;
  scr[M8_KH_NANA] = 0u; scr[M8_KH_NKL] = 0u; scr[M8_KH_NRES] = 0u; scr[M8_KH_NUNITS] = nunits;
  scr[M8_KH_OPEN] = 0u; scr[M8_KH_PHASE] = 0u;
  u32 i = 0u;
  while (i < nv) {
    scr[M8_KO_LVL + i] = 0u; scr[M8_KO_RSN + i] = 0xFFFFFFFFu; scr[M8_KO_FLAGS + i] = 0u;
    scr[M8_KO_QST + i] = i + 1u;
    scr[M8_KO_QPREV + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    scr[M8_KO_QNEXT + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  i = 0u;
  while (i < (nv << 1)) {
    scr[M8_KO_VALS + i] = 0u; scr[M8_KO_WHEAD + i] = 0xFFFFFFFFu; i = i + 1u;
  }
  i = 0u;
  while (i < nc) {
    u32 sz = scr[M8_KO_CL_META + i] & 0xFFFFu;
    if (sz >= 2u) {
      u32 off = scr[M8_KO_CL_OFF + i];
      full_k6_watch_m8(h, i, scr[M8_KO_ARENA + off], scr[M8_KO_ARENA + off + 1u], sz);
    }
    i = i + 1u;
  }
  if (full_k6_solve_m8(h, tick_lim) != 20ULL) { return false; }
  full_k6_core_m8(h);
  u32 z = 0u; while (z < 128u) { scr[M8_POS_MASK + z] = 0u; z = z + 1u; }
  bool any = false; u32 onc = scr[M8_KH_ORIG_NC]; i = 0u;
  while (i < onc) {
    if ((scr[M8_KO_CL_META + i] & KM_CORE) != 0u) {
      u32 eid = scr[M8_KO_CL_AUX + i];
      u32 idx = eid & 0x7FFu;
      u32 mbase = ((eid >> 11) == 0u) ? M8_POS_MASK : M8_NEG_MASK;
      u32 widx = mbase + (idx >> 5);
      scr[widx] = scr[widx] | (1u << (idx & 31u));
      any = true;
    }
    i = i + 1u;
  }
  if (any) { scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 1u; }
  return any;
}

void full_bve_def_k6_m8(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 16384ULL || np == 0u || nn == 0u ||
      np + nn < 3u || np + nn > M8_K6_MAX_ORIG) {
    return;
  }
  if (!full_k6_extract_and_solve_m8(h, v, np, nn, false, M8_K6_TICK_LIM)) { return; }
  full_k6_extract_and_solve_m8(h, v, np, nn, true, M8_K6_TICK_LIM * 10u);
}

void full_bve_gates_m8(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 130u) { scr[M8_POS_MASK + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m8(h, np, nn)) { return; }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (full_bve_find_and_m8(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m8(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m8(h, v, np, nn)) { return; }
  if (full_bve_find_xor_m8(h, v, np, nn)) { return; }
  full_bve_def_k6_m8(h, v, np, nn);
}

void full_bve_bce_side_m8(FullHdr *h, u32 lit, u32 off, u32 cnt, u32 opp_off, u32 opp_n) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if (full_bve_try_bce(h, lit, w, opp_off, opp_n)) {
      if ((w & PW_BIN_FLAG) != 0u) {
        if (full_extend_push2(h, lit, w & PW_LIT_MASK)) {
          full_delete_binary(h, lit, w & PW_LIT_MASK);
          h->bce_cnt = h->bce_cnt + 1ULL;
        }
      } else if (full_extend_push_cl(h, lit, w)) {
        ar[w] = ar[w] | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
        h->bce_cnt = h->bce_cnt + 1ULL;
      }
    }
    i = i + 1u;
  }
}

u64 full_bve_var_m7(FullHdr *h, u32 v) {
  if (h->scratch_cap < 2048ULL) { return 1ULL; }
  bool use_m8 = (h->scratch_cap >= 16384ULL);
  u32 occ_lim = use_m8 ? M8_OCC_LIM : 512u;
  u32 neg_off = use_m8 ? M8_NEG_OFF : 512u;
  u32 pos_mask = use_m8 ? M8_POS_MASK : 1024u;
  u32 neg_mask = use_m8 ? M8_NEG_MASK : 1040u;
  u32 gf_idx = use_m8 ? M8_GF_IDX : 1056u;
  u32 rg_idx = use_m8 ? M8_RG_IDX : 1057u;
  u64 r_off = use_m8 ? (u64)M8_RES_OFF : 1088ULL;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m7(h, pl, scr, occ_lim);
  u32 nn = full_bve_collect_m7(h, nl, scr + neg_off, occ_lim);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  u64 ext_need = full_bve_ext_need(h, 0u, np) + full_bve_ext_need(h, neg_off, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, neg_off, nn))) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    return 1ULL;
  }
  u64 rp = r_off;
  u64 r_cnt = 0ULL;
  u64 w_est = 0ULL;
  u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    if (use_m8) { full_bve_gates_m8(h, v, np, nn); }
    else { full_bve_gates_m7(h, v, np, nn); }
    bool gf = (scr[gf_idx] != 0u);
    bool rg = (scr[rg_idx] != 0u);
    u32 *wvec = (u32 *)h->watch_vec;
    u32 i = 0u;
    while (i < np && fit) {
      bool pi = ((scr[pos_mask + (i >> 5)] >> (i & 31u)) & 1u) != 0u;
      u32 j = 0u;
      while (j < nn && fit) {
        bool nj = ((scr[neg_mask + (j >> 5)] >> (j & 31u)) & 1u) != 0u;
        bool need_pair = !gf || (rg ? (pi || nj) : (pi != nj));
        if (need_pair && full_bve_resolve_pair(h, v, scr[i], scr[neg_off + j])) {
          u64 rlen = h->tmp_len;
          r_cnt = r_cnt + 1ULL;
          if (rlen > 100ULL || r_cnt > lim_cls || rp + 1ULL + rlen > h->scratch_cap) {
            fit = false;
            break;
          }
          scr[rp] = (u32)rlen;
          u32 *tmp = (u32 *)h->tmp_lits;
          u32 k = 0u;
          while ((u64)k < rlen) {
            u32 lk = tmp[k];
            scr[rp + 1ULL + (u64)k] = lk;
            if (rlen >= 2ULL && (u64)lk < (h->cur_vars << 1)) {
              w_est = w_est + (((u64)wvec[((u64)lk << 1) + 1ULL]) << 1) + 4ULL;
            }
            k = k + 1u;
          }
          rp = rp + 1ULL + rlen;
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
  }
  if (fit) {
    u64 ar_need = (rp - r_off) + (r_cnt * 2ULL) + 16ULL;
    u64 w_need = w_est + (r_cnt * 4ULL) + 16ULL;
    if (ar_need > h->arena_cap - h->arena_len) {
      fit = false;
    } else if (w_need > h->wcap - h->wlen) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (w_need > h->wcap - h->wlen) { fit = false; }
    }
  }
  if (fit) {
    if (!full_bve_weaken(h, pl, 0u, np) || !full_bve_weaken(h, nl, neg_off, nn)) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    u64 cr = full_bve_commit_res(h, r_off, rp);
    if (cr == 20ULL) { return 20ULL; }
    if (cr == 1ULL && !full_dense_flush_units_m7(h)) { return 20ULL; }
    return cr;
  }
  full_bve_bce_side_m8(h, pl, 0u, np, neg_off, nn);
  full_bve_bce_side_m8(h, nl, neg_off, nn, 0u, np);
  return 1ULL;
}

u64 full_bve_var(FullHdr *h, u32 v) {
  return full_bve_var_m7(h, v);
}

u64 full_bve_var_key_m7(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u64 pos = (u64)wvec[((u64)v << 2) + 1ULL];
  u64 neg = (u64)wvec[((u64)v << 2) + 3ULL];
  if (pos > 2000ULL) { pos = 2000ULL; }
  if (neg > 2000ULL) { neg = 2000ULL; }
  u64 base = (4004000ULL + pos + neg) - (pos * neg);
  u64 rel = 0ULL;
  if (h->stable != 0ULL) {
    u64 *sc = (u64 *)h->score;
    rel = sc[v] >> 32;
  } else {
    u32 *qs = (u32 *)h->q_stamp;
    rel = (u64)qs[v];
  }
  return (base << 32) | (0xFFFFFFFFULL - (rel & 0xFFFFFFFFULL));
}

/* === Rank #4: probe scheduling, probings count, 10M dticks, strict > === */

u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial) {
  if (initial) { return 10000000ULL; }
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 raw = (h->search_ticks > last_p) ? (h->search_ticks - last_p) : 0ULL;
  return (raw > 10000000ULL) ? raw : 10000000ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  h->probings = h->probings + 1ULL;
  if (!initial) {
    u64 parg = (h->probings > (~0ULL) - 9ULL) ? (~0ULL) : (h->probings + 9ULL);
    u64 qlog = full_log10_q16_m7(parg);
    u64 pc = (h->probings > 100000000ULL) ? 100000000ULL : h->probings;
    u64 nlogp = (100ULL * pc * qlog) >> 16;
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
  }
  u64 max_r = initial ? 1ULL : 2ULL;
  u64 round = 0ULL;
  while (round < max_r) {
    if (!initial && full_vivify_m6_hdr(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    u64 before_unass = h->unassigned;
    if (full_enter_dense(h)) {
      u64 dense_ok = 1ULL;
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        if (ca > cb) {
          if (full_rebuild_watches(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (!full_enter_dense(h)) {
            if (h->inconsistent != 0ULL) {
              m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
              return 20ULL;
            }
            dense_ok = 0ULL;
          }
        }
      }
      if (dense_ok != 0ULL) {
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
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  }
  u64 fr = 1ULL;
  u64 fp = 10ULL;
  u64 fa = h->unassigned / 10ULL;
  while (fa >= fp && fr < 19ULL) {
    fr = fr + 1ULL;
    fp = fp * 10ULL;
  }
  u64 fe5 = (h->eliminations > (~0ULL) - 5ULL) ? (~0ULL) : (h->eliminations + 5ULL);
  if (fr <= fe5 && full_enter_dense(h)) {
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

u64 full_search_m6(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  u64 reordered = 0ULL;
  u64 last_reduce_cfl = 0xFFFFFFFFFFFFFFFFULL;
  u64 lkr = full_lucky_late_m7(h);
  if (lkr == 10ULL || lkr == 20ULL) { return lkr; }
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
    } else if (h->unassigned == 0ULL) {
      return 10ULL;
    } else if (h->fuel == 0ULL) {
      return 0ULL;
    } else if (h->conflicts >= h->reduce_limit) {
      last_reduce_cfl = h->conflicts;
      h->fuel = h->fuel - 1ULL;
      u64 rr = full_reduce_m6(h, false);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
    } else if ((h->stable == 0ULL) ? (h->conflicts >= h->mode_confl_lim)
                                   : (h->search_ticks >= h->mode_tick_lim)) {
      h->fuel = h->fuel - 1ULL;
      full_switch_mode_m7(h);
    } else if (full_restart_due(h) != 0ULL) {
      h->fuel = h->fuel - 1ULL;
      full_restart(h);
    } else if (h->cur_level == 0ULL && h->conflicts >= reorder_limit) {
      reordered = reordered + 1ULL;
      reorder_limit = h->conflicts + 10000ULL * reordered;
      h->fuel = h->fuel - 1ULL;
      full_reorder_m6(h, 256ULL);
    } else if (h->stable != 0ULL && h->conflicts >= h->rephase_limit) {
      h->fuel = h->fuel - 1ULL;
      full_rephase(h);
    } else if (h->conflicts != last_reduce_cfl && h->conflicts > h->probe_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, true, false);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else if (h->conflicts != last_reduce_cfl && h->conflicts >= h->elim_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, false, true);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else {
      if (m6_hdr_decide_fid(h) == 0ULL) {
        return (h->unassigned == 0ULL) ? 10ULL : 0ULL;
      }
    }
  }
}
"

/-! ## 1. `Fn` Handles, Patch Definitions & Structural Splicing -/

def m8MinLitDfsFn : Fn :=
  ⟨"full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool], full_min_lit_dfs_m8_body⟩
def m8ShrinkLowerFn : Fn :=
  ⟨"full_shrink_lower_m8", [i64, i32, i32], [.bool], full_shrink_lower_m8_body⟩
def m8ShrinkBlkBoolFn : Fn :=
  ⟨"full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool], full_shrink_blk_bool_m8_body⟩
def m8MinShrinkM6Fn : Fn :=
  ⟨"full_min_shrink_m6", [i64], [], full_min_shrink_m6_body⟩

def m8BveFindEquivFn : Fn :=
  ⟨"full_bve_find_equiv_m8", [i64, i32, i32], [.bool], full_bve_find_equiv_m8_body⟩
def m8BveFindAndFn : Fn :=
  ⟨"full_bve_find_and_m8", [i64, i32, i32, i32], [.bool], full_bve_find_and_m8_body⟩
def m8BveMatchTernFn : Fn :=
  ⟨"full_bve_match_tern_m8", [i64, i32, i32, i32, i32, i32], [i32], full_bve_match_tern_m8_body⟩
def m8BveFindIteSideFn : Fn :=
  ⟨"full_bve_find_ite_side_m8", [i64, i32, i32, i32, .bool], [.bool],
    full_bve_find_ite_side_m8_body⟩
def m8BveFindIteFn : Fn :=
  ⟨"full_bve_find_ite_m8", [i64, i32, i32, i32], [.bool], full_bve_find_ite_m8_body⟩
def m8BveFindXorFn : Fn :=
  ⟨"full_bve_find_xor_m8", [i64, i32, i32, i32], [.bool], full_bve_find_xor_m8_body⟩
def m8K6WatchFn : Fn :=
  ⟨"full_k6_watch_m8", [i64, i32, i32, i32, i32], [], full_k6_watch_m8_body⟩
def m8K6AssignFn : Fn :=
  ⟨"full_k6_assign_m8", [i64, i32, i32], [], full_k6_assign_m8_body⟩
def m8K6MtfFn : Fn :=
  ⟨"full_k6_mtf_m8", [i64, i32], [], full_k6_mtf_m8_body⟩
def m8K6BacktrackFn : Fn :=
  ⟨"full_k6_backtrack_m8", [i64, i32], [], full_k6_backtrack_m8_body⟩
def m8K6PropFn : Fn :=
  ⟨"full_k6_prop_m8", [i64], [i32], full_k6_prop_m8_body⟩
def m8K6AnaClFn : Fn :=
  ⟨"full_k6_ana_cl_m8", [i64, i32, i32], [], full_k6_ana_cl_m8_body⟩
def m8K6AnalyzeFn : Fn :=
  ⟨"full_k6_analyze_m8", [i64, i32], [.bool], full_k6_analyze_m8_body⟩
def m8K6SolveFn : Fn :=
  ⟨"full_k6_solve_m8", [i64, i32], [i64], full_k6_solve_m8_body⟩
def m8K6CoreFn : Fn :=
  ⟨"full_k6_core_m8", [i64], [], full_k6_core_m8_body⟩
def m8K6ExtractSolveFn : Fn :=
  ⟨"full_k6_extract_and_solve_m8", [i64, i32, i32, i32, .bool, i32], [.bool],
    full_k6_extract_and_solve_m8_body⟩
def m8BveDefK6Fn : Fn :=
  ⟨"full_bve_def_k6_m8", [i64, i32, i32, i32], [], full_bve_def_k6_m8_body⟩
def m8BveGatesFn : Fn :=
  ⟨"full_bve_gates_m8", [i64, i32, i32, i32], [], full_bve_gates_m8_body⟩
def m8BveBceSideFn : Fn :=
  ⟨"full_bve_bce_side_m8", [i64, i32, i32, i32, i32, i32], [], full_bve_bce_side_m8_body⟩
def m8BveVarM7Fn : Fn :=
  ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩
def m8BveVarFn : Fn :=
  ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_body⟩
def m8BveVarKeyM7Fn : Fn :=
  ⟨"full_bve_var_key_m7", [i64, i32], [i64], full_bve_var_key_m7_body⟩

def m8ProbeDticksM6HdrFn : Fn :=
  ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], full_probe_dticks_m6_hdr_body⟩
def m8ProbeM6Fn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩
def m8SearchM6Fn : Fn :=
  ⟨"full_search_m6", [i64], [i64], full_search_m6_body⟩

def m8MinHelpers : List Fn :=
  [ m8MinLitDfsFn, m8ShrinkLowerFn, m8ShrinkBlkBoolFn ]

def m8BveHelpers : List Fn :=
  [ m8BveFindEquivFn, m8BveFindAndFn, m8BveMatchTernFn, m8BveFindIteSideFn
  , m8BveFindIteFn, m8BveFindXorFn, m8K6WatchFn, m8K6AssignFn, m8K6MtfFn
  , m8K6BacktrackFn, m8K6PropFn, m8K6AnaClFn, m8K6AnalyzeFn, m8K6SolveFn
  , m8K6CoreFn, m8K6ExtractSolveFn, m8BveDefK6Fn, m8BveGatesFn, m8BveBceSideFn ]

def m8CoreParityBefores : List (Sym × List Fn) :=
  [ ("full_min_shrink_m6", m8MinHelpers)
  , ("full_bve_var_m7", m8BveHelpers) ]

def m8CoreParityRepls : List Fn :=
  [ m8MinShrinkM6Fn, m8BveVarM7Fn, m8BveVarFn, m8BveVarKeyM7Fn
  , m8ProbeDticksM6HdrFn, m8ProbeM6Fn, m8SearchM6Fn ]

def m8CoreParityFns : List Fn :=
  mfPatchFns m8CoreParityRepls m8CoreParityBefores m7FidelityFns

def m8CoreParityModule : LeanQbe.T.Module :=
  { m7FidelityModule with fns := m8CoreParityFns }

/-! ## 2. Function Well-Formedness (`Func.Wf`), Length, Nodup & Acyclicity -/

theorem full_min_lit_dfs_m8_wf : Func.Wf full_min_lit_dfs_m8_body := by t_wf_reify
theorem full_shrink_lower_m8_wf : Func.Wf full_shrink_lower_m8_body := by t_wf_reify
theorem full_shrink_blk_bool_m8_wf : Func.Wf full_shrink_blk_bool_m8_body := by t_wf_reify
theorem full_min_shrink_m6_m8_wf : Func.Wf full_min_shrink_m6_body := by t_wf_reify
theorem full_bve_find_equiv_m8_wf : Func.Wf full_bve_find_equiv_m8_body := by t_wf_reify
theorem full_bve_find_and_m8_wf : Func.Wf full_bve_find_and_m8_body := by t_wf_reify
theorem full_bve_match_tern_m8_wf : Func.Wf full_bve_match_tern_m8_body := by t_wf_reify
theorem full_bve_find_ite_side_m8_wf : Func.Wf full_bve_find_ite_side_m8_body := by t_wf_reify
theorem full_bve_find_ite_m8_wf : Func.Wf full_bve_find_ite_m8_body := by t_wf_reify
theorem full_bve_find_xor_m8_wf : Func.Wf full_bve_find_xor_m8_body := by t_wf_reify
theorem full_k6_watch_m8_wf : Func.Wf full_k6_watch_m8_body := by t_wf_reify
theorem full_k6_assign_m8_wf : Func.Wf full_k6_assign_m8_body := by t_wf_reify
theorem full_k6_mtf_m8_wf : Func.Wf full_k6_mtf_m8_body := by t_wf_reify
theorem full_k6_backtrack_m8_wf : Func.Wf full_k6_backtrack_m8_body := by t_wf_reify
theorem full_k6_prop_m8_wf : Func.Wf full_k6_prop_m8_body := by t_wf_reify
theorem full_k6_ana_cl_m8_wf : Func.Wf full_k6_ana_cl_m8_body := by t_wf_reify
theorem full_k6_analyze_m8_wf : Func.Wf full_k6_analyze_m8_body := by t_wf_reify
theorem full_k6_solve_m8_wf : Func.Wf full_k6_solve_m8_body := by t_wf_reify
theorem full_k6_core_m8_wf : Func.Wf full_k6_core_m8_body := by t_wf_reify
theorem full_k6_extract_and_solve_m8_wf : Func.Wf full_k6_extract_and_solve_m8_body := by t_wf_reify
theorem full_bve_def_k6_m8_wf : Func.Wf full_bve_def_k6_m8_body := by t_wf_reify
theorem full_bve_gates_m8_wf : Func.Wf full_bve_gates_m8_body := by t_wf_reify
theorem full_bve_bce_side_m8_wf : Func.Wf full_bve_bce_side_m8_body := by t_wf_reify
theorem full_bve_var_m7_m8_wf : Func.Wf full_bve_var_m7_body := by t_wf_reify
theorem full_bve_var_m8_wf : Func.Wf full_bve_var_body := by t_wf_reify
theorem full_bve_var_key_m7_m8_wf : Func.Wf full_bve_var_key_m7_body := by t_wf_reify
theorem full_probe_dticks_m6_hdr_m8_wf : Func.Wf full_probe_dticks_m6_hdr_body := by t_wf_reify
theorem full_probe_m6_m8_wf : Func.Wf full_probe_m6_body := by t_wf_reify
theorem full_search_m6_m8_wf : Func.Wf full_search_m6_body := by t_wf_reify

theorem m8CoreParityRepls_wf : ∀ r ∈ m8CoreParityRepls, r.Wf := by
  intro r hr
  simp only [m8CoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_min_shrink_m6_m8_wf
  · exact full_bve_var_m7_m8_wf
  · exact full_bve_var_m8_wf
  · exact full_bve_var_key_m7_m8_wf
  · exact full_probe_dticks_m6_hdr_m8_wf
  · exact full_probe_m6_m8_wf
  · exact full_search_m6_m8_wf

theorem m8CoreParityBefores_wf : ∀ p ∈ m8CoreParityBefores, ∀ h ∈ p.2, h.Wf := by
  intro p hp h hh
  simp only [m8CoreParityBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [m8MinHelpers, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact full_min_lit_dfs_m8_wf
    · exact full_shrink_lower_m8_wf
    · exact full_shrink_blk_bool_m8_wf
  · simp only [m8BveHelpers, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact full_bve_find_equiv_m8_wf
    · exact full_bve_find_and_m8_wf
    · exact full_bve_match_tern_m8_wf
    · exact full_bve_find_ite_side_m8_wf
    · exact full_bve_find_ite_m8_wf
    · exact full_bve_find_xor_m8_wf
    · exact full_k6_watch_m8_wf
    · exact full_k6_assign_m8_wf
    · exact full_k6_mtf_m8_wf
    · exact full_k6_backtrack_m8_wf
    · exact full_k6_prop_m8_wf
    · exact full_k6_ana_cl_m8_wf
    · exact full_k6_analyze_m8_wf
    · exact full_k6_solve_m8_wf
    · exact full_k6_core_m8_wf
    · exact full_k6_extract_and_solve_m8_wf
    · exact full_bve_def_k6_m8_wf
    · exact full_bve_gates_m8_wf
    · exact full_bve_bce_side_m8_wf

theorem m8CoreParityFns_wf : ∀ f ∈ m8CoreParityFns, f.Wf :=
  mfPatchFns_wf m7FidelityFns_wf m8CoreParityRepls_wf m8CoreParityBefores_wf

theorem m8CoreParity_noExit : m8CoreParityModule.exits = [] := rfl

private theorem fid_idx_17 : m7FidelityFns[17]?.map Fn.sig =
    some ("full_wstack_defrag", [i64], []) := by t_kernel_rfl
private theorem fid_idx_31 : m7FidelityFns[31]?.map Fn.sig =
    some ("full_log10_q16_m7", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_32 : m7FidelityFns[32]?.map Fn.sig =
    some ("full_scale_delta_m5", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_66 : m7FidelityFns[66]?.map Fn.sig =
    some ("m6_hdr_delaying", [i64, i64], [.bool]) := by t_kernel_rfl
private theorem fid_idx_67 : m7FidelityFns[67]?.map Fn.sig =
    some ("m6_hdr_bump_delay", [i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_68 : m7FidelityFns[68]?.map Fn.sig =
    some ("m6_hdr_reduce_delay", [i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_70 : m7FidelityFns[70]?.map Fn.sig =
    some ("m6_hdr_get_watermark", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_71 : m7FidelityFns[71]?.map Fn.sig =
    some ("m6_hdr_set_watermark", [i64, i64, i64], []) := by t_kernel_rfl
private theorem fid_idx_86 : m7FidelityFns[86]?.map Fn.sig =
    some ("full_propagate", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_111 : m7FidelityFns[111]?.map Fn.sig =
    some ("full_reduce_m6", [i64, .bool], [i64]) := by t_kernel_rfl
private theorem fid_idx_124 : m7FidelityFns[124]?.map Fn.sig =
    some ("full_min_mark", [i64, i32, i8], []) := by t_kernel_rfl
private theorem fid_idx_129 : m7FidelityFns[129]?.map Fn.sig =
    some ("full_sort_tmp", [i64], []) := by t_kernel_rfl
private theorem fid_idx_135 : m7FidelityFns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := by t_kernel_rfl
private theorem fid_idx_151 : m7FidelityFns[151]?.map Fn.sig =
    some ("full_analyze_m6_hdr", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_169 : m7FidelityFns[169]?.map Fn.sig =
    some ("full_rephase", [i64], []) := by t_kernel_rfl
private theorem fid_idx_170 : m7FidelityFns[170]?.map Fn.sig =
    some ("full_restart_due", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_171 : m7FidelityFns[171]?.map Fn.sig =
    some ("full_restart", [i64], []) := by t_kernel_rfl
private theorem fid_idx_172 : m7FidelityFns[172]?.map Fn.sig =
    some ("full_extend_push2", [i64, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_173 : m7FidelityFns[173]?.map Fn.sig =
    some ("full_extend_push_cl", [i64, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_179 : m7FidelityFns[179]?.map Fn.sig =
    some ("full_delete_binary", [i64, i32, i32], []) := by t_kernel_rfl
private theorem fid_idx_180 : m7FidelityFns[180]?.map Fn.sig =
    some ("full_set_inactive", [i64, i32, i32], []) := by t_kernel_rfl
private theorem fid_idx_218 : m7FidelityFns[218]?.map Fn.sig =
    some ("full_vivify_m6_hdr", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_226 : m7FidelityFns[226]?.map Fn.sig =
    some ("full_backbone_m6", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_235 : m7FidelityFns[235]?.map Fn.sig =
    some ("full_substitute", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_236 : m7FidelityFns[236]?.map Fn.sig =
    some ("full_enter_dense", [i64], [.bool]) := by t_kernel_rfl
private theorem fid_idx_237 : m7FidelityFns[237]?.map Fn.sig =
    some ("full_rebuild_watches", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_275 : m7FidelityFns[275]?.map Fn.sig =
    some ("full_congruence_dense", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_299 : m7FidelityFns[299]?.map Fn.sig =
    some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_302 : m7FidelityFns[302]?.map Fn.sig =
    some ("full_dense_flush_units_m7", [i64], [.bool]) := by t_kernel_rfl
private theorem fid_idx_310 : m7FidelityFns[310]?.map Fn.sig =
    some ("full_bve_collect_m7", [i64, i32, i64, i32], [i32]) := by t_kernel_rfl
private theorem fid_idx_316 : m7FidelityFns[316]?.map Fn.sig =
    some ("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_320 : m7FidelityFns[320]?.map Fn.sig =
    some ("full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32]) := by t_kernel_rfl
private theorem fid_idx_332 : m7FidelityFns[332]?.map Fn.sig =
    some ("full_bve_gates_m7", [i64, i32, i32, i32], []) := by t_kernel_rfl
private theorem fid_idx_333 : m7FidelityFns[333]?.map Fn.sig =
    some ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_334 : m7FidelityFns[334]?.map Fn.sig =
    some ("full_bve_weaken", [i64, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_335 : m7FidelityFns[335]?.map Fn.sig =
    some ("full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool]) := by t_kernel_rfl
private theorem fid_idx_336 : m7FidelityFns[336]?.map Fn.sig =
    some ("full_bve_commit_res", [i64, i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_337 : m7FidelityFns[337]?.map Fn.sig =
    some ("full_bve_ext_need", [i64, i32, i32], [i64]) := by t_kernel_rfl
private theorem fid_idx_338 : m7FidelityFns[338]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := by t_kernel_rfl
private theorem fid_idx_339 : m7FidelityFns[339]?.map Fn.sig =
    some ("full_bve_var", [i64, i32], [i64]) := by t_kernel_rfl
private theorem fid_idx_353 : m7FidelityFns[353]?.map Fn.sig =
    some ("full_factor", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_371 : m7FidelityFns[371]?.map Fn.sig =
    some ("full_reorder_m6", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_376 : m7FidelityFns[376]?.map Fn.sig =
    some ("full_min_u64", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_379 : m7FidelityFns[379]?.map Fn.sig =
    some ("full_bve_var_key_m7", [i64, i32], [i64]) := by t_kernel_rfl
private theorem fid_idx_396 : m7FidelityFns[396]?.map Fn.sig =
    some ("full_lucky_late_m7", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_401 : m7FidelityFns[401]?.map Fn.sig =
    some ("full_switch_mode_m7", [i64], []) := by t_kernel_rfl
private theorem fid_idx_402 : m7FidelityFns[402]?.map Fn.sig =
    some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := by t_kernel_rfl
private theorem fid_idx_403 : m7FidelityFns[403]?.map Fn.sig =
    some ("full_probe_tail_m6", [i64, i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_404 : m7FidelityFns[404]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := by t_kernel_rfl
private theorem fid_idx_406 : m7FidelityFns[406]?.map Fn.sig =
    some ("full_simplify_m6", [i64, .bool, .bool], [i64]) := by t_kernel_rfl
private theorem fid_idx_407 : m7FidelityFns[407]?.map Fn.sig =
    some ("m6_hdr_decide_fid", [i64], [i64]) := by t_kernel_rfl
private theorem fid_idx_408 : m7FidelityFns[408]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) := by t_kernel_rfl

private theorem fid_sig_of_map {i : Nat} {s : SigEntry}
    (h : m7FidelityFns[i]?.map Fn.sig = some s) :
    ∃ g, m7FidelityFns[i]? = some g ∧ g.sig = s := by
  cases hg : m7FidelityFns[i]? with
  | none => simp [hg] at h
  | some g => exact ⟨g, rfl, by simpa [hg] using h⟩

private theorem m8_find_name_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) h)

private theorem m8_patchFns_names_map {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (mfPatchFns repls befores fs).map Fn.name =
      fs.flatMap fun f => (mfPatchInsAt befores f).map Fn.name ++ [f.name] := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    have hsig_r : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hname : ((repls.find? (fun x => x.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r => exact m8_find_name_eq h
    dsimp only [mfPatchFns] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [hname, ih hsig_r]

private theorem m8_patchFns_names_nodup {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hnd : (fs.map Fn.name).Nodup)
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig)
    (hinsNd : ∀ f ∈ fs, ((mfPatchInsAt befores f).map Fn.name).Nodup)
    (hinsDisj : ∀ f ∈ fs, ∀ h ∈ mfPatchInsAt befores f, h.name ∉ fs.map Fn.name)
    (hinsPair : ∀ f₁ ∈ fs, ∀ f₂ ∈ fs, f₁.name ≠ f₂.name →
      ∀ h ∈ mfPatchInsAt befores f₁, h.name ∉ (mfPatchInsAt befores f₂).map Fn.name) :
    ((mfPatchFns repls befores fs).map Fn.name).Nodup := by
  rw [m8_patchFns_names_map hsig]; clear hsig repls
  induction fs with
  | nil => exact List.nodup_nil
  | cons f rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hrest := ih hnd.2
      (fun g hg => hinsNd g (List.mem_cons_of_mem f hg))
      (fun g hg h hh hm =>
        hinsDisj g (List.mem_cons_of_mem f hg) h hh (by simp [List.mem_cons, hm]))
      (fun g₁ hg₁ g₂ hg₂ =>
        hinsPair g₁ (List.mem_cons_of_mem f hg₁) g₂ (List.mem_cons_of_mem f hg₂))
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨⟨hinsNd f List.mem_cons_self, by simp, ?_⟩, hrest, ?_⟩
    · intro x hx y hy hxy; subst hxy
      simp only [List.mem_singleton] at hy; subst hy
      rcases List.mem_map.mp hx with ⟨h, hh, hnm⟩
      exact hinsDisj f List.mem_cons_self h hh (by simp [List.mem_cons, hnm])
    · intro x hx y hy hxy; subst hxy
      rcases List.mem_flatMap.mp hy with ⟨g, hg, hy_g⟩
      have hne_fg : f.name ≠ g.name := fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hg)
      rcases List.mem_append.mp hx with hx_ins | hx_f
      · rcases List.mem_map.mp hx_ins with ⟨h, hh, rfl⟩
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · exact hinsPair f List.mem_cons_self g (List.mem_cons_of_mem f hg) hne_fg h hh hy_ins
        · simp only [List.mem_singleton] at hy_gname
          exact hinsDisj f List.mem_cons_self h hh
            (by simp [List.mem_cons, hy_gname, List.mem_map_of_mem hg])
      · simp only [List.mem_singleton] at hx_f; subst hx_f
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · rcases List.mem_map.mp hy_ins with ⟨h, hh, hnm⟩
          exact hinsDisj g (List.mem_cons_of_mem f hg) h hh (by simp [List.mem_cons, hnm])
        · simp only [List.mem_singleton] at hy_gname; exact hne_fg hy_gname

private theorem m8_checkFnsCallsOk_patch (exits : List Sym) (extSigs : List SigEntry)
    (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (origSeen : List Fn) (seen : List SigEntry) (fs : List Fn),
    (∀ g ∈ origSeen, g.sig ∈ seen) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (origSeen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post, fs = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk exits extSigs
        ((origSeen ++ pre).map Fn.sig) (mfPatchInsAt befores f) = true) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        ((origSeen ++ pre).map Fn.sig ++ (mfPatchInsAt befores f).map Fn.sig ++ extSigs)
        exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen (mfPatchFns repls befores fs) = true
  | _, _, [], _, _, _, _, _ => rfl
  | origSeen, seen, f :: rest, hsub, hchk, hsig, hins, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    dsimp only [mfPatchFns]; simp only [List.flatMap_cons]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hins_rest : ∀ pre g post, rest = pre ++ g :: post →
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs
          (((origSeen ++ [f]) ++ pre).map Fn.sig) (mfPatchInsAt befores g) = true := by
      intro pre g post hsplit; rw [List.append_assoc]
      exact hins (f :: pre) g post (by rw [hsplit]; rfl)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk
          (((origSeen ++ [f]) ++ pre).map Fn.sig ++
            (mfPatchInsAt befores g).map Fn.sig ++ extSigs) exits = true := by
      intro pre g post r hsplit hr hnm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hrepl (f :: pre) g post r (by rw [hsplit]; rfl) hr hnm
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (m8_find_name_eq h)
    have hsub_ext : ∀ s ∈ origSeen.map Fn.sig ++ extSigs, s ∈ seen ++ extSigs := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · rcases List.mem_map.mp hs1 with ⟨g, hg, rfl⟩
        exact List.mem_append_left _ (hsub g hg)
      · exact List.mem_append_right _ hs2
    have h_ins_ok : LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen
        (mfPatchInsAt befores f) = true := by
      have h0 := hins [] f rest rfl; simp only [List.append_nil] at h0
      exact checkFnsCallsOk_mono hsub_ext h0
    have h_mid_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        ((seen ++ (mfPatchInsAt befores f).map Fn.sig) ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none =>
        refine fn_checkCallsOk_mono (fun s hs => ?_) hchk.1
        rcases List.mem_append.mp (hsub_ext s hs) with hs1 | hs2
        · exact List.mem_append_left _ (List.mem_append_left _ hs1)
        · exact List.mem_append_right _ hs2
      | some r =>
        have h0 := hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (m8_find_name_eq h)
        simp only [List.append_nil] at h0
        refine fn_checkCallsOk_mono (fun s hs => ?_) h0
        rcases List.mem_append.mp hs with hs1 | hs2
        · rcases List.mem_append.mp hs1 with hs1a | hs1b
          · rcases List.mem_map.mp hs1a with ⟨g, hg, rfl⟩
            exact List.mem_append_left _ (List.mem_append_left _ (hsub g hg))
          · exact List.mem_append_left _ (List.mem_append_right _ hs1b)
        · exact List.mem_append_right _ hs2
    rw [List.append_assoc, checkFnsCallsOk_append, h_ins_ok, Bool.true_and,
      checkFnsCallsOk_append, LeanQbe.T.Module.checkFnsCallsOk, h_mid_ok]
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.true_and, List.map_singleton,
      List.append_assoc]
    have hsub_next : ∀ g ∈ origSeen ++ [f],
        g.sig ∈ seen ++ ((mfPatchInsAt befores f).map Fn.sig ++
          [((repls.find? (fun x => x.name == f.name)).getD f).sig]) := by
      intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact List.mem_append_left _ (hsub g hg1)
      · simp only [List.mem_singleton] at hg2; subst hg2
        exact List.mem_append_right _ (List.mem_append_right _ (by simp [hhead_sig]))
    have hchk2 :
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((origSeen ++ [f]).map Fn.sig) rest =
          true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    exact m8_checkFnsCallsOk_patch exits extSigs repls befores (origSeen ++ [f])
      (seen ++ ((mfPatchInsAt befores f).map Fn.sig ++
        [((repls.find? (fun x => x.name == f.name)).getD f).sig]))
      rest hsub_next hchk2 hsig_rest hins_rest hrepl_rest

private theorem m8_patchModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hnd : ((mfPatchFns repls befores M.fns).map Fn.name ++ M.externs.map Extern.name).Nodup)
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hins : ∀ pre f post, M.fns = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig)
        (pre.map Fn.sig) (mfPatchInsAt befores f) = true)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        (pre.map Fn.sig ++ (mfPatchInsAt befores f).map Fn.sig ++ M.externs.map Extern.sig)
        M.exits = true) :
    ({ M with fns := mfPatchFns repls befores M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨listNodup_iff.mpr hnd, ?_⟩
  exact m8_checkFnsCallsOk_patch M.exits (M.externs.map Extern.sig) repls befores [] [] M.fns
    (fun _ h => nomatch h) hM.2 hsig hins hrepl

private theorem m8_filter_false {α β} {b : Bool} {x : α} {f : α → β} (hb : b = false) :
    (if b then some (f x) else none) = none := by rw [hb]; rfl

private theorem m8_beq_false_of_ne {a b : String} (h : a ≠ b) : (a == b) = false :=
  Bool.eq_false_iff.mpr fun hq => h (beq_iff_eq.mp hq)

private theorem m8_insAt_cases (f : Fn) :
    mfPatchInsAt m8CoreParityBefores f = [] ∨
    (f.name = "full_min_shrink_m6" ∧ mfPatchInsAt m8CoreParityBefores f = m8MinHelpers) ∨
    (f.name = "full_bve_var_m7" ∧ mfPatchInsAt m8CoreParityBefores f = m8BveHelpers) := by
  by_cases h1 : f.name = "full_min_shrink_m6"
  · right; left; refine ⟨h1, ?_⟩
    dsimp only [mfPatchInsAt, m8CoreParityBefores]; rw [h1]; rfl
  · by_cases h2 : f.name = "full_bve_var_m7"
    · right; right; refine ⟨h2, ?_⟩
      dsimp only [mfPatchInsAt, m8CoreParityBefores]; rw [h2]; rfl
    · left
      have hb1 := m8_beq_false_of_ne (Ne.symm h1)
      have hb2 := m8_beq_false_of_ne (Ne.symm h2)
      dsimp only [mfPatchInsAt, m8CoreParityBefores]
      rw [List.filterMap_cons, m8_filter_false hb1, List.filterMap_cons, m8_filter_false hb2]
      rfl

private theorem m8MinHelpers_not_mem :
    ∀ h ∈ m8MinHelpers, h.name ∉ m7FidelityFns.map Fn.name := by
  have hdisj : ((m8MinHelpers.map Fn.name).all
      (fun nm => !(m7FidelityFns.map Fn.name).contains nm)) = true := by t_kernel_rfl
  intro h hh hm
  have := List.all_eq_true.mp hdisj h.name (List.mem_map_of_mem hh)
  simp only [Bool.not_eq_true'] at this
  exact absurd hm (by simpa using this)

private theorem m8BveHelpers_not_mem :
    ∀ h ∈ m8BveHelpers, h.name ∉ m7FidelityFns.map Fn.name := by
  have hdisj : ((m8BveHelpers.map Fn.name).all
      (fun nm => !(m7FidelityFns.map Fn.name).contains nm)) = true := by t_kernel_rfl
  intro h hh hm
  have := List.all_eq_true.mp hdisj h.name (List.mem_map_of_mem hh)
  simp only [Bool.not_eq_true'] at this
  exact absurd hm (by simpa using this)

theorem m8CoreParity_replSigs :
    ∀ r ∈ m8CoreParityRepls, ∀ f ∈ m7FidelityFns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨g135, hg135, hs135⟩ := fid_sig_of_map fid_idx_135
  obtain ⟨g338, hg338, hs338⟩ := fid_sig_of_map fid_idx_338
  obtain ⟨g339, hg339, hs339⟩ := fid_sig_of_map fid_idx_339
  obtain ⟨g379, hg379, hs379⟩ := fid_sig_of_map fid_idx_379
  obtain ⟨g402, hg402, hs402⟩ := fid_sig_of_map fid_idx_402
  obtain ⟨g404, hg404, hs404⟩ := fid_sig_of_map fid_idx_404
  obtain ⟨g408, hg408, hs408⟩ := fid_sig_of_map fid_idx_408
  intro r hr f hf hnm
  simp only [m8CoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg135
      (hnm.symm.trans (congrArg Prod.fst hs135.symm))) ▸ hs135.symm
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg338
      (hnm.symm.trans (congrArg Prod.fst hs338.symm))) ▸ hs338.symm
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg339
      (hnm.symm.trans (congrArg Prod.fst hs339.symm))) ▸ hs339.symm
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg379
      (hnm.symm.trans (congrArg Prod.fst hs379.symm))) ▸ hs379.symm
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg402
      (hnm.symm.trans (congrArg Prod.fst hs402.symm))) ▸ hs402.symm
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg404
      (hnm.symm.trans (congrArg Prod.fst hs404.symm))) ▸ hs404.symm
  · exact (fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hg408
      (hnm.symm.trans (congrArg Prod.fst hs408.symm))) ▸ hs408.symm

theorem m8CoreParityFns_names_nodup : (m8CoreParityFns.map Fn.name).Nodup := by
  refine m8_patchFns_names_nodup m7FidelityFns_names_nodup m8CoreParity_replSigs ?_ ?_ ?_
  · intro f _
    rcases m8_insAt_cases f with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;>
      first | simp | exact (by decide : (m8MinHelpers.map Fn.name).Nodup)
            | exact (by decide : (m8BveHelpers.map Fn.name).Nodup)
  · intro f _ h hh
    rcases m8_insAt_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩
    · rw [h0] at hh; cases hh
    · rw [h1] at hh; exact m8MinHelpers_not_mem h hh
    · rw [h2] at hh; exact m8BveHelpers_not_mem h hh
  · intro f₁ _ f₂ _ hne h hh hm
    rcases m8_insAt_cases f₁ with h1 | ⟨he1, hp1⟩ | ⟨he1, hp1⟩
    · rw [h1] at hh; cases hh
    · rw [hp1] at hh
      rcases m8_insAt_cases f₂ with h2 | ⟨he2, _⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · exact hne (he1.trans he2.symm)
      · rw [hp2] at hm
        have hdisj : ((m8MinHelpers.map Fn.name).all
            (fun nm => !(m8BveHelpers.map Fn.name).contains nm)) = true := by decide
        have := List.all_eq_true.mp hdisj h.name (List.mem_map_of_mem hh)
        simp only [Bool.not_eq_true'] at this
        exact absurd hm (by simpa using this)
    · rw [hp1] at hh
      rcases m8_insAt_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨he2, _⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm
        have hdisj : ((m8BveHelpers.map Fn.name).all
            (fun nm => !(m8MinHelpers.map Fn.name).contains nm)) = true := by decide
        have := List.all_eq_true.mp hdisj h.name (List.mem_map_of_mem hh)
        simp only [Bool.not_eq_true'] at this
        exact absurd hm (by simpa using this)
      · exact hne (he1.trans he2.symm)

theorem m8CoreParity_acyclic : m8CoreParityModule.checkAcyclic = true := by
  obtain ⟨g17, hg17, hsg17⟩ := fid_sig_of_map fid_idx_17
  obtain ⟨g31, hg31, hsg31⟩ := fid_sig_of_map fid_idx_31
  obtain ⟨g32, hg32, hsg32⟩ := fid_sig_of_map fid_idx_32
  obtain ⟨g66, hg66, hsg66⟩ := fid_sig_of_map fid_idx_66
  obtain ⟨g67, hg67, hsg67⟩ := fid_sig_of_map fid_idx_67
  obtain ⟨g68, hg68, hsg68⟩ := fid_sig_of_map fid_idx_68
  obtain ⟨g70, hg70, hsg70⟩ := fid_sig_of_map fid_idx_70
  obtain ⟨g71, hg71, hsg71⟩ := fid_sig_of_map fid_idx_71
  obtain ⟨g86, hg86, hsg86⟩ := fid_sig_of_map fid_idx_86
  obtain ⟨g111, hg111, hsg111⟩ := fid_sig_of_map fid_idx_111
  obtain ⟨g124, hg124, hsg124⟩ := fid_sig_of_map fid_idx_124
  obtain ⟨g129, hg129, hsg129⟩ := fid_sig_of_map fid_idx_129
  obtain ⟨g135, hg135, hsg135⟩ := fid_sig_of_map fid_idx_135
  obtain ⟨g151, hg151, hsg151⟩ := fid_sig_of_map fid_idx_151
  obtain ⟨g169, hg169, hsg169⟩ := fid_sig_of_map fid_idx_169
  obtain ⟨g170, hg170, hsg170⟩ := fid_sig_of_map fid_idx_170
  obtain ⟨g171, hg171, hsg171⟩ := fid_sig_of_map fid_idx_171
  obtain ⟨g172, hg172, hsg172⟩ := fid_sig_of_map fid_idx_172
  obtain ⟨g173, hg173, hsg173⟩ := fid_sig_of_map fid_idx_173
  obtain ⟨g179, hg179, hsg179⟩ := fid_sig_of_map fid_idx_179
  obtain ⟨g180, hg180, hsg180⟩ := fid_sig_of_map fid_idx_180
  obtain ⟨g218, hg218, hsg218⟩ := fid_sig_of_map fid_idx_218
  obtain ⟨g226, hg226, hsg226⟩ := fid_sig_of_map fid_idx_226
  obtain ⟨g235, hg235, hsg235⟩ := fid_sig_of_map fid_idx_235
  obtain ⟨g236, hg236, hsg236⟩ := fid_sig_of_map fid_idx_236
  obtain ⟨g237, hg237, hsg237⟩ := fid_sig_of_map fid_idx_237
  obtain ⟨g275, hg275, hsg275⟩ := fid_sig_of_map fid_idx_275
  obtain ⟨g299, hg299, hsg299⟩ := fid_sig_of_map fid_idx_299
  obtain ⟨g302, hg302, hsg302⟩ := fid_sig_of_map fid_idx_302
  obtain ⟨g310, hg310, hsg310⟩ := fid_sig_of_map fid_idx_310
  obtain ⟨g316, hg316, hsg316⟩ := fid_sig_of_map fid_idx_316
  obtain ⟨g320, hg320, hsg320⟩ := fid_sig_of_map fid_idx_320
  obtain ⟨g332, hg332, hsg332⟩ := fid_sig_of_map fid_idx_332
  obtain ⟨g333, hg333, hsg333⟩ := fid_sig_of_map fid_idx_333
  obtain ⟨g334, hg334, hsg334⟩ := fid_sig_of_map fid_idx_334
  obtain ⟨g335, hg335, hsg335⟩ := fid_sig_of_map fid_idx_335
  obtain ⟨g336, hg336, hsg336⟩ := fid_sig_of_map fid_idx_336
  obtain ⟨g337, hg337, hsg337⟩ := fid_sig_of_map fid_idx_337
  obtain ⟨g338, hg338, hsg338⟩ := fid_sig_of_map fid_idx_338
  obtain ⟨g339, hg339, hsg339⟩ := fid_sig_of_map fid_idx_339
  obtain ⟨g353, hg353, hsg353⟩ := fid_sig_of_map fid_idx_353
  obtain ⟨g371, hg371, hsg371⟩ := fid_sig_of_map fid_idx_371
  obtain ⟨g376, hg376, hsg376⟩ := fid_sig_of_map fid_idx_376
  obtain ⟨g379, hg379, hsg379⟩ := fid_sig_of_map fid_idx_379
  obtain ⟨g396, hg396, hsg396⟩ := fid_sig_of_map fid_idx_396
  obtain ⟨g401, hg401, hsg401⟩ := fid_sig_of_map fid_idx_401
  obtain ⟨g402, hg402, hsg402⟩ := fid_sig_of_map fid_idx_402
  obtain ⟨g403, hg403, hsg403⟩ := fid_sig_of_map fid_idx_403
  obtain ⟨g404, hg404, hsg404⟩ := fid_sig_of_map fid_idx_404
  obtain ⟨g406, hg406, hsg406⟩ := fid_sig_of_map fid_idx_406
  obtain ⟨g407, hg407, hsg407⟩ := fid_sig_of_map fid_idx_407
  obtain ⟨g408, hg408, hsg408⟩ := fid_sig_of_map fid_idx_408
  have hndApp : ((m8CoreParityFns.map Fn.name) ++
      m7FidelityModule.externs.map Extern.name).Nodup := by
    simpa [m7FidelityModule] using m8CoreParityFns_names_nodup
  refine m8_patchModule_checkAcyclic (M := m7FidelityModule) hndApp
    m7Fidelity_acyclic m8CoreParity_replSigs ?_ ?_
  · intro pre f post hsplit
    simp only [m7FidelityModule, List.map_nil] at hsplit ⊢
    rcases m8_insAt_cases f with h0 | ⟨he1, hp1⟩ | ⟨he2, hp2⟩
    · rw [h0]; rfl
    · rw [hp1]
      have he1' : f.name = g135.name := he1.trans (congrArg Prod.fst hsg135).symm
      have hc : LeanQbe.T.Module.checkFnsCallsOk [] []
          [("full_min_mark", [i64, i32, i8], [])] m8MinHelpers = true := by rfl
      refine checkFnsCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.append_nil, List.mem_singleton] at hs
      subst hs
      exact hsg124 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg135 he1' hg124
        (by decide)
    · rw [hp2]
      have he2' : f.name = g338.name := he2.trans (congrArg Prod.fst hsg338).symm
      have hc : LeanQbe.T.Module.checkFnsCallsOk [] []
          [ ("full_wstack_defrag", [i64], [])
          , ("full_extend_push2", [i64, i32, i32], [.bool])
          , ("full_extend_push_cl", [i64, i32, i32], [.bool])
          , ("full_delete_binary", [i64, i32, i32], [])
          , ("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool])
          , ("full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32])
          , ("full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool]) ]
          m8BveHelpers = true := by rfl
      refine checkFnsCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg17 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg17
          (by decide)
      · exact hsg172 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg172
          (by decide)
      · exact hsg173 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg173
          (by decide)
      · exact hsg179 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg179
          (by decide)
      · exact hsg316 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg316
          (by decide)
      · exact hsg320 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg320
          (by decide)
      · exact hsg335 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 he2' hg335
          (by decide)
  · intro pre f post r hsplit hr hnm
    simp only [m7FidelityModule, List.map_nil, List.append_nil] at hsplit ⊢
    simp only [m8CoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hn0 : f.name = g135.name := hnm.symm.trans (congrArg Prod.fst hsg135.symm)
      have hf135 : f.name = "full_min_shrink_m6" := hnm.symm
      have hp : mfPatchInsAt m8CoreParityBefores f = m8MinHelpers := by
        dsimp only [mfPatchInsAt, m8CoreParityBefores]; rw [hf135]; rfl
      have hc : m8MinShrinkM6Fn.checkCallsOk
          [ ("full_sort_tmp", [i64], [])
          , ("full_min_mark", [i64, i32, i8], [])
          , ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool])
          , ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact List.mem_append_left _
          (hsg129 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg135 hn0 hg129
            (by decide))
      · exact List.mem_append_left _
          (hsg124 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg135 hn0 hg124
            (by decide))
      · exact List.mem_append_right _ (by rw [hp]; simp [m8MinHelpers, m8MinLitDfsFn, Fn.sig])
      · exact List.mem_append_right _ (by rw [hp]; simp [m8MinHelpers, m8ShrinkBlkBoolFn, Fn.sig])
    · have hn0 : f.name = g338.name := hnm.symm.trans (congrArg Prod.fst hsg338.symm)
      have hf338 : f.name = "full_bve_var_m7" := hnm.symm
      have hp : mfPatchInsAt m8CoreParityBefores f = m8BveHelpers := by
        dsimp only [mfPatchInsAt, m8CoreParityBefores]; rw [hf338]; rfl
      have hc : m8BveVarM7Fn.checkCallsOk
          [ ("full_wstack_defrag", [i64], [])
          , ("full_set_inactive", [i64, i32, i32], [])
          , ("full_dense_flush_units_m7", [i64], [.bool])
          , ("full_bve_collect_m7", [i64, i32, i64, i32], [i32])
          , ("full_bve_gates_m7", [i64, i32, i32, i32], [])
          , ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool])
          , ("full_bve_weaken", [i64, i32, i32, i32], [.bool])
          , ("full_bve_commit_res", [i64, i64, i64], [i64])
          , ("full_bve_ext_need", [i64, i32, i32], [i64])
          , ("full_bve_gates_m8", [i64, i32, i32, i32], [])
          , ("full_bve_bce_side_m8", [i64, i32, i32, i32, i32, i32], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_append_left _
          (hsg17 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg17
            (by decide))
      · exact List.mem_append_left _
          (hsg180 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg180
            (by decide))
      · exact List.mem_append_left _
          (hsg302 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg302
            (by decide))
      · exact List.mem_append_left _
          (hsg310 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg310
            (by decide))
      · exact List.mem_append_left _
          (hsg332 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg332
            (by decide))
      · exact List.mem_append_left _
          (hsg333 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg333
            (by decide))
      · exact List.mem_append_left _
          (hsg334 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg334
            (by decide))
      · exact List.mem_append_left _
          (hsg336 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg336
            (by decide))
      · exact List.mem_append_left _
          (hsg337 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg338 hn0 hg337
            (by decide))
      · exact List.mem_append_right _ (by rw [hp]; simp [m8BveHelpers, m8BveGatesFn, Fn.sig])
      · exact List.mem_append_right _ (by rw [hp]; simp [m8BveHelpers, m8BveBceSideFn, Fn.sig])
    · have hn0 : f.name = g339.name := hnm.symm.trans (congrArg Prod.fst hsg339.symm)
      have hc : m8BveVarFn.checkCallsOk [("full_bve_var_m7", [i64, i32], [i64])] [] = true := by
        rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg338 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg339 hn0 hg338
        (by decide)
    · exact fn_checkCallsOk_mono (fun _ h => by simp at h)
        (by rfl : m8BveVarKeyM7Fn.checkCallsOk [] [] = true)
    · have hn0 : f.name = g402.name := hnm.symm.trans (congrArg Prod.fst hsg402.symm)
      have hc : m8ProbeDticksM6HdrFn.checkCallsOk
          [("m6_hdr_get_watermark", [i64, i64], [i64])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg70 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg402 hn0 hg70
        (by decide)
    · have hn0 : f.name = g404.name := hnm.symm.trans (congrArg Prod.fst hsg404.symm)
      have hc : m8ProbeM6Fn.checkCallsOk
          [ ("full_log10_q16_m7", [i64], [i64])
          , ("full_scale_delta_m5", [i64, i64], [i64])
          , ("m6_hdr_delaying", [i64, i64], [.bool])
          , ("m6_hdr_bump_delay", [i64, i64], [])
          , ("m6_hdr_reduce_delay", [i64, i64], [])
          , ("m6_hdr_set_watermark", [i64, i64, i64], [])
          , ("full_vivify_m6_hdr", [i64], [i64])
          , ("full_backbone_m6", [i64, i64], [i64])
          , ("full_substitute", [i64], [i64])
          , ("full_enter_dense", [i64], [.bool])
          , ("full_rebuild_watches", [i64], [i64])
          , ("full_congruence_dense", [i64, i64], [i64])
          , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
          , ("full_factor", [i64, i64], [i64])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
          , ("full_probe_tail_m6", [i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact hsg31 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg31
          (by decide)
      · exact hsg32 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg32
          (by decide)
      · exact hsg66 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg66
          (by decide)
      · exact hsg67 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg67
          (by decide)
      · exact hsg68 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg68
          (by decide)
      · exact hsg71 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg71
          (by decide)
      · exact hsg218 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg218
          (by decide)
      · exact hsg226 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg226
          (by decide)
      · exact hsg235 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg235
          (by decide)
      · exact hsg236 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg236
          (by decide)
      · exact hsg237 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg237
          (by decide)
      · exact hsg275 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg275
          (by decide)
      · exact hsg299 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg299
          (by decide)
      · exact hsg353 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg353
          (by decide)
      · exact hsg376 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg376
          (by decide)
      · exact hsg402 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg402
          (by decide)
      · exact hsg403 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg403
          (by decide)
    · have hn0 : f.name = g408.name := hnm.symm.trans (congrArg Prod.fst hsg408.symm)
      have hc : m8SearchM6Fn.checkCallsOk
          [ ("full_lucky_late_m7", [i64], [i64])
          , ("full_propagate", [i64], [i64])
          , ("full_analyze_m6_hdr", [i64], [i64])
          , ("full_reduce_m6", [i64, .bool], [i64])
          , ("full_switch_mode_m7", [i64], [])
          , ("full_restart_due", [i64], [i64])
          , ("full_restart", [i64], [])
          , ("full_reorder_m6", [i64, i64], [i64])
          , ("full_rephase", [i64], [])
          , ("full_simplify_m6", [i64, .bool, .bool], [i64])
          , ("m6_hdr_decide_fid", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg396 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg396
          (by decide)
      · exact hsg86 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg86
          (by decide)
      · exact hsg151 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg151
          (by decide)
      · exact hsg111 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg111
          (by decide)
      · exact hsg401 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg401
          (by decide)
      · exact hsg170 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg170
          (by decide)
      · exact hsg171 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg171
          (by decide)
      · exact hsg371 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg371
          (by decide)
      · exact hsg169 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg169
          (by decide)
      · exact hsg406 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg406
          (by decide)
      · exact hsg407 ▸ sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg408 hn0 hg407
          (by decide)

/-! ## 3. Compile-Time `#guard` Verification (Shape & Acyclicity) -/

section Guards

#guard m8CoreParityFns.length == 435
#guard (m8CoreParityFns.map Fn.name).eraseDups.length == 435
#guard m8CoreParityModule.checkAcyclic
#guard m8CoreParityModule.exits.isEmpty && m8CoreParityModule.externs.isEmpty

end Guards

end LeanQbe.T.Examples.Kissat.FullM8CoreParity

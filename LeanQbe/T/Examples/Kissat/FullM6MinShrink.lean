module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M6 Wave 2 (`PR-W2B`, `RC-18`): Cohesive Minimization, Block Shrink & Sorted VMTF Bumping

Standalone drop-in C0 overrides off `main` (`0` edits to `FullHdr` / `144` words frozen, `0` edits
to `Full1..3.lean`, `FullM4*.lean`, `FullM5*.lean`, or `M5Hub.lean`):
1. **Cohesive `minimize` + `shrink` parity (`RC-18`)**:
   - `full_min_lit_dfs_m6` / `full_min_lit_m6`: iterative binary-reason DFS (`cur_depth` increments
     only across large clauses; binary chains tracked safely inside `min_stk`), supporting optional
     `analyzed`-based `used[lvl] <= 1` check (`check_used`).
   - `full_shrink_lower_m6` / `full_shrink_blk_bool_m6` / `full_shrink_blk_m6`: lower-level
     shrink & UIP block shrinking.
   - `full_min_shrink_m6`: `analyzed`-based `used[lvl]` initialization on `shrink_stk`, clause
     minimization, compaction, **low-to-high** decision-level block shrinking with
     **`minimize_block` fallback** on failed block shrink, leaving `work_stk1` untouched.
2. **Sorted VMTF bumping & `decision_rate < 10` gate**:
   - `full_dr_init_m6` / `full_dr_update_m6` / `full_dr_allow_m6` / `full_decide_m6`: tracks
     per-mode `Q32` `decision_rate` in `h->delayed[0..11]` (init bit 63 + mode-switch bits 56..62
     packed in unused `h->delayed_len`; safe no-op fallback when `delayed_cap < 4`).
   - `full_ana_sift_m6` / `full_sort_ana_qs_m6` / `full_bump_analyzed_m6`: gates reason-side
     bumping on `decision_rate < 10`, sorts `work_stk1` ascending by `q_stamp` before focused
     `full_queue_mtf`, and guards bumping with `FL_ACTIVE` + focused-mode `full_queue_mtf`.
   - `full_restore_bump_ana_m6` / `full_deduce_1uip_m6` / `full_ana_failed_lit_m6` /
     `full_analyze_m6`: defers bumping until after `full_min_shrink_m6` (restoring resolved vars +
     surviving block UIPs to `work_stk1`) and implements level-1 multi-UIP failed-literal analysis.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6MinShrink "
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

#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE   1u

extern void full_min_mark(FullHdr *h, u32 v, u8 tag);
extern void full_sort_tmp(FullHdr *h);
extern bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var);
extern bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var);
extern void full_clear_ana(FullHdr *h);
extern bool full_otfs_large(FullHdr *h, u32 cref, u32 uip);
extern bool full_otfs_bin(FullHdr *h, u32 cref, u32 uip);
extern void full_otfs_subsume(
  FullHdr *h, u32 new_confl, u64 old_ctype, u64 old_cref, bool to_bin);
extern void full_bump_var(FullHdr *h, u32 v);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_bump_decay(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_tick_rel(FullHdr *h);
extern void full_ema_update(FullHdr *h, u64 glue);
extern u64 full_one_lit_confl(FullHdr *h);
extern u64 full_learn_clause(FullHdr *h, u64 glue);

void full_dr_init_m6(FullHdr *h) {
  if ((h->delayed_len >> 63) != 0ULL) { return; }
  u64 sw = h->switched & 127ULL;
  h->delayed_len = (1ULL << 63) | (sw << 56);
  if (h->delayed_cap < 4ULL) { return; }
  u32 *del = (u32 *)h->delayed;
  u64 i = 0ULL;
  while (i < 12ULL) { del[i] = 0u; i = i + 1ULL; }
  del[7] = 1u;
  del[11] = 1u;
}

void full_dr_update_m6(FullHdr *h) {
  full_dr_init_m6(h);
  if (h->delayed_cap < 4ULL) { return; }
  u32 *del = (u32 *)h->delayed;
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 cur = h->delayed_len & mask56;
  u64 last_sw = (h->delayed_len >> 56) & 127ULL;
  u64 cur_sw = h->switched & 127ULL;
  u64 off = (h->stable != 0ULL) ? 2ULL : 0ULL;
  u64 eoff = (h->stable != 0ULL) ? 8ULL : 4ULL;
  if (cur_sw != last_sw) {
    h->delayed_len = (1ULL << 63) | (cur_sw << 56) | cur;
    del[off] = (u32)cur; del[off + 1ULL] = (u32)(cur >> 32);
    del[eoff] = 0u; del[eoff + 1ULL] = 0u;
    del[eoff + 2ULL] = 0u; del[eoff + 3ULL] = 1u;
    return;
  }
  u64 prev = ((u64)del[off]) | (((u64)del[off + 1ULL]) << 32);
  del[off] = (u32)cur;
  del[off + 1ULL] = (u32)(cur >> 32);
  u64 d = (cur >= prev) ? (cur - prev) : 0ULL;
  if (d > 16383ULL) { d = 16383ULL; }
  u64 ys = d << 32;
  u64 sb = ((u64)del[eoff]) | (((u64)del[eoff + 1ULL]) << 32);
  u64 se = ((u64)del[eoff + 2ULL]) | (((u64)del[eoff + 3ULL]) << 32);
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  if (se > 0ULL) {
    u64 ds = se / 100000ULL;
    se = (ds == 0ULL) ? 0ULL : (se - ds);
  }
  del[eoff] = (u32)sb; del[eoff + 1ULL] = (u32)(sb >> 32);
  del[eoff + 2ULL] = (u32)se; del[eoff + 3ULL] = (u32)(se >> 32);
}

bool full_dr_allow_m6(FullHdr *h) {
  if (h->delayed_cap < 4ULL || (h->delayed_len >> 63) == 0ULL) { return true; }
  u32 *del = (u32 *)h->delayed;
  u64 eoff = (h->stable != 0ULL) ? 8ULL : 4ULL;
  u64 sb = ((u64)del[eoff]) | (((u64)del[eoff + 1ULL]) << 32);
  u64 se = ((u64)del[eoff + 2ULL]) | (((u64)del[eoff + 3ULL]) << 32);
  u64 scale = 1ULL << 32;
  u64 sd = (scale > se) ? (scale - se) : 0ULL;
  if (sd == 0ULL) { return true; }
  return sb < (sd * 10ULL);
}

u64 full_decide_m6(FullHdr *h) {
  u64 chosen = full_next_dec_var(h);
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) { return 0ULL; }
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 dph = ph[chosen];
  if (h->stable != 0ULL && ptgt[chosen] != (i8)0) { dph = ptgt[chosen]; }
  u32 lit = (dph < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
  u64 nlvl = h->cur_level + 1ULL;
  if (nlvl > h->max_vars) { return 0ULL; }
  ftrl[nlvl] = (u32)h->trail_end;
  fdec[nlvl] = lit;
  h->cur_level = nlvl;
  full_assign(h, lit, 0xFFFFFFFFu);
  full_dr_init_m6(h);
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 hi = h->delayed_len & (~mask56);
  u64 decs = h->delayed_len & mask56;
  if (decs < mask56) { h->delayed_len = hi | (decs + 1ULL); }
  return 1ULL;
}

void full_ana_sift_m6(u32 *qs, u32 *ana, u64 cv, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 ac = ana[ch];
    u32 qc = ((u64)ac < cv) ? qs[ac] : 0u;
    if (ch + 1ULL < n) {
      u32 ac1 = ana[ch + 1ULL];
      u32 qc1 = ((u64)ac1 < cv) ? qs[ac1] : 0u;
      if (qc < qc1) { ch = ch + 1ULL; qc = qc1; }
    }
    u32 ar = ana[root];
    u32 qr = ((u64)ar < cv) ? qs[ar] : 0u;
    if (qr >= qc) { break; }
    ana[root] = ana[ch]; ana[ch] = ar;
    root = ch;
  }
}

void full_sort_ana_qs_m6(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u64 cv = h->cur_vars;
  if (n > cv) { return; }
  u32 *qs = (u32 *)h->q_stamp;
  u32 *ana = (u32 *)h->work_stk1;
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_ana_sift_m6(qs, ana, cv, start, n);
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = ana[0]; ana[0] = ana[end]; ana[end] = t;
    full_ana_sift_m6(qs, ana, cv, 0ULL, end);
    end = end - 1ULL;
  }
}

void full_bump_analyzed_m6(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  if (full_dr_allow_m6(h)) {
    u64 lim = saved * 10ULL;
    u64 i = 0ULL;
    u64 tlen = h->tmp_len;
    if (tlen > cv) { tlen = cv; }
    while (i < tlen && h->min_clr_len <= lim) {
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
    }
  }
  u64 cnt = h->min_clr_len;
  if (h->stable == 0ULL && cnt <= cv) {
    full_sort_ana_qs_m6(h, cnt);
  }
  u64 k = 0ULL;
  while (k < cnt) {
    u32 bv = ana[k];
    if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
      full_bump_var(h, bv);
      if (h->stable == 0ULL) { full_queue_mtf(h, bv); }
    }
    k = k + 1ULL;
  }
  full_bump_decay(h);
}

void full_restore_bump_ana_m6(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u64 cv = h->cur_vars;
  u64 ana_n = h->res_sz;
  if (ana_n > cv) { ana_n = cv; }
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
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
  if (w > 0ULL) {
    full_bump_analyzed_m6(h);
    full_clear_ana(h);
  }
}

bool full_min_lit_dfs_m6(FullHdr *h, u32 root_lit, bool minimizing, bool check_used) {
  u64 cv = h->cur_vars;
  u32 root_v = root_lit >> 1;
  if ((u64)root_v >= cv || h->min_depth == 0ULL) { return false; }
  u32 *rsns = (u32 *)h->reason;
  if (rsns[root_v] == 0xFFFFFFFFu) { return false; }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena; u32 *stk = (u32 *)h->min_stk;
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
        if (check_used && (u64)ul < cv && (u64)ul < h->cur_level && used[ul] <= 1u) { break; }
        if (sp + 1ULL >= h->min_depth) { break; }
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
      if (check_used && (u64)ul < cv && (u64)ul < h->cur_level && used[ul] <= 1u) { break; }
      if (cur_depth + 1ULL >= h->min_depth || sp + 1ULL >= h->min_depth) { break; }
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

bool full_min_lit_m6(FullHdr *h, u32 root_lit) {
  return full_min_lit_dfs_m6(h, root_lit, false, false);
}

bool full_shrink_lower_m6(FullHdr *h, u32 ot, u32 ov) {
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[ov] & (u8)2) != (u8)0) { return true; }
  if ((mrk[ov] & (u8)4) != (u8)0 || !full_min_lit_dfs_m6(h, ot, false, false)) {
    full_min_mark(h, ov, (u8)4);
    return false;
  }
  full_min_mark(h, ov, (u8)2);
  return true;
}

bool full_shrink_blk_bool_m6(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
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
    }
    u32 i = 0u;
    while (i < csz && !failed) {
      u32 ot = is_bin ? (rsn & PW_LIT_MASK) : ar[(u64)rsn + 3ULL + (u64)i];
      u32 ov = ot >> 1;
      if (ot != uip && (u64)ov < cv && lvl[ov] > 0u && (mrk[ov] & (u8)8) == (u8)0) {
        if (lvl[ov] < blvl) {
          if (!full_shrink_lower_m6(h, ot, ov)) { failed = true; }
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

void full_shrink_blk_m6(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
  bool ok = full_shrink_blk_bool_m6(h, beg, end_b, blvl, max_tr);
  if (!ok) { return; }
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
  u32 *sstk = (u32 *)h->shrink_stk;
  u32 *ana = (u32 *)h->work_stk1;
  u64 ana_n = h->res_sz;
  if (ana_n > cv) { ana_n = cv; }
  u64 ai = 0ULL;
  while (ai < ana_n) {
    u32 av = ana[ai];
    if ((u64)av < cv) { u32 al = lvl[av]; if ((u64)al < cv) { sstk[al] = 0u; } }
    ai = ai + 1ULL;
  }
  ai = 0ULL;
  while (ai < orig_tlen) {
    u32 al = lvl[tmp[ai] >> 1];
    if ((u64)al < cv) { sstk[al] = 0u; }
    ai = ai + 1ULL;
  }
  ai = 0ULL;
  while (ai < ana_n) {
    u32 av = ana[ai];
    if ((u64)av < cv) {
      u32 al = lvl[av];
      if (al > 0u && (u64)al < h->cur_level && (u64)al < cv) { sstk[al] = sstk[al] + 1u; }
    }
    ai = ai + 1ULL;
  }
  i = 1ULL;
  while (i < orig_tlen) {
    if (full_min_lit_dfs_m6(h, tmp[i], true, true)) { tmp[i] = 0xFFFFFFFFu; }
    i = i + 1ULL;
  }
  ai = 0ULL;
  while (ai < ana_n) {
    u32 av = ana[ai];
    if ((u64)av < cv) { u32 al = lvl[av]; if ((u64)al < cv) { sstk[al] = 0u; } }
    ai = ai + 1ULL;
  }
  ai = 0ULL;
  while (ai < orig_tlen) {
    u32 tv = tmp[ai];
    if (tv != 0xFFFFFFFFu) { u32 al = lvl[tv >> 1]; if ((u64)al < cv) { sstk[al] = 0u; } }
    ai = ai + 1ULL;
  }
  u64 mk = 1ULL; u64 mp = 1ULL;
  while (mp < orig_tlen) {
    if (tmp[mp] != 0xFFFFFFFFu) { tmp[mk] = tmp[mp]; mk = mk + 1ULL; }
    mp = mp + 1ULL;
  }
  u64 tlen = mk;
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
      if (!full_shrink_blk_bool_m6(h, beg, end_b, blvl, max_tr)) {
        u64 mk2 = beg;
        while (mk2 < end_b) {
          if (full_min_lit_dfs_m6(h, tmp[mk2], false, false)) { tmp[mk2] = 0xFFFFFFFFu; }
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

u64 full_deduce_1uip_m6(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  if (!seed_ok || h->tmp_cnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (h->tmp_cnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= h->cur_vars) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      h->tmp_cnt = h->tmp_cnt - 1ULL;
      if (h->tmp_cnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      if (h->res_sz > 0ULL) { h->res_sz = h->res_sz - 1ULL; }
      if (h->ant_sz >= 3ULL && h->res_sz < h->ant_sz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (h->ant_sz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}

u64 full_ana_failed_lit_m6(FullHdr *h) {
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
  full_bump_analyzed_m6(h);
  full_clear_ana(h);
  full_backtrack(h, 0ULL);
  u64 k = 0ULL;
  while (k < ucnt) {
    u32 u = tmp[k];
    if (vals[u] < (i8)0) { return 20ULL; }
    if (vals[u] == (i8)0) { full_assign_lvl(h, u, 0xFFFFFFFFu, 0u); }
    k = k + 1ULL;
  }
  h->conflicts = h->conflicts + 1ULL;
  h->learned_lits = h->learned_lits + 1ULL;
  h->iterating = 1ULL;
  return 1ULL;
}

u64 full_analyze_m6(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  if (h->probing == 0ULL) { full_dr_update_m6(h); }
  u32 *lvl = (u32 *)h->level; u32 *tmp = (u32 *)h->tmp_lits; u32 *ar = (u32 *)h->arena;
  u64 iter = 0ULL; u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) { return 1ULL; }
    if (ol == 2ULL) { return 0ULL; }
    if (h->cur_level == 1ULL) { return full_ana_failed_lit_m6(h); }
    u64 dst = full_deduce_1uip_m6(h);
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
        full_restore_bump_ana_m6(h);
      }
      continue;
    }
    full_min_shrink_m6(h);
    if (h->probing == 0ULL) { full_restore_bump_ana_m6(h); full_tick_rel(h); }
    u64 glue = 1ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
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
"

/-- External callee signatures referenced by `m6MinShrink_fns`. -/
def m6MinShrinkExterns : List Extern :=
  [ ⟨"full_min_mark", [i64, i32, i8], []⟩
  , ⟨"full_sort_tmp", [i64], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool]⟩
  , ⟨"full_clear_ana", [i64], []⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool]⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], []⟩
  , ⟨"full_bump_var", [i64, i32], []⟩
  , ⟨"full_queue_mtf", [i64, i32], []⟩
  , ⟨"full_bump_decay", [i64], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_next_dec_var", [i64], [i64]⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_tick_rel", [i64], []⟩
  , ⟨"full_ema_update", [i64, i64], []⟩
  , ⟨"full_one_lit_confl", [i64], [i64]⟩
  , ⟨"full_learn_clause", [i64, i64], [i64]⟩
  ]

/-- Standalone Wave-2B minimization, shrink, failed-literal, and sorted VMTF bumping module. -/
def m6MinShrinkModule : LeanQbe.T.Module :=
  { fns := m6MinShrink_fns, externs := m6MinShrinkExterns, exits := [] }

/-- Canonical drop-in `Fn` handles (preserving `Full2.lean` / `Full` entry names). -/
def m6DecideFn : Fn := ⟨"full_decide", [i64], [i64], full_decide_m6_body⟩
def m6BumpAnalyzedFn : Fn := ⟨"full_bump_analyzed", [i64], [], full_bump_analyzed_m6_body⟩
def m6MinLitFn : Fn := ⟨"full_min_lit", [i64, i32], [.bool], full_min_lit_m6_body⟩
def m6ShrinkLowerFn : Fn :=
  ⟨"full_shrink_lower", [i64, i32, i32], [.bool], full_shrink_lower_m6_body⟩
def m6ShrinkBlkFn : Fn :=
  ⟨"full_shrink_blk", [i64, i64, i64, i32, i64], [], full_shrink_blk_m6_body⟩
def m6MinShrinkFn : Fn := ⟨"full_min_shrink", [i64], [], full_min_shrink_m6_body⟩
def m6Deduce1uipFn : Fn := ⟨"full_deduce_1uip", [i64], [i64], full_deduce_1uip_m6_body⟩
def m6AnalyzeFn : Fn := ⟨"full_analyze", [i64], [i64], full_analyze_m6_body⟩

theorem full_dr_init_m6_wf : Func.Wf full_dr_init_m6_body := by t_wf_reify
theorem full_dr_update_m6_wf : Func.Wf full_dr_update_m6_body := by t_wf_reify
theorem full_dr_allow_m6_wf : Func.Wf full_dr_allow_m6_body := by t_wf_reify
theorem full_decide_m6_wf : Func.Wf full_decide_m6_body := by t_wf_reify
theorem full_ana_sift_m6_wf : Func.Wf full_ana_sift_m6_body := by t_wf_reify
theorem full_sort_ana_qs_m6_wf : Func.Wf full_sort_ana_qs_m6_body := by t_wf_reify
theorem full_bump_analyzed_m6_wf : Func.Wf full_bump_analyzed_m6_body := by t_wf_reify
theorem full_restore_bump_ana_m6_wf : Func.Wf full_restore_bump_ana_m6_body := by t_wf_reify
theorem full_min_lit_dfs_m6_wf : Func.Wf full_min_lit_dfs_m6_body := by t_wf_reify
theorem full_min_lit_m6_wf : Func.Wf full_min_lit_m6_body := by t_wf_reify
theorem full_shrink_lower_m6_wf : Func.Wf full_shrink_lower_m6_body := by t_wf_reify
theorem full_shrink_blk_bool_m6_wf : Func.Wf full_shrink_blk_bool_m6_body := by t_wf_reify
theorem full_shrink_blk_m6_wf : Func.Wf full_shrink_blk_m6_body := by t_wf_reify
theorem full_min_shrink_m6_wf : Func.Wf full_min_shrink_m6_body := by t_wf_reify
theorem full_deduce_1uip_m6_wf : Func.Wf full_deduce_1uip_m6_body := by t_wf_reify
theorem full_ana_failed_lit_m6_wf : Func.Wf full_ana_failed_lit_m6_body := by t_wf_reify
theorem full_analyze_m6_wf : Func.Wf full_analyze_m6_body := by t_wf_reify

theorem m6MinShrink_fns_wf : ∀ f ∈ m6MinShrink_fns, f.Wf := by
  simp only [m6MinShrink_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_dr_init_m6_wf, full_dr_update_m6_wf, full_dr_allow_m6_wf, full_decide_m6_wf,
    full_ana_sift_m6_wf, full_sort_ana_qs_m6_wf, full_bump_analyzed_m6_wf,
    full_restore_bump_ana_m6_wf, full_min_lit_dfs_m6_wf, full_min_lit_m6_wf,
    full_shrink_lower_m6_wf, full_shrink_blk_bool_m6_wf, full_shrink_blk_m6_wf,
    full_min_shrink_m6_wf, full_deduce_1uip_m6_wf, full_ana_failed_lit_m6_wf,
    full_analyze_m6_wf⟩

theorem m6MinShrink_acyclic : m6MinShrinkModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6MinShrink

module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M6 Wave 2 (`RC-26b` + `RC-27`): Parse-Time Unit BCP, ProbSAT Walk & VSIDS Rescale

Standalone `FullHdr`-free drop-in C0 overrides (`0` edits to `Full1..3`, `FullM4*`, `FullM5*`, or
`FullHdr`), implementing two high-ROI Wave-2 upgrades:
1. **`RC-26b` (`full_parse_body_m6`):** Eager level-0 unit propagation during DIMACS clause
   ingestion (`src/internal.c:351-364`). Calls canonical `full_ingest_cl` and runs
   `full_propagate` immediately whenever at least one binary/large clause has been added and new
   level-0 units await propagation (saving/restoring `fuel` and `search_ticks`, clearing `oom` on
   abort, and leaving pure `UnitUnsatTrace` paths untouched), satisfying exact canonical
   `Full.fullParseBodySpec`.
2. **`RC-27` (`full_rescale_m6`, ProbSAT `V3b` `full_walk_core_m6`, `full_walk_m6`):**
   - `full_rescale_m6`: finer EVSIDS rescaling (`>> 16ULL`, preserving 12 extra bits of activity
     ranking; exact `Full.fullRescaleSpec`).
   - `full_walk_core_m6` (+ 6 pure/CSR helpers): zero-`malloc`, zero-`double` Q30 integer ProbSAT
     local search in fixed `Mem 64` scratch buffers (`work_stk1`/`work_stk2`/`tarjan_mark`/
     `tarjan_reach`/`wsort`/`scratch_buf`), with `walk.c` piecewise-linear `cb`, adaptive flip
     budget `clamp(2 * ncl, 256, 4096)`, O(deg) CSR break/flip maintenance, and lazy best-phase
     trail, satisfying exact canonical `Full.fullWalkSpec`.
   - `full_walk_m6`: wires `full_warmup` (landed `PR-W1A` `FullM5HeurCore.m5WarmupFn`) directly
     before `full_walk_core_m6` (`src/walk.c:960-965`), satisfying `m6WalkSpec` (identical footprint
     to `Full.fullWarmupSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6WalkParse

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6WalkParse "
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

#define PH_GARB     0x00080000u
#define PH_RED      0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern u64 full_rng_next(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_skip_cl(u64 cnf_end, KissatDimacs *d);
extern u64 full_ingest_cl(FullHdr *h, u64 cnf_end);
extern u64 full_propagate(FullHdr *h);
extern void full_warmup(FullHdr *h);

void full_rescale_m6(FullHdr *h) {
  u64 *sc = (u64 *)h->score;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  while (v < cv) { sc[v] = sc[v] >> 16ULL; v = v + 1ULL; }
  h->scinc = h->scinc >> 16ULL;
  if (h->scinc < (1ULL << 20)) { h->scinc = 1ULL << 20; }
}

u64 full_parse_body_m6(FullHdr *h, u64 cnf_end) {
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
  if (unsat_seen) { return 20ULL; }
  return 1ULL;
}

u64 full_walk_cb_inv_m6(u64 total_lits, u64 ncl, u64 walks_cnt) {
  if ((walks_cnt & 1ULL) == 0ULL || ncl == 0ULL) { return 32768ULL; }
  u64 avg = (total_lits >= (1ULL << 55)) ? 2048ULL : ((total_lits << 8) / ncl);
  u64 cb_q8 = 1894ULL;
  if (avg <= 768ULL) { cb_q8 = 640ULL; }
  else if (avg <= 1024ULL) { cb_q8 = 640ULL + (((avg - 768ULL) * 90ULL) >> 8); }
  else if (avg <= 1280ULL) { cb_q8 = 730ULL + (((avg - 1024ULL) * 217ULL) >> 8); }
  else if (avg <= 1536ULL) { cb_q8 = 947ULL + (((avg - 1280ULL) * 359ULL) >> 8); }
  else if (avg <= 1792ULL) { cb_q8 = 1306ULL + (((avg - 1536ULL) * 588ULL) >> 8); }
  return (1ULL << 24) / cb_q8;
}

u32 full_walk_score_m6(u64 inv_q16, u64 brk) {
  u64 lim = (brk > 30ULL) ? 30ULL : brk;
  u64 inv = (inv_q16 > 65536ULL) ? 65536ULL : inv_q16;
  u64 sc = 1ULL << 30;
  u64 i = 0ULL;
  while (i < lim) {
    sc = (sc * inv) >> 16;
    if (sc <= 1ULL) { return 1u; }
    i = i + 1ULL;
  }
  return (sc == 0ULL) ? 1u : (u32)sc;
}

u64 full_walk_collect_m6(FullHdr *h, u64 max_cl, u64 occ_cap) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  u32 *occ_len = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  while (l < nlits) { occ_len[l] = 0u; l = l + 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  i8 *vals = (i8 *)h->values;
  u64 n = 0ULL;
  u64 tot = 0ULL;
  l = 0ULL;
  while (l < nlits && n < max_cl && tot + 2ULL <= occ_cap) {
    if (vals[l] == (i8)0) {
      u64 off = (u64)wvec[l << 1];
      u64 end = off + (u64)wvec[(l << 1) + 1ULL];
      while (off < end && n < max_cl && tot + 2ULL <= occ_cap) {
        u32 w0 = wstk[off];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if (l < (u64)ot && vals[ot] == (i8)0) {
            scr[n << 1] = ((u32)l) | PW_BIN_FLAG;
            scr[(n << 1) + 1ULL] = ot;
            occ_len[l] = occ_len[l] + 1u;
            occ_len[ot] = occ_len[ot] + 1u;
            tot = tot + 2ULL;
            n = n + 1ULL;
          }
          off = off + 1ULL;
        } else { off = off + 2ULL; }
      }
    }
    l = l + 1ULL;
  }
  u64 p = 0ULL;
  while (p < h->arena_len && n < max_cl) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) == 0u && sz >= 3u) {
      bool root_sat = false;
      u64 unass = 0ULL;
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        i8 lv = vals[lit];
        if (lv > (i8)0) { root_sat = true; break; }
        if (lv == (i8)0) { unass = unass + 1ULL; }
        k = k + 1u;
      }
      if (!root_sat && unass >= 2ULL && unass <= occ_cap - tot) {
        scr[n << 1] = (u32)p; scr[(n << 1) + 1ULL] = 0u;
        k = 0u;
        while (k < sz) {
          u32 lit = ar[p + 3ULL + (u64)k];
          if (vals[lit] == (i8)0) { occ_len[lit] = occ_len[lit] + 1u; }
          k = k + 1u;
        }
        tot = tot + unass;
        n = n + 1ULL;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  return n;
}

u64 full_walk_build_csr_m6(FullHdr *h, u64 ncl, u64 max_cl, u64 occ_cap) {
  u64 nlits = h->cur_vars << 1;
  u32 *occ_off = (u32 *)h->work_stk1;
  u32 *occ_len = (u32 *)h->work_stk2;
  u32 *occ_cur = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  i8 *wv = (i8 *)h->walk_vals;
  u64 acc = 0ULL;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 deg = (u64)occ_len[l];
    if (deg > occ_cap - acc) { deg = occ_cap - acc; occ_len[l] = (u32)deg; }
    occ_off[l] = (u32)acc;
    occ_cur[l] = (u32)acc;
    acc = acc + deg;
    l = l + 1ULL;
  }
  u64 base_sat = max_cl << 1;
  u64 base_upos = max_cl * 3ULL;
  u64 base_ulist = max_cl << 2;
  u64 base_occ = max_cl * 5ULL;
  u64 ulen = 0ULL;
  u64 ci = 0ULL;
  while (ci < ncl) {
    u32 w0 = scr[ci << 1];
    u32 sc = 0u;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 a = w0 & PW_LIT_MASK;
      u32 b = scr[(ci << 1) + 1ULL];
      if (vals[a] == (i8)0) {
        if (wv[a] > (i8)0) { sc = sc + 1u; }
        u64 pos = (u64)occ_cur[a];
        if (pos < occ_cap) { scr[base_occ + pos] = (u32)ci; occ_cur[a] = (u32)(pos + 1ULL); }
      }
      if (vals[b] == (i8)0) {
        if (wv[b] > (i8)0) { sc = sc + 1u; }
        u64 pos = (u64)occ_cur[b];
        if (pos < occ_cap) { scr[base_occ + pos] = (u32)ci; occ_cur[b] = (u32)(pos + 1ULL); }
      }
    } else {
      u32 sz = ar[(u64)w0 + 2ULL];
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[(u64)w0 + 3ULL + (u64)k];
        if (vals[lit] == (i8)0) {
          if (wv[lit] > (i8)0) { sc = sc + 1u; }
          u64 pos = (u64)occ_cur[lit];
          if (pos < occ_cap) {
            scr[base_occ + pos] = (u32)ci; occ_cur[lit] = (u32)(pos + 1ULL);
          }
        }
        k = k + 1u;
      }
    }
    scr[base_sat + ci] = sc;
    if (sc == 0u && ulen < ncl) {
      scr[base_upos + ci] = (u32)ulen;
      scr[base_ulist + ulen] = (u32)ci;
      ulen = ulen + 1ULL;
    } else {
      scr[base_upos + ci] = 0xFFFFFFFFu;
    }
    ci = ci + 1ULL;
  }
  return ulen;
}

u64 full_walk_break_m6(FullHdr *h, u32 lit, u64 ncl, u64 max_cl, u64 occ_cap) {
  u64 nlit = (u64)(lit ^ 1u);
  if (nlit >= (h->cur_vars << 1)) { return 0ULL; }
  u32 *occ_off = (u32 *)h->work_stk1;
  u32 *occ_len = (u32 *)h->work_stk2;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 off = (u64)occ_off[nlit];
  u64 len = (u64)occ_len[nlit];
  if (off > occ_cap || len > occ_cap - off) { return 0ULL; }
  u64 base_sat = max_cl << 1;
  u64 base_occ = max_cl * 5ULL;
  u64 brk = 0ULL;
  u64 k = 0ULL;
  while (k < len) {
    u32 ci = scr[base_occ + off + k];
    if ((u64)ci < ncl && scr[base_sat + (u64)ci] == 1u) { brk = brk + 1ULL; }
    k = k + 1ULL;
  }
  return brk;
}

u32 full_walk_pick_m6(FullHdr *h, u64 ci, u64 ncl, u64 max_cl, u64 occ_cap, u64 inv_q16) {
  u64 cv = h->cur_vars;
  i8 *vals = (i8 *)h->values;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ws = (u32 *)h->wsort;
  u32 w0 = scr[ci << 1];
  u64 m = 0ULL;
  u64 sum_s = 0ULL;
  u64 zcnt = 0ULL;
  u32 zlit = 0xFFFFFFFFu;
  if ((w0 & PW_BIN_FLAG) != 0u) {
    u32 a = w0 & PW_LIT_MASK;
    u32 b = scr[(ci << 1) + 1ULL];
    if (vals[a] == (i8)0 && m < cv) {
      u64 brk = full_walk_break_m6(h, a, ncl, max_cl, occ_cap);
      if (brk == 0ULL) { zcnt = 1ULL; zlit = a; }
      u32 sc = full_walk_score_m6(inv_q16, brk);
      ws[m << 1] = a; ws[(m << 1) + 1ULL] = sc;
      sum_s = sum_s + (u64)sc; m = m + 1ULL;
    }
    if (vals[b] == (i8)0 && m < cv) {
      u64 brk = full_walk_break_m6(h, b, ncl, max_cl, occ_cap);
      if (brk == 0ULL) {
        zcnt = zcnt + 1ULL;
        if (zcnt == 1ULL || (full_rng_next(h) % zcnt) == 0ULL) { zlit = b; }
      }
      u32 sc = full_walk_score_m6(inv_q16, brk);
      ws[m << 1] = b; ws[(m << 1) + 1ULL] = sc;
      sum_s = sum_s + (u64)sc; m = m + 1ULL;
    }
  } else {
    u32 sz = ar[(u64)w0 + 2ULL];
    u32 k = 0u;
    while (k < sz && m < cv) {
      u32 lit = ar[(u64)w0 + 3ULL + (u64)k];
      if (vals[lit] == (i8)0) {
        u64 brk = full_walk_break_m6(h, lit, ncl, max_cl, occ_cap);
        if (brk == 0ULL) {
          zcnt = zcnt + 1ULL;
          if (zcnt == 1ULL || (full_rng_next(h) % zcnt) == 0ULL) { zlit = lit; }
        }
        u32 sc = full_walk_score_m6(inv_q16, brk);
        ws[m << 1] = lit; ws[(m << 1) + 1ULL] = sc;
        sum_s = sum_s + (u64)sc; m = m + 1ULL;
      }
      k = k + 1u;
    }
  }
  if (m == 0ULL) { return 0xFFFFFFFFu; }
  if (zcnt > 0ULL) { return zlit; }
  if (sum_s == 0ULL) { return ws[0]; }
  u64 target = full_rng_next(h) % sum_s;
  u64 acc = 0ULL;
  u64 i = 0ULL;
  while (i < m) {
    acc = acc + (u64)ws[(i << 1) + 1ULL];
    if (acc > target) { return ws[i << 1]; }
    i = i + 1ULL;
  }
  return ws[(m - 1ULL) << 1];
}

u64 full_walk_flip_m6(FullHdr *h, u32 lit, u64 ncl, u64 max_cl, u64 occ_cap, u64 ulen) {
  u64 v = (u64)(lit >> 1);
  if (v >= h->cur_vars) { return ulen; }
  i8 *wv = (i8 *)h->walk_vals;
  u32 *occ_off = (u32 *)h->work_stk1;
  u32 *occ_len = (u32 *)h->work_stk2;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 pos_lit = v << 1;
  u64 old_t = (wv[pos_lit] > (i8)0) ? pos_lit : (pos_lit ^ 1ULL);
  u64 new_t = old_t ^ 1ULL;
  wv[old_t] = (i8)(-1);
  wv[new_t] = (i8)1;
  u64 base_sat = max_cl << 1;
  u64 base_upos = max_cl * 3ULL;
  u64 base_ulist = max_cl << 2;
  u64 base_occ = max_cl * 5ULL;
  u64 off1 = (u64)occ_off[old_t];
  u64 len1 = (u64)occ_len[old_t];
  if (off1 <= occ_cap && len1 <= occ_cap - off1) {
    u64 k = 0ULL;
    while (k < len1) {
      u32 ci = scr[base_occ + off1 + k];
      if ((u64)ci < ncl) {
        u32 sc = scr[base_sat + (u64)ci];
        if (sc > 0u) {
          sc = sc - 1u;
          scr[base_sat + (u64)ci] = sc;
          if (sc == 0u && ulen < ncl && scr[base_upos + (u64)ci] == 0xFFFFFFFFu) {
            scr[base_upos + (u64)ci] = (u32)ulen;
            scr[base_ulist + ulen] = ci;
            ulen = ulen + 1ULL;
          }
        }
      }
      k = k + 1ULL;
    }
  }
  u64 off2 = (u64)occ_off[new_t];
  u64 len2 = (u64)occ_len[new_t];
  if (off2 <= occ_cap && len2 <= occ_cap - off2) {
    u64 k = 0ULL;
    while (k < len2) {
      u32 ci = scr[base_occ + off2 + k];
      if ((u64)ci < ncl) {
        u32 osc = scr[base_sat + (u64)ci];
        scr[base_sat + (u64)ci] = osc + 1u;
        if (osc == 0u && ulen > 0ULL && ulen <= ncl) {
          u32 up = scr[base_upos + (u64)ci];
          if ((u64)up < ulen) {
            ulen = ulen - 1ULL;
            u32 last = scr[base_ulist + ulen];
            scr[base_ulist + (u64)up] = last;
            if ((u64)last < ncl) { scr[base_upos + (u64)last] = up; }
            scr[base_upos + (u64)ci] = 0xFFFFFFFFu;
          }
        }
      }
      k = k + 1ULL;
    }
  }
  return ulen;
}

void full_walk_core_m6(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 cap = h->scratch_cap;
  if (cv == 0ULL || cap < 20ULL) { return; }
  u64 max_cl = cap / 10ULL;
  if (max_cl > 65536ULL) { max_cl = 65536ULL; }
  u64 occ_cap = cap - max_cl * 5ULL;
  u64 ncl = full_walk_collect_m6(h, max_cl, occ_cap);
  if (ncl == 0ULL) { return; }
  u64 nlits = cv << 1;
  u32 *occ_len = (u32 *)h->work_stk2;
  u64 total_lits = 0ULL;
  u64 li = 0ULL;
  while (li < nlits) { total_lits = total_lits + (u64)occ_len[li]; li = li + 1ULL; }
  i8 *vals = (i8 *)h->values;
  i8 *wv = (i8 *)h->walk_vals;
  i8 *wb = (i8 *)h->walk_best;
  i8 *ph = (i8 *)h->phases;
  u64 v = 0ULL;
  while (v < cv) {
    i8 rv = vals[v << 1];
    i8 s = (rv != (i8)0) ? ((rv < (i8)0) ? (i8)(-1) : (i8)1) : ((ph[v] < (i8)0) ? (i8)(-1) : (i8)1);
    wv[v << 1] = s;
    wv[(v << 1) + 1ULL] = (i8)(-s);
    wb[v] = s;
    v = v + 1ULL;
  }
  u64 ulen = full_walk_build_csr_m6(h, ncl, max_cl, occ_cap);
  u64 init_unsat = ulen;
  u64 inv_q16 = full_walk_cb_inv_m6(total_lits, ncl, h->walk_cnt_stat);
  u64 max_flips = ncl << 1;
  if (max_flips < 256ULL) { max_flips = 256ULL; }
  if (max_flips > 4096ULL) { max_flips = 4096ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ftrail = (u32 *)h->tarjan_reach;
  u64 base_ulist = max_cl << 2;
  u64 best_unsat = ulen;
  u64 trail_cap = nlits;
  u64 trail_len = 0ULL;
  u64 best_pos = 0ULL;
  bool trail_valid = true;
  u64 flip = 0ULL;
  while (flip < max_flips && ulen > 0ULL && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    u64 ridx = full_rng_next(h) % ulen;
    u32 ci = scr[base_ulist + ridx];
    if ((u64)ci >= ncl) { break; }
    u32 lit = full_walk_pick_m6(h, (u64)ci, ncl, max_cl, occ_cap, inv_q16);
    if (lit == 0xFFFFFFFFu) { break; }
    ulen = full_walk_flip_m6(h, lit, ncl, max_cl, occ_cap, ulen);
    if (trail_valid) {
      if (trail_len < trail_cap) {
        ftrail[trail_len] = lit >> 1;
        trail_len = trail_len + 1ULL;
      } else {
        u64 ti = 0ULL;
        while (ti < best_pos) {
          u32 fv = ftrail[ti];
          if ((u64)fv < cv) { wb[fv] = (i8)(-wb[fv]); }
          ti = ti + 1ULL;
        }
        best_pos = 0ULL;
        trail_len = 0ULL;
        trail_valid = false;
      }
    }
    if (ulen < best_unsat) {
      best_unsat = ulen;
      if (trail_valid) {
        best_pos = trail_len;
      } else {
        v = 0ULL;
        while (v < cv) { wb[v] = wv[v << 1]; v = v + 1ULL; }
        trail_len = 0ULL;
        best_pos = 0ULL;
        trail_valid = true;
      }
    }
    flip = flip + 1ULL;
  }
  if (trail_valid && best_pos > 0ULL) {
    u64 ti = 0ULL;
    while (ti < best_pos) {
      u32 fv = ftrail[ti];
      if ((u64)fv < cv) { wb[fv] = (i8)(-wb[fv]); }
      ti = ti + 1ULL;
    }
  }
  if (best_unsat < init_unsat) {
    v = 0ULL;
    while (v < cv) { ph[v] = wb[v]; v = v + 1ULL; }
  }
  h->walk_cnt_stat = h->walk_cnt_stat + 1ULL;
}

void full_walk_m6(FullHdr *h) {
  if (h->cur_level == 0ULL && h->dense_mode == 0ULL &&
      h->unassigned > 0ULL && h->fuel > 0ULL && h->oom == 0ULL) {
    full_warmup(h);
  }
  full_walk_core_m6(h);
}
"

/-- External canonical callees referenced by `m6WalkParse_fns`. -/
def m6WalkParseExterns : List Extern :=
  [ ⟨"kissat_skip_ws_comments", [i64, i64], [i64]⟩
  , ⟨"full_rng_next", [i64], [i64]⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool]⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_warmup", [i64], []⟩ ]

/-- Standalone M6 Wave-2 `RC-26b` + `RC-27` module (`11` functions + `7` externs, `0` exits). -/
def m6WalkParseModule : LeanQbe.T.Module :=
  { fns := m6WalkParse_fns, externs := m6WalkParseExterns, exits := [] }

/-! ## Drop-In Replacement `Fn` Handles for `FullM6` Unification -/

def m6RescaleFn : Fn :=
  ⟨"full_rescale", [i64], [], full_rescale_m6_body⟩
def m6ParseBodyFn : Fn :=
  ⟨"full_parse_body", [i64, i64], [i64], full_parse_body_m6_body⟩
def m6WalkCbInvFn : Fn :=
  ⟨"full_walk_cb_inv_m6", [i64, i64, i64], [i64], full_walk_cb_inv_m6_body⟩
def m6WalkScoreFn : Fn :=
  ⟨"full_walk_score_m6", [i64, i64], [i32], full_walk_score_m6_body⟩
def m6WalkCollectFn : Fn :=
  ⟨"full_walk_collect_m6", [i64, i64, i64], [i64], full_walk_collect_m6_body⟩
def m6WalkBuildCsrFn : Fn :=
  ⟨"full_walk_build_csr_m6", [i64, i64, i64, i64], [i64], full_walk_build_csr_m6_body⟩
def m6WalkBreakFn : Fn :=
  ⟨"full_walk_break_m6", [i64, i32, i64, i64, i64], [i64], full_walk_break_m6_body⟩
def m6WalkPickFn : Fn :=
  ⟨"full_walk_pick_m6", [i64, i64, i64, i64, i64, i64], [i32], full_walk_pick_m6_body⟩
def m6WalkFlipFn : Fn :=
  ⟨"full_walk_flip_m6", [i64, i32, i64, i64, i64, i64], [i64], full_walk_flip_m6_body⟩
def m6WalkCoreHelperFn : Fn :=
  ⟨"full_walk_core_m6", [i64], [], full_walk_core_m6_body⟩
def m6WalkCoreFn : Fn :=
  ⟨"full_walk", [i64], [], full_walk_core_m6_body⟩
def m6WalkFn : Fn :=
  ⟨"full_walk", [i64], [], full_walk_m6_body⟩

theorem full_rescale_m6_wf : Func.Wf full_rescale_m6_body := by t_wf_reify
theorem full_parse_body_m6_wf : Func.Wf full_parse_body_m6_body := by t_wf_reify
theorem full_walk_cb_inv_m6_wf : Func.Wf full_walk_cb_inv_m6_body := by t_wf_reify
theorem full_walk_score_m6_wf : Func.Wf full_walk_score_m6_body := by t_wf_reify
theorem full_walk_collect_m6_wf : Func.Wf full_walk_collect_m6_body := by t_wf_reify
theorem full_walk_build_csr_m6_wf : Func.Wf full_walk_build_csr_m6_body := by t_wf_reify
theorem full_walk_break_m6_wf : Func.Wf full_walk_break_m6_body := by t_wf_reify
theorem full_walk_pick_m6_wf : Func.Wf full_walk_pick_m6_body := by t_wf_reify
theorem full_walk_flip_m6_wf : Func.Wf full_walk_flip_m6_body := by t_wf_reify
theorem full_walk_core_m6_wf : Func.Wf full_walk_core_m6_body := by t_wf_reify
theorem full_walk_m6_wf : Func.Wf full_walk_m6_body := by t_wf_reify

theorem m6WalkParse_fns_wf : ∀ f ∈ m6WalkParse_fns, f.Wf := by
  simp only [m6WalkParse_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_rescale_m6_wf, full_parse_body_m6_wf, full_walk_cb_inv_m6_wf, full_walk_score_m6_wf,
    full_walk_collect_m6_wf, full_walk_build_csr_m6_wf, full_walk_break_m6_wf, full_walk_pick_m6_wf,
    full_walk_flip_m6_wf, full_walk_core_m6_wf, full_walk_m6_wf⟩

theorem m6WalkParse_acyclic : m6WalkParseModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6WalkParse

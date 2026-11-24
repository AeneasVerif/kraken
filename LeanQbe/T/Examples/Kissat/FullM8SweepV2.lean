/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM6Sweep
public import LeanQbe.T.Examples.Kissat.FullM8FidV12
public import LeanQbe.T.Examples.Kissat.FullM7Splice
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityCore
import all LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
import all LeanQbe.T.Examples.Kissat.FullM7Splice
import all LeanQbe.T.Examples.Kissat.FullM7
import all LeanQbe.T.Examples.Kissat.FullM5
import all LeanQbe.T.Examples.Kissat.FullM6CongSubst
import all LeanQbe.T.Examples.Kissat.FullM6CompactFlush
import all LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import all LeanQbe.T.Examples.Kissat.FullM6MinShrink
import all LeanQbe.T.Examples.Kissat.FullM6Hdr
import all LeanQbe.T.Examples.Kissat.FullM6VivBackbone
import all LeanQbe.T.Examples.Kissat.FullM6
import all LeanQbe.T.Examples.Kissat.FullM6Orch
import all LeanQbe.T.Examples.Kissat.FullM7Bump
import all LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
import all LeanQbe.T.Examples.Kissat.FullM7Walk
import all LeanQbe.T.Examples.Kissat.FullM7CongHash
import all LeanQbe.T.Examples.Kissat.FullM7CongIte
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M8 Revived Dense Sweep (`V3t2`, Tier B, `FullM8SweepV2`)

Strictly additive (`Class S`) C0 implementation of the tuned `V3t2` sweep module over
`m8FidV12Module` (`413 + 36 = 449` functions, zero ABI/header changes, zero overlap with
`FullM7V2Robust` (`P`)), implementing the `REPORT.md` §6 `V3t2` deltas:
1. `full_m6_sweep_cone`: compute `mv_c`/`mc_c` before `full_k6_init(h, mv_c)`, seed
   isolated xorshift32 state `k[25] = (root_v ^ 0x9E3779B9u) | 1u`.
2. `full_k6_add_clause`: `full_k6_add_ticks(k, 1ULL)` on non-unit clause insert.
3. `full_k6_propagate` & `full_k6_flip`: `(visits >> 4)` scaling and `ticks++` before
   `vals[other] == 1u` in non-binary watch inspection.
4. `full_m6_sweep_rand_phases` & `full_m6_sweep_flip_round`: `k[25]` isolated xorshift32 PRNG
   (`13 / 17 / 5`), refreshing every 32 steps (`(step & 31u) == 0u`), removing `full_rng_next`.
5. `full_m6_sweep_sim`: `round < 2u`, 1 flip round per SIM round, `(u64)k[K6H_TICKS] < sim_lim`
   guard.
6. `full_m6_collect_cands`: pre-filter `dp > 0 && dn > 0 && dp <= 1024 && dn <= 1024` while
   keeping `fl[]` read-only (`REPORT.md` §6.209) so `full_m6_collect_cands_wp` transfers cleanly.
7. `full_m6_sweep_vars` & `full_sweep_dense_m6`: `per_v = 16384ULL`,
   `spent = ((u64)k[K6H_TICKS] << 2) + 512ULL`, and single-pass `full_sweep_dense_m6`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8SweepV2

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM8FidV12

kissat_c0! m8SweepV2 "
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

#define PH_GARB 0x00080000u
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE 1u
#define FL_SWEEP  1024u

#define K6_BIN_FLAG 0x80000000u
#define K6_LIT_MASK 0x7FFFFFFFu

#define K6H_NV       0u
#define K6H_NC       1u
#define K6H_PROP     3u
#define K6H_TRL_END  4u
#define K6H_UNASS    5u
#define K6H_INCONS   6u
#define K6H_QLAST    8u
#define K6H_QSEARCH  9u
#define K6H_QSTAMP   10u
#define K6H_TICKS    11u
#define K6H_ALEN     13u
#define K6H_ACAP     14u
#define K6H_NASSUMP  15u
#define K6H_STATUS   18u
#define K6H_PHASE    19u
#define K6H_MAX_V    21u
#define K6H_MAX_CL   23u

extern u64  full_m6_max_v(u64 cap);
extern void full_k6_add_ticks(u32 *k, u64 delta);
extern void full_k6_init(FullHdr *h, u32 mv);
extern void full_k6_watch(u32 *k, u32 cid, u32 l0, u32 l1);
extern void full_k6_assign(u32 *k, u32 lit, u32 rsn);
extern void full_m6_sweep_refine_sig(FullHdr *h, u32 nv, u32 bit);
extern u64  full_m6_sweep_solve(FullHdr *h, u32 nv, u64 tick_lim);
extern void full_m6_cand_sift(u32 *cands, u32 *deg, u32 i, u32 n);
extern bool full_m6_dense_prop(FullHdr *h);
extern u64  full_m6_sweep_var(FullHdr *h, u32 v, u64 tick_lim);

bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (sz == 0u) { k[K6H_INCONS] = 1u; return true; }
  if (sz == 1u) {
    u32 *vals = k + (32u + 10u * mv);
    u32 ul = lits[0]; u32 uv = vals[ul];
    if (uv == 2u) { k[K6H_INCONS] = 1u; }
    else if (uv == 0u) { full_k6_assign(k, ul, 0xFFFFFFFFu); }
    return true;
  }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN];
  if (nc >= k[K6H_MAX_CL] || off + sz > k[K6H_ACAP]) { return false; }
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  u32 i = 0u;
  while (i < sz) { arena[off + i] = lits[i]; i = i + 1u; }
  k[K6H_ALEN] = off + sz;
  cl_off[nc] = off; cl_sz[nc] = sz;
  k[K6H_NC] = nc + 1u;
  full_k6_add_ticks(k, 1ULL);
  full_k6_watch(k, nc, lits[0], lits[1]);
  return true;
}

u32 full_k6_propagate(u32 *k) {
  u32 mv = k[K6H_MAX_V];
  u32 *trl = k + (32u + 5u * mv); u32 *vals = k + (32u + 10u * mv);
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  u64 ticks = 0ULL;
  while (k[K6H_PROP] < k[K6H_TRL_END]) {
    u32 lit = trl[k[K6H_PROP]]; k[K6H_PROP] = k[K6H_PROP] + 1u;
    u32 nl = lit ^ 1u; u64 visits = 0ULL;
    u32 prev = 0xFFFFFFFFu; u32 w = whead[nl];
    while (w != 0xFFFFFFFFu) {
      u32 nxt = wnext[w]; visits = visits + 1ULL;
      u32 wb = wblit[w]; u32 bv = wb & K6_LIT_MASK;
      u32 bvv = vals[bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          full_k6_add_ticks(k, ticks + (visits >> 4) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign(k, bv, cid); }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
      u32 other = arena[off + (slot ^ 1u)];
      ticks = ticks + 1ULL;
      if (vals[other] == 1u) { wblit[w] = other; prev = w; w = nxt; continue; }
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = arena[off + r];
        if (vals[cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        arena[off + slot] = repl; arena[off + ri] = nl;
        if (prev == 0xFFFFFFFFu) { whead[nl] = nxt; } else { wnext[prev] = nxt; }
        wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
        w = nxt; continue;
      }
      wblit[w] = other; prev = w; w = nxt;
      u32 ov = vals[other];
      if (ov == 2u) {
        full_k6_add_ticks(k, ticks + (visits >> 4) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign(k, other, cid); }
    }
    ticks = ticks + (visits >> 4) + 1ULL;
  }
  full_k6_add_ticks(k, ticks);
  return 0xFFFFFFFFu;
}

bool full_k6_flip(FullHdr *h, u32 lit) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 v = lit >> 1;
  u32 *lvl = k + 32u; u32 *vals = k + (32u + 10u * mv);
  if (k[K6H_STATUS] != 10u || v >= k[K6H_NV] || vals[lit] != 1u || lvl[v] == 0u) {
    return false;
  }
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  u32 w = whead[lit]; u32 prev = 0xFFFFFFFFu;
  u64 visits = 0ULL; u64 ticks = 1ULL; bool ok = true;
  while (w != 0xFFFFFFFFu) {
    u32 nxt = wnext[w]; visits = visits + 1ULL;
    u32 wb = wblit[w]; u32 bv = wb & K6_LIT_MASK;
    if ((wb & K6_BIN_FLAG) != 0u) {
      if (bv == lit || vals[bv] != 1u) { ok = false; break; }
      prev = w; w = nxt; continue;
    }
    if (bv != lit && vals[bv] == 1u) { prev = w; w = nxt; continue; }
    ticks = ticks + 1ULL;
    u32 cid = w >> 1; u32 slot = w & 1u; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
    u32 other = arena[off + (slot ^ 1u)];
    if (other != lit && vals[other] == 1u) {
      wblit[w] = other; prev = w; w = nxt; continue;
    }
    u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
    while (r < sz) {
      u32 cand = arena[off + r];
      if (cand != lit && vals[cand] == 1u) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) { ok = false; break; }
    arena[off + slot] = repl; arena[off + ri] = lit;
    if (prev == 0xFFFFFFFFu) { whead[lit] = nxt; } else { wnext[prev] = nxt; }
    wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
    w = nxt;
  }
  full_k6_add_ticks(k, ticks + (visits >> 4));
  if (!ok) { return false; }
  vals[lit] = 2u; vals[lit ^ 1u] = 1u;
  return true;
}

u64 full_m6_sweep_cone(FullHdr *h, u32 root_v) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0ULL; }
  u32 max_orig = mv * 3u;
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *fl = (u32 *)h->flags;
  u32 mv_c = (mv < 256u) ? mv : 256u; u32 mc_c = (max_orig < 1024u) ? max_orig : 1024u;
  full_k6_init(h, mv_c);
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  k[25] = (root_v ^ 0x9E3779B9u) | 1u;
  u32 nv = 1u; u32 nc = 0u;
  cone_v[0] = root_v; tmk[root_v] = 1u;
  u32 qi = 0u; u32 depth = 0u; bool limit_reached = false;
  while (qi < nv && depth < 2u && !limit_reached && nc < mc_c) {
    u32 layer_end = nv; depth = depth + 1u;
    while (qi < layer_end && !limit_reached && nc < mc_c) {
      u32 cv = cone_v[qi]; u32 cur_tmk = tmk[cv]; u32 map_c = cur_tmk - 1u;
      qi = qi + 1u;
      u32 pol = 0u;
      while (pol < 2u && !limit_reached && nc < mc_c) {
        u32 lit = (cv << 1) | pol;
        u64 off = (u64)wvec[(u64)lit << 1];
        u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
        u64 p = off;
        while (p < end && !limit_reached && nc < mc_c) {
          u32 w0 = wstk[p]; p = p + 1ULL;
          if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 1ULL; continue; }
          u32 ot = w0 & PW_LIT_MASK; u32 ov = ot >> 1;
          if ((u64)ov >= h->cur_vars || (fl[ov] & FL_ACTIVE) == 0u) { continue; }
          i8 ovv = vals[ot];
          if (ovv > (i8)0) { continue; }
          if (ov == cv) {
            if (ot == lit) {
              tmp[0] = (map_c << 1) | pol;
              if (full_k6_add_clause(h, tmp, 1u)) {
                nc = nc + 1u;
                if (k[K6H_INCONS] != 0u) { limit_reached = true; }
              } else { limit_reached = true; }
            }
            continue;
          }
          if (ovv < (i8)0) {
            tmp[0] = (map_c << 1) | pol;
            if (full_k6_add_clause(h, tmp, 1u)) {
              nc = nc + 1u;
              if (k[K6H_INCONS] != 0u) { limit_reached = true; }
            } else { limit_reached = true; }
            continue;
          }
          if (tmk[ov] != 0u && tmk[ov] < cur_tmk) { continue; }
          u32 saved_nv = nv;
          if (tmk[ov] == 0u) {
            if (nv >= mv_c) { limit_reached = true; break; }
            cone_v[nv] = ov; nv = nv + 1u; tmk[ov] = nv;
          }
          tmp[0] = (map_c << 1) | pol;
          tmp[1] = ((tmk[ov] - 1u) << 1) | (ot & 1u);
          if (full_k6_add_clause(h, tmp, 2u)) {
            nc = nc + 1u;
          } else {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            limit_reached = true;
          }
        }
        pol = pol + 1u;
      }
      pol = 0u;
      while (pol < 2u && !limit_reached && nc < mc_c) {
        u32 lit = (cv << 1) | pol;
        u64 off = (u64)wvec[(u64)lit << 1];
        u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
        u64 p = off;
        while (p < end && !limit_reached && nc < mc_c) {
          u32 w0 = wstk[p]; p = p + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
          if (p >= end) { break; }
          u32 cr = wstk[p]; p = p + 1ULL;
          if ((u64)cr + 3ULL > h->arena_len) { continue; }
          u32 sz = ar[(u64)cr + 2ULL];
          if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || sz < 3u ||
              (u64)cr + 3ULL + (u64)sz > h->arena_len) { continue; }
          u32 saved_nv = nv; bool drop = false; u32 cnt = 0u; u32 idx = 0u;
          while (idx < sz) {
            u32 l = ar[(u64)cr + 3ULL + (u64)idx];
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { drop = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if ((fl[lv] & FL_ACTIVE) == 0u) { drop = true; break; }
              u32 ltm = tmk[lv];
              if ((ltm != 0u && ltm < cur_tmk) || (lv == cv && (l & 1u) < pol)) {
                drop = true; break;
              }
              if (ltm == 0u) {
                if (nv >= mv_c) { limit_reached = true; drop = true; break; }
                cone_v[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              tmp[cnt] = ((tmk[lv] - 1u) << 1) | (l & 1u); cnt = cnt + 1u;
            }
            idx = idx + 1u;
          }
          if (drop) {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            continue;
          }
          if (full_k6_add_clause(h, tmp, cnt)) {
            nc = nc + 1u;
            if (k[K6H_INCONS] != 0u) { limit_reached = true; }
          } else {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            limit_reached = true;
          }
        }
        pol = pol + 1u;
      }
    }
  }
  u32 te = k[K6H_TRL_END];
  k[K6H_NV] = nv;
  k[K6H_UNASS] = (te <= nv) ? (nv - te) : 0u;
  if (nv > 0u) {
    u32 *qnext = k + (32u + 3u * mv);
    k[K6H_QLAST] = nv - 1u; k[K6H_QSEARCH] = nv - 1u;
    k[K6H_QSTAMP] = nv; qnext[nv - 1u] = 0xFFFFFFFFu;
  }
  return (u64)nv | ((u64)nc << 16);
}

void full_m6_sweep_rand_phases(FullHdr *h, u32 nv) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *flags = k + (32u + 6u * mv);
  u32 rs = k[25]; if (rs == 0u) { rs = 0x9E3779B9u; }
  rs = rs ^ (rs << 13); rs = rs ^ (rs >> 17); rs = rs ^ (rs << 5);
  u64 rbits = (u64)rs;
  u32 i = 0u;
  while (i < nv) {
    if ((i & 31u) == 0u && i > 0u) {
      rs = rs ^ (rs << 13); rs = rs ^ (rs >> 17); rs = rs ^ (rs << 5);
      rbits = (u64)rs;
    }
    u32 fl = flags[i];
    flags[i] = (fl & (~1u)) | ((u32)rbits & 1u);
    rbits = rbits >> 1; i = i + 1u;
  }
  k[25] = rs;
  k[K6H_PHASE] = k[K6H_PHASE] ^ 1u;
}

u32 full_m6_sweep_flip_round(FullHdr *h, u32 nv) {
  if (nv == 0u) { return 0u; }
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *vals = k + (32u + 10u * mv);
  u32 rs = k[25]; if (rs == 0u) { rs = 0x9E3779B9u; }
  rs = rs ^ (rs << 13); rs = rs ^ (rs >> 17); rs = rs ^ (rs << 5);
  u32 start = rs % nv;
  rs = rs ^ (rs << 13); rs = rs ^ (rs >> 17); rs = rs ^ (rs << 5);
  u64 rbits = (u64)rs;
  u32 flipped = 0u; u32 step = 0u;
  while (step < nv) {
    if ((step & 31u) == 0u && step > 0u) {
      rs = rs ^ (rs << 13); rs = rs ^ (rs >> 17); rs = rs ^ (rs << 5);
      rbits = (u64)rs;
    }
    if ((rbits & 1ULL) != 0ULL) {
      u32 v = start + step;
      if (v >= nv) { v = v - nv; }
      u32 lit = (vals[v << 1] == 1u) ? (v << 1) : ((v << 1) | 1u);
      if (full_k6_flip(h, lit)) { flipped = flipped + 1u; }
    }
    rbits = rbits >> 1; step = step + 1u;
  }
  k[25] = rs;
  return flipped;
}

u32 full_m6_sweep_sim(FullHdr *h, u32 nv, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 i = 0u; while (i < nv) { sig[cone_v[i]] = 0ULL; i = i + 1u; }
  k[K6H_NASSUMP] = 0u;
  u64 st0 = full_m6_sweep_solve(h, nv, tick_lim);
  if (st0 == 20ULL) { return 0xFFFFFFFFu; }
  if (st0 != 10ULL) { return 0u; }
  u32 rbit = 0u; full_m6_sweep_refine_sig(h, nv, rbit); rbit = 1u;
  u64 sim_lim = (tick_lim < 2048ULL) ? tick_lim : 2048ULL;
  u32 round = 0u;
  while (round < 2u && rbit < 64u && (u64)k[K6H_TICKS] < sim_lim && h->fuel > 0ULL) {
    if (full_m6_sweep_flip_round(h, nv) > 0u) {
      full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
    }
    round = round + 1u;
    u64 cur_t = (u64)k[K6H_TICKS];
    if (round < 2u && rbit < 64u && cur_t < sim_lim && h->fuel > 0ULL) {
      k[K6H_NASSUMP] = 0u;
      u64 st = full_m6_sweep_solve(h, nv, sim_lim - cur_t);
      if (st == 20ULL) { return 0xFFFFFFFFu; }
      if (st != 10ULL) { break; }
      full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
    }
  }
  return rbit;
}

u32 full_m6_collect_cands(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv == 0ULL) { return 0u; }
  u32 *cands = (u32 *)h->tarjan_reach; u32 *deg = (u32 *)h->work_stk2;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 nc = 0u; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
      u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
      if (dp > 0ULL && dn > 0ULL && dp <= 1024ULL && dn <= 1024ULL) {
        u64 d = dp + dn;
        deg[v] = (d > 0xFFFFFFFFULL) ? 0xFFFFFFFFu : (u32)d;
        cands[nc] = (u32)v; nc = nc + 1u;
      }
    }
    v = v + 1ULL;
  }
  if (nc < 2u) { return nc; }
  u32 s = nc >> 1;
  while (s > 0u) { s = s - 1u; full_m6_cand_sift(cands, deg, s, nc); }
  u32 end = nc;
  while (end > 1u) {
    end = end - 1u;
    u32 t = cands[0]; cands[0] = cands[end]; cands[end] = t;
    full_m6_cand_sift(cands, deg, 0u, end);
  }
  return nc;
}

u64 full_m6_sweep_vars(FullHdr *h, u64 budget, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (!full_m6_dense_prop(h)) { return 20ULL; }
  u32 nc = full_m6_collect_cands(h);
  if (nc == 0u) { return 1ULL; }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 per_v = 16384ULL;
  u32 ci = 0u; u64 rem_b = budget;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci]; ci = ci + 1u;
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); rem_b = rem_b - 1ULL;
      u64 vlim = (rem_ticks > per_v) ? per_v : rem_ticks;
      if (full_m6_sweep_var(h, v, vlim) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
      u64 spent = ((u64)k[K6H_TICKS] << 2) + 512ULL;
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim) {
  if (full_m6_max_v(h->scratch_cap) == 0ULL || budget == 0ULL || tick_lim == 0ULL) {
    return 1ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark; u64 cv = h->cur_vars;
  u64 i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  if (full_m6_sweep_vars(h, budget, tick_lim) == 20ULL) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}
"

/-! ## 1. Ordered `36` Sweep Helpers + `full_sweep_dense_m6` Replacement -/

def m8sw_full_m6_max_v : Fn := ⟨"full_m6_max_v", [i64], [i64], FullM6Sweep.full_m6_max_v_body⟩
def m8sw_full_k6_add_ticks : Fn := ⟨"full_k6_add_ticks", [i64, i64], [], FullM6Sweep.full_k6_add_ticks_body⟩
def m8sw_full_k6_init : Fn := ⟨"full_k6_init", [i64, i32], [], FullM6Sweep.full_k6_init_body⟩
def m8sw_full_k6_watch : Fn := ⟨"full_k6_watch", [i64, i32, i32, i32], [], FullM6Sweep.full_k6_watch_body⟩
def m8sw_full_k6_assign : Fn := ⟨"full_k6_assign", [i64, i32, i32], [], FullM6Sweep.full_k6_assign_body⟩
def m8sw_full_k6_add_clause : Fn := ⟨"full_k6_add_clause", [i64, i64, i32], [.bool], full_k6_add_clause_body⟩
def m8sw_full_k6_mtf : Fn := ⟨"full_k6_mtf", [i64, i32], [], FullM6Sweep.full_k6_mtf_body⟩
def m8sw_full_k6_backtrack : Fn := ⟨"full_k6_backtrack", [i64, i32], [], FullM6Sweep.full_k6_backtrack_body⟩
def m8sw_full_k6_propagate : Fn := ⟨"full_k6_propagate", [i64], [i32], full_k6_propagate_body⟩
def m8sw_full_k6_ana_clause : Fn :=
  ⟨"full_k6_ana_clause", [i64, i32, i32], [], FullM6Sweep.full_k6_ana_clause_body⟩
def m8sw_full_k6_analyze : Fn := ⟨"full_k6_analyze", [i64, i32], [.bool], FullM6Sweep.full_k6_analyze_body⟩
def m8sw_full_k6_solve : Fn := ⟨"full_k6_solve", [i64, i64], [i64], FullM6Sweep.full_k6_solve_body⟩
def m8sw_full_k6_flip : Fn := ⟨"full_k6_flip", [i64, i32], [.bool], full_k6_flip_body⟩
def m8sw_full_k512_add_live_m6 : Fn :=
  ⟨"full_k512_add_live_m6", [i64, i32, i32], [], FullM6Sweep.full_k512_add_live_m6_body⟩
def m8sw_full_m6_dense_prop_lit : Fn :=
  ⟨"full_m6_dense_prop_lit", [i64, i32], [.bool], FullM6Sweep.full_m6_dense_prop_lit_body⟩
def m8sw_full_m6_dense_prop : Fn := ⟨"full_m6_dense_prop", [i64], [.bool], FullM6Sweep.full_m6_dense_prop_body⟩
def m8sw_full_m6_sweep_cone : Fn := ⟨"full_m6_sweep_cone", [i64, i32], [i64], full_m6_sweep_cone_body⟩
def m8sw_full_m6_sweep_refine_sig : Fn :=
  ⟨"full_m6_sweep_refine_sig", [i64, i32, i32], [], FullM6Sweep.full_m6_sweep_refine_sig_body⟩
def m8sw_full_m6_sweep_rand_phases : Fn :=
  ⟨"full_m6_sweep_rand_phases", [i64, i32], [], full_m6_sweep_rand_phases_body⟩
def m8sw_full_m6_sweep_solve : Fn :=
  ⟨"full_m6_sweep_solve", [i64, i32, i64], [i64], FullM6Sweep.full_m6_sweep_solve_body⟩
def m8sw_full_m6_sweep_flip_round : Fn :=
  ⟨"full_m6_sweep_flip_round", [i64, i32], [i32], full_m6_sweep_flip_round_body⟩
def m8sw_full_m6_sweep_sim : Fn := ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], full_m6_sweep_sim_body⟩
def m8sw_full_m6_sweep_rearm : Fn := ⟨"full_m6_sweep_rearm", [i64, i32], [], FullM6Sweep.full_m6_sweep_rearm_body⟩
def m8sw_full_m6_sweep_build_pht : Fn :=
  ⟨"full_m6_sweep_build_pht", [i64, i32, i64], [], FullM6Sweep.full_m6_sweep_build_pht_body⟩
def m8sw_full_m6_extract_pht : Fn :=
  ⟨"full_m6_extract_pht", [i64, i32, i64], [i32], FullM6Sweep.full_m6_extract_pht_body⟩
def m8sw_full_m6_refine_partition : Fn :=
  ⟨"full_m6_refine_partition", [i64, i32, i32], [i32], FullM6Sweep.full_m6_refine_partition_body⟩
def m8sw_full_m6_sweep_units : Fn :=
  ⟨"full_m6_sweep_units", [i64, i32, i32, i64], [i64], FullM6Sweep.full_m6_sweep_units_body⟩
def m8sw_full_m6_sweep_classes : Fn :=
  ⟨"full_m6_sweep_classes", [i64, i32, i32, i64], [i64], FullM6Sweep.full_m6_sweep_classes_body⟩
def m8sw_full_m6_els_ar : Fn := ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], FullM6Sweep.full_m6_els_ar_body⟩
def m8sw_full_m6_els_lit : Fn := ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], FullM6Sweep.full_m6_els_lit_body⟩
def m8sw_full_m6_els_fold : Fn := ⟨"full_m6_els_fold", [i64, i32], [.bool], FullM6Sweep.full_m6_els_fold_body⟩
def m8sw_full_m6_dense_els : Fn := ⟨"full_m6_dense_els", [i64, i32], [.bool], FullM6Sweep.full_m6_dense_els_body⟩
def m8sw_full_m6_sweep_var : Fn :=
  ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], FullM6Sweep.full_m6_sweep_var_body⟩
def m8sw_full_m6_cand_sift : Fn :=
  ⟨"full_m6_cand_sift", [i64, i64, i32, i32], [], FullM6Sweep.full_m6_cand_sift_body⟩
def m8sw_full_m6_collect_cands : Fn := ⟨"full_m6_collect_cands", [i64], [i32], full_m6_collect_cands_body⟩
def m8sw_full_m6_sweep_vars : Fn := ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_body⟩

def m8SweepDenseFn : Fn := ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], full_sweep_dense_m6_body⟩

def m8SweepV2Helpers : List Fn :=
  [ m8sw_full_m6_max_v, m8sw_full_k6_add_ticks, m8sw_full_k6_init, m8sw_full_k6_watch
  , m8sw_full_k6_assign, m8sw_full_k6_add_clause, m8sw_full_k6_mtf, m8sw_full_k6_backtrack
  , m8sw_full_k6_propagate, m8sw_full_k6_ana_clause, m8sw_full_k6_analyze, m8sw_full_k6_solve
  , m8sw_full_k6_flip, m8sw_full_k512_add_live_m6, m8sw_full_m6_dense_prop_lit, m8sw_full_m6_dense_prop
  , m8sw_full_m6_sweep_cone, m8sw_full_m6_sweep_refine_sig, m8sw_full_m6_sweep_rand_phases
  , m8sw_full_m6_sweep_solve, m8sw_full_m6_sweep_flip_round, m8sw_full_m6_sweep_sim
  , m8sw_full_m6_sweep_rearm, m8sw_full_m6_sweep_build_pht, m8sw_full_m6_extract_pht
  , m8sw_full_m6_refine_partition, m8sw_full_m6_sweep_units, m8sw_full_m6_sweep_classes
  , m8sw_full_m6_els_ar, m8sw_full_m6_els_lit, m8sw_full_m6_els_fold, m8sw_full_m6_dense_els
  , m8sw_full_m6_sweep_var, m8sw_full_m6_cand_sift, m8sw_full_m6_collect_cands, m8sw_full_m6_sweep_vars ]

def m8SweepV2Repls : List Fn :=
  [ m8SweepDenseFn ]

def m8FidV123t2Befores : List (Sym × List Fn) :=
  [ ("full_sweep_dense_m6",
      [ m8sw_full_m6_max_v, m8sw_full_k6_add_ticks, m8sw_full_k6_init, m8sw_full_k6_watch
      , m8sw_full_k6_assign, m8sw_full_k6_add_clause, m8sw_full_k6_mtf, m8sw_full_k6_backtrack
      , m8sw_full_k6_propagate, m8sw_full_k6_ana_clause, m8sw_full_k6_analyze, m8sw_full_k6_solve
      , m8sw_full_k6_flip, m8sw_full_k512_add_live_m6, m8sw_full_m6_dense_prop_lit, m8sw_full_m6_dense_prop
      , m8sw_full_m6_sweep_cone, m8sw_full_m6_sweep_refine_sig, m8sw_full_m6_sweep_rand_phases
      , m8sw_full_m6_sweep_solve, m8sw_full_m6_sweep_flip_round, m8sw_full_m6_sweep_sim
      , m8sw_full_m6_sweep_rearm, m8sw_full_m6_sweep_build_pht, m8sw_full_m6_extract_pht
      , m8sw_full_m6_refine_partition, m8sw_full_m6_sweep_units, m8sw_full_m6_sweep_classes
      , m8sw_full_m6_els_ar, m8sw_full_m6_els_lit, m8sw_full_m6_els_fold, m8sw_full_m6_dense_els
      , m8sw_full_m6_sweep_var, m8sw_full_m6_cand_sift, m8sw_full_m6_collect_cands, m8sw_full_m6_sweep_vars ]) ]

/-- Ordered `449`-function spliced module list for `M8` Tier B (`V12 + V3t2`). -/
def m8FidV123t2Fns : List Fn :=
  patchFns m8SweepV2Repls m8FidV123t2Befores m8FidV12Fns

/-- Closed `449`-function `M8` Tier B module (`0` externs, `0` exits). -/
def m8FidV123t2Module : LeanQbe.T.Module :=
  { m8FidV12Module with fns := m8FidV123t2Fns }

/-! ## 2. Structural Theorems: Well-Formedness, Length `449`, `Nodup`, & Acyclicity -/

theorem full_k6_add_clause_wf : Func.Wf full_k6_add_clause_body := by t_wf_reify
theorem full_k6_propagate_wf : Func.Wf full_k6_propagate_body := by t_wf_reify
theorem full_k6_flip_wf : Func.Wf full_k6_flip_body := by t_wf_reify
theorem full_m6_sweep_cone_wf : Func.Wf full_m6_sweep_cone_body := by t_wf_reify
theorem full_m6_sweep_rand_phases_wf : Func.Wf full_m6_sweep_rand_phases_body := by t_wf_reify
theorem full_m6_sweep_flip_round_wf : Func.Wf full_m6_sweep_flip_round_body := by t_wf_reify
theorem full_m6_sweep_sim_wf : Func.Wf full_m6_sweep_sim_body := by t_wf_reify
theorem full_m6_collect_cands_wf : Func.Wf full_m6_collect_cands_body := by t_wf_reify
theorem full_m6_sweep_vars_wf : Func.Wf full_m6_sweep_vars_body := by t_wf_reify
theorem full_sweep_dense_m6_wf : Func.Wf full_sweep_dense_m6_body := by t_wf_reify

theorem m8SweepV2Helpers_length : m8SweepV2Helpers.length = 36 := by rfl

theorem m8SweepV2Helpers_wf : ∀ h ∈ m8SweepV2Helpers, h.Wf := by
  intro h hh
  simp only [m8SweepV2Helpers, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact FullM6Sweep.full_m6_max_v_wf
  · exact FullM6Sweep.full_k6_add_ticks_wf
  · exact FullM6Sweep.full_k6_init_wf
  · exact FullM6Sweep.full_k6_watch_wf
  · exact FullM6Sweep.full_k6_assign_wf
  · exact full_k6_add_clause_wf
  · exact FullM6Sweep.full_k6_mtf_wf
  · exact FullM6Sweep.full_k6_backtrack_wf
  · exact full_k6_propagate_wf
  · exact FullM6Sweep.full_k6_ana_clause_wf
  · exact FullM6Sweep.full_k6_analyze_wf
  · exact FullM6Sweep.full_k6_solve_wf
  · exact full_k6_flip_wf
  · exact FullM6Sweep.full_k512_add_live_m6_wf
  · exact FullM6Sweep.full_m6_dense_prop_lit_wf
  · exact FullM6Sweep.full_m6_dense_prop_wf
  · exact full_m6_sweep_cone_wf
  · exact FullM6Sweep.full_m6_sweep_refine_sig_wf
  · exact full_m6_sweep_rand_phases_wf
  · exact FullM6Sweep.full_m6_sweep_solve_wf
  · exact full_m6_sweep_flip_round_wf
  · exact full_m6_sweep_sim_wf
  · exact FullM6Sweep.full_m6_sweep_rearm_wf
  · exact FullM6Sweep.full_m6_sweep_build_pht_wf
  · exact FullM6Sweep.full_m6_extract_pht_wf
  · exact FullM6Sweep.full_m6_refine_partition_wf
  · exact FullM6Sweep.full_m6_sweep_units_wf
  · exact FullM6Sweep.full_m6_sweep_classes_wf
  · exact FullM6Sweep.full_m6_els_ar_wf
  · exact FullM6Sweep.full_m6_els_lit_wf
  · exact FullM6Sweep.full_m6_els_fold_wf
  · exact FullM6Sweep.full_m6_dense_els_wf
  · exact FullM6Sweep.full_m6_sweep_var_wf
  · exact FullM6Sweep.full_m6_cand_sift_wf
  · exact full_m6_collect_cands_wf
  · exact full_m6_sweep_vars_wf

theorem m8SweepV2Repls_wf : ∀ r ∈ m8SweepV2Repls, r.Wf := by
  intro r hr
  simp only [m8SweepV2Repls, List.mem_singleton] at hr
  subst hr
  exact full_sweep_dense_m6_wf

private theorem list_nodup_name_eq {α : Type _} (name : α → Sym) {xs : List α}
    (hnd : (xs.map name).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (hnm : name x = name y) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hx hy
    rcases hx with hxa | hx <;> rcases hy with hya | hy
    · exact hxa.trans hya.symm
    · rw [hxa] at hnm
      exact absurd (hnm ▸ List.mem_map.mpr ⟨y, hy, rfl⟩) hnd.1
    · rw [hya] at hnm
      exact absurd (hnm.symm ▸ List.mem_map.mpr ⟨x, hx, rfl⟩) hnd.1
    · exact ih hnd.2 hx hy

private theorem list_nodup_append_unique {α : Type _} (name : α → Sym)
    {xs p1 s1 p2 s2 : List α} {x y : α}
    (hnd : (xs.map name).Nodup)
    (h1 : xs = p1 ++ x :: s1) (h2 : xs = p2 ++ y :: s2)
    (hnm : name x = name y) :
    p1 = p2 ∧ x = y ∧ s1 = s2 := by
  have hx : x ∈ xs := h1 ▸ List.mem_append_right _ List.mem_cons_self
  have hy : y ∈ xs := h2 ▸ List.mem_append_right _ List.mem_cons_self
  have hxy : x = y := list_nodup_name_eq name hnd hx hy hnm
  subst hxy
  have hnd1 := hnd
  rw [h1, List.map_append, List.map_cons, List.nodup_append] at hnd1
  have hnotin1 : name x ∉ p1.map name := fun hm => hnd1.2.2 _ hm _ List.mem_cons_self rfl
  have hnd2 := hnd
  rw [h2, List.map_append, List.map_cons, List.nodup_append] at hnd2
  have hnotin2 : name x ∉ p2.map name := fun hm => hnd2.2.2 _ hm _ List.mem_cons_self rfl
  have heq : p1 ++ x :: s1 = p2 ++ x :: s2 := h1.symm.trans h2
  clear h1 h2 hnd hnd1 hnd2 hx hy hnm
  induction p1 generalizing p2 with
  | nil =>
    cases p2 with
    | nil => simp_all
    | cons b t =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      exfalso; exact hnotin2 (by simp [heq.1])
  | cons a t ih =>
    cases p2 with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      exfalso; exact hnotin1 (by simp [heq.1])
    | cons b t2 =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, htail⟩
      have h1' : name x ∉ t.map name := fun hm => hnotin1 (List.mem_cons_of_mem _ hm)
      have h2' : name x ∉ t2.map name := fun hm => hnotin2 (List.mem_cons_of_mem _ hm)
      rcases ih h1' h2' htail with ⟨rfl, _, rfl⟩
      exact ⟨rfl, rfl, rfl⟩

private theorem take_append_prefix {α : Type _} (l₁ l₂ : List α) {k : Nat} (hk : l₁.length ≤ k) :
    ∀ g ∈ l₁, g ∈ (l₁ ++ l₂).take k := by
  intro g hg
  rw [List.mem_iff_getElem] at hg ⊢
  rcases hg with ⟨i, hi, rfl⟩
  refine ⟨i, by simp; omega, ?_⟩
  simp [List.getElem_take, List.getElem_append_left hi]

private theorem m8FidV12_split_299 :
    ∃ pfx r299 sfx,
      m8FidV12Fns = pfx ++ r299 :: sfx ∧
      r299.name = "full_sweep_dense_m6" ∧
      r299.sig = ("full_sweep_dense_m6", [i64, i64, i64], [i64]) ∧
      (∀ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        (g.name = "full_enter_dense" ∧ g.as = [i64] ∧ g.rs = [.bool] →
          g.sig ∈ pfx.map Fn.sig) ∧
        (g.name ∉ m7FidRepls.map Fn.name ∧ g.name ∉ m8FidV12Repls.map Fn.name →
          g.sig ∈ pfx.map Fn.sig)) := by
  have hm299 : FullM7.m7Fns[299]? = FullM7.m7FnsPart3[23]? := by
    simpa using (m7_get_p3 (k := 23))
  have hf299_spec : FullM7.m7FnsPart3[23]? = some FullM6Orch.m6oSweepDenseM6Fn := by
    t_kernel_rfl
  rw [hf299_spec] at hm299
  have hm7p3_len : FullM7.m7FnsPart3.length = 134 := by t_kernel_rfl
  have hm7_len : FullM7.m7Fns.length = 410 := by
    dsimp only [FullM7.m7Fns]
    rw [List.length_append, List.length_append, m7_p1_len, m7_p2_len, hm7p3_len]
  have hlt : 299 < FullM7.m7Fns.length := by rw [hm7_len]; omega
  have htake : FullM7.m7Fns =
      FullM7.m7Fns.take 299 ++ FullM6Orch.m6oSweepDenseM6Fn :: FullM7.m7Fns.drop 300 := by
    have hg : FullM7.m7Fns[299] = FullM6Orch.m6oSweepDenseM6Fn :=
      Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hm299)
    have hd : FullM7.m7Fns.drop 299 = FullM6Orch.m6oSweepDenseM6Fn :: FullM7.m7Fns.drop 300 := by
      rw [List.drop_eq_getElem_cons hlt, hg]
    exact (List.take_append_drop 299 FullM7.m7Fns).symm.trans
      (congrArg (FullM7.m7Fns.take 299 ++ ·) hd)
  have mfPatchFns_append_local :
      ∀ (fs₁ fs₂ : List Fn),
        mfPatchFns m7FidRepls m7FidBefores (fs₁ ++ fs₂) =
          mfPatchFns m7FidRepls m7FidBefores fs₁ ++ mfPatchFns m7FidRepls m7FidBefores fs₂ := by
    intro fs₁ fs₂
    dsimp only [mfPatchFns]
    exact List.flatMap_append
  have hnm299 : FullM6Orch.m6oSweepDenseM6Fn.name = "full_sweep_dense_m6" := by t_kernel_rfl
  have hsig299 :
      FullM6Orch.m6oSweepDenseM6Fn.sig = ("full_sweep_dense_m6", [i64, i64, i64], [i64]) := by
    t_kernel_rfl
  have hmf : m7FidelityFns =
      mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299) ++
        (mfPatchInsAt m7FidBefores FullM6Orch.m6oSweepDenseM6Fn ++
          [((m7FidRepls.find? (fun x => x.name == FullM6Orch.m6oSweepDenseM6Fn.name)).getD
            FullM6Orch.m6oSweepDenseM6Fn)]) ++
        mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.drop 300) := by
    have mfPatchFns_cons_local :
        ∀ (f : Fn) (fs : List Fn),
          mfPatchFns m7FidRepls m7FidBefores (f :: fs) =
            (mfPatchInsAt m7FidBefores f ++
              [((m7FidRepls.find? (fun x => x.name == f.name)).getD f)]) ++
            mfPatchFns m7FidRepls m7FidBefores fs := fun f fs => by
      dsimp only [mfPatchFns]
      rw [List.flatMap_cons]
    dsimp only [m7FidelityFns]
    conv => lhs; rw [htake]
    rw [mfPatchFns_append_local, mfPatchFns_cons_local, ← List.append_assoc]
  have hins0 : mfPatchInsAt m7FidBefores FullM6Orch.m6oSweepDenseM6Fn = [] := by
    dsimp only [mfPatchInsAt]
    rw [hnm299]
    t_kernel_rfl
  have hrepl0 :
      (m7FidRepls.find? (fun x => x.name == FullM6Orch.m6oSweepDenseM6Fn.name)).getD
        FullM6Orch.m6oSweepDenseM6Fn = FullM6Orch.m6oSweepDenseM6Fn := by
    have hnone : m7FidRepls.find? (fun x => x.name == FullM6Orch.m6oSweepDenseM6Fn.name) = none := by
      rw [hnm299, List.find?_eq_none]
      intro r hr heq
      have hm : r.name ∈ m7FidRepls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
      rw [beq_iff_eq.mp heq] at hm
      exact absurd hm (by decide)
    rw [hnone]; rfl
  rw [hins0, hrepl0, List.nil_append] at hmf
  have hm8 : m8FidV12Fns =
      spliceFns m8FidV12Repls (mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299)) ++
        (m8FidV12Repls.find? (fun x => x.name == FullM6Orch.m6oSweepDenseM6Fn.name)).getD
          FullM6Orch.m6oSweepDenseM6Fn ::
        spliceFns m8FidV12Repls (mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.drop 300)) := by
    dsimp only [m8FidV12Fns]
    conv => lhs; rw [hmf]
    rw [spliceFns_append, spliceFns_append, List.append_assoc]
    simp only [spliceFns, List.map_cons, List.map_nil, List.singleton_append]
  have hrepl8 :
      (m8FidV12Repls.find? (fun x => x.name == FullM6Orch.m6oSweepDenseM6Fn.name)).getD
        FullM6Orch.m6oSweepDenseM6Fn = FullM6Orch.m6oSweepDenseM6Fn := by
    have hnone :
        m8FidV12Repls.find? (fun x => x.name == FullM6Orch.m6oSweepDenseM6Fn.name) = none := by
      rw [hnm299, List.find?_eq_none]
      intro r hr heq
      simp only [m8FidV12Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact absurd (beq_iff_eq.mp heq) (by decide)
    rw [hnone]; rfl
  rw [hrepl8] at hm8
  have hlen12 : (FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2).length ≤ 299 := by
    rw [List.length_append, m7_p1_len, m7_p2_len]; omega
  have h7eq : FullM7.m7Fns = (FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2) ++ FullM7.m7FnsPart3 := by
    dsimp only [FullM7.m7Fns]
  refine ⟨spliceFns m8FidV12Repls (mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299)),
    FullM6Orch.m6oSweepDenseM6Fn, _, hm8, hnm299, hsig299, fun g hg0 => ?_⟩
  have hg : g ∈ FullM7.m7Fns.take 299 := by
    rw [h7eq]
    exact take_append_prefix (FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2) FullM7.m7FnsPart3 hlen12 g hg0
  have hmem_fid :
      ((m7FidRepls.find? (fun x => x.name == g.name)).getD g) ∈
        mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299) := by
    dsimp only [mfPatchFns]
    exact List.mem_flatMap.mpr ⟨g, hg, List.mem_append_right _ List.mem_cons_self⟩
  have hmem_m8 :
      ((m8FidV12Repls.find?
          (fun x => x.name == ((m7FidRepls.find? (fun x => x.name == g.name)).getD g).name)).getD
        ((m7FidRepls.find? (fun x => x.name == g.name)).getD g)) ∈
        spliceFns m8FidV12Repls (mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299)) :=
    List.mem_map.mpr ⟨_, hmem_fid, rfl⟩
  constructor
  · rintro ⟨hgnm, hgas, hgrs⟩
    have hnone1 : m7FidRepls.find? (fun x => x.name == g.name) = none := by
      rw [List.find?_eq_none]
      intro r hr heq
      have hm : r.name ∈ m7FidRepls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
      rw [beq_iff_eq.mp heq, hgnm] at hm
      exact absurd hm (by decide)
    have hfind8 :
        m8FidV12Repls.find? (fun x => x.name == g.name) = some m8EnterDenseFn := by
      rw [hgnm]
      t_kernel_rfl
    have hmem_ed : m8EnterDenseFn ∈
        spliceFns m8FidV12Repls (mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299)) := by
      simpa only [hnone1, Option.getD_none, hfind8, Option.getD_some] using hmem_m8
    have hed_sig : m8EnterDenseFn.sig = ("full_enter_dense", [i64], [.bool]) := by t_kernel_rfl
    have hgsig : g.sig = m8EnterDenseFn.sig := by
      rw [hed_sig]
      exact Prod.ext hgnm (Prod.ext hgas hgrs)
    exact List.mem_map.mpr ⟨m8EnterDenseFn, hmem_ed, hgsig.symm⟩
  · rintro ⟨hn1, hn2⟩
    have hnone1 : m7FidRepls.find? (fun x => x.name == g.name) = none := by
      rw [List.find?_eq_none]
      intro r hr heq
      have hm : r.name ∈ m7FidRepls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
      rw [beq_iff_eq.mp heq] at hm
      exact hn1 hm
    have hnone2 : m8FidV12Repls.find? (fun x => x.name == g.name) = none := by
      rw [List.find?_eq_none]
      intro r hr heq
      have hm : r.name ∈ m8FidV12Repls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
      rw [beq_iff_eq.mp heq] at hm
      exact hn2 hm
    have hmem_g : g ∈
        spliceFns m8FidV12Repls (mfPatchFns m7FidRepls m7FidBefores (FullM7.m7Fns.take 299)) := by
      simpa only [hnone1, Option.getD_none, hnone2, Option.getD_none] using hmem_m8
    exact List.mem_map.mpr ⟨g, hmem_g, rfl⟩

private theorem m8SweepV2Helpers_names_nodup :
    (m8SweepV2Helpers.map Fn.name).Nodup := by
  decide

private theorem mem_spliceFns_name {repls fs : List Fn} {x : Fn}
    (hx : x ∈ spliceFns repls fs) :
    x.name ∈ fs.map Fn.name := by
  rcases List.mem_map.mp hx with ⟨g, hg, rfl⟩
  cases hf : repls.find? (fun r => r.name == g.name) with
  | none =>
    simp only [Option.getD_none]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  | some r =>
    have hnm : r.name = g.name :=
      beq_iff_eq.mp (List.find?_some (p := fun r : Fn => r.name == g.name) hf)
    simp only [Option.getD_some, hnm]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩

private theorem mem_mfPatchFns_name {repls fs : List Fn} {befores : List (Sym × List Fn)}
    {x : Fn} (hx : x ∈ mfPatchFns repls befores fs) :
    x.name ∈ fs.map Fn.name ∨
      ∃ p ∈ befores, x.name ∈ p.2.map Fn.name := by
  dsimp only [mfPatchFns] at hx
  rcases List.mem_flatMap.mp hx with ⟨a, ha, hax⟩
  rcases List.mem_append.mp hax with hins | hrep
  · dsimp only [mfPatchInsAt] at hins
    simp only [List.mem_flatten, List.mem_filterMap] at hins
    rcases hins with ⟨l, ⟨p, hp, hpeq⟩, hxl⟩
    by_cases hpe : (p.1 == a.name) = true
    · simp only [hpe, ↓reduceIte, Option.some.injEq] at hpeq
      subst hpeq
      exact Or.inr ⟨p, hp, List.mem_map.mpr ⟨x, hxl, rfl⟩⟩
    · simp only [hpe] at hpeq
      cases hpeq
  · rcases List.mem_singleton.mp hrep with rfl
    cases hf : repls.find? (fun r => r.name == a.name) with
    | none =>
      simp only [Option.getD_none]
      exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)
    | some r =>
      have hnm : r.name = a.name :=
        beq_iff_eq.mp (List.find?_some (p := fun r : Fn => r.name == a.name) hf)
      simp only [Option.getD_some, hnm]
      exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)

private theorem m8SweepV2Helpers_not_in_m7Fid :
    ∀ h ∈ m8SweepV2Helpers, ¬ h.name ∈ m8FidV12Fns.map Fn.name := by
  have hp1 : ∀ g ∈ FullM7.m7FnsPart1, g.name ∉ m8SweepV2Helpers.map Fn.name := by
    have hall : (FullM7.m7FnsPart1.all
        (fun g => !(m8SweepV2Helpers.map Fn.name).contains g.name)) = true := by
      unfold FullM7.m7FnsPart1
      simp only [List.all_append, Bool.and_eq_true]
      repeat (first | refine ⟨?_, ?_⟩ | exact (by t_kernel_rfl))
    intro g hg hmem
    have hf := List.all_eq_true.mp hall g hg
    simp [hmem] at hf
  have hp2 : ∀ g ∈ FullM7.m7FnsPart2, g.name ∉ m8SweepV2Helpers.map Fn.name := by
    have hall : (FullM7.m7FnsPart2.all
        (fun g => !(m8SweepV2Helpers.map Fn.name).contains g.name)) = true := by
      unfold FullM7.m7FnsPart2
      simp only [List.all_append, Bool.and_eq_true]
      repeat (first | refine ⟨?_, ?_⟩ | exact (by t_kernel_rfl))
    intro g hg hmem
    have hf := List.all_eq_true.mp hall g hg
    simp [hmem] at hf
  have hp3 : ∀ g ∈ FullM7.m7FnsPart3, g.name ∉ m8SweepV2Helpers.map Fn.name := by
    have hall : (FullM7.m7FnsPart3.all
        (fun g => !(m8SweepV2Helpers.map Fn.name).contains g.name)) = true := by
      unfold FullM7.m7FnsPart3
      simp only [List.all_append, Bool.and_eq_true]
      repeat (first | refine ⟨?_, ?_⟩ | exact (by t_kernel_rfl))
    intro g hg hmem
    have hf := List.all_eq_true.mp hall g hg
    simp [hmem] at hf
  intro h hh hmem
  rcases List.mem_map.mp hmem with ⟨x, hx, hnm⟩
  have hx1 := mem_spliceFns_name hx
  rcases List.mem_map.mp hx1 with ⟨y, hy, hynm⟩
  rw [← hynm] at hnm
  rcases mem_mfPatchFns_name hy with hy7 | ⟨p, hp, hxp⟩
  · have hnm_in : h.name ∈ FullM7.m7Fns.map Fn.name := hnm ▸ hy7
    have h7 : FullM7.m7Fns = FullM7.m7FnsPart1 ++ (FullM7.m7FnsPart2 ++ FullM7.m7FnsPart3) := by
      dsimp only [FullM7.m7Fns]; rw [List.append_assoc]
    rw [h7, List.map_append, List.map_append, List.mem_append, List.mem_append] at hnm_in
    have hhm : h.name ∈ m8SweepV2Helpers.map Fn.name := List.mem_map.mpr ⟨h, hh, rfl⟩
    rcases hnm_in with h1 | h2 | h3
    · rcases List.mem_map.mp h1 with ⟨g, hg, hgnm⟩
      exact hp1 g hg (hgnm ▸ hhm)
    · rcases List.mem_map.mp h2 with ⟨g, hg, hgnm⟩
      exact hp2 g hg (hgnm ▸ hhm)
    · rcases List.mem_map.mp h3 with ⟨g, hg, hgnm⟩
      exact hp3 g hg (hgnm ▸ hhm)
  · have hb :
        p.2 = [FullM7FidelityCore.fidBvaMatchLargeFidFn] ∨
        p.2 = [FullM7FidelityCore.fidReorderSiftFidFn] ∨
        p.2 = [FullM7FidelitySearch.fidHdrDecideFn] := by
      dsimp only [m7FidBefores, FullM7FidelityCore.fidCorePatchBefores,
        FullM7FidelitySearch.fidSearchPatchBefores] at hp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (h1 | h2) | h3
      · rw [h1]; simp
      · rw [h2]; simp
      · rw [h3]; simp
    have hhm : h.name ∈ m8SweepV2Helpers.map Fn.name := List.mem_map.mpr ⟨h, hh, rfl⟩
    rw [hnm] at hxp
    rcases hb with hb | hb | hb <;> rw [hb] at hxp <;>
      simp only [List.map_singleton, List.mem_singleton] at hxp <;>
      · rw [hxp] at hhm
        exact absurd hhm (by decide)

private theorem patchFns_len_sum (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ fs : List Fn,
      (patchFns repls befores fs).length =
        fs.length + (fs.map (fun f => (patchInsAt befores f).length)).sum
  | [] => rfl
  | f :: t => by
    have ih := patchFns_len_sum repls befores t
    unfold patchFns at ih ⊢
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem m8FidV123t2Fns_length : m8FidV123t2Fns.length = 449 := by
  have hb_eq : m8FidV123t2Befores = [("full_sweep_dense_m6", m8SweepV2Helpers)] := rfl
  have hsum : (m8FidV12Fns.map (fun f => (patchInsAt m8FidV123t2Befores f).length)).sum = 36 := by
    rw [hb_eq]
    have hnd := m8FidV12Fns_names_nodup
    rcases m8FidV12_split_299 with ⟨pfx, r299, sfx, hm8, hnm, _, _⟩
    rw [hm8]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    have hpfx0 : ∀ g ∈ pfx, (patchInsAt [("full_sweep_dense_m6", m8SweepV2Helpers)] g).length = 0 := by
      intro g hg
      have hne : g.name ≠ "full_sweep_dense_m6" := by
        intro heq
        have hnd' := hnd
        rw [hm8, List.map_append, List.map_cons, List.nodup_append] at hnd'
        exact hnd'.2.2 _ (heq ▸ List.mem_map.mpr ⟨g, hg, rfl⟩) _ List.mem_cons_self hnm.symm
      dsimp only [patchInsAt]
      simp [hne.symm]
    have hsfx0 : ∀ g ∈ sfx, (patchInsAt [("full_sweep_dense_m6", m8SweepV2Helpers)] g).length = 0 := by
      intro g hg
      have hne : g.name ≠ "full_sweep_dense_m6" := by
        intro heq
        have hnd' := hnd
        rw [hm8, List.map_append, List.map_cons, List.nodup_append] at hnd'
        have hc := hnd'.2.1
        rw [List.nodup_cons] at hc
        exact hc.1 (hnm ▸ heq ▸ List.mem_map.mpr ⟨g, hg, rfl⟩)
      dsimp only [patchInsAt]
      simp [hne.symm]
    have hr : (patchInsAt [("full_sweep_dense_m6", m8SweepV2Helpers)] r299).length = 36 := by
      dsimp only [patchInsAt]
      simp [hnm.symm, m8SweepV2Helpers_length]
    have hsum0 : ∀ {fs : List Fn},
        (∀ g ∈ fs, (patchInsAt [("full_sweep_dense_m6", m8SweepV2Helpers)] g).length = 0) →
        (fs.map (fun f => (patchInsAt [("full_sweep_dense_m6", m8SweepV2Helpers)] f).length)).sum = 0 := by
      intro fs hfs
      induction fs with
      | nil => rfl
      | cons a t ih =>
        simp [hfs a List.mem_cons_self, ih fun b hb => hfs b (List.mem_cons_of_mem _ hb)]
    rw [hsum0 hpfx0, hr, hsum0 hsfx0]
  dsimp only [m8FidV123t2Fns]
  have hlen : m8FidV12Fns.length = 413 := by
    dsimp only [m8FidV12Fns]
    rw [spliceFns_length, m7FidelityFns_length]
  rw [patchFns_len_sum, hlen, hsum]

private theorem patchInsAt_single_pos {a : Sym} {hs : List Fn} {f : Fn} (h : a = f.name) :
    patchInsAt [(a, hs)] f = hs := by
  simp [patchInsAt, h]

private theorem patchInsAt_single_neg {a : Sym} {hs : List Fn} {f : Fn} (h : a ≠ f.name) :
    patchInsAt [(a, hs)] f = [] := by
  simp [patchInsAt, h]

private theorem m8FidV12_repl_sig :
    ∀ r ∈ m8SweepV2Repls, ∀ f ∈ m8FidV12Fns, r.name = f.name → r.sig = f.sig := by
  intro r hr f hf hnm
  simp only [m8SweepV2Repls, List.mem_singleton] at hr
  subst hr
  rcases m8FidV12_split_299 with ⟨pfx, r299, sfx, hm8, hrnm, hrsig, _⟩
  have hr299_mem : r299 ∈ m8FidV12Fns := hm8 ▸ List.mem_append_right _ List.mem_cons_self
  have hfeq : f = r299 :=
    list_nodup_name_eq Fn.name m8FidV12Fns_names_nodup hf hr299_mem (hnm.symm.trans hrnm.symm)
  subst hfeq
  exact hrsig.symm

theorem m8FidV123t2Fns_names_nodup : (m8FidV123t2Fns.map Fn.name).Nodup := by
  have hbef : m8FidV123t2Befores = [("full_sweep_dense_m6", m8SweepV2Helpers)] := rfl
  dsimp only [m8FidV123t2Fns]
  refine patchFns_names_nodup m8FidV12Fns_names_nodup m8FidV12_repl_sig ?_ ?_ ?_
  · intro f _
    rw [hbef]
    by_cases hnm : f.name = "full_sweep_dense_m6"
    · rw [patchInsAt_single_pos hnm.symm]
      exact m8SweepV2Helpers_names_nodup
    · rw [patchInsAt_single_neg (Ne.symm hnm)]
      exact List.nodup_nil
  · intro f _ h hh
    rw [hbef] at hh
    by_cases hnm : f.name = "full_sweep_dense_m6"
    · rw [patchInsAt_single_pos hnm.symm] at hh
      exact m8SweepV2Helpers_not_in_m7Fid h hh
    · rw [patchInsAt_single_neg (Ne.symm hnm)] at hh
      cases hh
  · intro f1 _ f2 _ hne h hh1 hh2
    rw [hbef] at hh1 hh2
    by_cases h1 : f1.name = "full_sweep_dense_m6" <;> by_cases h2 : f2.name = "full_sweep_dense_m6"
    · exact absurd (h1.trans h2.symm) hne
    · rw [patchInsAt_single_neg (Ne.symm h2)] at hh2
      simp at hh2
    · rw [patchInsAt_single_neg (Ne.symm h1)] at hh1
      simp at hh1
    · rw [patchInsAt_single_neg (Ne.symm h1)] at hh1
      simp at hh1

private def m8SweepExtSigs : List SigEntry :=
  [ ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
  , ("full_assign_lvl", [i64, i32, i32, i32], [])
  , ("full_backtrack", [i64, i64], [])
  , ("full_propagate", [i64], [i64])
  , ("full_extend_push2", [i64, i32, i32], [.bool])
  , ("full_add_bin", [i64, i32, i32], [i64])
  , ("full_set_inactive", [i64, i32, i32], [])
  , ("full_add_unit", [i64, i32], [.bool])
  , ("full_substitute", [i64], [i64])
  , ("full_enter_dense", [i64], [.bool])
  , ("full_rebuild_watches", [i64], [i64]) ]

private theorem m7P2_mem_ext {g : Fn}
    (hp :
      g = FullM6CompactFlush.m6cfExtendPush2Fn ∨
      g = FullM6OrchAdapters.m6aAddBinFn ∨
      g ∈ (FullM5.m5Fns.drop 108).take 10 ∨
      g ∈ (FullM6CongSubst.m6CongSubst_fns.drop 1).take 3 ∨
      g = FullM6CompactFlush.m6cfEnterDenseFn ∨
      g ∈ (FullM5.m5Fns.drop 146).take 1) :
    g ∈ FullM7.m7FnsPart2 := by
  unfold FullM7.m7FnsPart2
  rcases hp with rfl | rfl | hg | hg | rfl | hg
  · simp only [List.mem_append, List.mem_cons, true_or, or_true]
  · simp only [List.mem_append, List.mem_cons, true_or, or_true]
  · simp only [List.mem_append, hg, true_or, or_true]
  · simp only [List.mem_append, hg, true_or, or_true]
  · simp only [List.mem_append, List.mem_cons, true_or, or_true]
  · simp only [List.mem_append, hg, true_or, or_true]

private theorem option_map_some {α β : Type _} {x : Option α} {f : α → β} {b : β}
    (h : x.map f = some b) : ∃ a, x = some a ∧ f a = b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

theorem m8FidV123t2_acyclic : m8FidV123t2Module.checkAcyclic = true := by
  have m8Ext : m8FidV12Module.externs = [] := by t_kernel_rfl
  have m8Ex : m8FidV12Module.exits = [] := m8FidV12_noExit
  have hbef : m8FidV123t2Befores = [("full_sweep_dense_m6", m8SweepV2Helpers)] := rfl
  dsimp only [m8FidV123t2Module, m8FidV123t2Fns]
  have hnd :
      ((patchFns m8SweepV2Repls m8FidV123t2Befores m8FidV12Module.fns).map Fn.name ++
        m8FidV12Module.externs.map Extern.name).Nodup := by
    rw [m8Ext, List.map_nil, List.append_nil]
    exact m8FidV123t2Fns_names_nodup
  have hExt_ok :
      LeanQbe.T.Module.checkFnsCallsOk [] [] m8SweepExtSigs m8SweepV2Helpers = true := by
    t_kernel_rfl
  have hDense_ok :
      m8SweepDenseFn.checkCallsOk (m8SweepExtSigs ++ m8SweepV2Helpers.map Fn.sig) [] = true := by
    t_kernel_rfl
  rcases m8FidV12_split_299 with ⟨pfx, r299, sfx, hm8, hrnm, _, hk⟩
  have hpfx_sigs : ∀ s ∈ m8SweepExtSigs, s ∈ pfx.map Fn.sig := by
    have mem_p1 : ∀ {k : Nat} {g : Fn}, FullM7.m7FnsPart1[k]? = some g →
        g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2 := fun h =>
      List.mem_append_left _ (List.mem_of_getElem? h)
    have h18_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) :=
      (option_map_some (by t_kernel_rfl : (FullM7.m7FnsPart1[18]?).map Fn.sig =
        some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]))).elim
          fun g hg => ⟨g, mem_p1 hg.1, hg.2⟩
    have h35_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_assign_lvl", [i64, i32, i32, i32], []) :=
      (option_map_some (by t_kernel_rfl : (FullM7.m7FnsPart1[35]?).map Fn.sig =
        some ("full_assign_lvl", [i64, i32, i32, i32], []))).elim
          fun g hg => ⟨g, mem_p1 hg.1, hg.2⟩
    have h39_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_backtrack", [i64, i64], []) :=
      (option_map_some (by t_kernel_rfl : (FullM7.m7FnsPart1[39]?).map Fn.sig =
        some ("full_backtrack", [i64, i64], []))).elim
          fun g hg => ⟨g, mem_p1 hg.1, hg.2⟩
    have h86_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_propagate", [i64], [i64]) :=
      (option_map_some (by t_kernel_rfl : (FullM7.m7FnsPart1[86]?).map Fn.sig =
        some ("full_propagate", [i64], [i64]))).elim
          fun g hg => ⟨g, mem_p1 hg.1, hg.2⟩
    have h180_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_set_inactive", [i64, i32, i32], []) :=
      (option_map_some (by t_kernel_rfl : (((FullM5.m5Fns.drop 108).take 10)[1]?).map Fn.sig =
        some ("full_set_inactive", [i64, i32, i32], []))).elim fun g hg =>
          ⟨g, List.mem_append_right _ (m7P2_mem_ext (Or.inr (Or.inr (Or.inl (List.mem_of_getElem? hg.1))))), hg.2⟩
    have h181_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_add_unit", [i64, i32], [.bool]) :=
      (option_map_some (by t_kernel_rfl : (((FullM5.m5Fns.drop 108).take 10)[2]?).map Fn.sig =
        some ("full_add_unit", [i64, i32], [.bool]))).elim fun g hg =>
          ⟨g, List.mem_append_right _ (m7P2_mem_ext (Or.inr (Or.inr (Or.inl (List.mem_of_getElem? hg.1))))), hg.2⟩
    have h235_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_substitute", [i64], [i64]) :=
      (option_map_some (by t_kernel_rfl : (((FullM6CongSubst.m6CongSubst_fns.drop 1).take 3)[2]?).map Fn.sig =
        some ("full_substitute", [i64], [i64]))).elim fun g hg =>
          ⟨g, List.mem_append_right _
            (m7P2_mem_ext (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_getElem? hg.1)))))), hg.2⟩
    have h237_ex : ∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2,
        g.sig = ("full_rebuild_watches", [i64], [i64]) :=
      (option_map_some (by t_kernel_rfl : (((FullM5.m5Fns.drop 146).take 1)[0]?).map Fn.sig =
        some ("full_rebuild_watches", [i64], [i64]))).elim fun g hg =>
          ⟨g, List.mem_append_right _
            (m7P2_mem_ext (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (List.mem_of_getElem? hg.1))))))), hg.2⟩
    have mem_untouched : ∀ {nm as rs},
        (∃ g ∈ FullM7.m7FnsPart1 ++ FullM7.m7FnsPart2, g.sig = (nm, as, rs)) →
        nm ∉ m7FidRepls.map Fn.name → nm ∉ m8FidV12Repls.map Fn.name →
        (nm, as, rs) ∈ pfx.map Fn.sig := by
      rintro nm as rs ⟨g, hg, hsig⟩ hn1 hn2
      have hgnm : g.name = nm := congrArg Prod.fst hsig
      exact hsig ▸ (hk g hg).2 ⟨hgnm ▸ hn1, hgnm ▸ hn2⟩
    intro s hs
    simp only [m8SweepExtSigs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_untouched h18_ex (by decide) (by decide)
    · exact mem_untouched h35_ex (by decide) (by decide)
    · exact mem_untouched h39_ex (by decide) (by decide)
    · exact mem_untouched h86_ex (by decide) (by decide)
    · exact mem_untouched ⟨FullM6CompactFlush.m6cfExtendPush2Fn,
        List.mem_append_right _ (m7P2_mem_ext (Or.inl rfl)), by t_kernel_rfl⟩ (by decide) (by decide)
    · exact mem_untouched ⟨FullM6OrchAdapters.m6aAddBinFn,
        List.mem_append_right _ (m7P2_mem_ext (Or.inr (Or.inl rfl))), by t_kernel_rfl⟩ (by decide) (by decide)
    · exact mem_untouched h180_ex (by decide) (by decide)
    · exact mem_untouched h181_ex (by decide) (by decide)
    · exact mem_untouched h235_ex (by decide) (by decide)
    · have hed_mem := List.mem_append_right FullM7.m7FnsPart1
        (m7P2_mem_ext (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have heds := (hk FullM6CompactFlush.m6cfEnterDenseFn hed_mem).1
        ⟨by t_kernel_rfl, by t_kernel_rfl, by t_kernel_rfl⟩
      have hed_sig : FullM6CompactFlush.m6cfEnterDenseFn.sig = ("full_enter_dense", [i64], [.bool]) := by
        t_kernel_rfl
      exact hed_sig ▸ heds
    · exact mem_untouched h237_ex (by decide) (by decide)
  refine patchModule_checkAcyclic (M := m8FidV12Module) hnd m8FidV12_acyclic m8FidV12_repl_sig
    ?_ ?_
  · intro pre f post hsplit
    change m8FidV12Fns = pre ++ f :: post at hsplit
    rw [m8Ext, m8Ex, hbef]
    by_cases hnm : f.name = "full_sweep_dense_m6"
    · rw [patchInsAt_single_pos hnm.symm]
      have huniq := list_nodup_append_unique Fn.name m8FidV12Fns_names_nodup hsplit hm8 (hnm.trans hrnm.symm)
      rw [huniq.1, List.map_nil]
      exact checkFnsCallsOk_mono (fun s hs => by
        simp only [List.append_nil] at hs
        exact List.mem_append_left _ (hpfx_sigs s hs)) hExt_ok
    · rw [patchInsAt_single_neg (Ne.symm hnm)]
      rfl
  · intro pre f post r hsplit hr hnm
    simp only [m8SweepV2Repls, List.mem_singleton] at hr
    subst hr
    change m8FidV12Fns = pre ++ f :: post at hsplit
    have huniq := list_nodup_append_unique Fn.name m8FidV12Fns_names_nodup hsplit hm8 (hnm.symm.trans hrnm.symm)
    have hins_eq : patchInsAt m8FidV123t2Befores f = m8SweepV2Helpers := by
      rw [huniq.2.1, hbef, patchInsAt_single_pos hrnm.symm]
    rw [huniq.1, hins_eq, m8Ext, m8Ex]
    simp only [List.map_nil, List.append_nil]
    refine fn_checkCallsOk_mono (fun s hs => ?_) hDense_ok
    rcases List.mem_append.mp hs with hs1 | hs2
    · exact List.mem_append_left _ (hpfx_sigs s hs1)
    · exact List.mem_append_right _ hs2

theorem m8FidV123t2_noExit : m8FidV123t2Module.exits = [] :=
  m8FidV12_noExit

end LeanQbe.T.Examples.Kissat.FullM8SweepV2

end

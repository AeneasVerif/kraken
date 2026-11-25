/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM6Sweep
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM7Splice
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
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
# Kissat Upstream 4.0.4 `sweep.c` Full-Fidelity Parity (`FullFidelitySweep`)

Purely additive C0 layer closing all three upstream Kissat 4.0.4 `sweep.c` algorithmic fidelity
gaps (`GAP-SWP-01`, `GAP-SWP-02`, `GAP-SWP-03`) with zero edits to existing `FullM4*`–`FullM8*`
modules and zero `FullHdr` word-layout growth:

1. **Verified Persistent Storage (`h->glue_used[28..30]`):**
   - `SWP_GU_COMPLETED = 28u`: `solver->statistics.sweep_completed` (`u32`, `0`-initialized).
   - `SWP_GU_INCOMPLETE = 29u`: `solver->sweep_incomplete` (`0u` or `1u`, `0`-initialized).
   - `SWP_GU_CURSOR = 30u`: persistent sweep variable cursor across probing rounds.
   - Disjoint from `FullM7Search` (`gu[36..55]`), `FullM7FidelitySearch` (`gu[56..63]`), and
     `M6HdrExt` (`FullM6Hdr`, `FullM8WaveACore`), while remaining inside `FullMem` so all four
     replaced functions preserve their exact existing `FullM6Sweep` / `FullDefSweep` specs.
2. **`GAP-SWP-01` (`sweep.c:107-138` geometric cone escalation):**
   - `full_m6_sweep_cone` reads `comp = min(gu[28], 5u)`, computing upstream limits
     `vlim = 256u << comp` (`256..8192`), `clim = 1024u << comp` (`1024..32768`), and
     `depth_lim = (comp > 0u) ? 3u : 2u`, clamped to `mv = full_m6_max_v(h->scratch_cap)` and
     `max_orig = 3 * mv` so small `8,192 B` fixtures bail out safely.
   - `full_m6_sweep_sim` uses `sim_lim = tick_lim` so escalated cones with `>= 2048` clauses
     still execute their 2 flip/simulation rounds without artificial starvation.
3. **`GAP-SWP-02` (`sweep.c:1498-1646` persistent `sweep_incomplete` schedule & cursor):**
   - `full_m6_sweep_vars` maintains `sweep_incomplete`, clears `FL_SWEEP` on non-schedulable or
     assigned variables, re-marks schedulable active unassigned variables on fresh rounds, resumes
     from `gu[SWP_GU_CURSOR]` across probings, and increments `gu[SWP_GU_COMPLETED]` on round
     completion.
   - `full_m6_collect_cands` uses escalated `max_occ = 1024u << comp` and scans cyclically from
     `gu[SWP_GU_CURSOR]` while keeping `fl[]` and `gu[]` read-only.
4. **`GAP-SWP-03` (`sweep.c:53-60, 1673` exact `1x` Kitten ticks):**
   - `full_m6_sweep_vars` passes `rem_ticks` directly to `full_m6_sweep_var` and charges
     `spent = (u64)k[K6H_TICKS]` (removing the `per_v = 16384` cap and `((ticks << 2) + 512)`
     multiplier).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweep

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM8SweepV2

/-- `glue_used` word index for persistent `sweep_completed` counter (`sweep.c:107`). -/
def swpGuCompletedIdx : Nat := 28
/-- `glue_used` word index for persistent `sweep_incomplete` flag (`sweep.c:1503`). -/
def swpGuIncompleteIdx : Nat := 29
/-- `glue_used` word index for persistent sweep variable cursor (`sweep.c:1602-1642`). -/
def swpGuCursorIdx : Nat := 30

kissat_c0! fidSweep "
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

#define K6H_NV       0u
#define K6H_TRL_END  4u
#define K6H_UNASS    5u
#define K6H_INCONS   6u
#define K6H_QLAST    8u
#define K6H_QSEARCH  9u
#define K6H_QSTAMP   10u
#define K6H_TICKS    11u
#define K6H_NASSUMP  15u

#define SWP_GU_COMPLETED   28u
#define SWP_GU_INCOMPLETE  29u
#define SWP_GU_CURSOR      30u

extern u64  full_m6_max_v(u64 cap);
extern void full_k6_init(FullHdr *h, u32 mv);
extern bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz);
extern void full_m6_sweep_refine_sig(FullHdr *h, u32 nv, u32 bit);
extern u64  full_m6_sweep_solve(FullHdr *h, u32 nv, u64 tick_lim);
extern u32  full_m6_sweep_flip_round(FullHdr *h, u32 nv);
extern void full_m6_cand_sift(u32 *cands, u32 *deg, u32 i, u32 n);
extern bool full_m6_dense_prop(FullHdr *h);
extern u64  full_m6_sweep_var(FullHdr *h, u32 v, u64 tick_lim);

u64 full_m6_sweep_cone(FullHdr *h, u32 root_v) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0ULL; }
  u32 max_orig = mv * 3u;
  u32 *gu = (u32 *)h->glue_used;
  u32 comp = gu[SWP_GU_COMPLETED];
  if (comp > 5u) { comp = 5u; }
  u32 vlim = 256u << comp;
  u32 clim = 1024u << comp;
  u32 depth_lim = (comp > 0u) ? 3u : 2u;
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *fl = (u32 *)h->flags;
  u32 mv_c = (mv < vlim) ? mv : vlim;
  u32 mc_c = (max_orig < clim) ? max_orig : clim;
  full_k6_init(h, mv_c);
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  k[25] = (root_v ^ 0x9E3779B9u) | 1u;
  u32 nv = 1u; u32 nc = 0u;
  cone_v[0] = root_v; tmk[root_v] = 1u;
  u32 qi = 0u; u32 depth = 0u; bool limit_reached = false;
  while (qi < nv && depth < depth_lim && !limit_reached && nc < mc_c) {
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
  u64 sim_lim = tick_lim;
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
  u32 *gu = (u32 *)h->glue_used;
  u32 comp = gu[SWP_GU_COMPLETED];
  if (comp > 5u) { comp = 5u; }
  u64 max_occ = (u64)(1024u << comp);
  u64 cur = (u64)gu[SWP_GU_CURSOR];
  if (cur >= cv) { cur = 0ULL; }
  u32 *cands = (u32 *)h->tarjan_reach; u32 *deg = (u32 *)h->work_stk2;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 nc = 0u; u64 step = 0ULL;
  while (step < cv) {
    u64 v = cur + step;
    if (v >= cv) { v = v - cv; }
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
      u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
      if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
        u64 d = dp + dn;
        deg[v] = (d > 0xFFFFFFFFULL) ? 0xFFFFFFFFu : (u32)d;
        cands[nc] = (u32)v; nc = nc + 1u;
      }
    }
    step = step + 1ULL;
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
  u64 cv = h->cur_vars;
  if (cv == 0ULL) { return 1ULL; }
  u32 *gu = (u32 *)h->glue_used;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 comp = gu[SWP_GU_COMPLETED];
  if (comp > 5u) { comp = 5u; }
  u64 max_occ = (u64)(1024u << comp);
  bool need_mark = (gu[SWP_GU_INCOMPLETE] == 0u);
  if (!need_mark) {
    u64 rem_inc = 0ULL; u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP)) {
        if (vals[v << 1] == (i8)0) {
          u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
          u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
          if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
            rem_inc = rem_inc + 1ULL;
          } else {
            fl[v] = fl[v] & (~FL_SWEEP);
          }
        } else {
          fl[v] = fl[v] & (~FL_SWEEP);
        }
      }
      v = v + 1ULL;
    }
    if (rem_inc == 0ULL) {
      if (gu[SWP_GU_COMPLETED] < 0xFFFFFFFFu) {
        gu[SWP_GU_COMPLETED] = gu[SWP_GU_COMPLETED] + 1u;
      }
      comp = gu[SWP_GU_COMPLETED];
      if (comp > 5u) { comp = 5u; }
      max_occ = (u64)(1024u << comp);
      need_mark = true;
    }
  }
  if (need_mark) {
    u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
        u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
        if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
          fl[v] = fl[v] | FL_SWEEP;
        } else {
          fl[v] = fl[v] & (~FL_SWEEP);
        }
      } else {
        fl[v] = fl[v] & (~FL_SWEEP);
      }
      v = v + 1ULL;
    }
    gu[SWP_GU_INCOMPLETE] = 1u;
    gu[SWP_GU_CURSOR] = 0u;
  }
  u32 nc = full_m6_collect_cands(h);
  if (nc == 0u) {
    gu[SWP_GU_INCOMPLETE] = 0u;
    gu[SWP_GU_CURSOR] = 0u;
    if (gu[SWP_GU_COMPLETED] < 0xFFFFFFFFu) {
      gu[SWP_GU_COMPLETED] = gu[SWP_GU_COMPLETED] + 1u;
    }
    return 1ULL;
  }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u32 ci = 0u; u64 rem_b = budget;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci]; ci = ci + 1u;
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); rem_b = rem_b - 1ULL;
      gu[SWP_GU_CURSOR] = ((u64)v + 1ULL < cv) ? (v + 1u) : 0u;
      if (full_m6_sweep_var(h, v, rem_ticks) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
      u64 spent = (u64)k[K6H_TICKS];
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  u64 left_inc = 0ULL; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
      u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
      if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
        left_inc = 1ULL;
        break;
      }
      fl[v] = fl[v] & (~FL_SWEEP);
    }
    v = v + 1ULL;
  }
  if (left_inc == 0ULL) {
    gu[SWP_GU_INCOMPLETE] = 0u;
    gu[SWP_GU_CURSOR] = 0u;
    if (gu[SWP_GU_COMPLETED] < 0xFFFFFFFFu) {
      gu[SWP_GU_COMPLETED] = gu[SWP_GU_COMPLETED] + 1u;
    }
  }
  return 1ULL;
}
"

/-! ## 1. Drop-In `Fn` Handles, Replacement List & `449`-Fn Spliced Module -/

def fidSweepConeFn : Fn :=
  ⟨"full_m6_sweep_cone", [i64, i32], [i64], full_m6_sweep_cone_body⟩

def fidSweepSimFn : Fn :=
  ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], full_m6_sweep_sim_body⟩

def fidCollectCandsFn : Fn :=
  ⟨"full_m6_collect_cands", [i64], [i32], full_m6_collect_cands_body⟩

def fidSweepVarsFn : Fn :=
  ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_body⟩

/-- Exact `4`-function drop-in replacement list for `PatchModule` / `FullFidelityAssembly`
(`0` added helpers, exact same signatures & contracts as `FullM8SweepV2`). -/
def fidSweepRepls : List Fn :=
  [ fidSweepConeFn, fidSweepSimFn, fidCollectCandsFn, fidSweepVarsFn ]

/-- Standalone `4`-function extern table for `fidSweep_fns`. -/
def fidSweepExterns : List Extern :=
  [ ⟨"full_m6_max_v", [i64], [i64]⟩
  , ⟨"full_k6_init", [i64, i32], []⟩
  , ⟨"full_k6_add_clause", [i64, i64, i32], [.bool]⟩
  , ⟨"full_m6_sweep_refine_sig", [i64, i32, i32], []⟩
  , ⟨"full_m6_sweep_solve", [i64, i32, i64], [i64]⟩
  , ⟨"full_m6_sweep_flip_round", [i64, i32], [i32]⟩
  , ⟨"full_m6_cand_sift", [i64, i64, i32, i32], []⟩
  , ⟨"full_m6_dense_prop", [i64], [.bool]⟩
  , ⟨"full_m6_sweep_var", [i64, i32, i64], [i64]⟩ ]

/-- Standalone `4`-function module (`9` externs, `0` exits) for quick codegen / legalization. -/
def fidSweepStandModule : LeanQbe.T.Module :=
  { fns := fidSweep_fns, externs := fidSweepExterns, exits := [] }

/-- Ordered `449`-function spliced module list over `FullM8SweepV2.m8FidV123t2Fns`. -/
def fidSweepFns : List Fn :=
  spliceFns fidSweepRepls m8FidV123t2Fns

/-- Closed `449`-function module (`0` externs, `0` exits) patching `fidSweepRepls` onto
`FullM8SweepV2.m8FidV123t2Module`. -/
def fidSweepModule : LeanQbe.T.Module :=
  { m8FidV123t2Module with fns := fidSweepFns }

/-! ## 2. Structural Theorems: Well-Formedness, Length `449`, `Nodup`, & Acyclicity -/

theorem full_m6_sweep_cone_wf : Func.Wf full_m6_sweep_cone_body := by t_wf_reify
theorem full_m6_sweep_sim_wf : Func.Wf full_m6_sweep_sim_body := by t_wf_reify
theorem full_m6_collect_cands_wf : Func.Wf full_m6_collect_cands_body := by t_wf_reify
theorem full_m6_sweep_vars_wf : Func.Wf full_m6_sweep_vars_body := by t_wf_reify

theorem fidSweepRepls_wf : ∀ r ∈ fidSweepRepls, r.Wf := by
  intro r hr
  simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact full_m6_sweep_cone_wf
  · exact full_m6_sweep_sim_wf
  · exact full_m6_collect_cands_wf
  · exact full_m6_sweep_vars_wf

theorem fidSweepStand_acyclic : fidSweepStandModule.checkAcyclic = true := by
  t_kernel_rfl

private theorem fid_sig_of_map {xs : List Fn} {i : Nat} {s : SigEntry}
    (h : xs[i]?.map Fn.sig = some s) : ∃ g, xs[i]? = some g ∧ g.sig = s := by
  cases hg : xs[i]? with
  | none => rw [hg] at h; cases h
  | some g => rw [hg] at h; exact ⟨g, rfl, Option.some.inj h⟩

private theorem fid_nodup_name_eq {xs : List Fn} (hnd : (xs.map Fn.name).Nodup)
    {x y : Fn} (hx : x ∈ xs) (hy : y ∈ xs) (hnm : x.name = y.name) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd (hnm ▸ List.mem_map.mpr ⟨y, hy, rfl⟩) hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map.mpr ⟨x, hx, rfl⟩) hnd.1
    · exact ih hnd.2 hx hy

private theorem fid_mem_pre_of_lt {xs pre post : List Fn} {f g : Fn} {i j : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hsplit : xs = pre ++ f :: post)
    (hi : xs[i]? = some f) (hj : xs[j]? = some g) (hlt : j < i) : g ∈ pre := by
  have hle : i < xs.length := by
    cases Nat.lt_or_ge i xs.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hi; cases hi
  have hlp : pre.length < xs.length := by rw [hsplit, List.length_append]; simp
  have hfp : xs[pre.length]? = some f := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hf1 : xs[pre.length]'hlp = f := Option.some.inj (by rwa [← List.getElem?_eq_getElem hlp])
  have hf2 : xs[i]'hle = f := Option.some.inj (by rwa [← List.getElem?_eq_getElem hle])
  have hpw := List.pairwise_iff_getElem.mp hnd
  have hpre_len : pre.length = i := by
    rcases Nat.lt_trichotomy pre.length i with hlt' | heq | hgt'
    · exact False.elim ((hpw pre.length i (by simp [hlp]) (by simp [hle]) hlt')
        (by simp [hf1, hf2]))
    · exact heq
    · exact False.elim ((hpw i pre.length (by simp [hle]) (by simp [hlp]) hgt')
        (by simp [hf1, hf2]))
  have hj_pre : pre[j]? = some g := by
    rw [hsplit, List.getElem?_append_left (by omega)] at hj; exact hj
  exact List.mem_of_getElem? hj_pre

private theorem fid_slot_299 :
    m8FidV123t2Fns[299]?.map Fn.sig = some ("full_m6_max_v", [i64], [i64]) := by t_kernel_rfl
private theorem fid_slot_301 :
    m8FidV123t2Fns[301]?.map Fn.sig = some ("full_k6_init", [i64, i32], []) := by t_kernel_rfl
private theorem fid_slot_304 :
    m8FidV123t2Fns[304]?.map Fn.sig =
      some ("full_k6_add_clause", [i64, i64, i32], [.bool]) := by t_kernel_rfl
private theorem fid_slot_314 :
    m8FidV123t2Fns[314]?.map Fn.sig =
      some ("full_m6_dense_prop", [i64], [.bool]) := by t_kernel_rfl
private theorem fid_slot_315 :
    m8FidV123t2Fns[315]?.map Fn.sig =
      some ("full_m6_sweep_cone", [i64, i32], [i64]) := by t_kernel_rfl
private theorem fid_slot_316 :
    m8FidV123t2Fns[316]?.map Fn.sig =
      some ("full_m6_sweep_refine_sig", [i64, i32, i32], []) := by t_kernel_rfl
private theorem fid_slot_318 :
    m8FidV123t2Fns[318]?.map Fn.sig =
      some ("full_m6_sweep_solve", [i64, i32, i64], [i64]) := by t_kernel_rfl
private theorem fid_slot_319 :
    m8FidV123t2Fns[319]?.map Fn.sig =
      some ("full_m6_sweep_flip_round", [i64, i32], [i32]) := by t_kernel_rfl
private theorem fid_slot_320 :
    m8FidV123t2Fns[320]?.map Fn.sig =
      some ("full_m6_sweep_sim", [i64, i32, i64], [i32]) := by t_kernel_rfl
private theorem fid_slot_331 :
    m8FidV123t2Fns[331]?.map Fn.sig =
      some ("full_m6_sweep_var", [i64, i32, i64], [i64]) := by t_kernel_rfl
private theorem fid_slot_332 :
    m8FidV123t2Fns[332]?.map Fn.sig =
      some ("full_m6_cand_sift", [i64, i64, i32, i32], []) := by t_kernel_rfl
private theorem fid_slot_333 :
    m8FidV123t2Fns[333]?.map Fn.sig =
      some ("full_m6_collect_cands", [i64], [i32]) := by t_kernel_rfl
private theorem fid_slot_334 :
    m8FidV123t2Fns[334]?.map Fn.sig =
      some ("full_m6_sweep_vars", [i64, i64, i64], [i64]) := by t_kernel_rfl

theorem fidSweep_replSigs :
    ∀ r ∈ fidSweepRepls, ∀ f ∈ m8FidV123t2Fns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨g315, hg315, hs315⟩ := fid_sig_of_map fid_slot_315
  obtain ⟨g320, hg320, hs320⟩ := fid_sig_of_map fid_slot_320
  obtain ⟨g333, hg333, hs333⟩ := fid_sig_of_map fid_slot_333
  obtain ⟨g334, hg334, hs334⟩ := fid_sig_of_map fid_slot_334
  intro r hr f hf hnm
  simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hfg := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hf (List.mem_of_getElem? hg315)
      (hnm.symm.trans (congrArg Prod.fst hs315).symm)
    subst hfg; exact hs315.symm
  · have hfg := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hf (List.mem_of_getElem? hg320)
      (hnm.symm.trans (congrArg Prod.fst hs320).symm)
    subst hfg; exact hs320.symm
  · have hfg := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hf (List.mem_of_getElem? hg333)
      (hnm.symm.trans (congrArg Prod.fst hs333).symm)
    subst hfg; exact hs333.symm
  · have hfg := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hf (List.mem_of_getElem? hg334)
      (hnm.symm.trans (congrArg Prod.fst hs334).symm)
    subst hfg; exact hs334.symm

theorem fidSweepFns_length : fidSweepFns.length = 449 := by
  dsimp only [fidSweepFns, spliceFns]
  rw [List.length_map]; exact m8FidV123t2Fns_length

theorem fidSweepFns_sigs : fidSweepFns.map Fn.sig = m8FidV123t2Fns.map Fn.sig :=
  spliceFns_sigs fidSweep_replSigs

theorem fidSweepFns_names_nodup : (fidSweepFns.map Fn.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) fidSweepFns_sigs
  simp only [List.map_map, Function.comp_def, Fn.sig] at hm
  rw [hm]; exact m8FidV123t2Fns_names_nodup

theorem fidSweep_acyclic : fidSweepModule.checkAcyclic = true := by
  dsimp only [fidSweepModule, fidSweepFns]
  change ({ m8FidV123t2Module with
      fns := spliceFns fidSweepRepls m8FidV123t2Module.fns } :
    LeanQbe.T.Module).checkAcyclic = true
  obtain ⟨g299, hg299, hs299⟩ := fid_sig_of_map fid_slot_299
  obtain ⟨g301, hg301, hs301⟩ := fid_sig_of_map fid_slot_301
  obtain ⟨g304, hg304, hs304⟩ := fid_sig_of_map fid_slot_304
  obtain ⟨g314, hg314, hs314⟩ := fid_sig_of_map fid_slot_314
  obtain ⟨g315, hg315, hs315⟩ := fid_sig_of_map fid_slot_315
  obtain ⟨g316, hg316, hs316⟩ := fid_sig_of_map fid_slot_316
  obtain ⟨g318, hg318, hs318⟩ := fid_sig_of_map fid_slot_318
  obtain ⟨g319, hg319, hs319⟩ := fid_sig_of_map fid_slot_319
  obtain ⟨g320, hg320, hs320⟩ := fid_sig_of_map fid_slot_320
  obtain ⟨g331, hg331, hs331⟩ := fid_sig_of_map fid_slot_331
  obtain ⟨g332, hg332, hs332⟩ := fid_sig_of_map fid_slot_332
  obtain ⟨g333, hg333, hs333⟩ := fid_sig_of_map fid_slot_333
  obtain ⟨g334, hg334, hs334⟩ := fid_sig_of_map fid_slot_334
  have hchkCone : fidSweepConeFn.checkCallsOk
      [("full_m6_max_v", [i64], [i64]), ("full_k6_init", [i64, i32], []),
       ("full_k6_add_clause", [i64, i64, i32], [.bool])] [] = true := by t_kernel_rfl
  have hchkSim : fidSweepSimFn.checkCallsOk
      [("full_m6_max_v", [i64], [i64]), ("full_m6_sweep_refine_sig", [i64, i32, i32], []),
       ("full_m6_sweep_solve", [i64, i32, i64], [i64]),
       ("full_m6_sweep_flip_round", [i64, i32], [i32])] [] = true := by t_kernel_rfl
  have hchkCands : fidCollectCandsFn.checkCallsOk
      [("full_m6_cand_sift", [i64, i64, i32, i32], [])] [] = true := by t_kernel_rfl
  have hchkVars : fidSweepVarsFn.checkCallsOk
      [("full_m6_max_v", [i64], [i64]), ("full_m6_dense_prop", [i64], [.bool]),
       ("full_m6_sweep_var", [i64, i32, i64], [i64]),
       ("full_m6_collect_cands", [i64], [i32])] [] = true := by t_kernel_rfl
  refine spliceModule_checkAcyclic (M := m8FidV123t2Module) m8FidV123t2_acyclic
    fidSweep_replSigs ?_
  intro pre f post r hsplit hr hnm
  change m8FidV123t2Fns = pre ++ f :: post at hsplit
  have hfm : f ∈ m8FidV123t2Fns := hsplit ▸ List.mem_append_right _ List.mem_cons_self
  have hEx : m8FidV123t2Module.exits = [] := m8FidV123t2_noExit
  rw [hEx]
  have addPre : ∀ {i j : Nat} {g : Fn} {s : SigEntry},
      m8FidV123t2Fns[i]? = some f → m8FidV123t2Fns[j]? = some g → j < i → g.sig = s →
      s ∈ pre.map Fn.sig ++ m8FidV123t2Module.externs.map Extern.sig := fun hi hj hlt hs =>
    List.mem_append_left _ (hs ▸ List.mem_map_of_mem
      (fid_mem_pre_of_lt m8FidV123t2Fns_names_nodup hsplit hi hj hlt))
  simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hfeq : f = g315 := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hfm
      (List.mem_of_getElem? hg315) (hnm.symm.trans (congrArg Prod.fst hs315).symm)
    subst hfeq
    refine fn_checkCallsOk_mono (fun s hs => ?_) hchkCone
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact addPre hg315 hg299 (by decide) hs299
    · exact addPre hg315 hg301 (by decide) hs301
    · exact addPre hg315 hg304 (by decide) hs304
  · have hfeq : f = g320 := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hfm
      (List.mem_of_getElem? hg320) (hnm.symm.trans (congrArg Prod.fst hs320).symm)
    subst hfeq
    refine fn_checkCallsOk_mono (fun s hs => ?_) hchkSim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact addPre hg320 hg299 (by decide) hs299
    · exact addPre hg320 hg316 (by decide) hs316
    · exact addPre hg320 hg318 (by decide) hs318
    · exact addPre hg320 hg319 (by decide) hs319
  · have hfeq : f = g333 := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hfm
      (List.mem_of_getElem? hg333) (hnm.symm.trans (congrArg Prod.fst hs333).symm)
    subst hfeq
    refine fn_checkCallsOk_mono (fun s hs => ?_) hchkCands
    simp only [List.mem_singleton] at hs; subst hs
    exact addPre hg333 hg332 (by decide) hs332
  · have hfeq : f = g334 := fid_nodup_name_eq m8FidV123t2Fns_names_nodup hfm
      (List.mem_of_getElem? hg334) (hnm.symm.trans (congrArg Prod.fst hs334).symm)
    subst hfeq
    refine fn_checkCallsOk_mono (fun s hs => ?_) hchkVars
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact addPre hg334 hg299 (by decide) hs299
    · exact addPre hg334 hg314 (by decide) hs314
    · exact addPre hg334 hg331 (by decide) hs331
    · exact addPre hg334 hg333 (by decide) hs333

theorem fidSweep_noExit : fidSweepModule.exits = [] :=
  m8FidV123t2_noExit

end LeanQbe.T.Examples.Kissat.FullFidelitySweep

end

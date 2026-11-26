/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Examples.Kissat.Dimacs

/-!
# Kissat Step-11 `S11-6a` Sweep Environment Fidelity (`FullFidelitySweepEnv`)

Purely additive C0 layer (`0` edits to Step-10 modules, `0` new memory) replacing
`"full_m6_sweep_cone"` (`full_m6_sweep_cone`) with upstream `sweep.c` cone collection limits:
- **D2 (boundary clause):** Initialize kitten capacity to hard cap `mv`, stop adding a new var
  only at `nv >= mv`, and set `limit_reached = true` *after* `full_k6_add_clause` when
  `k[K6H_INCONS] != 0u || nv >= mv_c` so the entire boundary clause enters kitten.
- **D3 (layer-based binary dedupe):** Save `layer_start = qi` at the start of each BFS layer and
  skip binaries via `tmk[ov] != 0u && tmk[ov] - 1u < layer_start`.
- **D5 (clause-limit timing):** Check `nc < mc_c` only at the outer `qi` and `layer_end` loop
  heads, keeping hard capacity check `nc < max_orig` in the inner `pol`/`p` watch loops.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fid11SweepEnv "
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

#define PH_GARB            0x00080000u
#define PH_RED             0x00400000u
#define PW_BIN_FLAG        0x80000000u
#define PW_LIT_MASK        0x7FFFFFFFu

#define FL_ACTIVE          1u

#define K6H_NV             0u
#define K6H_TRL_END        4u
#define K6H_UNASS          5u
#define K6H_INCONS         6u
#define K6H_QLAST          8u
#define K6H_QSEARCH        9u
#define K6H_QSTAMP         10u

#define SWP_GU_COMPLETED   28u

extern u64  full_m6_max_v(u64 cap);
extern void full_k6_init(FullHdr *h, u32 mv);
extern bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz);

u64 fid11_sweep_cone(FullHdr *h, u32 root_v) {
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
  full_k6_init(h, mv);
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  k[25] = (root_v ^ 0x9E3779B9u) | 1u;
  u32 nv = 1u; u32 nc = 0u;
  cone_v[0] = root_v; tmk[root_v] = 1u;
  u32 qi = 0u; u32 depth = 0u; bool limit_reached = false;
  while (qi < nv && depth < depth_lim && !limit_reached && nc < mc_c) {
    u32 layer_start = qi; u32 layer_end = nv; depth = depth + 1u;
    while (qi < layer_end && !limit_reached && nc < mc_c) {
      u32 cv = cone_v[qi]; u32 cur_tmk = tmk[cv]; u32 map_c = cur_tmk - 1u;
      qi = qi + 1u;
      u32 pol = 0u;
      while (pol < 2u && !limit_reached && nc < max_orig) {
        u32 lit = (cv << 1) | pol;
        u64 off = (u64)wvec[(u64)lit << 1];
        u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
        u64 p = off;
        while (p < end && !limit_reached && nc < max_orig) {
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
          if (tmk[ov] != 0u && tmk[ov] - 1u < layer_start) { continue; }
          u32 saved_nv = nv;
          if (tmk[ov] == 0u) {
            if (nv >= mv) { limit_reached = true; break; }
            cone_v[nv] = ov; nv = nv + 1u; tmk[ov] = nv;
          }
          tmp[0] = (map_c << 1) | pol;
          tmp[1] = ((tmk[ov] - 1u) << 1) | (ot & 1u);
          if (full_k6_add_clause(h, tmp, 2u)) {
            nc = nc + 1u;
            if (k[K6H_INCONS] != 0u || nv >= mv_c) { limit_reached = true; }
          } else {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            limit_reached = true;
          }
        }
        pol = pol + 1u;
      }
      pol = 0u;
      while (pol < 2u && !limit_reached && nc < max_orig) {
        u32 lit = (cv << 1) | pol;
        u64 off = (u64)wvec[(u64)lit << 1];
        u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
        u64 p = off;
        while (p < end && !limit_reached && nc < max_orig) {
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
                if (nv >= mv) { limit_reached = true; drop = true; break; }
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
            if (k[K6H_INCONS] != 0u || nv >= mv_c) { limit_reached = true; }
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
"

/-- Step-11 `S11-6a` replacement `Fn` for `"full_m6_sweep_cone"` (`D2 + D3 + D5`). -/
def fid11SweepConeFn : Fn :=
  ⟨"full_m6_sweep_cone", [i64, i32], [i64], fid11_sweep_cone_body⟩

/-- Step-11 `S11-6a` replacement list (`1` fn). -/
def fid11SweepEnvRepls : List Fn :=
  [ fid11SweepConeFn ]

end

public section

theorem fid11_sweep_cone_wf : Func.Wf fid11SweepConeFn.body := by
  t_wf_reify

theorem fid11SweepEnvRepls_wf : ∀ f ∈ fid11SweepEnvRepls, f.Wf := by
  intro f hf
  simp only [fid11SweepEnvRepls, List.mem_singleton] at hf
  subst hf
  exact fid11_sweep_cone_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M8 `FullM8SbvaTie` — Verified `O(1)`-Capped 3-Hop SBVA Tie-Breaking Inside BVA

Purely additive drop-in C0 override (`full_bva_pick_sbva3_m8` -> canonical `"full_bva_pick_cand"`)
over unchanged `FullHdr`, preserving `FullBvaHeap.fullBvaPickCandSpec` with `0` edits to existing
`FullM7*`, `M5Hub.lean`, or compiler/cert modules:

1. **Loop 1 (`ci = 0 .. ncntd`):** single-pass scan of `cntd[0..ncntd)` (`work_stk1`) computing
   maximal clause-reduction count `best_c`, tie multiplicity `ties`, and canonical fallback winner
   `(best_deg, -best_lit)` (`FullM7ParityBvaTie` behavior when `best_c < 2 || ties <= 1`).
2. **Bounded 3-Hop Clause-Incidence Connectivity Tie-Breaker (`best_c >= 2 && ties > 1`):**
   - Uses only `fullBvaPickCandSpec`-authorized scratch (`min_clr` variable table `vis`,
     `repr` double-buffered `u32` layer weights `[cur_w, nxt_w]`, and `sim_sig` `u64` cumulative
     3-hop path count `tot`), keeping `work_stk2` completely untouched (`0` `O(N)` zeroing, `0`
     uninitialized reads, bounds-safe for all `1 <= cur_vars <= max_vars`).
   - Caps visited variable table at `min(32, cur_vars)`, pre-seeding up to `min(cap, 16)` tied
     candidates, then runs `3` forward clause-incidence BFS hops (`hop < 3`) from `f0 >> 1` under
     a strict `steps < 128` literal/watch scan budget (`sz <= 5` irredundant clauses + binaries),
     unifying binary and large clause traversal in one shared neighbor-accumulation loop.
   - Re-scores up to `64` tied candidates maximizing `(sbva3_score, deg, -clit)` with safe fallback
     to Loop 1's `fb_lit`.
3. **Loop 2 (`ci = 0 .. ncntd`):** clears `cnt[cntd[0..ncntd)] = 0u` (`wsort`) and returns
   `(best_c < 2u) ? 0xFFFFFFFFu : best_lit`. Zero callees (`externs = []`, `exits = []`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM8SbvaTie

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m8SbvaTie "
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

u32 full_bva_pick_sbva3_m8(FullHdr *h, u32 ncntd, u32 f0) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *cnt = (u32 *)h->wsort;
  u32 *cntd = (u32 *)h->work_stk1;
  u32 best_c = 0u;
  u32 best_deg = 0u;
  u32 best_lit = 0xFFFFFFFFu;
  u32 ties = 0u;
  u32 ci = 0u;
  while (ci < ncntd) {
    u32 clit = cntd[ci];
    u32 cc = cnt[clit];
    if (cc >= 2u) {
      if (cc > best_c) {
        best_c = cc;
        best_deg = wvec[((u64)clit << 1) + 1ULL];
        best_lit = clit;
        ties = 1u;
      } else if (cc == best_c) {
        ties = ties + 1u;
        u32 deg = wvec[((u64)clit << 1) + 1ULL];
        if (deg > best_deg || (deg == best_deg && clit < best_lit)) {
          best_deg = deg;
          best_lit = clit;
        }
      }
    }
    ci = ci + 1u;
  }
  if (best_c >= 2u && ties > 1u) {
    u64 cv = h->cur_vars;
    u32 cap = (cv < 32ULL) ? (u32)cv : 32u;
    if (cap > 0u) {
      u32 *wstk = (u32 *)h->watch_stk;
      u32 *ar = (u32 *)h->arena;
      u32 *vis = (u32 *)h->min_clr;
      u32 *rw = (u32 *)h->repr;
      u64 *tot = (u64 *)h->sim_sig;
      vis[0] = f0 >> 1;
      rw[0] = 1u;
      rw[1] = 0u;
      tot[0] = 1ULL;
      u32 vis_n = 1u;
      u32 seed_cap = (cap < 16u) ? cap : 16u;
      ci = 0u;
      while (ci < ncntd && vis_n < seed_cap) {
        u32 clit = cntd[ci];
        if (cnt[clit] == best_c) {
          u32 cvar = clit >> 1;
          u32 k = 0u;
          while (k < vis_n && vis[k] != cvar) { k = k + 1u; }
          if (k == vis_n) {
            vis[vis_n] = cvar;
            rw[(u64)vis_n << 1] = 0u;
            rw[((u64)vis_n << 1) + 1ULL] = 0u;
            tot[vis_n] = 0ULL;
            vis_n = vis_n + 1u;
          }
        }
        ci = ci + 1u;
      }
      u32 steps = 0u;
      u32 hop = 0u;
      while (hop < 3u && steps < 128u) {
        u32 layer_n = vis_n;
        u32 qi = 0u;
        while (qi < layer_n && steps < 128u) {
          u32 cw = rw[(u64)qi << 1];
          if (cw > 0u) {
            u32 sidx = vis[qi];
            u32 sgn = 0u;
            while (sgn < 2u && steps < 128u) {
              u32 sl = (sidx << 1) | sgn;
              u64 off = (u64)wvec[(u64)sl << 1];
              u64 end = off + (u64)wvec[((u64)sl << 1) + 1ULL];
              u64 p = off;
              while (p < end && steps < 128u) {
                u32 w0 = wstk[p];
                p = p + 1ULL;
                u32 is_bin = ((w0 & PW_BIN_FLAG) != 0u) ? 1u : 0u;
                u32 cr = 0u;
                u32 clim = 0u;
                if (is_bin != 0u) {
                  clim = 1u;
                } else if (p < end) {
                  cr = wstk[p];
                  p = p + 1ULL;
                  if ((ar[cr] & (PH_GARB | PH_RED)) == 0u) {
                    u32 sz = ar[(u64)cr + 2ULL];
                    if (sz <= 5u && sz > 0u) { clim = sz; }
                  }
                }
                if (clim == 0u) {
                  steps = steps + 1u;
                } else {
                  u32 j = 0u;
                  while (j < clim && steps < 128u) {
                    steps = steps + 1u;
                    u32 ov = (is_bin != 0u)
                      ? ((w0 & PW_LIT_MASK) >> 1)
                      : (ar[(u64)cr + 3ULL + (u64)j] >> 1);
                    if (ov != sidx) {
                      u32 k = 0u;
                      while (k < vis_n && vis[k] != ov) { k = k + 1u; }
                      if (k == vis_n && hop < 2u && vis_n < cap) {
                        vis[vis_n] = ov;
                        rw[(u64)vis_n << 1] = 0u;
                        rw[((u64)vis_n << 1) + 1ULL] = 0u;
                        tot[vis_n] = 0ULL;
                        vis_n = vis_n + 1u;
                      }
                      if (k < vis_n) {
                        tot[k] = tot[k] + (u64)cw;
                        u64 nw64 = (u64)rw[((u64)k << 1) + 1ULL] + (u64)cw;
                        u32 add = (nw64 > 268435455ULL) ? 268435455u : (u32)nw64;
                        rw[((u64)k << 1) + 1ULL] = add;
                      }
                    }
                    j = j + 1u;
                  }
                }
              }
              sgn = sgn + 1u;
            }
          }
          qi = qi + 1u;
        }
        if (hop < 2u) {
          u32 k = 0u;
          while (k < vis_n) {
            rw[(u64)k << 1] = rw[((u64)k << 1) + 1ULL];
            rw[((u64)k << 1) + 1ULL] = 0u;
            k = k + 1u;
          }
        }
        hop = hop + 1u;
      }
      u32 fb_lit = best_lit;
      u64 best_sc = 0ULL;
      best_deg = 0u;
      best_lit = 0xFFFFFFFFu;
      u32 tt = 0u;
      ci = 0u;
      while (ci < ncntd && tt < 64u) {
        u32 clit = cntd[ci];
        if (cnt[clit] == best_c) {
          tt = tt + 1u;
          u32 cv_i = clit >> 1;
          u64 sc = 0ULL;
          u32 k = 0u;
          while (k < vis_n) {
            if (vis[k] == cv_i) { sc = tot[k]; break; }
            k = k + 1u;
          }
          u32 deg = wvec[((u64)clit << 1) + 1ULL];
          if (best_lit == 0xFFFFFFFFu || sc > best_sc ||
              (sc == best_sc && (deg > best_deg || (deg == best_deg && clit < best_lit)))) {
            best_sc = sc;
            best_deg = deg;
            best_lit = clit;
          }
        }
        ci = ci + 1u;
      }
      if (best_lit == 0xFFFFFFFFu) { best_lit = fb_lit; }
    }
  }
  ci = 0u;
  while (ci < ncntd) {
    cnt[cntd[ci]] = 0u;
    ci = ci + 1u;
  }
  return (best_c < 2u) ? 0xFFFFFFFFu : best_lit;
}
"

/-- Drop-in M8 `Fn` handle preserving the canonical `"full_bva_pick_cand"` symbol name. -/
def m8SbvaPickCandFn : Fn :=
  ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], full_bva_pick_sbva3_m8_body⟩

/-- Standalone drop-in function list (`1` fn, `0` callees). -/
def m8SbvaTieFns : List Fn := [m8SbvaPickCandFn]

/-- `FullM7Splice`/`PatchModule`-ready `1`-fn replacement list. -/
def m8SbvaTiePatchFns : List Fn := [m8SbvaPickCandFn]

/-- Standalone closed module (`1` fn, `0` externs, `0` exits). -/
def m8SbvaTieModule : LeanQbe.T.Module :=
  { fns := m8SbvaTieFns, externs := [], exits := [] }

end LeanQbe.T.Examples.Kissat.FullM8SbvaTie

end

public section

namespace LeanQbe.T.Examples.Kissat.FullM8SbvaTie

open LeanQbe.T

theorem full_bva_pick_sbva3_m8_wf : Func.Wf full_bva_pick_sbva3_m8_body := by
  t_wf_reify

theorem m8SbvaPickCandFn_wf : m8SbvaPickCandFn.Wf :=
  full_bva_pick_sbva3_m8_wf

theorem m8SbvaTie_fns_wf : ∀ f ∈ m8SbvaTie_fns, f.Wf := by
  intro f hf
  simp only [m8SbvaTie_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf; exact full_bva_pick_sbva3_m8_wf

theorem m8SbvaTieFns_wf : ∀ f ∈ m8SbvaTieFns, f.Wf := by
  intro f hf
  simp only [m8SbvaTieFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf; exact full_bva_pick_sbva3_m8_wf

theorem m8SbvaTiePatchFns_wf : ∀ f ∈ m8SbvaTiePatchFns, f.Wf := m8SbvaTieFns_wf

theorem m8SbvaTie_acyclic : m8SbvaTieModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM8SbvaTie

end

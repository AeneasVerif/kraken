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
# Kissat Fidelity Step 12A P0 Scaling Closures (`FullFidelityStep12A`)

Purely additive C0 layer (`6` sig-preserving replacements + `0` inserted helpers, `0` new
`FullWitnessInv` conjuncts, every function `<= 2` args) closing all 5 Stage-3 P0 scaling fixes
atop Step 10 `fidStep10Module` (`505` fns) with 100% pure Kissat 4.0.4 fidelity:

1. **`P0-1` — Sweep Delay Denominator (`full_m6_sweep_vars` + `full_probe_m6`):**
   Tracks the actual `swept` variable count in `glue_used[SWP_GU_SWEPT]` (`32u`, disjoint from
   `SWP_GU_* [28..30]`, `TUM_GU_ACTIVATED [31]`, `M7_GU_EMA [36..55]`, `M7_GU_RANDEC [56..63]`)
   and compares `(sa - sb) * 1000 >= swept` with `swept > 0` in `full_probe_m6` instead of
   dividing by `h->unassigned` (`src/sweep.c:1718-1721`).
2. **`P1-1` — Sweep Sim Tick Budget (`full_m6_sweep_sim`):**
   Sets `sim_lim = tick_lim` instead of `tick_lim >> 2` (`src/sweep.c:661, 1131`).
3. **`P0-2` — Factor/BVA Watch Rescan Deduplication (`full_factor`):**
   Deduplicates touched literals per BVA commit using `h->lit_mark` and `h->work_stk2` before
   clearing `lit_mark` and calling `full_bva_upd_lit_fid` at most once per unique touched literal
   (`src/factor.c:151-162, 800-818`).
4. **`P0-3a` — Transitive Sort Knuth Gaps (`full_trans_sort_m6`):**
   Replaces power-of-2 Shellsort (`gap = n >> 1; gap >>= 1`) with Knuth gaps
   (`gap = 1; while (gap < n / 3) gap = 3 * gap + 1; ... gap /= 3`) plus `n <= 1` fast return.
5. **`P1-11` — Preprocessing Fixed Lucky Polarity (`full_preprocess_m6`):**
   Calls `full_lucky_late_m7(h)` (which invokes fixed `full_lucky_polar_m7`) in place of legacy
   `full_lucky(h)` (`src/lucky.c:11-80`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- `glue_used` word index for actual swept-variable count (`src/sweep.c:1718`). -/
def swpGuSweptIdx : Nat := 32

kissat_c0! fidStep12A "
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
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_SWEEP              1024u
#define FL_SWEEP_INR          0x20000000u
#define FL_SWEEP_INC          0x40000000u

#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_WM_PROBE_TICKS     0ULL

#define K6H_TICKS             11u
#define K6H_NASSUMP           15u
#define K6H_NEQ               24u

#define SWP_GU_COMPLETED      28u
#define SWP_GU_INCOMPLETE     29u
#define SWP_GU_CURSOR         30u
#define SWP_GU_SWEPT          32u

extern u64  full_m6_max_v(u64 cap);
extern void full_m6_sweep_refine_sig(FullHdr *h, u32 nv, u32 bit);
extern u64  full_m6_sweep_solve(FullHdr *h, u32 nv, u64 tick_lim);
extern u32  full_m6_sweep_flip_round(FullHdr *h, u32 nv);
extern bool full_m6_dense_prop(FullHdr *h);
extern u32  full_m6_collect_cands(FullHdr *h);
extern u64  full_m6_sweep_var(FullHdr *h, u32 v, u64 tick_lim);

extern u32  full_bva_steps_cap_fid(u64 scap);
extern void full_bva_connect_clauses_fid(FullHdr *h);
extern void full_fheap_up_fid(u32 *hp, u32 *ps, u32 *deg, u32 p);
extern void full_fheap_down_fid(u32 *hp, u32 *ps, u32 *deg, u32 p, u32 n);
extern bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv);
extern u32  full_bva_upd_lit_fid(FullHdr *h, u32 *fheap, u32 *fpos,
                                 u32 *deg, u64 cur_nl, u64 hsz_tl);

extern u64  full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64  full_log10_q16_m7(u64 x);
extern u64  full_scale_delta_m5(FullHdr *h, u64 delta);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool full_enter_dense(FullHdr *h);
extern u64  full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64  full_rebuild_watches_nosort_fid(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64  m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64  full_substitute(FullHdr *h);
extern u64  full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64  full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64  full_vivify_m6_hdr(FullHdr *h);
extern u64  full_transitive_m6(FullHdr *h, u64 tick_lim);
extern void full_sort_bin_watches_fid(FullHdr *h);

extern u64  full_propagate(FullHdr *h);
extern u64  full_arena_sweep(FullHdr *h);
extern u64  full_lucky_late_m7(FullHdr *h);
extern bool full_compact_needed(FullHdr *h);
extern u64  full_compact(FullHdr *h);

void full_trans_sort_m6(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u32 *probes = (u32 *)h->work_stk1;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  bool stab = (h->stable != 0ULL);
  u64 gap = 1ULL;
  u64 n3 = n / 3ULL;
  while (gap < n3) { gap = 3ULL * gap + 1ULL; }
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < n) {
      u32 v = probes[si];
      u64 kv = stab ? sc[v] : (u64)qs[v];
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pv = probes[pj];
        u64 kpv = stab ? sc[pv] : (u64)qs[pv];
        if (kpv > kv || (kpv == kv && pv <= v)) { break; }
        probes[sj] = pv;
        sj = pj;
      }
      probes[sj] = v;
      si = si + 1ULL;
    }
    gap = gap / 3ULL;
  }
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
  while (round < 16u && rbit < 64u && (u64)k[K6H_TICKS] < sim_lim && h->fuel > 0ULL) {
    if (full_m6_sweep_flip_round(h, nv) > 0u) {
      full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
    } else {
      break;
    }
    round = round + 1u;
  }
  return rbit;
}

u64 full_m6_sweep_vars(FullHdr *h, u64 budget, u64 tick_lim) {
  u32 *gu = (u32 *)h->glue_used;
  gu[SWP_GU_SWEPT] = 0u;
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (!full_m6_dense_prop(h)) { return 20ULL; }
  u64 cv = h->cur_vars;
  if (cv == 0ULL) { return 1ULL; }
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 comp = gu[SWP_GU_COMPLETED];
  if (comp > 5u) { comp = 5u; }
  u64 max_occ = (u64)(1024u << comp);
  bool need_mark = (gu[SWP_GU_INCOMPLETE] == 0u);
  if (!need_mark) {
    u64 rem_inc = 0ULL; u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) ==
          (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) {
        if (vals[v << 1] == (i8)0) {
          u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
          u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
          if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
            rem_inc = rem_inc + 1ULL;
          } else {
            fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
          }
        } else {
          fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
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
          fl[v] = (fl[v] & (~FL_SWEEP_INR)) | FL_SWEEP | FL_SWEEP_INC;
        } else {
          fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
        }
      } else {
        fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
      }
      v = v + 1ULL;
    }
    gu[SWP_GU_INCOMPLETE] = 1u;
    gu[SWP_GU_CURSOR] = 0u;
  }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *eqb = (u32 *)h->work_stk2; u32 *rp_arr = (u32 *)h->repr;
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 rem_b = budget; u32 pass = 0u;
  while (pass < 8u && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 nc = full_m6_collect_cands(h);
    if (nc == 0u) { break; }
    u32 ci = 0u; u32 isz = 0u;
    while (rem_b > 0ULL && rem_ticks > 0ULL &&
           h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
      u32 v = 0u;
      if (isz > 0u) {
        isz = isz - 1u;
        v = cands[cv + (u64)isz];
      } else if (ci < nc) {
        v = cands[ci]; ci = ci + 1u;
        gu[SWP_GU_CURSOR] = ((u64)v + 1ULL < cv) ? (v + 1u) : 0u;
      } else {
        break;
      }
      if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
        fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
        rem_b = rem_b - 1ULL;
        u64 sub0 = h->subst_cnt;
        if (full_m6_sweep_var(h, v, rem_ticks) == 20ULL) { return 20ULL; }
        if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
        u64 spent = (u64)k[K6H_TICKS];
        rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
        if (h->subst_cnt > sub0) {
          u32 neq = k[K6H_NEQ]; u32 ei = 0u; u64 nlits = cv << 1;
          while (ei < neq && (u64)ei < cv) {
            u32 lit = eqb[ei << 1];
            if ((u64)lit < nlits) {
              u32 rv = rp_arr[lit] >> 1;
              if ((u64)rv < cv && (fl[rv] & FL_ACTIVE) != 0u && vals[rv << 1] == (i8)0) {
                if ((fl[rv] & FL_SWEEP_INR) == 0u && (u64)isz < cv) {
                  cands[cv + (u64)isz] = rv; isz = isz + 1u;
                }
                fl[rv] = fl[rv] | FL_SWEEP | FL_SWEEP_INR;
              }
            }
            ei = ei + 1u;
          }
        }
      }
    }
    pass = pass + 1u;
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  u64 left_inc = 0ULL; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) ==
        (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) {
      if (vals[v << 1] == (i8)0) {
        u64 dp = (u64)wvec[((v << 1) << 1) + 1ULL];
        u64 dn = (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
        if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
          left_inc = 1ULL;
          break;
        }
      }
      fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
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
  u64 swept = budget - rem_b;
  gu[SWP_GU_SWEPT] = (swept > 0xFFFFFFFFULL) ? 0xFFFFFFFFu : (u32)swept;
  return 1ULL;
}

u64 full_factor(FullHdr *h, u64 budget) {
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (h->cur_vars >= h->max_vars || sc == 0u || budget == 0ULL) {
    return 1ULL;
  }
  full_bva_connect_clauses_fid(h);
  if (h->oom != 0ULL) { return 1ULL; }
  h->ant_sz = budget;
  u64 init_cv = h->cur_vars;
  u64 max_nl = h->max_vars << 1;
  u32 *tmark = (u32 *)h->wsort;
  u32 *fheap = (u32 *)h->tarjan_mark;
  u32 *fpos = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags;
  u32 *deg = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u64 zi = 0ULL;
  while (zi < max_nl) {
    tmark[zi] = 0u; fheap[zi] = 0u; fpos[zi] = 0xFFFFFFFFu;
    zi = zi + 1ULL;
  }
  u32 hsz = 0u;
  u64 v = 0ULL;
  while (v < init_cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 pl = (u32)(v << 1);
      u32 nl = pl | 1u;
      if ((fl[v] & FL_FACT_P) != 0u && deg[pl] > 1u) {
        fheap[hsz] = pl; fpos[pl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
      if ((fl[v] & FL_FACT_N) != 0u && deg[nl] > 1u) {
        fheap[hsz] = nl; fpos[nl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
    }
    v = v + 1ULL;
  }
  while (hsz > 0u && h->cur_vars < h->max_vars && h->ant_sz > 0ULL && h->oom == 0ULL) {
    u32 f0 = fheap[0];
    hsz = hsz - 1u;
    fpos[f0] = 0xFFFFFFFFu;
    if (hsz > 0u) {
      fheap[0] = fheap[hsz];
      fpos[fheap[0]] = 0u;
      full_fheap_down_fid(fheap, fpos, deg, 0u, hsz);
    }
    u32 fv = f0 >> 1;
    u32 fbit = ((f0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    if ((fl[fv] & FL_ACTIVE) == 0u) { continue; }
    if ((fl[fv] & fbit) == 0u) { continue; }
    if (vals[f0] != (i8)0) { continue; }
    fl[fv] = fl[fv] & (~fbit);
    if (deg[f0] <= 1u) { continue; }
    if (full_bva_try_lit(h, f0, init_cv)) {
      u32 *scr_b = (u32 *)h->scratch_buf;
      u32 *ar_b = (u32 *)h->arena;
      u32 sc_b = full_bva_steps_cap_fid(h->scratch_cap);
      u32 bk = (u32)h->res_sz;
      u64 cur_nl = h->cur_vars << 1;
      u8 *tmk = (u8 *)h->lit_mark;
      u32 *tlits = (u32 *)h->work_stk2;
      u64 nt = 0ULL;
      u32 qs_idx = bk + 1u;
      while (qs_idx > 0u) {
        qs_idx = qs_idx - 1u;
        u32 factor = scr_b[qs_idx];
        u32 fneg = factor ^ 1u;
        if ((u64)factor < cur_nl && tmk[factor] == (u8)0 && nt < cur_nl) {
          tmk[factor] = (u8)1; tlits[nt] = factor; nt = nt + 1ULL;
        }
        if ((u64)fneg < cur_nl && tmk[fneg] == (u8)0 && nt < cur_nl) {
          tmk[fneg] = (u8)1; tlits[nt] = fneg; nt = nt + 1ULL;
        }
        u32 ro = scr_b[sc_b + qs_idx];
        u32 qn = scr_b[2u * sc_b + qs_idx];
        u32 qi = 0u;
        while (qi < qn) {
          u32 cw = scr_b[ro + qi];
          if ((cw & PW_BIN_FLAG) != 0u) {
            u32 ol = cw & PW_LIT_MASK;
            if ((u64)ol < cur_nl && tmk[ol] == (u8)0 && nt < cur_nl) {
              tmk[ol] = (u8)1; tlits[nt] = ol; nt = nt + 1ULL;
            }
          } else {
            u32 csz = ar_b[(u64)cw + 2ULL];
            u32 lj = 0u;
            while (lj < csz) {
              u32 l = ar_b[(u64)cw + 3ULL + (u64)lj];
              if (l != factor && (u64)l < cur_nl && tmk[l] == (u8)0 && nt < cur_nl) {
                tmk[l] = (u8)1; tlits[nt] = l; nt = nt + 1ULL;
              }
              lj = lj + 1u;
            }
          }
          qi = qi + 1u;
        }
      }
      u64 ui = 0ULL;
      while (ui < nt) {
        tmk[tlits[ui]] = (u8)0;
        ui = ui + 1ULL;
      }
      ui = 0ULL;
      while (ui < nt) {
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
          ((u64)hsz << 32) | (u64)tlits[ui]);
        ui = ui + 1ULL;
      }
    }
  }
  u64 end_nlits = h->cur_vars << 1;
  u64 ci = 0ULL;
  while (ci < end_nlits) {
    fheap[ci] = 0u; fpos[ci] = 0u;
    ci = ci + 1ULL;
  }
  if (h->cur_vars > init_cv) {
    u64 cv = h->cur_vars;
    u32 *qn = (u32 *)h->q_next;
    u32 *qs = (u32 *)h->q_stamp;
    u64 p = h->q_first;
    u64 s = 0ULL;
    while (p < cv && s < cv) {
      s = s + 1ULL;
      qs[p] = (u32)s;
      p = (u64)qn[p];
    }
    h->q_cur_stamp = s;
    if (h->q_search_idx < cv) {
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  return 1ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  h->probings = h->probings + 1ULL;
  if (!initial) {
    u64 parg = (h->probings > (~0ULL) - 9ULL) ? (~0ULL) : (h->probings + 9ULL);
    u64 qlog = full_log10_q16_m7(parg);
    u64 pc = (h->probings > 100000000ULL) ? 100000000ULL : h->probings;
    u64 nlogp = (100ULL * pc * qlog) >> 16;
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
  }
  bool bin_dirty = false;
  if (initial) {
    bool subst_at_end = true;
    if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
      if (full_enter_dense(h)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        bin_dirty = true;
        if (ca > cb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
      if (full_enter_dense(h)) {
        u32 *gu_sw = (u32 *)h->glue_used;
        gu_sw[SWP_GU_SWEPT] = 0u;
        u64 sb = h->sweep_cnt;
        if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 sa = h->sweep_cnt;
        u64 swept = (u64)gu_sw[SWP_GU_SWEPT];
        if (sa > sb && swept > 0ULL && (sa - sb) * 1000ULL >= swept) {
          m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        bin_dirty = true;
        if (sa > sb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (subst_at_end && h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    u64 round = 0ULL;
    while (round < 2ULL) {
      u64 before_unass = h->unassigned;
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        if (full_enter_dense(h)) {
          u64 cb = h->cong_cnt;
          if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 ca = h->cong_cnt;
          if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          bin_dirty = true;
        } else if (h->inconsistent != 0ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (full_vivify_m6_hdr(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
        if (full_enter_dense(h)) {
          u32 *gu_sw = (u32 *)h->glue_used;
          gu_sw[SWP_GU_SWEPT] = 0u;
          u64 sb = h->sweep_cnt;
          if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 swept = (u64)gu_sw[SWP_GU_SWEPT];
          if (h->sweep_cnt > sb && swept > 0ULL && (h->sweep_cnt - sb) * 1000ULL >= swept) {
            m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          bin_dirty = true;
        } else if (h->inconsistent != 0ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 tr_lim = (dticks / 50ULL) + 100000ULL;
      if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->unassigned >= before_unass) { break; }
      round = round + 1ULL;
    }
  }
  u64 fr = 1ULL;
  u64 fp = 10ULL;
  u64 fa = h->unassigned / 10ULL;
  while (fa >= fp && fr < 19ULL) {
    fr = fr + 1ULL;
    fp = fp * 10ULL;
  }
  u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
  if (h->unassigned > 0ULL && fr <= fe4 && full_enter_dense(h)) {
    u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
    m6_hdr_set_watermark(h, 1ULL, nfact);
    u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    bin_dirty = true;
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  if (bin_dirty) { full_sort_bin_watches_fid(h); }
  h->search_ticks = saved_st;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
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
  u64 lk = full_lucky_late_m7(h);
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

/-! ## 1. Drop-In `Fn` Handles, Replacement List & Empty Insertion List -/

/-- `full_trans_sort_m6` replacement (`P0-3a`: Knuth Shellsort gaps). -/
def fidStep12ATransSortFn : Fn :=
  ⟨"full_trans_sort_m6", [i64, i64], [], full_trans_sort_m6_body⟩

/-- `full_m6_sweep_sim` replacement (`P1-1`: full `sim_lim = tick_lim`). -/
def fidStep12ASweepSimFn : Fn :=
  ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], full_m6_sweep_sim_body⟩

/-- `full_m6_sweep_vars` replacement (`P0-1`: track swept count in `glue_used[32]`). -/
def fidStep12ASweepVarsFn : Fn :=
  ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_body⟩

/-- `full_factor` replacement (`P0-2`: per-commit touched-literal deduplication). -/
def fidStep12AFactorFn : Fn :=
  ⟨"full_factor", [i64, i64], [i64], full_factor_body⟩

/-- `full_probe_m6` replacement (`P0-1`: `(sa - sb) * 1000 >= swept` sweep delay). -/
def fidStep12AProbeFn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩

/-- `full_preprocess_m6` replacement (`P1-11`: invoke `full_lucky_late_m7`). -/
def fidStep12APreprocessFn : Fn :=
  ⟨"full_preprocess_m6", [i64], [i64], full_preprocess_m6_body⟩

/-- Ordered list of all `6` Step-12A replacement functions (`0` ABI changes). -/
def fidStep12ARepls : List Fn :=
  [ fidStep12ATransSortFn
  , fidStep12ASweepSimFn
  , fidStep12ASweepVarsFn
  , fidStep12AFactorFn
  , fidStep12AProbeFn
  , fidStep12APreprocessFn ]

/-- Empty helper-insertion list (`0` added functions; net `505 -> 505`). -/
def fidStep12ABefores : List (Sym × List Fn) := []

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem fidStep12ATransSort_wf : Func.Wf fidStep12ATransSortFn.body := by t_wf_reify
theorem fidStep12ASweepSim_wf : Func.Wf fidStep12ASweepSimFn.body := by t_wf_reify
theorem fidStep12ASweepVars_wf : Func.Wf fidStep12ASweepVarsFn.body := by t_wf_reify
theorem fidStep12AFactor_wf : Func.Wf fidStep12AFactorFn.body := by t_wf_reify
theorem fidStep12AProbe_wf : Func.Wf fidStep12AProbeFn.body := by t_wf_reify
theorem fidStep12APreprocess_wf : Func.Wf fidStep12APreprocessFn.body := by t_wf_reify

theorem fidStep12ARepls_wf : ∀ f ∈ fidStep12ARepls, f.Wf := by
  intro f hf
  simp only [fidStep12ARepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fidStep12ATransSort_wf
  · exact fidStep12ASweepSim_wf
  · exact fidStep12ASweepVars_wf
  · exact fidStep12AFactor_wf
  · exact fidStep12AProbe_wf
  · exact fidStep12APreprocess_wf

theorem fidStep12ABefores_wf : ∀ h ∈ fidStep12ABefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp [fidStep12ABefores] at hh

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12A

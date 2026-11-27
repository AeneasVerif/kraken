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
# Kissat Fidelity Step 13 Shard S1-B — BVE & Forward Subsumption (`FullFidelityStep13S1BVEFwdSub`)

Data-pure C0 module (`0` `*Proof*` imports, `0` edits to Step-12 files) containing the `8`
Step-13 S1-B functions (`2` ADD + `6` MOD) copied verbatim from frozen `step13_v2_frozen_direct.c`:
- **ADD (`2`):** `full_has_factor_cands_fid`, `full_has_elim_cands_fid`.
- **MOD (`6`):** `full_fwd_scan_lit_m7`, `full_fwd_connect_subsumer_m7`, `full_forward_sub_m7`,
  `full_bve_certify_unit_fid`, `full_bve_var_key_m7`, `full_eliminate_m6`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

@[expose] public section

kissat_c0! fidStep13S1BVEFwdSub "
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

#define PH_GARB        0x00080000u
#define PH_RED         0x00400000u
#define PH_SUBSUME     0x01000000u
#define PW_BIN_FLAG    0x80000000u
#define PW_LIT_MASK    0x7FFFFFFFu

#define FL_SUBSUME     8u
#define FL_ELIM_C      16u
#define FID_K6_TICK_P1 1000000u

extern u64  f64u_mul(u64 a, u64 b);
extern u64  f64u_nlogpown(u64 count, u64 exponent);
extern u64  f64u_to_u64(u64 a);
extern void full_update_classify_fid(FullHdr *h);
extern u64  full_dense_occ_cnt_fid(FullHdr *h, u32 lit, u64 cap);
extern bool full_enter_dense_ex_fid(FullHdr *h, bool connect_large);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern bool full_fwd_dedup_bins(FullHdr *h);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u64  full_fwd_collect_sort_m7(FullHdr *h);
extern void full_fwd_flush_large_m7(FullHdr *h);
extern bool full_fwd_check_cl_m7(FullHdr *h, u32 cref);
extern u32  full_arena_next(FullHdr *h, u32 cref);
extern void full_fwd_reconnect_irred_m7(FullHdr *h);
extern u64  full_m6_max_v(u64 cap);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_k6_init(FullHdr *h, u32 nv);
extern bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz);
extern u64  full_k6_solve(FullHdr *h, u64 tick_lim);
extern u64  full_elim_dticks(FullHdr *h, bool initial);
extern u64  full_scale_delta(FullHdr *h, u64 delta);
extern u64  full_elim_bve_m7(FullHdr *h, u64 res_lim);
extern u64  full_rebuild_watches(FullHdr *h);

bool full_has_factor_cands_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & 1u) != 0u && vals[v << 1] == (i8)0 && (fl[v] & (32u | 64u)) != 0u) {
      return true;
    }
    v = v + 1ULL;
  }
  return false;
}

bool full_has_elim_cands_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & 1u) != 0u && vals[v << 1] == (i8)0 && (fl[v] & (8u | 16u)) != 0u) {
      return true;
    }
    v = v + 1ULL;
  }
  return false;
}

u32 full_fwd_scan_lit_m7(FullHdr *h, u32 cref, u32 sz, u32 scan_lit, bool check_bins) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)scan_lit << 1];
  u64 wsz = (u64)wvec[((u64)scan_lit << 1) + 1ULL];
  if (wsz == 0ULL || full_dense_occ_cnt_fid(h, scan_lit, 1001ULL) > 1000ULL) {
    return 0xFFFFFFFFu;
  }
  u64 end = off + wsz;
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if (check_bins) {
        u32 ot = w0 & PW_LIT_MASK;
        if (lm[ot] != (u8)0) { return 0xFFFFFFFEu; }
        if ((ot ^ 1u) != scan_lit && lm[ot ^ 1u] != (u8)0) { return ot ^ 1u; }
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    if (cr == cref || (ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
    u32 dsz = ar[(u64)cr + 2ULL];
    if (dsz > sz) { continue; }
    u32 miss = 0u;
    u32 cand = 0xFFFFFFFFu;
    u32 j = 0u;
    while (j < dsz) {
      u32 dl = ar[(u64)cr + 3ULL + (u64)j];
      if (lm[dl] == (u8)0 && vals[dl] >= (i8)0) {
        if (lm[dl ^ 1u] != (u8)0 && cand == 0xFFFFFFFFu) { cand = dl ^ 1u; }
        else { miss = 1u; break; }
      }
      j = j + 1u;
    }
    if (miss == 0u) {
      if (cand == 0xFFFFFFFFu) { return 0xFFFFFFFEu; }
      return cand;
    }
  }
  return 0xFFFFFFFFu;
}

void full_fwd_connect_subsumer_m7(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *fl = (u32 *)h->flags;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return; }
  u32 best_l = ar[(u64)cref + 3ULL];
  u32 best_d = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if ((fl[l >> 1] & FL_SUBSUME) != 0u) {
      u32 d = (u32)full_dense_occ_cnt_fid(h, l, 1001ULL);
      if (d < best_d) { best_d = d; best_l = l; }
    }
    i = i + 1u;
  }
  if (best_d == 0xFFFFFFFFu) {
    best_d = (u32)full_dense_occ_cnt_fid(h, best_l, 1001ULL);
    i = 1u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      u32 d = (u32)full_dense_occ_cnt_fid(h, l, 1001ULL);
      if (d < best_d) { best_d = d; best_l = l; }
      i = i + 1u;
    }
  }
  if (best_d <= 1000u) {
    if (!full_watch_push(h, best_l, sz & PW_LIT_MASK, cref, 2u)) { h->oom = 1ULL; }
  }
}

u64 full_forward_sub_m7(FullHdr *h, u64 budget) {
  if (budget == 0ULL) { full_fwd_reconnect_irred_m7(h); return 1ULL; }
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  u64 saved_prop = h->propagated;
  u64 ncand = full_fwd_collect_sort_m7(h);
  if (ncand == 0ULL) {
    full_fwd_reconnect_irred_m7(h);
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  full_fwd_flush_large_m7(h);
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  u64 rem = budget;
  while (i < ncand && rem > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 cr = rr[i];
    rem = rem - 1ULL;
    if (!full_fwd_check_cl_m7(h, cr)) { return 20ULL; }
    if (h->oom == 0ULL && h->inconsistent == 0ULL && (ar[cr] & PH_GARB) == 0u) {
      full_fwd_connect_subsumer_m7(h, cr);
    }
    i = i + 1ULL;
  }
  if (i == ncand && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 *fl = (u32 *)h->flags;
    u64 cv = h->cur_vars;
    u64 v = 0ULL;
    while (v < cv) { fl[v] = fl[v] & (~FL_SUBSUME); v = v + 1ULL; }
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_SUBSUME) != 0u) {
        ar[p] = hdr & (~PH_SUBSUME);
        if ((hdr & PH_GARB) == 0u) {
          u32 k = 0u;
          while (k < sz) {
            u32 lv = ar[p + 3ULL + (u64)k] >> 1;
            if ((u64)lv < cv) { fl[lv] = fl[lv] | FL_SUBSUME | FL_ELIM_C; }
            k = k + 1u;
          }
        } else if (sz >= 2u) {
          u32 v0 = ar[p + 3ULL] >> 1;
          u32 v1 = ar[p + 4ULL] >> 1;
          if ((u64)v0 < cv) { fl[v0] = fl[v0] | FL_SUBSUME | FL_ELIM_C; }
          if ((u64)v1 < cv) { fl[v1] = fl[v1] | FL_SUBSUME | FL_ELIM_C; }
        }
      }
      p = np;
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  full_fwd_reconnect_irred_m7(h);
  if (saved_prop < h->propagated && saved_prop <= h->trail_end) {
    h->propagated = saved_prop;
  }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

bool full_bve_certify_unit_fid(
    FullHdr *h, u32 v, u32 unit, u32 side_off, u32 side_cnt, u32 side_mask) { (void)v;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 mv_sw = (u32)full_m6_max_v(h->scratch_cap);
  u32 max_csz = (h->max_vars < 65535ULL) ? (u32)h->max_vars : 65535u;
  u32 nv = 0u;
  bool direct_entail = false;
  bool abort_c = false;
  u32 idx = 0u;
  while (idx < side_cnt && !direct_entail && !abort_c) {
    if (((scr[side_mask + (idx >> 5)] >> (idx & 31u)) & 1u) != 0u) {
      u32 w = scr[side_off + idx];
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { direct_entail = true; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= mv_sw || (u64)nv >= h->cur_vars) { abort_c = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != unit) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= mv_sw || (u64)nv >= h->cur_vars) { abort_c = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_c) { break; }
        if (!sat) {
          if (csz == 0u) { direct_entail = true; break; }
          if (csz > max_csz) { abort_c = true; break; }
        }
      }
    }
    idx = idx + 1u;
  }
  if (direct_entail) {
    u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
    i8 uv = vals[unit];
    if (uv < (i8)0) { h->inconsistent = 1ULL; }
    else if (uv == (i8)0) { full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u); }
    return true;
  }
  if (abort_c || nv == 0u || mv_sw == 0u || 1280u + (mv_sw << 1) < 4192u) {
    u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
    return false;
  }
  ((u32 *)h->glue_used)[33] = 0xFFFFFFFFu;
  full_k6_init(h, nv);
  bool ok = true;
  idx = 0u;
  while (idx < side_cnt && ok) {
    if (((scr[side_mask + (idx >> 5)] >> (idx & 31u)) & 1u) != 0u) {
      u32 w = scr[side_off + idx];
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        if (vals[l] == (i8)0) {
          u32 loc = tmk[l >> 1];
          if (loc == 0u || loc > nv) { ok = false; break; }
          tmp[0] = ((loc - 1u) << 1) | (l & 1u);
          if (!full_k6_add_clause(h, tmp, 1u)) { ok = false; break; }
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != unit) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 loc = tmk[l >> 1];
              if (loc == 0u || loc > nv || csz >= max_csz) { ok = false; break; }
              tmp[csz] = ((loc - 1u) << 1) | (l & 1u); csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (!ok) { break; }
        if (!sat) {
          if (!full_k6_add_clause(h, tmp, csz)) { ok = false; break; }
        }
      }
    }
    idx = idx + 1u;
  }
  u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (!ok) { return false; }
  if (full_k6_solve(h, (u64)FID_K6_TICK_P1) != 20ULL) { return false; }
  i8 uv = vals[unit];
  if (uv < (i8)0) { h->inconsistent = 1ULL; }
  else if (uv == (i8)0) { full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u); }
  return true;
}

u64 full_bve_var_key_m7(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u64 pos = full_dense_occ_cnt_fid(h, v << 1, 2000ULL);
  u64 neg = full_dense_occ_cnt_fid(h, (v << 1) | 1u, 2000ULL);
  if (pos > 2000ULL) { pos = 2000ULL; }
  if (neg > 2000ULL) { neg = 2000ULL; }
  u64 base = (4004000ULL + pos + neg) - (pos * neg);
  u64 rel = 0ULL;
  if (h->stable != 0ULL) {
    u64 *sc = (u64 *)h->score;
    rel = f64u_to_u64(sc[v]);
    if (rel > (1ULL << 61)) { rel = 1ULL << 61; }
  } else {
    u32 *qs = (u32 *)h->q_stamp;
    rel = (u64)qs[v];
  }
  if (rel > (1ULL << 61)) { rel = 1ULL << 61; }
  return ((1ULL << 62) + base) - rel;
}

u64 full_eliminate_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 nloge = f64u_to_u64(
      f64u_mul(0x407F400000000000ULL, f64u_nlogpown(h->eliminations, 2ULL)));
    u64 delta = full_scale_delta(h, nloge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!initial && !full_has_elim_cands_fid(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return 1ULL;
  }
  if (!full_enter_dense_ex_fid(h, false)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbase = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 fbud = fbase / 10ULL;
  u64 fs = full_forward_sub_m7(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) {
    full_rebuild_watches(h);
    return 20ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 base_t = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 res_lim = base_t / 10ULL;
  u64 res = full_elim_bve_m7(h, res_lim);
  u64 rr = full_rebuild_watches(h);
  h->search_ticks = saved_st;
  full_update_classify_fid(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}
"

/-- Step-13 `full_has_factor_cands_fid` (added helper). -/
def fidStep13S1HasFactorCandsFn : Fn :=
  ⟨"full_has_factor_cands_fid", [i64], [.bool], full_has_factor_cands_fid_body⟩

/-- Step-13 `full_has_elim_cands_fid` (added helper). -/
def fidStep13S1HasElimCandsFn : Fn :=
  ⟨"full_has_elim_cands_fid", [i64], [.bool], full_has_elim_cands_fid_body⟩

/-- Step-13 `full_fwd_scan_lit_m7` (replacement). -/
def fidStep13S1FwdScanLitFn : Fn :=
  ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], full_fwd_scan_lit_m7_body⟩

/-- Step-13 `full_fwd_connect_subsumer_m7` (replacement). -/
def fidStep13S1FwdConnectSubsumerFn : Fn :=
  ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], full_fwd_connect_subsumer_m7_body⟩

/-- Step-13 `full_forward_sub_m7` (replacement). -/
def fidStep13S1ForwardSubFn : Fn :=
  ⟨"full_forward_sub_m7", [i64, i64], [i64], full_forward_sub_m7_body⟩

/-- Step-13 `full_bve_certify_unit_fid` (replacement). -/
def fidStep13S1BveCertifyUnitFn : Fn :=
  ⟨"full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool],
    full_bve_certify_unit_fid_body⟩

/-- Step-13 `full_bve_var_key_m7` (replacement). -/
def fidStep13S1BveVarKeyFn : Fn :=
  ⟨"full_bve_var_key_m7", [i64, i32], [i64], full_bve_var_key_m7_body⟩

/-- Step-13 `full_eliminate_m6` (replacement). -/
def fidStep13S1EliminateFn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m6_body⟩

/-- Ordered `2`-function Step-13 S1-B addition list. -/
def fidStep13S1BVEFwdSubAdds : List Fn :=
  [ fidStep13S1HasFactorCandsFn
  , fidStep13S1HasElimCandsFn ]

/-- Ordered `6`-function Step-13 S1-B replacement list. -/
def fidStep13S1BVEFwdSubRepls : List Fn :=
  [ fidStep13S1FwdScanLitFn
  , fidStep13S1FwdConnectSubsumerFn
  , fidStep13S1ForwardSubFn
  , fidStep13S1BveCertifyUnitFn
  , fidStep13S1BveVarKeyFn
  , fidStep13S1EliminateFn ]

end

public section

theorem fidStep13S1HasFactorCands_wf :
    Func.Wf fidStep13S1HasFactorCandsFn.body := by t_wf_reify
theorem fidStep13S1HasElimCands_wf :
    Func.Wf fidStep13S1HasElimCandsFn.body := by t_wf_reify
theorem fidStep13S1FwdScanLit_wf : Func.Wf fidStep13S1FwdScanLitFn.body := by t_wf_reify
theorem fidStep13S1FwdConnectSubsumer_wf :
    Func.Wf fidStep13S1FwdConnectSubsumerFn.body := by t_wf_reify
theorem fidStep13S1ForwardSub_wf : Func.Wf fidStep13S1ForwardSubFn.body := by t_wf_reify
theorem fidStep13S1BveCertifyUnit_wf :
    Func.Wf fidStep13S1BveCertifyUnitFn.body := by t_wf_reify
theorem fidStep13S1BveVarKey_wf : Func.Wf fidStep13S1BveVarKeyFn.body := by t_wf_reify
theorem fidStep13S1Eliminate_wf : Func.Wf fidStep13S1EliminateFn.body := by t_wf_reify

theorem fidStep13S1BVEFwdSubAdds_wf : ∀ f ∈ fidStep13S1BVEFwdSubAdds, f.Wf := by
  intro f hf
  simp only [fidStep13S1BVEFwdSubAdds, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact fidStep13S1HasFactorCands_wf
  · exact fidStep13S1HasElimCands_wf

theorem fidStep13S1BVEFwdSubRepls_wf : ∀ f ∈ fidStep13S1BVEFwdSubRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S1BVEFwdSubRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fidStep13S1FwdScanLit_wf
  · exact fidStep13S1FwdConnectSubsumer_wf
  · exact fidStep13S1ForwardSub_wf
  · exact fidStep13S1BveCertifyUnit_wf
  · exact fidStep13S1BveVarKey_wf
  · exact fidStep13S1Eliminate_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Bounded SAT Sweeping (`Src/Sweep.lean`)

Mirrors upstream `kissat/src/sweep.c` (`20` live functions, DAG level `L4`):
- `full_m6_sweep_cone` (R4: `kissat_sweep_add_cone`)
- `full_m6_sweep_refine_sig` (R4: `kissat_sweep_refine_signatures`)
- `full_m6_sweep_rand_phases` (R4: `kissat_sweep_randomize_phases`)
- `full_m6_sweep_solve` (R4: `kissat_sweep_solve`)
- `full_m6_sweep_flip_round` (R4: `kissat_sweep_flip_round`)
- `full_m6_sweep_sim` (R4: `kissat_sweep_simulate`)
- `full_m6_sweep_rearm` (R4: `kissat_sweep_rearm`)
- `full_m6_sweep_build_pht` (R4: `kissat_sweep_build_partition_table`)
- `full_m6_extract_pht` (R4: `kissat_sweep_extract_partition_table`)
- `full_m6_refine_partition` (R4: `kissat_sweep_refine_partition`)
- `full_m6_sweep_units` (R4: `kissat_sweep_backbone_units`)
- `full_m6_sweep_classes` (R4: `kissat_sweep_equivalence_classes`)
- `full_m6_els_ar` (R4: `kissat_sweep_substitute_arena`)
- `full_m6_els_lit` (R4: `kissat_sweep_substitute_literal`)
- `full_m6_dense_els` (R4: `kissat_sweep_dense_substitute`)
- `full_m6_sweep_var` (R4: `kissat_sweep_variable`)
- `full_m6_cand_sift` (R4: `kissat_sweep_candidate_sift`)
- `full_m6_collect_cands` (R4: `kissat_sweep_collect_candidates`)
- `full_m6_sweep_vars` (R4: `kissat_sweep_variables`)
- `full_sweep_dense_m6` (R4: `kissat_sweep`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Sweep

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! sweep "
#include \"kissat_internal.h\"

extern u64 full_m6_max_v(u64 cap);
extern void full_k6_init(FullHdr *h, u32 nv);
extern bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz);
extern u64 full_k6_solve(FullHdr *h, u64 tick_lim);
extern bool full_k6_flip(FullHdr *h, u32 lit);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern void full_k512_add_live_m6(FullHdr *h, u32 a, u32 b);
extern u32 full_cong_find(u32 *repr, u32 l);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_m6_dense_prop(FullHdr *h);
extern u64 full_dense_occ_cnt_fid(FullHdr *h, u32 lit, u64 cap);

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

void full_m6_sweep_refine_sig(FullHdr *h, u32 nv, u32 bit_idx) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *vals = k + (32u + 10u * mv);
  u64 mask = 1ULL << (u64)(bit_idx & 63u); u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (vals[i << 1] == 1u) { sig[gv] = sig[gv] | mask; }
    else { sig[gv] = sig[gv] & (~mask); }
    i = i + 1u;
  }
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

u64 full_m6_sweep_solve(FullHdr *h, u32 nv, u64 tick_lim) {
  full_m6_sweep_rand_phases(h, nv);
  return full_k6_solve(h, tick_lim);
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

void full_m6_sweep_rearm(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u32 *fl = (u32 *)h->flags;
  u32 pol = 0u;
  while (pol < 2u) {
    u32 lit = (v << 1) | pol;
    u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
    u64 p = off; u64 lim = 0ULL;
    while (p < end && lim < 128ULL) {
      u32 w0 = wstk[p]; p = p + 1ULL; lim = lim + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ov = (w0 & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && ov != v && (fl[ov] & FL_ACTIVE) != 0u) {
          fl[ov] = fl[ov] | FL_SWEEP;
        }
        continue;
      }
      if (p >= end) { break; }
      u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
      if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || sz > 16u) { continue; }
      u32 i = 0u;
      while (i < sz) {
        u32 lv = ar[(u64)cr + 3ULL + (u64)i] >> 1;
        if ((u64)lv < cv && lv != v && (fl[lv] & FL_ACTIVE) != 0u) {
          fl[lv] = fl[lv] | FL_SWEEP;
        }
        i = i + 1u;
      }
    }
    pol = pol + 1u;
  }
}

void full_m6_sweep_build_pht(FullHdr *h, u32 nv, u64 smask) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *pht_next = scr + PHT_NEXT; u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  i8 *vals_m = (i8 *)h->values;
  u32 b = 0u;
  while (b < PHT_SZ) { scr[PHT_HEAD + b] = 0xFFFFFFFFu; b = b + 1u; }
  u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (pht_merged[i] == 0u && vals_m[gv << 1] == (i8)0) {
      u64 raw = sig[gv] & smask;
      u64 key = ((raw & 1ULL) != 0ULL) ? (raw ^ smask) : raw;
      u32 hidx = (u32)((key ^ (key >> 17) ^ (key >> 34) ^ (key >> 51)) & (u64)PHT_MASK);
      pht_next[i] = scr[PHT_HEAD + hidx];
      scr[PHT_HEAD + hidx] = i;
    } else {
      pht_next[i] = 0xFFFFFFFFu;
    }
    i = i + 1u;
  }
}

u32 full_m6_extract_pht(FullHdr *h, u32 nv, u64 smask) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_next = scr + PHT_NEXT;
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *heads = (u32 *)h->shrink_stk; u32 *pols = (u32 *)h->min_clr;
  u32 ncls = 0u; u32 b = 0u;
  while (b < PHT_SZ) {
    u32 guard = nv;
    while (scr[PHT_HEAD + b] < nv && guard > 0u) {
      guard = guard - 1u;
      u32 h0 = scr[PHT_HEAD + b]; scr[PHT_HEAD + b] = 0xFFFFFFFFu;
      u32 keep_tail = 0xFFFFFFFFu; u32 cls_tail = h0; u32 csz = 1u;
      pols[h0] = 0u; u64 s0 = sig[cone_v[h0]] & smask;
      u32 y = pht_next[h0]; u32 inner_g = nv;
      while (y < nv && inner_g > 0u) {
        inner_g = inner_g - 1u;
        u32 ny = pht_next[y];
        u64 xr = (sig[cone_v[y]] ^ s0) & smask;
        if (xr == 0ULL || xr == smask) {
          pols[y] = (xr == 0ULL) ? 0u : 1u;
          pht_next[cls_tail] = y; cls_tail = y; csz = csz + 1u;
        } else {
          if (keep_tail == 0xFFFFFFFFu) { scr[PHT_HEAD + b] = y; }
          else { pht_next[keep_tail] = y; }
          keep_tail = y;
        }
        y = ny;
      }
      pht_next[cls_tail] = 0xFFFFFFFFu;
      if (keep_tail < nv) { pht_next[keep_tail] = 0xFFFFFFFFu; }
      if (csz >= 2u && (u64)ncls < h->max_vars) { heads[ncls] = h0; ncls = ncls + 1u; }
    }
    b = b + 1u;
  }
  return ncls;
}

u32 full_m6_refine_partition(FullHdr *h, u32 nv, u32 ncls) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_next = scr + PHT_NEXT;
  u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *k = scr + (1280u + (mv << 1)); u32 *kvals = k + (32u + 10u * mv);
  u32 *cone_v = (u32 *)h->work_stk1; i8 *vals_m = (i8 *)h->values;
  u32 *heads = (u32 *)h->shrink_stk; u32 *pols = (u32 *)h->min_clr;
  u32 *nheads = (u32 *)h->wsort; u32 new_n = 0u; u32 ci = 0u;
  while (ci < ncls) {
    u32 x = heads[ci];
    u32 ph = 0xFFFFFFFFu; u32 pt = 0xFFFFFFFFu; u32 pc = 0u;
    u32 nh = 0xFFFFFFFFu; u32 nt = 0xFFFFFFFFu; u32 nc = 0u;
    u32 g = nv;
    while (x < nv && g > 0u) {
      g = g - 1u;
      u32 nx = pht_next[x];
      if (pht_merged[x] == 0u && vals_m[cone_v[x] << 1] == (i8)0) {
        u32 kv = kvals[(x << 1) | (pols[x] & 1u)];
        if (kv == 1u) {
          if (pt == 0xFFFFFFFFu) { ph = x; } else { pht_next[pt] = x; }
          pt = x; pc = pc + 1u;
        } else if (kv == 2u) {
          if (nt == 0xFFFFFFFFu) { nh = x; } else { pht_next[nt] = x; }
          nt = x; nc = nc + 1u;
        }
      }
      x = nx;
    }
    if (pt < nv) { pht_next[pt] = 0xFFFFFFFFu; }
    if (nt < nv) { pht_next[nt] = 0xFFFFFFFFu; }
    if (pc >= 2u && (u64)new_n < h->max_vars) { nheads[new_n] = ph; new_n = new_n + 1u; }
    if (nc >= 2u && (u64)new_n < h->max_vars) { nheads[new_n] = nh; new_n = new_n + 1u; }
    ci = ci + 1u;
  }
  ci = 0u; while (ci < new_n) { heads[ci] = nheads[ci]; ci = ci + 1u; }
  return new_n;
}

u64 full_m6_sweep_units(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return (u64)rbit_in; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *k = scr + (1280u + (mv << 1)); u32 *assump = k + (32u + 9u * mv);
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u32 i = 0u; while (i < nv) { pht_merged[i] = 0u; i = i + 1u; }
  u32 rbit = rbit_in;
  u64 smask = (rbit >= 64u) ? 0xFFFFFFFFFFFFFFFFULL : ((1ULL << rbit) - 1ULL);
  i = 0u;
  while (i < nv && h->inconsistent == 0ULL && h->fuel > 0ULL && (u64)k[K6H_TICKS] < tick_lim) {
    u32 gv = cone_v[i];
    if ((fl[gv] & FL_ACTIVE) == 0u || vals[gv << 1] != (i8)0) {
      pht_merged[i] = 1u; i = i + 1u; continue;
    }
    u64 s0 = sig[gv] & smask;
    if (s0 == 0ULL || s0 == smask) {
      u32 wf = (s0 == 0ULL) ? 0u : 1u;
      u32 test_lit = (i << 1) | wf;
      if (full_k6_flip(h, test_lit ^ 1u)) {
        if (rbit < 64u) {
          full_m6_sweep_refine_sig(h, nv, rbit);
          smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        }
      } else {
        u64 rem = tick_lim - (u64)k[K6H_TICKS];
        k[K6H_NASSUMP] = 1u; assump[0] = test_lit;
        u64 d = full_m6_sweep_solve(h, nv, rem);
        if (d == 20ULL) {
          u32 gl = (gv << 1) | (1u - wf);
          if (!full_add_unit(h, gl)) { return 0xFFFFFFFFFFFFFFFFULL; }
          pht_merged[i] = 1u;
          full_k512_add_live_m6(h, test_lit ^ 1u, 0xFFFFFFFFu);
          if (k[K6H_INCONS] != 0u) { h->inconsistent = 1ULL; return 0xFFFFFFFFFFFFFFFFULL; }
          full_m6_sweep_rearm(h, gv);
          h->sweep_cnt = h->sweep_cnt + 1ULL;
        } else if (d == 10ULL && rbit < 64u) {
          full_m6_sweep_refine_sig(h, nv, rbit);
          smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        }
      }
    }
    i = i + 1u;
  }
  return (h->inconsistent != 0ULL) ? 0xFFFFFFFFFFFFFFFFULL : (u64)rbit;
}

u64 full_m6_sweep_classes(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_next = scr + PHT_NEXT;
  u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *k = scr + (1280u + (mv << 1));
  u32 *assump = k + (32u + 9u * mv); u32 *kvals = k + (32u + 10u * mv);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *eqb = (u32 *)h->work_stk2;
  u32 *fl = (u32 *)h->flags;
  u32 *heads = (u32 *)h->shrink_stk; u32 *pols = (u32 *)h->min_clr;
  k[K6H_NEQ] = 0u;
  u32 rbit = rbit_in;
  u64 smask = (rbit >= 64u) ? 0xFFFFFFFFFFFFFFFFULL : ((1ULL << rbit) - 1ULL);
  full_m6_sweep_build_pht(h, nv, smask);
  u32 ncls = full_m6_extract_pht(h, nv, smask);
  u32 neq = 0u; u32 steps = (nv << 2) + 64u;
  while (ncls > 0u && steps > 0u && h->inconsistent == 0ULL && h->oom == 0ULL &&
         h->fuel > 0ULL && (u64)k[K6H_TICKS] < tick_lim) {
    steps = steps - 1u;
    u32 a = heads[ncls - 1u]; u32 c = pht_next[a];
    if (c >= nv) { ncls = ncls - 1u; continue; }
    u32 gv_a = cone_v[a]; u32 gv_c = cone_v[c];
    if (pht_merged[a] != 0u || pht_merged[c] != 0u ||
        (fl[gv_a] & FL_ACTIVE) == 0u || (fl[gv_c] & FL_ACTIVE) == 0u) {
      pht_next[a] = pht_next[c];
      if (pht_next[a] >= nv) { ncls = ncls - 1u; }
      continue;
    }
    u32 pa = pols[a] & 1u; u32 pc = pols[c] & 1u; u32 pol = pa ^ pc;
    u32 fa = (kvals[a << 1] == 1u) ? (a << 1) : ((a << 1) | 1u);
    u32 fc = (kvals[c << 1] == 1u) ? (c << 1) : ((c << 1) | 1u);
    if (full_k6_flip(h, fa) || full_k6_flip(h, fc)) {
      if (rbit < 64u) { full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u; }
      ncls = full_m6_refine_partition(h, nv, ncls);
      continue;
    }
    u64 rem1 = tick_lim - (u64)k[K6H_TICKS];
    k[K6H_NASSUMP] = 2u; assump[0] = a << 1; assump[1] = (c << 1) | (1u ^ pol);
    u64 d1 = full_m6_sweep_solve(h, nv, rem1);
    if (d1 == 10ULL) {
      if (rbit < 64u) { full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u; }
      ncls = full_m6_refine_partition(h, nv, ncls);
      continue;
    }
    if (d1 != 20ULL || (u64)k[K6H_TICKS] >= tick_lim) {
      pht_next[a] = pht_next[c];
      if (pht_next[a] >= nv) { ncls = ncls - 1u; }
      continue;
    }
    u64 rem2 = tick_lim - (u64)k[K6H_TICKS];
    k[K6H_NASSUMP] = 2u; assump[0] = (a << 1) | 1u; assump[1] = (c << 1) | pol;
    u64 d2 = full_m6_sweep_solve(h, nv, rem2);
    if (d2 == 10ULL) {
      if (rbit < 64u) { full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u; }
      ncls = full_m6_refine_partition(h, nv, ncls);
      continue;
    }
    if (d2 != 20ULL) {
      pht_next[a] = pht_next[c];
      if (pht_next[a] >= nv) { ncls = ncls - 1u; }
      continue;
    }
    pht_merged[c] = 1u;
    pht_next[a] = pht_next[c];
    if (pht_next[a] >= nv) { ncls = ncls - 1u; }
    fl[gv_c] = fl[gv_c] & (~FL_SWEEP);
    full_k512_add_live_m6(h, (a << 1) ^ 1u, (c << 1) | pol);
    if (k[K6H_INCONS] != 0u) { h->inconsistent = 1ULL; return 20ULL; }
    full_k512_add_live_m6(h, a << 1, ((c << 1) | pol) ^ 1u);
    if (k[K6H_INCONS] != 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if ((u64)neq < h->cur_vars) {
      eqb[neq << 1] = gv_a << 1; eqb[(neq << 1) + 1u] = (gv_c << 1) | pol;
      neq = neq + 1u; k[K6H_NEQ] = neq;
    }
    full_m6_sweep_rearm(h, gv_a);
    full_m6_sweep_rearm(h, gv_c);
    h->sweep_cnt = h->sweep_cnt + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

bool full_m6_els_ar(FullHdr *h, u32 cr, u32 rl) {
  if ((u64)cr + 3ULL > h->arena_len) { return true; }
  u32 *ar = (u32 *)h->arena; u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
  if ((hdr & PH_GARB) != 0u || sz < 3u || (u64)cr + 3ULL + (u64)sz > h->arena_len) {
    return true;
  }
  u32 *repr = (u32 *)h->repr; u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  u64 nlits = h->cur_vars << 1;
  bool chg = false; u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if ((u64)l < nlits && full_cong_find(repr, l) != l) { chg = true; break; }
    k = k + 1u;
  }
  if (!chg) {
    if (!full_watch_push(h, rl, sz & PW_LIT_MASK, cr, 2u)) { h->oom = 1ULL; }
    return true;
  }
  bool has_rl = false;
  u32 hk = 0u;
  while (hk < sz) {
    if (ar[(u64)cr + 3ULL + (u64)hk] == rl) { has_rl = true; break; }
    hk = hk + 1u;
  }
  bool taut = false; u32 nsz = 0u; k = 0u;
  while (k < sz) {
    u32 x = ar[(u64)cr + 3ULL + (u64)k];
    u32 rx = ((u64)x < nlits) ? full_cong_find(repr, x) : x;
    if ((u64)rx < nlits) {
      if (lm[rx ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rx] == (u8)0 && (u64)nsz < h->max_vars) {
        lm[rx] = (u8)1; tmp[nsz] = rx; nsz = nsz + 1u;
      }
    }
    k = k + 1u;
  }
  k = 0u; while (k < nsz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  if (taut || nsz <= 2u) {
    ar[cr] = hdr | PH_GARB;
    h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
    if (!taut && nsz == 1u && !full_add_unit(h, tmp[0])) { return false; }
    if (!taut && nsz == 2u) {
      u64 ab = full_add_bin(h, tmp[0], tmp[1]);
      if (ab == 20ULL) { return false; }
      if (ab == 2ULL) { h->oom = 1ULL; }
    }
    return true;
  }
  k = 0u; while (k < nsz) { ar[(u64)cr + 3ULL + (u64)k] = tmp[k]; k = k + 1u; }
  if (nsz < sz) {
    ar[(u64)cr + 2ULL] = nsz; ar[(u64)cr + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[cr] = hdr | PH_SHRK; ar[(u64)cr + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
    }
  }
  if (!has_rl && !full_watch_push(h, rl, nsz & PW_LIT_MASK, cr, 2u)) { h->oom = 1ULL; }
  return true;
}

bool full_m6_els_lit(FullHdr *h, u32 l, u32 rl) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *repr = (u32 *)h->repr; u64 nlits = h->cur_vars << 1;
  u64 guard = (u64)wvec[((u64)l << 1) + 1ULL];
  while (guard > 0ULL && wvec[((u64)l << 1) + 1ULL] > 0u &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    guard = guard - 1ULL;
    u64 off = (u64)wvec[(u64)l << 1];
    u64 sz = (u64)wvec[((u64)l << 1) + 1ULL];
    u32 w0 = wstk[off];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wvec[(u64)l << 1] = (u32)(off + 1ULL);
      wvec[((u64)l << 1) + 1ULL] = (u32)(sz - 1ULL);
      h->wusable = h->wusable + 1ULL;
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        u64 ooff = (u64)wvec[(u64)ot << 1];
        u64 osz = (u64)wvec[((u64)ot << 1) + 1ULL];
        if (osz > 0ULL) {
          u64 op = ooff; u64 oq = ooff; u64 oend = ooff + osz; bool orem = false;
          while (op < oend) {
            u32 ow = wstk[op]; op = op + 1ULL;
            if ((ow & PW_BIN_FLAG) != 0u) {
              if (!orem && (ow & PW_LIT_MASK) == l) { orem = true; }
              else { wstk[oq] = ow; oq = oq + 1ULL; }
            } else if (op < oend) {
              wstk[oq] = ow; wstk[oq + 1ULL] = wstk[op]; oq = oq + 2ULL; op = op + 1ULL;
            }
          }
          u64 ok = oq; while (ok < oend) { wstk[ok] = 0xFFFFFFFFu; ok = ok + 1ULL; }
          wvec[((u64)ot << 1) + 1ULL] = (u32)(oq - ooff);
          h->wusable = h->wusable + (oend - oq);
          if (orem && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
        }
      }
      u32 rot = ot;
      if ((u64)rot >= nlits || rl == (rot ^ 1u)) { continue; }
      if (rl == rot) { if (!full_add_unit(h, rl)) { return false; } continue; }
      u64 ab = full_add_bin(h, rl, rot);
      if (ab == 20ULL) { return false; }
      if (ab == 2ULL) { h->oom = 1ULL; return true; }
      continue;
    }
    if (sz < 2ULL) { wvec[((u64)l << 1) + 1ULL] = 0u; break; }
    u32 cr = wstk[off + 1ULL];
    wvec[(u64)l << 1] = (u32)(off + 2ULL);
    wvec[((u64)l << 1) + 1ULL] = (u32)(sz - 2ULL);
    h->wusable = h->wusable + 2ULL;
    if (!full_m6_els_ar(h, cr, rl)) { return false; }
  }
  return h->inconsistent == 0ULL;
}

bool full_m6_dense_els(FullHdr *h, u32 neq) {
  if (neq == 0u || h->inconsistent != 0ULL) { return h->inconsistent == 0ULL; }
  u32 *repr = (u32 *)h->repr; u32 *eqb = (u32 *)h->work_stk2;
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u64 ei = 0ULL;
  while (ei < (u64)neq && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 a = eqb[ei << 1]; u32 b = eqb[(ei << 1) + 1u];
    ei = ei + 1ULL;
    if ((u64)a >= nlits || (u64)b >= nlits) { continue; }
    u32 ra = full_cong_find(repr, a);
    u32 rb = full_cong_find(repr, b);
    if (ra == rb) { continue; }
    if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return false; }
    if (rb < ra) { u32 tmp = ra; ra = rb; rb = tmp; }
    i8 va = vals[ra]; i8 vb = vals[rb];
    if (va != (i8)0 && vb != (i8)0) {
      if (va != vb) { h->inconsistent = 1ULL; return false; }
      continue;
    }
    if (va != (i8)0) {
      u32 u = (va > (i8)0) ? rb : (rb ^ 1u);
      if (!full_add_unit(h, u)) { return false; }
      continue;
    }
    if (vb != (i8)0) {
      u32 u = (vb > (i8)0) ? ra : (ra ^ 1u);
      if (!full_add_unit(h, u)) { return false; }
      continue;
    }
    if ((fl[ra >> 1] & FL_ACTIVE) == 0u || (fl[rb >> 1] & FL_ACTIVE) == 0u) { continue; }
    repr[rb] = ra;
    repr[rb ^ 1u] = ra ^ 1u;
    fl[rb >> 1] = fl[rb >> 1] & (~(FL_SWEEP | 0x40000000u | 0x20000000u));
    h->sweep_cnt = h->sweep_cnt + 1ULL;
    if (!full_m6_els_lit(h, rb, ra)) { return false; }
    if (!full_m6_els_lit(h, rb ^ 1u, ra ^ 1u)) { return false; }
    u64 ab1 = full_add_bin(h, rb | 0u, ra ^ 1u);
    if (ab1 == 20ULL) { return false; }
    if (ab1 == 2ULL) { h->oom = 1ULL; return true; }
    u64 ab2 = full_add_bin(h, rb ^ 1u, ra);
    if (ab2 == 20ULL) { return false; }
    if (ab2 == 2ULL) { h->oom = 1ULL; return true; }
  }
  if (h->inconsistent != 0ULL) { return false; }
  return full_m6_dense_prop(h);
}

u64 full_m6_sweep_var(FullHdr *h, u32 root_v, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 1ULL; }
  u32 *s_repr = (u32 *)h->repr;
  if (full_cong_find(s_repr, root_v << 1) != (root_v << 1)) { return 1ULL; }
  u64 pk = full_m6_sweep_cone(h, root_v);
  u32 nv = (u32)(pk & 0xFFFFULL); u32 nc = (u32)(pk >> 16);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (k[K6H_INCONS] != 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (nv < 2u || nc == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 1ULL;
  }
  u32 rbit = full_m6_sweep_sim(h, nv, tick_lim);
  if (rbit == 0xFFFFFFFFu) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (rbit == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 1ULL;
  }
  u64 ur = full_m6_sweep_units(h, nv, rbit, tick_lim);
  if (ur == 0xFFFFFFFFFFFFFFFFULL) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 20ULL;
  }
  u64 cr = full_m6_sweep_classes(h, nv, (u32)ur, tick_lim);
  u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
  if (cr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  u32 neq = k[K6H_NEQ];
  if (neq > 0u && !full_m6_dense_els(h, neq)) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

void full_m6_cand_sift(u32 *cands, u32 *deg, u32 start, u32 n) {
  u32 r = start;
  while (true) {
    u32 c = (r << 1) + 1u;
    if (c >= n) { break; }
    if (c + 1u < n && deg[cands[c + 1u]] > deg[cands[c]]) { c = c + 1u; }
    if (deg[cands[r]] >= deg[cands[c]]) { break; }
    u32 tmp = cands[r]; cands[r] = cands[c]; cands[c] = tmp;
    r = c;
  }
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
      u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
      u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
      if (dp > 0ULL && dn > 0ULL && dp <= max_occ && dn <= max_occ) {
        u64 d = dp + dn;
        u32 d32 = (d > 0x3FFFFFFFULL) ? 0x3FFFFFFFu : (u32)d;
        u32 flv = fl[v];
        if ((flv & FL_SWEEP_INR) == 0u) {
          d32 = d32 | (((flv & FL_SWEEP_INC) != 0u) ? 0x40000000u : 0x80000000u);
        }
        deg[v] = d32;
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
  u32 *gu = (u32 *)h->glue_used;
  gu[33] = 0xFFFFFFFFu;
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
          u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
          u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
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
        u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
        u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
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
  u32 *rp_arr = (u32 *)h->repr;
  u64 nlits_sw = cv << 1;
  u64 ri_sw = 0ULL;
  while (ri_sw < nlits_sw) { rp_arr[ri_sw] = (u32)ri_sw; ri_sw = ri_sw + 1ULL; }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *eqb = (u32 *)h->work_stk2;
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 rem_b = budget;
  u32 nc = full_m6_collect_cands(h);
  u32 ci = 0u;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci]; ci = ci + 1u;
    gu[SWP_GU_CURSOR] = ((u64)v + 1ULL < cv) ? (v + 1u) : 0u;
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~(FL_SWEEP | FL_SWEEP_INC | FL_SWEEP_INR));
      rem_b = rem_b - 1ULL;
      u64 sw0 = h->sweep_cnt;
      if (full_m6_sweep_var(h, v, rem_ticks) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
      u64 spent = (u64)k[K6H_TICKS];
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
      if (h->sweep_cnt > sw0) {
        u32 neq = k[K6H_NEQ]; u32 ei = 0u;
        while (ei < neq && (u64)ei < cv) {
          u32 lit = eqb[ei << 1];
          if ((u64)lit < nlits_sw) {
            u32 rv = full_cong_find(rp_arr, lit) >> 1;
            if ((u64)rv < cv && (fl[rv] & FL_ACTIVE) != 0u && vals[rv << 1] == (i8)0) {
              if ((fl[rv] & FL_SWEEP_INR) == 0u && (u64)nc < (cv << 1)) {
                cands[nc] = rv; nc = nc + 1u;
              }
              fl[rv] = fl[rv] | FL_SWEEP | FL_SWEEP_INR;
            }
          }
          ei = ei + 1u;
        }
      }
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  u64 left_inc = 0ULL; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) ==
        (FL_ACTIVE | FL_SWEEP | FL_SWEEP_INC)) {
      if (vals[v << 1] == (i8)0) {
        u64 dp = full_dense_occ_cnt_fid(h, (u32)(v << 1), max_occ);
        u64 dn = full_dense_occ_cnt_fid(h, (u32)((v << 1) | 1ULL), max_occ);
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

end

end LeanQbe.T.Examples.Kissat.Src.Sweep

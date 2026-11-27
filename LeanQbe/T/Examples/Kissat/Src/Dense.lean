/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Dense Watch Mode Transition & Propagation (`Src/Dense.lean`)

Mirrors upstream `kissat/src/dense.c, propdense.c` (`7` live functions, DAG level `L3`):
- `full_enter_dense` (R4: `kissat_enter_dense_mode`)
- `full_rebuild_watches_nosort_fid` (R4: `kissat_resume_sparse_nosort`)
- `full_rebuild_watches` (R4: `kissat_resume_sparse_mode`)
- `full_m6_dense_prop_lit` (R4: `kissat_dense_propagate_literal`)
- `full_m6_dense_prop` (R4: `kissat_dense_propagate`)
- `full_dense_prop_unit_m7` (R4: `kissat_dense_propagate_unit`)
- `full_dense_flush_units_m7` (R4: `kissat_dense_flush_units`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Dense

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! dense "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_sort_bin_watches_fid(FullHdr *h);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_propagate(FullHdr *h);
extern u64 full_flush_trail(FullHdr *h);
extern void full_sweep_bins(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);

bool full_enter_dense(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return false; }
  if (h->dense_mode != 0ULL) { return true; }
  if (full_flush_trail(h) != 1ULL) { return false; }
  if (h->unflushed > 0ULL) {
    u64 sr_d = full_arena_sweep(h);
    if (sr_d == 2ULL) { h->inconsistent = 1ULL; return false; }
    if (full_propagate(h) == 1ULL) { h->inconsistent = 1ULL; return false; }
    if (full_flush_trail(h) != 1ULL) { return false; }
    h->unflushed = 0ULL;
  }
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
          h->oom = 0ULL; full_arena_sweep(h); return false;
        }
        k = k + 1u;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  h->dense_mode = 1ULL;
  return true;
}

u64 full_rebuild_watches_nosort_fid(FullHdr *h) {
  h->dense_mode = 0ULL;
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (sr == 0ULL) { h->unflushed = 0ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    if (sr == 0ULL) { break; }
  }
  return 1ULL;
}

u64 full_rebuild_watches(FullHdr *h) {
  u64 rr = full_rebuild_watches_nosort_fid(h);
  if (rr == 1ULL) { full_sort_bin_watches_fid(h); }
  return rr;
}

bool full_m6_dense_prop_lit(FullHdr *h, u32 lit) {
  u32 not_lit = lit ^ 1u; u64 nlits = h->cur_vars << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)not_lit << 1];
  u64 end = off + (u64)wvec[((u64)not_lit << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot >= nlits || vals[ot] > (i8)0) { continue; }
      if (vals[ot] < (i8)0) {
        h->inconsistent = 1ULL; h->confl_type = 1ULL;
        h->confl_lit0 = (u64)not_lit; h->confl_lit1 = (u64)ot; return false;
      }
      full_assign_lvl(h, ot, 0xFFFFFFFFu, 0u);
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    if ((u64)cr + 3ULL > h->arena_len) { continue; }
    u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
    if ((hdr & PH_GARB) != 0u || csz < 3u || (u64)cr + 3ULL + (u64)csz > h->arena_len) {
      continue;
    }
    bool sat = false; u32 non_false = 0u; u32 unit = 0xFFFFFFFFu; u32 i = 0u;
    while (i < csz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)i];
      if ((u64)cl < nlits) {
        i8 v = vals[cl];
        if (v > (i8)0) { sat = true; break; }
        if (v == (i8)0) {
          non_false = non_false + 1u; unit = cl;
          if (non_false > 1u) { break; }
        }
      }
      i = i + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      continue;
    }
    if (non_false == 0u) {
      h->inconsistent = 1ULL; h->confl_type = 2ULL; h->confl_ref = (u64)cr; return false;
    }
    if (non_false == 1u && vals[unit] == (i8)0) {
      full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u);
    }
  }
  return true;
}

bool full_m6_dense_prop(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  while (h->propagated < h->trail_end && h->inconsistent == 0ULL) {
    u32 lit = trl[h->propagated];
    h->propagated = h->propagated + 1ULL;
    if (!full_m6_dense_prop_lit(h, lit)) { return false; }
  }
  return h->inconsistent == 0ULL;
}

bool full_dense_prop_unit_m7(FullHdr *h, u32 lit) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  if ((u64)lit >= nlits || vals[lit] <= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 nl = lit ^ 1u;
  u64 off = (u64)wvec[(u64)nl << 1];
  u64 end = off + (u64)wvec[((u64)nl << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      i8 vo = vals[ot];
      if (vo < (i8)0) { h->inconsistent = 1ULL; return false; }
      if (vo == (i8)0 && !full_add_unit(h, ot)) { return false; }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    u32 hdr = ar[cr];
    if ((hdr & PH_GARB) != 0u) { continue; }
    u32 sz = ar[(u64)cr + 2ULL];
    bool sat = false;
    u32 unass = 0u;
    u32 ulit = 0u;
    u32 k = 0u;
    while (k < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)k];
      i8 vl = vals[cl];
      if (vl > (i8)0) { sat = true; break; }
      if (vl == (i8)0) {
        unass = unass + 1u;
        if (unass > 1u) { break; }
        ulit = cl;
      }
      k = k + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    } else if (unass == 0u) {
      h->inconsistent = 1ULL;
      return false;
    } else if (unass == 1u) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, ulit)) { return false; }
    }
  }
  off = (u64)wvec[(u64)lit << 1];
  end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    u32 hdr = ar[cr];
    if ((hdr & PH_GARB) != 0u) { continue; }
    u32 sz = ar[(u64)cr + 2ULL];
    bool sat = false;
    u32 k = 0u;
    while (k < sz) {
      if (vals[ar[(u64)cr + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
      k = k + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    }
  }
  return true;
}

bool full_dense_flush_units_m7(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  u64 q = h->propagated;
  while (q < h->trail_end && h->inconsistent == 0ULL) {
    u32 lit = trl[q];
    q = q + 1ULL;
    if (!full_dense_prop_unit_m7(h, lit)) { return false; }
  }
  h->propagated = (q <= h->trail_end) ? q : h->trail_end;
  return h->inconsistent == 0ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Dense

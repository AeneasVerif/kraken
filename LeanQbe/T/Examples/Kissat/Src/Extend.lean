/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Reconstruction Stack & Model Extension (`Src/Extend.lean`)

Mirrors upstream `kissat/src/extend.c, weaken.c` (`5` live functions, DAG level `L0`):
- `full_extend_push2` (R4: `kissat_weaken_binary`)
- `full_extend_push_cl` (R4: `kissat_weaken_clause`)
- `full_extend_core_fid` (R4: `kissat_extend_stack`)
- `full_unperm_fid` (R4: `kissat_unpermute_model`)
- `full_extend` (R4: `kissat_extend`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Extend

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! extend "
#include \"kissat_internal.h\"

bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other) {
  u64 nlits = h->cur_vars << 1;
  u32 ot = other & PW_LIT_MASK;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool skip_ot = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] < (i8)0);
  u64 need = skip_ot ? 1ULL : 2ULL;
  if (h->extend_len > h->extend_cap || need > h->extend_cap - h->extend_len) {
    return false;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = (blk_lit & PW_LIT_MASK) | EXT_BLK_FLAG;
  if (!skip_ot) { ext[p + 1ULL] = ot; }
  h->extend_len = p + need;
  return true;
}

bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 sz = ar[(u64)cref + 2ULL];
  if ((u64)cref + 3ULL + (u64)sz > h->arena_len) { return false; }
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 bl = blk_lit & PW_LIT_MASK;
  u64 keep = 0ULL;
  u32 i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i] & PW_LIT_MASK;
    if (lit != bl && !((u64)lit < nlits && lvl[lit >> 1] == 0u && vals[lit] < (i8)0)) {
      keep = keep + 1ULL;
    }
    i = i + 1u;
  }
  u64 need = 1ULL + keep;
  if (h->extend_len > h->extend_cap || need > h->extend_cap - h->extend_len) {
    return false;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = bl | EXT_BLK_FLAG;
  p = p + 1ULL;
  i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i] & PW_LIT_MASK;
    if (lit != bl && !((u64)lit < nlits && lvl[lit >> 1] == 0u && vals[lit] < (i8)0)) {
      ext[p] = lit; p = p + 1ULL;
    }
    i = i + 1u;
  }
  h->extend_len = p;
  return true;
}

void full_extend_core_fid(FullHdr *h) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ext = (u32 *)h->extend_stk;
  u64 mx = h->max_vars;
  u64 v = 0ULL;
  while (v < mx) {
    if ((fl[v] & (FL_ELIM | FL_SUBST)) != 0u || vals[v << 1] == (i8)0) {
      vals[v << 1] = (i8)1; vals[(v << 1) | 1ULL] = (i8)(-1);
    }
    v = v + 1ULL;
  }
  u64 end = h->extend_len;
  while (end > 0ULL) {
    u64 start = end;
    while (start > 0ULL) {
      start = start - 1ULL;
      if ((ext[start] & EXT_BLK_FLAG) != 0u) { break; }
    }
    u32 head = ext[start];
    if ((head & EXT_COMPACT_FLAG) != 0u) {
      u64 ncv = (u64)(head & EXT_CNT_MASK);
      if (start + 1ULL + ncv <= end && ncv <= mx) {
        u64 k = ncv;
        while (k > 0ULL) {
          k = k - 1ULL;
          u32 ov = ext[start + 1ULL + k];
          if ((u64)ov < mx) {
            i8 pv = vals[k << 1];
            i8 nv = vals[(k << 1) | 1ULL];
            vals[(u64)ov << 1] = pv;
            vals[((u64)ov << 1) | 1ULL] = nv;
          }
        }
        u64 j = 0ULL;
        u64 g = 0ULL;
        while (g < mx) {
          u64 nxt = (j < ncv) ? (u64)ext[start + 1ULL + j] : mx;
          if (g == nxt) { j = j + 1ULL; }
          else { vals[g << 1] = (i8)1; vals[(g << 1) | 1ULL] = (i8)(-1); }
          g = g + 1ULL;
        }
      }
    } else {
      bool sat = false;
      u64 p = start;
      while (p < end) {
        u32 lit = ext[p] & PW_LIT_MASK;
        if ((u64)(lit >> 1) < mx && vals[lit] > (i8)0) { sat = true; break; }
        p = p + 1ULL;
      }
      u32 blk = head & PW_LIT_MASK;
      if (!sat && (u64)(blk >> 1) < mx) {
        vals[blk] = (i8)1; vals[blk ^ 1u] = (i8)(-1);
      }
    }
    end = start;
  }
}

void full_unperm_fid(FullHdr *h) {
  u64 len = h->extend_len;
  if (len == 0ULL || len > h->extend_cap) { return; }
  u32 *ext = (u32 *)h->extend_stk;
  u32 head = ext[0];
  if ((head & (EXT_BLK_FLAG | EXT_COMPACT_FLAG | EXT_PERM_FLAG)) !=
      (EXT_BLK_FLAG | EXT_PERM_FLAG)) {
    return;
  }
  u64 mv = (u64)(head & EXT_PERM_MASK);
  u64 mx = h->max_vars;
  if (mv > mx || 1ULL + mv > len) { return; }
  i8 *vals = (i8 *)h->values;
  u64 e = 0ULL;
  while (e < mv) {
    u32 iv = ext[1ULL + e];
    i8 pv = (i8)1;
    if ((u64)iv < mx) {
      i8 vv = vals[(u64)iv << 1];
      if (vv < (i8)0) { pv = (i8)(-1); }
    }
    vals[(e << 1) | 1ULL] = pv;
    e = e + 1ULL;
  }
  e = 0ULL;
  while (e < mv) {
    i8 pv = vals[(e << 1) | 1ULL];
    vals[e << 1] = pv;
    vals[(e << 1) | 1ULL] = (pv > (i8)0) ? (i8)(-1) : (i8)1;
    e = e + 1ULL;
  }
}

void full_extend(FullHdr *h) {
  full_extend_core_fid(h);
  full_unperm_fid(h);
}
"

/-- Ordered live functions of `Src/Extend.lean` (`5` fns). -/
def fns : List Fn := extend_fns

end

public section

theorem full_extend_push2_wf : Func.Wf full_extend_push2_body := by kissat_wf_reify
theorem full_extend_push_cl_wf : Func.Wf full_extend_push_cl_body := by kissat_wf_reify
theorem full_extend_core_fid_wf : Func.Wf full_extend_core_fid_body := by kissat_wf_reify
theorem full_unperm_fid_wf : Func.Wf full_unperm_fid_body := by kissat_wf_reify
theorem full_extend_wf : Func.Wf full_extend_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, extend_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_extend_push2_wf
  · exact full_extend_push_cl_wf
  · exact full_extend_core_fid_wf
  · exact full_unperm_fid_wf
  · exact full_extend_wf

end

end LeanQbe.T.Examples.Kissat.Src.Extend

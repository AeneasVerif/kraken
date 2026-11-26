/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Literal Assignment, Phase Saving & Chronological Backtracking (`Src/Backtrack.lean`)

Mirrors upstream `kissat/src/assign.c, backtrack.c` (`6` live functions, DAG level `L1`):
- `full_assign_lvl` (R4: `kissat_assign_at_level`)
- `full_assign` (R4: `kissat_assign`)
- `full_save_target_best` (R4: `kissat_update_target_and_best_phases`)
- `full_backtrack_raw_m5` (R4: `kissat_backtrack_without_updating_phases`)
- `full_backtrack` (R4: `kissat_backtrack`)
- `full_backtrack_ac_fid` (R4: `kissat_backtrack_after_conflict`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Backtrack

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! backtrack "
#include \"kissat_internal.h\"

extern void full_heap_push(FullHdr *h, u32 v);

void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl) {
  u32 v = lit >> 1;
  if ((u64)v >= h->cur_vars || h->trail_end >= h->max_vars) { return; }
  i8 *vals = (i8 *)h->values;
  if (vals[lit] != (i8)0) { return; }
  i8 *ph = (i8 *)h->phases;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  vals[lit] = (i8)1;
  vals[lit ^ 1u] = (i8)(-1);
  if ((fl[v] & FL_ACTIVE) != 0u && h->unassigned > 0ULL) {
    h->unassigned = h->unassigned - 1ULL;
  }
  if (h->probing == 0ULL) {
    ph[v] = ((lit & 1u) != 0u) ? (i8)(-1) : (i8)1;
  }
  lvl[v] = alvl;
  if (alvl == 0u) {
    rsns[v] = 0xFFFFFFFFu;
    fl[v] = fl[v] & (~FL_ACTIVE);
    h->unflushed = h->unflushed + 1ULL;
  } else {
    rsns[v] = rsn;
  }
  tpos[v] = (u32)h->trail_end;
  trl[h->trail_end] = lit;
  h->trail_end = h->trail_end + 1ULL;
}

void full_assign(FullHdr *h, u32 lit, u32 rsn) {
  full_assign_lvl(h, lit, rsn, (u32)h->cur_level);
}

void full_save_target_best(FullHdr *h) {
  if (h->probing != 0ULL || h->stable == 0ULL) { return; }
  i8 *vals = (i8 *)h->values;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  u64 assigned = (cv > h->unassigned) ? (cv - h->unassigned) : 0ULL;
  if (assigned > h->target_assigned) {
    h->target_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) {
      i8 tv = vals[k << 1];
      if (tv != (i8)0) { ptgt[k] = tv; }
      k = k + 1ULL;
    }
  }
  if (assigned > h->best_assigned) {
    h->best_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) {
      i8 tv = vals[k << 1];
      if (tv != (i8)0) { pbst[k] = tv; }
      k = k + 1ULL;
    }
  }
}

void full_backtrack_raw_m5(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  full_save_target_best(h);
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail;
  u64 cv = h->cur_vars;
  u64 q = (u64)ftrl[target_lvl + 1ULL];
  if (q > h->trail_end) { q = h->trail_end; }
  u64 q_start = q;
  u64 p = q;
  while (p < h->trail_end) {
    u32 lit = trl[p];
    u32 v = lit >> 1;
    if ((u64)v < cv && (u64)lvl[v] <= target_lvl) {
      trl[q] = lit; tpos[v] = (u32)q; q = q + 1ULL;
    } else if ((u64)v < cv) {
      vals[lit] = (i8)0; vals[lit ^ 1u] = (i8)0;
      lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
      if ((fl[v] & FL_ACTIVE) != 0u) { h->unassigned = h->unassigned + 1ULL; }
      if (h->stable != 0ULL) { full_heap_push(h, v); }
      else if ((u64)qs[v] > h->q_search_stamp) {
        h->q_search_idx = (u64)v; h->q_search_stamp = (u64)qs[v];
      }
    }
    p = p + 1ULL;
  }
  h->trail_end = q;
  if (h->propagated > q_start) { h->propagated = q_start; }
  if (h->propagated > q) { h->propagated = q; }
  h->cur_level = target_lvl;
}

void full_backtrack(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  full_save_target_best(h);
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  full_backtrack_raw_m5(h, target_lvl);
  h->probing = saved_prob;
}

void full_backtrack_ac_fid(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  if (h->probing == 0ULL && h->stable != 0ULL) {
    u64 back = h->cur_level - 1ULL;
    if (back < h->max_vars) {
      h->probing = 1ULL;
      full_backtrack_raw_m5(h, back);
      h->probing = 0ULL;
      full_save_target_best(h);
      if (target_lvl < back) {
        h->probing = 1ULL;
        full_backtrack_raw_m5(h, target_lvl);
        h->probing = 0ULL;
      }
      return;
    }
    full_save_target_best(h);
  }
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  full_backtrack_raw_m5(h, target_lvl);
  h->probing = saved_prob;
}
"

/-- Ordered live functions of `Src/Backtrack.lean` (`6` fns). -/
def fns : List Fn := backtrack_fns

end

public section

theorem full_assign_lvl_wf : Func.Wf full_assign_lvl_body := by kissat_wf_reify
theorem full_assign_wf : Func.Wf full_assign_body := by kissat_wf_reify
theorem full_save_target_best_wf : Func.Wf full_save_target_best_body := by kissat_wf_reify
theorem full_backtrack_raw_m5_wf : Func.Wf full_backtrack_raw_m5_body := by kissat_wf_reify
theorem full_backtrack_wf : Func.Wf full_backtrack_body := by kissat_wf_reify
theorem full_backtrack_ac_fid_wf : Func.Wf full_backtrack_ac_fid_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, backtrack_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_assign_lvl_wf
  · exact full_assign_wf
  · exact full_save_target_best_wf
  · exact full_backtrack_raw_m5_wf
  · exact full_backtrack_wf
  · exact full_backtrack_ac_fid_wf

end

end LeanQbe.T.Examples.Kissat.Src.Backtrack

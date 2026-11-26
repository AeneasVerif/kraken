/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Clause Creation (Large, Binary & Unit) (`Src/Clause.lean`)

Mirrors upstream `kissat/src/clause.c` (`4` live functions, DAG level `L2`):
- `full_add_clause` (R4: `kissat_new_clause`)
- `full_add_bin_m6` (R4: `kissat_new_binary_clause_impl`)
- `full_add_bin` (R4: `kissat_new_binary_clause`)
- `full_add_unit` (R4: `kissat_assign_unit`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Clause

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! clause "
#include \"kissat_internal.h\"

extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_watch_pop_c0(FullHdr *h, u32 lit, u32 cnt);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack(FullHdr *h, u64 target_lvl);

u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red) {
  u32 *tmp = (u32 *)h->tmp_lits;
  if (len == 2u) {
    u32 b0 = (tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (tmp[0] & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, tmp[0], b0, 0u, 1u)) { return 0xFFFFFFFFULL; }
    if (!full_watch_push(h, tmp[1], b1, 0u, 1u)) {
      full_watch_pop_c0(h, tmp[0], 1u);
      return 0xFFFFFFFFULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFEULL;
  }
  if (len < 3u) { return 0xFFFFFFFFULL; }
  u64 cref = full_alloc_cl(h, len, glue, red);
  if (cref == 0xFFFFFFFFULL) { return 0xFFFFFFFFULL; }
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < len) { ar[cref + 3ULL + (u64)i] = tmp[i]; i = i + 1u; }
  if (!full_watch_push(h, tmp[0], tmp[1] & PW_LIT_MASK, (u32)cref, 2u)) {
    h->arena_len = cref;
    return 0xFFFFFFFFULL;
  }
  if (!full_watch_push(h, tmp[1], tmp[0] & PW_LIT_MASK, (u32)cref, 2u)) {
    full_watch_pop_c0(h, tmp[0], 2u);
    h->arena_len = cref;
    return 0xFFFFFFFFULL;
  }
  if (red) {
    h->num_redundant = h->num_redundant + 1ULL;
    if (h->first_reducible == 0xFFFFFFFFULL) { h->first_reducible = cref; }
  } else {
    h->num_irred = h->num_irred + 1ULL;
  }
  return cref;
}

u64 full_add_bin_m6(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == (b ^ 1u)) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  if (vals[a] > (i8)0 || vals[b] > (i8)0) { return 0ULL; }
  if (vals[a] < (i8)0 && vals[b] < (i8)0) { h->inconsistent = 1ULL; return 20ULL; }
  if (vals[a] < (i8)0 || a == b) { full_assign_lvl(h, b, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (vals[b] < (i8)0) { full_assign_lvl(h, a, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (full_has_bin(h, a, b)) { return 0ULL; }
  u32 b0 = (b & PW_LIT_MASK) | PW_BIN_FLAG;
  u32 b1 = (a & PW_LIT_MASK) | PW_BIN_FLAG;
  if (!full_watch_push(h, a, b0, 0u, 1u) || !full_watch_push(h, b, b1, 0u, 1u)) {
    h->oom = 1ULL; return 2ULL;
  }
  u32 *fl = (u32 *)h->flags;
  u32 va = a >> 1; u32 vb = b >> 1;
  u32 addf = FL_TRANS | FL_BONE0 | FL_BONE1;
  fl[va] = fl[va] | addf;
  fl[vb] = fl[vb] | addf;
  h->num_binary = h->num_binary + 1ULL;
  return 1ULL;
}

u64 full_add_bin(FullHdr *h, u32 a, u32 b) {
  return full_add_bin_m6(h, a, b);
}

bool full_add_unit(FullHdr *h, u32 lit) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if ((u64)(lit >> 1) >= h->cur_vars) { return false; }
  i8 *vals = (i8 *)h->values;
  if (vals[lit] > (i8)0) { return true; }
  if (vals[lit] < (i8)0) { h->inconsistent = 1ULL; return false; }
  full_assign_lvl(h, lit, 0xFFFFFFFFu, 0u);
  return true;
}
"

/-- Ordered live functions of `Src/Clause.lean` (`4` fns). -/
def fns : List Fn := clause_fns

end

public section

theorem full_add_clause_wf : Func.Wf full_add_clause_body := by kissat_wf_reify
theorem full_add_bin_m6_wf : Func.Wf full_add_bin_m6_body := by kissat_wf_reify
theorem full_add_bin_wf : Func.Wf full_add_bin_body := by kissat_wf_reify
theorem full_add_unit_wf : Func.Wf full_add_unit_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, clause_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_add_clause_wf
  · exact full_add_bin_m6_wf
  · exact full_add_bin_wf
  · exact full_add_unit_wf

end

end LeanQbe.T.Examples.Kissat.Src.Clause

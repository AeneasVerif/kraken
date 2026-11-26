/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 VSIDS Binary Max-Heap (`Src/Heap.lean`)

Mirrors upstream `kissat/src/heap.c` (`4` live functions, DAG level `L0`):
- `full_heap_up` (R4: `kissat_bubble_up`)
- `full_heap_down` (R4: `kissat_bubble_down`)
- `full_heap_push` (R4: `kissat_push_heap`)
- `full_heap_pop` (R4: `kissat_pop_heap`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Heap

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! heap "
#include \"kissat_internal.h\"

void full_heap_up(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  if ((u64)p >= h->heap_len || h->heap_len > h->cur_vars || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (p > 0u) {
    u32 pp = (p - 1u) >> 1;
    u32 pv = hp[pp];
    if ((u64)pv >= h->cur_vars || sc[pv] >= vsc) { break; }
    hp[p] = pv; ps[pv] = p; p = pp;
  }
  hp[p] = v; ps[v] = p;
}

void full_heap_down(FullHdr *h, u32 v) {
  u64 nvars = h->cur_vars;
  if ((u64)v >= nvars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  u64 hlen = h->heap_len;
  if ((u64)p >= hlen || hlen > nvars || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (true) {
    u64 cp = ((u64)p << 1) + 1ULL;
    if (cp >= hlen) { break; }
    u32 cv = hp[cp];
    if ((u64)cv >= nvars) { break; }
    u64 csc = sc[cv];
    u64 sp = cp + 1ULL;
    if (sp < hlen) {
      u32 sv = hp[sp];
      if ((u64)sv < nvars) {
        u64 ssc = sc[sv];
        if (ssc > csc) { cp = sp; cv = sv; csc = ssc; }
      }
    }
    if (csc <= vsc) { break; }
    hp[p] = cv;
    ps[cv] = p;
    p = (u32)cp;
  }
  hp[p] = v;
  ps[v] = p;
}

void full_heap_push(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  if (ps[v] != 0xFFFFFFFFu || h->heap_len >= h->cur_vars) { return; }
  u32 idx = (u32)h->heap_len;
  h->heap_len = h->heap_len + 1ULL;
  hp[idx] = v; ps[v] = idx;
  full_heap_up(h, v);
}

u64 full_heap_pop(FullHdr *h) {
  u64 nvars = h->cur_vars;
  u64 hlen = h->heap_len;
  if (hlen == 0ULL || hlen > nvars) { return 0xFFFFFFFFULL; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 top = hp[0];
  u64 nlen = hlen - 1ULL;
  h->heap_len = nlen;
  u32 last = hp[nlen];
  if ((u64)top < nvars) { ps[top] = 0xFFFFFFFFu; }
  if (nlen > 0ULL && (u64)last < nvars) {
    hp[0] = last;
    ps[last] = 0u;
    full_heap_down(h, last);
  }
  if ((u64)top >= nvars) { return 0xFFFFFFFFULL; }
  return (u64)top;
}
"

/-- Ordered live functions of `Src/Heap.lean` (`4` fns). -/
def fns : List Fn := heap_fns

end

public section

theorem full_heap_up_wf : Func.Wf full_heap_up_body := by kissat_wf_reify
theorem full_heap_down_wf : Func.Wf full_heap_down_body := by kissat_wf_reify
theorem full_heap_push_wf : Func.Wf full_heap_push_body := by kissat_wf_reify
theorem full_heap_pop_wf : Func.Wf full_heap_pop_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, heap_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_heap_up_wf
  · exact full_heap_down_wf
  · exact full_heap_push_wf
  · exact full_heap_pop_wf

end

end LeanQbe.T.Examples.Kissat.Src.Heap

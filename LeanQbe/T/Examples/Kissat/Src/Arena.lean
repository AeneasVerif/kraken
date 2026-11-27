/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Clause Arena Allocation & Traversal (`Src/Arena.lean`)

Mirrors upstream `kissat/src/arena.c` (`2` live functions, DAG level `L0`):
- `full_arena_next` (R4: `kissat_arena_next`)
- `full_alloc_cl` (R4: `kissat_allocate_clause`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Arena

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! arena "
#include \"kissat_internal.h\"

u32 full_arena_next(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u64 alen = h->arena_len;
  if ((u64)cref + 3ULL > alen) { return (u32)alen; }
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  u64 p = (u64)cref + 3ULL + (u64)sz;
  if (p > alen) { return (u32)alen; }
  if ((hdr & PH_SHRK) != 0u) {
    while (p < alen && ar[p] != 0xFFFFFFFFu) { p = p + 1ULL; }
    if (p < alen) { p = p + 1ULL; }
  }
  return (u32)p;
}

u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red) {
  u64 need = 3ULL + (u64)sz;
  if (need > h->arena_cap - h->arena_len) { return 0xFFFFFFFFULL; }
  u64 cref = h->arena_len;
  h->arena_len = cref + need;
  u32 *ar = (u32 *)h->arena;
  u32 g = (glue > PH_GLUE_MASK) ? PH_GLUE_MASK : glue;
  ar[cref] = g | (red ? PH_RED : 0u);
  ar[cref + 1ULL] = 2u;
  ar[cref + 2ULL] = sz;
  return cref;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Arena

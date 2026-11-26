/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Flat-Array C0 AIG Core (`Bitblast/Src/Aig.lean`)

Provides:
- `bv_hash_pair`: pure integer hash over `(lhs, rhs)` (zero pointer-value hashing)
- `bv_aig_init`: initializes AIG pointers and clears the untrusted HT hint array
- `bv_mk_and`: constant/negation/AND folding + untrusted HT lookup with mandatory dynamic
  verification `A < idx && idx < len && aig[idx] == key`
- `bv_aig_not`, `bv_aig_or`, `bv_aig_xor`, `bv_aig_beq`, `bv_aig_ite`
- `bv_lits_mark`, `bv_lits_release`, `bv_lits_alloc`: bump-allocated `lits` pool
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.Aig

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! aig "
#include \"bitblast_internal.h\"

u32 bv_hash_pair(u32 lhs, u32 rhs) {
  u64 x = ((u64)lhs) * 2654435761ULL ^ ((u64)rhs) * 2246822519ULL;
  x = (x ^ (x >> 16)) * 0x45d9f3bULL;
  return (u32)(x ^ (x >> 16));
}

void bv_aig_init(BVHdr *h, u64 aig_ptr, u32 aig_cap, u64 ht_ptr, u32 ht_mask, u32 num_atoms) {
  h->aig_ptr = aig_ptr;
  h->aig_cap = aig_cap;
  h->ht_ptr = ht_ptr;
  h->ht_mask = ht_mask;
  h->num_atoms = num_atoms;
  h->aig_len = num_atoms + 1u;
  h->oom = 0u;
  u32 *ht = (u32 *)ht_ptr;
  u64 nslots = (u64)ht_mask + 1ULL;
  u64 i = 0ULL;
  while (i < nslots) {
    ht[i] = 0u;
    i = i + 1ULL;
  }
}

u32 bv_mk_and(BVHdr *h, u32 lhs, u32 rhs) {
  if (h->oom != 0u) { return 0u; }
  if (lhs == 0u || rhs == 0u) { return 0u; }
  if (lhs == 1u) { return rhs; }
  if (rhs == 1u) { return lhs; }
  if (lhs == rhs) { return lhs; }
  if (lhs == (rhs ^ 1u)) { return 0u; }
  if (lhs > rhs) {
    u32 tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  u32 A = h->num_atoms;
  u32 len = h->aig_len;
  if (len <= A || (lhs >> 1) >= len || (rhs >> 1) >= len) {
    h->oom = 1u;
    return 0u;
  }
  u64 key = ((u64)lhs) | (((u64)rhs) << 32);
  u32 *ht = (u32 *)h->ht_ptr;
  u64 *aig = (u64 *)h->aig_ptr;
  u32 mask = h->ht_mask;
  u32 h0 = bv_hash_pair(lhs, rhs) & mask;
  u32 slot = h0;
  u32 write_slot = h0;
  u32 probe = 0u;
  while (probe < 16u) {
    u32 idx = ht[slot];
    if (idx == 0u) {
      write_slot = slot;
      break;
    }
    if (idx > A && idx < len && aig[idx] == key) {
      return idx << 1;
    }
    slot = (slot + 1u) & mask;
    probe = probe + 1u;
  }
  u32 n_gates = len - (A + 1u);
  if (len >= h->aig_cap || (u64)len >= BV_DIMACS_BOUND || n_gates >= BV_MAX_GATES) {
    h->oom = 1u;
    return 0u;
  }
  aig[len] = key;
  h->aig_len = len + 1u;
  ht[write_slot] = len;
  return len << 1;
}

u32 bv_aig_not(u32 l) {
  return l ^ 1u;
}

u32 bv_aig_or(BVHdr *h, u32 a, u32 b) {
  return bv_mk_and(h, a ^ 1u, b ^ 1u) ^ 1u;
}

u32 bv_aig_xor(BVHdr *h, u32 a, u32 b) {
  u32 nab = bv_mk_and(h, a, b) ^ 1u;
  u32 na_nb = bv_mk_and(h, a ^ 1u, b ^ 1u) ^ 1u;
  return bv_mk_and(h, nab, na_nb);
}

u32 bv_aig_beq(BVHdr *h, u32 a, u32 b) {
  return bv_aig_xor(h, a, b) ^ 1u;
}

u32 bv_aig_ite(BVHdr *h, u32 c, u32 t, u32 f) {
  if (c == 1u) { return t; }
  if (c == 0u) { return f; }
  if (t == f) { return t; }
  u32 n_ct = bv_mk_and(h, c, t) ^ 1u;
  u32 n_ncf = bv_mk_and(h, c ^ 1u, f) ^ 1u;
  return bv_mk_and(h, n_ct, n_ncf) ^ 1u;
}

u32 bv_lits_mark(BVHdr *h) {
  return h->lits_len;
}

void bv_lits_release(BVHdr *h, u32 mark) {
  if (mark <= h->lits_len) {
    h->lits_len = mark;
  }
}

u32 bv_lits_alloc(BVHdr *h, u32 count) {
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u64 cur = (u64)h->lits_len;
  u64 cap = (u64)h->lits_cap;
  if (cur > cap || (u64)count > cap - cur) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  h->lits_len = (u32)(cur + (u64)count);
  return (u32)cur;
}
"

/-- Ordered live functions of `Bitblast/Src/Aig.lean` (`11` fns). -/
def fns : List Fn := aig_fns

end

public section

theorem bv_hash_pair_wf : Func.Wf bv_hash_pair_body := by bitblast_wf_reify
theorem bv_aig_init_wf : Func.Wf bv_aig_init_body := by bitblast_wf_reify
theorem bv_mk_and_wf : Func.Wf bv_mk_and_body := by bitblast_wf_reify
theorem bv_aig_not_wf : Func.Wf bv_aig_not_body := by bitblast_wf_reify
theorem bv_aig_or_wf : Func.Wf bv_aig_or_body := by bitblast_wf_reify
theorem bv_aig_xor_wf : Func.Wf bv_aig_xor_body := by bitblast_wf_reify
theorem bv_aig_beq_wf : Func.Wf bv_aig_beq_body := by bitblast_wf_reify
theorem bv_aig_ite_wf : Func.Wf bv_aig_ite_body := by bitblast_wf_reify
theorem bv_lits_mark_wf : Func.Wf bv_lits_mark_body := by bitblast_wf_reify
theorem bv_lits_release_wf : Func.Wf bv_lits_release_body := by bitblast_wf_reify
theorem bv_lits_alloc_wf : Func.Wf bv_lits_alloc_body := by bitblast_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, aig_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bv_hash_pair_wf
  · exact bv_aig_init_wf
  · exact bv_mk_and_wf
  · exact bv_aig_not_wf
  · exact bv_aig_or_wf
  · exact bv_aig_xor_wf
  · exact bv_aig_beq_wf
  · exact bv_aig_ite_wf
  · exact bv_lits_mark_wf
  · exact bv_lits_release_wf
  · exact bv_lits_alloc_wf

end

end LeanQbe.T.Examples.Bitblast.Src.Aig

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Phase-A MVP Core Bitblasting Operations (`Bitblast/Src/OpsCore.lean`)

Provides clean, iterative, overflow-checked C0 bitblasting functions (calling `extern` AIG
primitives from `Bitblast/Src/Aig.lean`) for all Phase-A `S3` operations:
- `BVExpr`: `.extract`, `.append`, `.un .not`, `.bin .and`, `.bin .or`, `.bin .xor`, `.bin .add`
- `BVPred`: `.bin .eq`, `.bin .ult`, `.getLsbD`

Exports `opsCoreFns`, `opsCoreModule`, `opsCoreFns_wf` (`<= std3`), and `opsCore_checkAcyclic`.
Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.OpsCore

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! ops_core "
#include \"bitblast_internal.h\"

extern u32 bv_mk_and(BVHdr *h, u32 lhs, u32 rhs);
extern u32 bv_aig_not(u32 l);
extern u32 bv_aig_or(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_xor(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_beq(BVHdr *h, u32 a, u32 b);
extern u32 bv_lits_alloc(BVHdr *h, u32 count);

bool bv_slice_ok(BVHdr *h, u32 off, u32 w) {
  u64 len = (u64)h->lits_len;
  u64 cap = (u64)h->lits_cap;
  if (len > cap) { return false; }
  if (w > 0u && h->lits_ptr == 0ULL) { return false; }
  return (u64)off <= len && (u64)w <= len - (u64)off;
}

u32 bv_blast_extract(BVHdr *h, u32 a_off, u32 aw, u32 start, u32 len) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, aw)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  if (len > 0u && h->lits_ptr == 0ULL) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, len);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < len) {
    u64 pos = (u64)start + (u64)j;
    if (pos < (u64)aw) {
      lits[out + j] = lits[a_off + (u32)pos];
    } else {
      lits[out + j] = 0u;
    }
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_append(BVHdr *h, u32 lhs_off, u32 lw, u32 rhs_off, u32 rw) {
  if (h->oom != 0u || !bv_slice_ok(h, lhs_off, lw) || !bv_slice_ok(h, rhs_off, rw)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u64 total = (u64)lw + (u64)rw;
  if (total > 0xFFFFFFFFULL) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, (u32)total);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < rw) {
    lits[out + j] = lits[rhs_off + j];
    j = j + 1u;
  }
  j = 0u;
  while (j < lw) {
    lits[out + rw + j] = lits[lhs_off + j];
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_not(BVHdr *h, u32 a_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    lits[out + j] = bv_aig_not(lits[a_off + j]);
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_bin_bitwise(BVHdr *h, u32 a_off, u32 b_off, u32 w, u32 op) {
  if (op != BV_OP_AND && op != BV_OP_OR && op != BV_OP_XOR) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) || !bv_slice_ok(h, b_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    u32 la = lits[a_off + j];
    u32 lb = lits[b_off + j];
    u32 g = 0u;
    if (op == BV_OP_AND) {
      g = bv_mk_and(h, la, lb);
    } else if (op == BV_OP_OR) {
      g = bv_aig_or(h, la, lb);
    } else {
      g = bv_aig_xor(h, la, lb);
    }
    if (h->oom != 0u) { return 0xFFFFFFFFu; }
    lits[out + j] = g;
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_and(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  return bv_blast_bin_bitwise(h, a_off, b_off, w, BV_OP_AND);
}

u32 bv_blast_or(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  return bv_blast_bin_bitwise(h, a_off, b_off, w, BV_OP_OR);
}

u32 bv_blast_xor(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  return bv_blast_bin_bitwise(h, a_off, b_off, w, BV_OP_XOR);
}

u32 bv_full_adder_carry(BVHdr *h, u32 a, u32 b, u32 cin) {
  if (h->oom != 0u) { return 0u; }
  u32 sub = bv_aig_xor(h, a, b);
  if (h->oom != 0u) { return 0u; }
  u32 c1 = bv_mk_and(h, sub, cin);
  if (h->oom != 0u) { return 0u; }
  u32 c2 = bv_mk_and(h, a, b);
  if (h->oom != 0u) { return 0u; }
  u32 cout = bv_aig_or(h, c1, c2);
  if (h->oom != 0u) { return 0u; }
  return cout;
}

u32 bv_blast_add(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) || !bv_slice_ok(h, b_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 cin = 0u;
  u32 j = 0u;
  while (j < w) {
    u32 li = lits[a_off + j];
    u32 ri = lits[b_off + j];
    u32 sub = bv_aig_xor(h, li, ri);
    if (h->oom != 0u) { return 0xFFFFFFFFu; }
    u32 sum = bv_aig_xor(h, sub, cin);
    if (h->oom != 0u) { return 0xFFFFFFFFu; }
    lits[out + j] = sum;
    if (j + 1u < w) {
      cin = bv_full_adder_carry(h, li, ri, cin);
      if (h->oom != 0u) { return 0xFFFFFFFFu; }
    }
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_eq(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) || !bv_slice_ok(h, b_off, w)) {
    h->oom = 1u;
    return 0u;
  }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 acc = 1u;
  u32 j = 0u;
  while (j < w) {
    u32 eqj = bv_aig_beq(h, lits[a_off + j], lits[b_off + j]);
    if (h->oom != 0u) { return 0u; }
    acc = bv_mk_and(h, acc, eqj);
    if (h->oom != 0u) { return 0u; }
    j = j + 1u;
  }
  return acc;
}

u32 bv_blast_ult(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) || !bv_slice_ok(h, b_off, w)) {
    h->oom = 1u;
    return 0u;
  }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 cin = 1u;
  u32 j = 0u;
  while (j < w) {
    u32 ri_not = bv_aig_not(lits[b_off + j]);
    cin = bv_full_adder_carry(h, lits[a_off + j], ri_not, cin);
    if (h->oom != 0u) { return 0u; }
    j = j + 1u;
  }
  return bv_aig_not(cin);
}

u32 bv_blast_get_lsb_d(BVHdr *h, u32 a_off, u32 aw, u32 idx) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, aw)) {
    h->oom = 1u;
    return 0u;
  }
  if (idx < aw) {
    u32 *lits = (u32 *)h->lits_ptr;
    return lits[a_off + idx];
  }
  return 0u;
}
"

/-- Ordered live functions of `Bitblast/Src/OpsCore.lean` (`13` fns). -/
def opsCoreFns : List Fn := ops_core_fns

/-- Alias matching `Src/{Aig,Validate,Tseitin,Driver}.lean` convention. -/
abbrev fns : List Fn := opsCoreFns

/-- External AIG primitives from `Bitblast/Src/Aig.lean` used by `OpsCore`. -/
def opsCoreExterns : List Extern :=
  [ ⟨"bv_mk_and", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_not", [i32], [i32]⟩
  , ⟨"bv_aig_or", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_xor", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_beq", [i64, i32, i32], [i32]⟩
  , ⟨"bv_lits_alloc", [i64, i32], [i32]⟩ ]

/-- Closed acyclic `LeanQbe.T.Module` view of `OpsCore` against `Aig` externs. -/
def opsCoreModule : LeanQbe.T.Module :=
  { fns := opsCoreFns, externs := opsCoreExterns, exits := [] }

end

public section

theorem bv_slice_ok_wf : Func.Wf bv_slice_ok_body := by bitblast_wf_reify
theorem bv_blast_extract_wf : Func.Wf bv_blast_extract_body := by bitblast_wf_reify
theorem bv_blast_append_wf : Func.Wf bv_blast_append_body := by bitblast_wf_reify
theorem bv_blast_not_wf : Func.Wf bv_blast_not_body := by bitblast_wf_reify
theorem bv_blast_bin_bitwise_wf : Func.Wf bv_blast_bin_bitwise_body := by bitblast_wf_reify
theorem bv_blast_and_wf : Func.Wf bv_blast_and_body := by bitblast_wf_reify
theorem bv_blast_or_wf : Func.Wf bv_blast_or_body := by bitblast_wf_reify
theorem bv_blast_xor_wf : Func.Wf bv_blast_xor_body := by bitblast_wf_reify
theorem bv_full_adder_carry_wf : Func.Wf bv_full_adder_carry_body := by bitblast_wf_reify
theorem bv_blast_add_wf : Func.Wf bv_blast_add_body := by bitblast_wf_reify
theorem bv_blast_eq_wf : Func.Wf bv_blast_eq_body := by bitblast_wf_reify
theorem bv_blast_ult_wf : Func.Wf bv_blast_ult_body := by bitblast_wf_reify
theorem bv_blast_get_lsb_d_wf : Func.Wf bv_blast_get_lsb_d_body := by bitblast_wf_reify

theorem opsCoreFns_wf : ∀ f ∈ opsCoreFns, f.Wf := by
  intro f hf
  simp only [opsCoreFns, ops_core_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bv_slice_ok_wf
  · exact bv_blast_extract_wf
  · exact bv_blast_append_wf
  · exact bv_blast_not_wf
  · exact bv_blast_bin_bitwise_wf
  · exact bv_blast_and_wf
  · exact bv_blast_or_wf
  · exact bv_blast_xor_wf
  · exact bv_full_adder_carry_wf
  · exact bv_blast_add_wf
  · exact bv_blast_eq_wf
  · exact bv_blast_ult_wf
  · exact bv_blast_get_lsb_d_wf

theorem fns_wf : ∀ f ∈ fns, f.Wf := opsCoreFns_wf

theorem opsCore_checkAcyclic : opsCoreModule.checkAcyclic = true := by
  bitblast_kernel_rfl

end

end LeanQbe.T.Examples.Bitblast.Src.OpsCore

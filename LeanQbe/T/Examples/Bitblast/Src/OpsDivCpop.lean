/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Phase-B Division & Popcount Bitblasting Operations (`Bitblast/Src/OpsDivCpop.lean`)

Provides iterative, overflow-checked C0 bitblasting functions (calling `extern` AIG primitives
from `Bitblast/Src/Aig.lean` and slice/equality helpers from `Bitblast/Src/OpsCore.lean`) for
all Phase-B `S5` operations:
- `BV_OP_UDIV` (`bv_blast_udiv`), `BV_OP_UMOD` (`bv_blast_umod`) via restoring division
  matching `Init`'s `divRec_succ` / `udiv_eq_divRec` / `getLsbD_udiv` / `getLsbD_umod` with
  exact Lean `BitVec` `d = 0` semantics (`x / 0 = 0`, `x % 0 = x`) and `w = 0` safety
- `BV_OP_CPOP` (`bv_blast_cpop`) via iterative parallel-prefix addition tree matching
  `Init`'s `cpop_eq_cpopRec` with bump-pool `bv_lits_mark`/`bv_lits_release` cleanup

Exports `opsDivCpopFns`, `fns`, `opsDivCpopExterns`, `opsDivCpopModule`, `*_wf`,
`opsDivCpopFns_wf`, `fns_wf`, and `opsDivCpop_checkAcyclic` (`<= std3`).
Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! ops_div_cpop "
#include \"bitblast_internal.h\"

extern u32 bv_mk_and(BVHdr *h, u32 lhs, u32 rhs);
extern u32 bv_aig_not(u32 l);
extern u32 bv_aig_or(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_xor(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_ite(BVHdr *h, u32 c, u32 t, u32 f);
extern u32 bv_lits_mark(BVHdr *h);
extern void bv_lits_release(BVHdr *h, u32 mark);
extern u32 bv_lits_alloc(BVHdr *h, u32 count);
extern bool bv_slice_ok(BVHdr *h, u32 off, u32 w);
extern u32 bv_blast_eq(BVHdr *h, u32 a_off, u32 b_off, u32 w);

bool bv_blast_ite_into(BVHdr *h, u32 cond, u32 t_off, u32 f_off, u32 out_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, t_off, w) ||
      !bv_slice_ok(h, f_off, w) || !bv_slice_ok(h, out_off, w)) {
    h->oom = 1u;
    return false;
  }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    u32 r = bv_aig_ite(h, cond, lits[t_off + j], lits[f_off + j]);
    if (h->oom != 0u) { return false; }
    lits[out_off + j] = r;
    j = j + 1u;
  }
  return true;
}

u32 bv_blast_ite_slice(BVHdr *h, u32 cond, u32 t_off, u32 f_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, t_off, w) || !bv_slice_ok(h, f_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 mark0 = bv_lits_mark(h);
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (!bv_blast_ite_into(h, cond, t_off, f_off, out, w)) {
    bv_lits_release(h, mark0);
    return 0xFFFFFFFFu;
  }
  return out;
}

u32 bv_blast_sub_with_borrow(BVHdr *h, u32 a_off, u32 b_off, u32 out_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) ||
      !bv_slice_ok(h, b_off, w) || !bv_slice_ok(h, out_off, w)) {
    h->oom = 1u;
    return 0u;
  }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 cin = 1u;
  u32 j = 0u;
  while (j < w) {
    u32 ai = lits[a_off + j];
    u32 nbi = bv_aig_not(lits[b_off + j]);
    u32 sub = bv_aig_xor(h, ai, nbi);
    if (h->oom != 0u) { return 0u; }
    u32 diff = bv_aig_xor(h, sub, cin);
    if (h->oom != 0u) { return 0u; }
    lits[out_off + j] = diff;
    u32 c1 = bv_mk_and(h, sub, cin);
    if (h->oom != 0u) { return 0u; }
    u32 c2 = bv_mk_and(h, ai, nbi);
    if (h->oom != 0u) { return 0u; }
    cin = bv_aig_or(h, c1, c2);
    if (h->oom != 0u) { return 0u; }
    j = j + 1u;
  }
  return bv_aig_not(cin);
}

u32 bv_blast_udiv_umod(BVHdr *h, u32 n_off, u32 d_off, u32 w, u32 want_rem) {
  if (h->oom != 0u || !bv_slice_ok(h, n_off, w) || !bv_slice_ok(h, d_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 mark0 = bv_lits_mark(h);
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 mark = bv_lits_mark(h);
  u32 q = bv_lits_alloc(h, w);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }
  u32 r = bv_lits_alloc(h, w);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }
  u32 r_prime = bv_lits_alloc(h, w);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }
  u32 diff = bv_lits_alloc(h, w);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }

  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    lits[q + j] = 0u;
    lits[r + j] = 0u;
    j = j + 1u;
  }

  u32 d_zero = bv_blast_eq(h, d_off, q, w);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }

  u32 step = 0u;
  while (step < w) {
    u32 wn = w - 1u - step;
    lits[r_prime] = lits[n_off + wn];
    j = 1u;
    while (j < w) {
      lits[r_prime + j] = lits[r + j - 1u];
      j = j + 1u;
    }

    u32 discr = bv_blast_sub_with_borrow(h, r_prime, d_off, diff, w);
    if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }

    if (!bv_blast_ite_into(h, discr, r_prime, diff, r, w)) {
      bv_lits_release(h, mark0);
      return 0xFFFFFFFFu;
    }

    u32 k = w - 1u;
    while (k > 0u) {
      lits[q + k] = lits[q + k - 1u];
      k = k - 1u;
    }
    lits[q] = bv_aig_not(discr);
    step = step + 1u;
  }

  if (want_rem != 0u) {
    if (!bv_blast_ite_into(h, d_zero, n_off, r, out, w)) {
      bv_lits_release(h, mark0);
      return 0xFFFFFFFFu;
    }
  } else {
    j = 0u;
    while (j < w) {
      lits[r_prime + j] = 0u;
      j = j + 1u;
    }
    if (!bv_blast_ite_into(h, d_zero, r_prime, q, out, w)) {
      bv_lits_release(h, mark0);
      return 0xFFFFFFFFu;
    }
  }

  bv_lits_release(h, mark);
  return out;
}

u32 bv_blast_udiv(BVHdr *h, u32 n_off, u32 d_off, u32 w) {
  return bv_blast_udiv_umod(h, n_off, d_off, w, 0u);
}

u32 bv_blast_umod(BVHdr *h, u32 n_off, u32 d_off, u32 w) {
  return bv_blast_udiv_umod(h, n_off, d_off, w, 1u);
}

bool bv_blast_add_into(BVHdr *h, u32 a_off, u32 b_off, u32 out_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) ||
      !bv_slice_ok(h, b_off, w) || !bv_slice_ok(h, out_off, w)) {
    h->oom = 1u;
    return false;
  }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 cin = 0u;
  u32 j = 0u;
  while (j < w) {
    u32 li = lits[a_off + j];
    u32 ri = lits[b_off + j];
    u32 sub = bv_aig_xor(h, li, ri);
    if (h->oom != 0u) { return false; }
    u32 sum = bv_aig_xor(h, sub, cin);
    if (h->oom != 0u) { return false; }
    lits[out_off + j] = sum;
    if (j + 1u < w) {
      u32 c1 = bv_mk_and(h, sub, cin);
      if (h->oom != 0u) { return false; }
      u32 c2 = bv_mk_and(h, li, ri);
      if (h->oom != 0u) { return false; }
      cin = bv_aig_or(h, c1, c2);
      if (h->oom != 0u) { return false; }
    }
    j = j + 1u;
  }
  return true;
}

bool bv_blast_cpop_layer(BVHdr *h, u32 cur_off, u32 nxt_off, u32 len, u32 w) {
  u64 cur_need = (u64)len * (u64)w;
  u64 new_len = ((u64)len + 1ULL) >> 1;
  u64 nxt_need = new_len * (u64)w;
  if (h->oom != 0u || cur_need > 0xFFFFFFFFULL || nxt_need > 0xFFFFFFFFULL ||
      !bv_slice_ok(h, cur_off, (u32)cur_need) ||
      !bv_slice_ok(h, nxt_off, (u32)nxt_need)) {
    h->oom = 1u;
    return false;
  }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 i = 0u;
  while ((u64)i < new_len) {
    u32 op1 = (u32)((u64)cur_off + 2ULL * (u64)i * (u64)w);
    u32 dst = (u32)((u64)nxt_off + (u64)i * (u64)w);
    if (2ULL * (u64)i + 1ULL < (u64)len) {
      u32 op2 = (u32)((u64)cur_off + (2ULL * (u64)i + 1ULL) * (u64)w);
      if (!bv_blast_add_into(h, op1, op2, dst, w)) {
        return false;
      }
    } else {
      u32 j = 0u;
      while (j < w) {
        lits[dst + j] = lits[op1 + j];
        j = j + 1u;
      }
    }
    i = i + 1u;
  }
  return true;
}

u32 bv_blast_cpop(BVHdr *h, u32 a_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 mark0 = bv_lits_mark(h);
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  if (w == 1u) {
    lits[out] = lits[a_off];
    return out;
  }
  u64 ww = (u64)w * (u64)w;
  u64 half_w = (((u64)w + 1ULL) >> 1) * (u64)w;
  if (ww > 0xFFFFFFFFULL || half_w > 0xFFFFFFFFULL) {
    h->oom = 1u;
    bv_lits_release(h, mark0);
    return 0xFFFFFFFFu;
  }
  u32 mark = bv_lits_mark(h);
  u32 cur = bv_lits_alloc(h, (u32)ww);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }
  u32 nxt = bv_lits_alloc(h, (u32)half_w);
  if (h->oom != 0u) { bv_lits_release(h, mark0); return 0xFFFFFFFFu; }

  u32 k = 0u;
  while (k < w) {
    u32 base = k * w;
    lits[cur + base] = lits[a_off + k];
    u32 j = 1u;
    while (j < w) {
      lits[cur + base + j] = 0u;
      j = j + 1u;
    }
    k = k + 1u;
  }

  u32 len = w;
  while (len > 1u) {
    if (!bv_blast_cpop_layer(h, cur, nxt, len, w)) {
      bv_lits_release(h, mark0);
      return 0xFFFFFFFFu;
    }
    u32 tmp = cur;
    cur = nxt;
    nxt = tmp;
    len = (u32)(((u64)len + 1ULL) >> 1);
  }

  u32 j = 0u;
  while (j < w) {
    lits[out + j] = lits[cur + j];
    j = j + 1u;
  }
  bv_lits_release(h, mark);
  return out;
}
"

/-- Ordered live functions of `Bitblast/Src/OpsDivCpop.lean` (`9` fns). -/
def opsDivCpopFns : List Fn := ops_div_cpop_fns

/-- Alias matching `Src/{Aig,Validate,Tseitin,OpsCore,Driver}.lean` convention. -/
abbrev fns : List Fn := opsDivCpopFns

/-- External AIG and `OpsCore` primitives used by `OpsDivCpop`. -/
def opsDivCpopExterns : List Extern :=
  [ ⟨"bv_mk_and", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_not", [i32], [i32]⟩
  , ⟨"bv_aig_or", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_xor", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_ite", [i64, i32, i32, i32], [i32]⟩
  , ⟨"bv_lits_mark", [i64], [i32]⟩
  , ⟨"bv_lits_release", [i64, i32], []⟩
  , ⟨"bv_lits_alloc", [i64, i32], [i32]⟩
  , ⟨"bv_slice_ok", [i64, i32, i32], [.bool]⟩
  , ⟨"bv_blast_eq", [i64, i32, i32, i32], [i32]⟩ ]

/-- Closed acyclic `LeanQbe.T.Module` view of `OpsDivCpop` against `Aig` and `OpsCore`. -/
def opsDivCpopModule : LeanQbe.T.Module :=
  { fns := opsDivCpopFns, externs := opsDivCpopExterns, exits := [] }

end

public section

theorem bv_blast_ite_into_wf : Func.Wf bv_blast_ite_into_body := by bitblast_wf_reify
theorem bv_blast_ite_slice_wf : Func.Wf bv_blast_ite_slice_body := by bitblast_wf_reify
theorem bv_blast_sub_with_borrow_wf : Func.Wf bv_blast_sub_with_borrow_body := by
  bitblast_wf_reify
theorem bv_blast_udiv_umod_wf : Func.Wf bv_blast_udiv_umod_body := by bitblast_wf_reify
theorem bv_blast_udiv_wf : Func.Wf bv_blast_udiv_body := by bitblast_wf_reify
theorem bv_blast_umod_wf : Func.Wf bv_blast_umod_body := by bitblast_wf_reify
theorem bv_blast_add_into_wf : Func.Wf bv_blast_add_into_body := by bitblast_wf_reify
theorem bv_blast_cpop_layer_wf : Func.Wf bv_blast_cpop_layer_body := by bitblast_wf_reify
theorem bv_blast_cpop_wf : Func.Wf bv_blast_cpop_body := by bitblast_wf_reify

theorem opsDivCpopFns_wf : ∀ f ∈ opsDivCpopFns, f.Wf := by
  intro f hf
  simp only [opsDivCpopFns, ops_div_cpop_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bv_blast_ite_into_wf
  · exact bv_blast_ite_slice_wf
  · exact bv_blast_sub_with_borrow_wf
  · exact bv_blast_udiv_umod_wf
  · exact bv_blast_udiv_wf
  · exact bv_blast_umod_wf
  · exact bv_blast_add_into_wf
  · exact bv_blast_cpop_layer_wf
  · exact bv_blast_cpop_wf

theorem fns_wf : ∀ f ∈ fns, f.Wf := opsDivCpopFns_wf

theorem opsDivCpop_checkAcyclic : opsDivCpopModule.checkAcyclic = true := by
  bitblast_kernel_rfl

end

end LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop

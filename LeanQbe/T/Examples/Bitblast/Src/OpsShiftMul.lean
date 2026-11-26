/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Phase-B Shift, Rotate, Reverse, Multiply, and CLZ Ops (`Bitblast/Src/OpsShiftMul.lean`)

Provides clean, iterative, overflow-checked C0 bitblasting functions (calling `extern` AIG
primitives from `Aig.lean` and `bv_slice_ok`/`bv_blast_add` from `OpsCore.lean`) for all
Phase-B `S4` `BVExpr` operations:
- `bv_blast_replicate` (`BV_OP_REPLICATE`)
- `bv_blast_rotl` (`BV_OP_ROTL`)
- `bv_blast_rotr` (`BV_OP_ROTR`)
- `bv_blast_ashrc` (`BV_OP_ASHRC`)
- `bv_blast_reverse` (`BV_OP_REVERSE`)
- `bv_blast_shl` (`BV_OP_SHL`)
- `bv_blast_ushr` (`BV_OP_USHR`)
- `bv_blast_ashr` (`BV_OP_ASHR`)
- `bv_blast_mul` (`BV_OP_MUL`)
- `bv_blast_clz` (`BV_OP_CLZ`)

Exports `opsShiftMulFns`, `fns`, `opsShiftMulExterns`, `opsShiftMulModule`, `*_wf`,
`opsShiftMulFns_wf`, `fns_wf`, and `opsShiftMul_checkAcyclic` (`<= std3`).
Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! ops_shift_mul "
#include \"bitblast_internal.h\"

extern u32 bv_mk_and(BVHdr *h, u32 lhs, u32 rhs);
extern u32 bv_aig_or(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_ite(BVHdr *h, u32 c, u32 t, u32 f);
extern u32 bv_lits_mark(BVHdr *h);
extern void bv_lits_release(BVHdr *h, u32 mark);
extern u32 bv_lits_alloc(BVHdr *h, u32 count);
extern bool bv_slice_ok(BVHdr *h, u32 off, u32 w);
extern u32 bv_blast_add(BVHdr *h, u32 a_off, u32 b_off, u32 w);

void bv_copy_lits(BVHdr *h, u32 dst_off, u32 src_off, u32 w) {
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    lits[dst_off + j] = lits[src_off + j];
    j = j + 1u;
  }
}

u32 bv_blast_replicate(BVHdr *h, u32 a_off, u32 aw, u32 n) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, aw)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u64 total = (u64)aw * (u64)n;
  if (total > 0xFFFFFFFFULL) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, (u32)total);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (aw > 0u && n > 0u) {
    u32 k = 0u;
    while (k < n) {
      bv_copy_lits(h, out + k * aw, a_off, aw);
      k = k + 1u;
    }
  }
  return out;
}

u32 bv_blast_rotl(BVHdr *h, u32 a_off, u32 w, u32 n) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 r = n % w;
  u32 j = 0u;
  while (j < w) {
    if (j < r) {
      lits[out + j] = lits[a_off + (w - r + j)];
    } else {
      lits[out + j] = lits[a_off + (j - r)];
    }
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_rotr(BVHdr *h, u32 a_off, u32 w, u32 n) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 r = n % w;
  u32 cut = w - r;
  u32 j = 0u;
  while (j < w) {
    if (j < cut) {
      lits[out + j] = lits[a_off + (r + j)];
    } else {
      lits[out + j] = lits[a_off + (j - cut)];
    }
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_ashrc(BVHdr *h, u32 a_off, u32 w, u32 n) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 sign = lits[a_off + (w - 1u)];
  u32 j = 0u;
  while (j < w) {
    u64 pos = (u64)n + (u64)j;
    if (pos < (u64)w) {
      lits[out + j] = lits[a_off + (u32)pos];
    } else {
      lits[out + j] = sign;
    }
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_reverse(BVHdr *h, u32 a_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    lits[out + j] = lits[a_off + (w - 1u - j)];
    j = j + 1u;
  }
  return out;
}

u32 bv_blast_shift_var(BVHdr *h, u32 a_off, u32 w, u32 b_off, u32 nw, u32 op) {
  if (op != BV_OP_SHL && op != BV_OP_USHR && op != BV_OP_ASHR) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) || !bv_slice_ok(h, b_off, nw)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  bv_copy_lits(h, out, a_off, w);
  if (nw == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 pow = 0u;
  if (w > 1u) {
    u32 mark = bv_lits_mark(h);
    u32 tmp = bv_lits_alloc(h, w);
    if (h->oom != 0u) {
      bv_lits_release(h, mark);
      return 0xFFFFFFFFu;
    }
    while (pow < nw && pow < 32u && (1ULL << pow) < (u64)w) {
      u32 dist = (u32)(1ULL << pow);
      u32 cond = lits[b_off + pow];
      if (cond != 0u) {
        u32 j = 0u;
        while (j < w) {
          u32 sbit = 0u;
          if (op == BV_OP_SHL) {
            if (j >= dist) { sbit = lits[out + (j - dist)]; }
          } else if (op == BV_OP_USHR) {
            if (j < w - dist) { sbit = lits[out + (j + dist)]; }
          } else {
            if (j < w - dist) {
              sbit = lits[out + (j + dist)];
            } else {
              sbit = lits[out + (w - 1u)];
            }
          }
          lits[tmp + j] = bv_aig_ite(h, cond, sbit, lits[out + j]);
          if (h->oom != 0u) {
            bv_lits_release(h, mark);
            return 0xFFFFFFFFu;
          }
          j = j + 1u;
        }
        bv_copy_lits(h, out, tmp, w);
      }
      pow = pow + 1u;
    }
    bv_lits_release(h, mark);
  }
  if (pow < nw) {
    u32 any_hi = 0u;
    while (pow < nw && any_hi != 1u) {
      any_hi = bv_aig_or(h, any_hi, lits[b_off + pow]);
      if (h->oom != 0u) { return 0xFFFFFFFFu; }
      pow = pow + 1u;
    }
    if (any_hi != 0u) {
      u32 fill = 0u;
      if (op == BV_OP_ASHR) { fill = lits[out + (w - 1u)]; }
      u32 j = 0u;
      while (j < w) {
        lits[out + j] = bv_aig_ite(h, any_hi, fill, lits[out + j]);
        if (h->oom != 0u) { return 0xFFFFFFFFu; }
        j = j + 1u;
      }
    }
  }
  return out;
}

u32 bv_blast_shl(BVHdr *h, u32 a_off, u32 w, u32 b_off, u32 nw) {
  return bv_blast_shift_var(h, a_off, w, b_off, nw, BV_OP_SHL);
}

u32 bv_blast_ushr(BVHdr *h, u32 a_off, u32 w, u32 b_off, u32 nw) {
  return bv_blast_shift_var(h, a_off, w, b_off, nw, BV_OP_USHR);
}

u32 bv_blast_ashr(BVHdr *h, u32 a_off, u32 w, u32 b_off, u32 nw) {
  return bv_blast_shift_var(h, a_off, w, b_off, nw, BV_OP_ASHR);
}

u32 bv_blast_mul(BVHdr *h, u32 a_off, u32 b_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w) || !bv_slice_ok(h, b_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 y0 = lits[b_off];
  u32 j = 0u;
  while (j < w) {
    lits[out + j] = bv_mk_and(h, y0, lits[a_off + j]);
    if (h->oom != 0u) { return 0xFFFFFFFFu; }
    j = j + 1u;
  }
  if (w == 1u) { return out; }
  u32 mark = bv_lits_mark(h);
  u32 shifted = bv_lits_alloc(h, w);
  if (h->oom != 0u) {
    bv_lits_release(h, mark);
    return 0xFFFFFFFFu;
  }
  u32 s = 1u;
  while (s < w) {
    u32 ys = lits[b_off + s];
    if (ys != 0u) {
      j = 0u;
      while (j < s) {
        lits[shifted + j] = 0u;
        j = j + 1u;
      }
      while (j < w) {
        lits[shifted + j] = lits[a_off + (j - s)];
        j = j + 1u;
      }
      u32 iter_mark = bv_lits_mark(h);
      u32 added = bv_blast_add(h, out, shifted, w);
      if (h->oom != 0u) {
        bv_lits_release(h, mark);
        return 0xFFFFFFFFu;
      }
      j = 0u;
      while (j < w) {
        lits[out + j] = bv_aig_ite(h, ys, lits[added + j], lits[out + j]);
        if (h->oom != 0u) {
          bv_lits_release(h, mark);
          return 0xFFFFFFFFu;
        }
        j = j + 1u;
      }
      bv_lits_release(h, iter_mark);
    }
    s = s + 1u;
  }
  bv_lits_release(h, mark);
  return out;
}

u32 bv_blast_clz(BVHdr *h, u32 a_off, u32 w) {
  if (h->oom != 0u || !bv_slice_ok(h, a_off, w)) {
    h->oom = 1u;
    return 0xFFFFFFFFu;
  }
  u32 out = bv_lits_alloc(h, w);
  if (h->oom != 0u) { return 0xFFFFFFFFu; }
  if (w == 0u) { return out; }
  u32 *lits = (u32 *)h->lits_ptr;
  u32 j = 0u;
  while (j < w) {
    u32 wbit = 0u;
    if (j < 32u) { wbit = (w >> j) & 1u; }
    lits[out + j] = wbit;
    j = j + 1u;
  }
  u32 curr = 0u;
  while (curr < w) {
    u32 xc = lits[a_off + curr];
    if (xc != 0u) {
      u32 val = w - 1u - curr;
      j = 0u;
      while (j < w) {
        u32 cbit = 0u;
        if (j < 32u) { cbit = (val >> j) & 1u; }
        lits[out + j] = bv_aig_ite(h, xc, cbit, lits[out + j]);
        if (h->oom != 0u) { return 0xFFFFFFFFu; }
        j = j + 1u;
      }
    }
    curr = curr + 1u;
  }
  return out;
}
"

/-- Ordered live functions of `Bitblast/Src/OpsShiftMul.lean` (`12` fns). -/
def opsShiftMulFns : List Fn := ops_shift_mul_fns

/-- Alias matching `Src/{Aig,Validate,Tseitin,OpsCore,Driver}.lean` convention. -/
abbrev fns : List Fn := opsShiftMulFns

/-- External AIG and core helpers from `Aig.lean` and `OpsCore.lean` used by `OpsShiftMul`. -/
def opsShiftMulExterns : List Extern :=
  [ ⟨"bv_mk_and", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_or", [i64, i32, i32], [i32]⟩
  , ⟨"bv_aig_ite", [i64, i32, i32, i32], [i32]⟩
  , ⟨"bv_lits_mark", [i64], [i32]⟩
  , ⟨"bv_lits_release", [i64, i32], []⟩
  , ⟨"bv_lits_alloc", [i64, i32], [i32]⟩
  , ⟨"bv_slice_ok", [i64, i32, i32], [.bool]⟩
  , ⟨"bv_blast_add", [i64, i32, i32, i32], [i32]⟩ ]

/-- Closed acyclic `LeanQbe.T.Module` view of `OpsShiftMul` against `Aig` + `OpsCore` externs. -/
def opsShiftMulModule : LeanQbe.T.Module :=
  { fns := opsShiftMulFns, externs := opsShiftMulExterns, exits := [] }

end

public section

theorem bv_copy_lits_wf : Func.Wf bv_copy_lits_body := by bitblast_wf_reify
theorem bv_blast_replicate_wf : Func.Wf bv_blast_replicate_body := by bitblast_wf_reify
theorem bv_blast_rotl_wf : Func.Wf bv_blast_rotl_body := by bitblast_wf_reify
theorem bv_blast_rotr_wf : Func.Wf bv_blast_rotr_body := by bitblast_wf_reify
theorem bv_blast_ashrc_wf : Func.Wf bv_blast_ashrc_body := by bitblast_wf_reify
theorem bv_blast_reverse_wf : Func.Wf bv_blast_reverse_body := by bitblast_wf_reify
theorem bv_blast_shift_var_wf : Func.Wf bv_blast_shift_var_body := by bitblast_wf_reify
theorem bv_blast_shl_wf : Func.Wf bv_blast_shl_body := by bitblast_wf_reify
theorem bv_blast_ushr_wf : Func.Wf bv_blast_ushr_body := by bitblast_wf_reify
theorem bv_blast_ashr_wf : Func.Wf bv_blast_ashr_body := by bitblast_wf_reify
theorem bv_blast_mul_wf : Func.Wf bv_blast_mul_body := by bitblast_wf_reify
theorem bv_blast_clz_wf : Func.Wf bv_blast_clz_body := by bitblast_wf_reify

theorem opsShiftMulFns_wf : ∀ f ∈ opsShiftMulFns, f.Wf := by
  intro f hf
  simp only [opsShiftMulFns, ops_shift_mul_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bv_copy_lits_wf
  · exact bv_blast_replicate_wf
  · exact bv_blast_rotl_wf
  · exact bv_blast_rotr_wf
  · exact bv_blast_ashrc_wf
  · exact bv_blast_reverse_wf
  · exact bv_blast_shift_var_wf
  · exact bv_blast_shl_wf
  · exact bv_blast_ushr_wf
  · exact bv_blast_ashr_wf
  · exact bv_blast_mul_wf
  · exact bv_blast_clz_wf

theorem fns_wf : ∀ f ∈ fns, f.Wf := opsShiftMulFns_wf

theorem opsShiftMul_checkAcyclic : opsShiftMulModule.checkAcyclic = true := by
  bitblast_kernel_rfl

end

end LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

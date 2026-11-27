/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Backward-Sweep COI and Top-Down DIMACS Writer (`Bitblast/Src/Tseitin.lean`)

Implements non-recursive backward COI marking (`g = len - 1 downto A + 1`), forward byte-length
counting pass, and forward top-down ASCII DIMACS emission into `[work_end - dimacs_len, work_end)`
matching `Bitblast.Ref.Tseitin.tseitin` + `LratBytes.encodeDimacs` byte-for-byte.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.Tseitin

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! tseitin "
#include \"bitblast_internal.h\"

void bv_coi_mark(BVHdr *h, u32 root) {
  u32 len = h->aig_len;
  if (len == 0u || h->marks_ptr == 0ULL) { return; }
  u8 *marks = (u8 *)h->marks_ptr;
  u32 i = 0u;
  while (i < len) {
    marks[i] = (u8)0;
    i = i + 1u;
  }
  u32 rn = root >> 1;
  if (rn < len) {
    marks[rn] = (u8)1;
  }
  u32 A = h->num_atoms;
  u64 *aig = (u64 *)h->aig_ptr;
  u32 g = len;
  while (g > A + 1u) {
    g = g - 1u;
    if (marks[g] != (u8)0) {
      u64 packed = aig[g];
      u32 lhs = (u32)(packed & 0xFFFFFFFFULL);
      u32 rhs = (u32)(packed >> 32);
      u32 is_ite = 0u;
      u32 ic = 0u;
      u32 it = 0u;
      u32 if_ = 0u;
      if ((lhs & rhs & 1u) != 0u) {
        u32 ln = lhs >> 1;
        u32 rn2 = rhs >> 1;
        if (ln > A && rn2 > A) {
          u64 lp = aig[ln];
          u64 rp = aig[rn2];
          u32 l0 = (u32)(lp & 0xFFFFFFFFULL);
          u32 l1 = (u32)(lp >> 32);
          u32 r0 = (u32)(rp & 0xFFFFFFFFULL);
          u32 r1 = (u32)(rp >> 32);
          if (l0 == (r0 ^ 1u)) {
            is_ite = 1u; ic = l0; it = l1 ^ 1u; if_ = r1 ^ 1u;
          } else if (l0 == (r1 ^ 1u)) {
            is_ite = 1u; ic = l0; it = l1 ^ 1u; if_ = r0 ^ 1u;
          } else if (l1 == (r0 ^ 1u)) {
            is_ite = 1u; ic = l1; it = l0 ^ 1u; if_ = r1 ^ 1u;
          } else if (l1 == (r1 ^ 1u)) {
            is_ite = 1u; ic = l1; it = l0 ^ 1u; if_ = r0 ^ 1u;
          }
        }
      }
      if (is_ite != 0u) {
        u32 cn = ic >> 1;
        u32 tn = it >> 1;
        u32 fn = if_ >> 1;
        if (cn < len) { marks[cn] = (u8)1; }
        if (tn < len) { marks[tn] = (u8)1; }
        if (fn < len) { marks[fn] = (u8)1; }
      } else {
        u32 lnode = lhs >> 1;
        u32 rnode = rhs >> 1;
        if (lnode < len) { marks[lnode] = (u8)1; }
        if (rnode < len) { marks[rnode] = (u8)1; }
      }
    }
  }
}

u64 bv_dec_len(u32 v) {
  if (v < 10u) { return 1ULL; }
  u64 n = 0ULL;
  while (v > 0u) {
    n = n + 1ULL;
    v = v / 10u;
  }
  return n;
}

u64 bv_lit_bytes(u32 lit) {
  u64 sign = (u64)(lit & 1u);
  u32 v = (lit >> 1) + 1u;
  return sign + bv_dec_len(v) + 1ULL;
}

u64 bv_write_dec(u64 p, u32 v) {
  u64 len = bv_dec_len(v);
  u64 end = p + len;
  if (v == 0u) {
    *(u8 *)p = (u8)48;
    return end;
  }
  u64 cur = end;
  while (v > 0u) {
    cur = cur - 1ULL;
    *(u8 *)cur = (u8)(48u + (v % 10u));
    v = v / 10u;
  }
  return end;
}

u64 bv_write_lit(u64 p, u32 lit) {
  if ((lit & 1u) != 0u) {
    *(u8 *)p = (u8)45;
    p = p + 1ULL;
  }
  p = bv_write_dec(p, (lit >> 1) + 1u);
  *(u8 *)p = (u8)32;
  return p + 1ULL;
}

u64 bv_write_dimacs_hdr(u64 p, u32 mv, u32 nc) {
  *(u8 *)p = (u8)112;
  *(u8 *)(p + 1ULL) = (u8)32;
  *(u8 *)(p + 2ULL) = (u8)99;
  *(u8 *)(p + 3ULL) = (u8)110;
  *(u8 *)(p + 4ULL) = (u8)102;
  *(u8 *)(p + 5ULL) = (u8)32;
  p = bv_write_dec(p + 6ULL, mv);
  *(u8 *)p = (u8)32;
  p = bv_write_dec(p + 1ULL, nc);
  *(u8 *)p = (u8)10;
  return p + 1ULL;
}

u64 bv_write_clause_end(u64 p) {
  *(u8 *)p = (u8)48;
  *(u8 *)(p + 1ULL) = (u8)10;
  return p + 2ULL;
}

bool bv_dimacs_write(BVHdr *h, u32 root) {
  if (root == 0u) {
    u64 floor0 = h->work_base + BV_HDR_BYTES;
    if (h->work_end < floor0 || 12ULL > h->work_end - floor0) {
      h->oom = 1u;
      h->dimacs_start = 0ULL;
      h->dimacs_len = 0u;
      return false;
    }
    u64 start0 = h->work_end - 12ULL;
    u64 p0 = bv_write_dimacs_hdr(start0, 0u, 1u);
    (void)bv_write_clause_end(p0);
    h->dimacs_start = start0;
    h->dimacs_len = 12u;
    return true;
  }
  u32 len = h->aig_len;
  u32 A = h->num_atoms;
  if (len <= A || h->marks_ptr == 0ULL) {
    h->oom = 1u;
    h->dimacs_start = 0ULL;
    h->dimacs_len = 0u;
    return false;
  }
  u8 *marks = (u8 *)h->marks_ptr;
  u64 *aig = (u64 *)h->aig_ptr;
  u32 max_var = (root >> 1) + 1u;
  if ((u64)max_var >= BV_DIMACS_BOUND) {
    h->oom = 1u;
    h->dimacs_start = 0ULL;
    h->dimacs_len = 0u;
    return false;
  }
  u32 num_clauses = 1u;
  u64 body_bytes = bv_lit_bytes(root) + 2ULL;
  u32 g = A + 1u;
  while (g < len) {
    if (marks[g] != (u8)0) {
      u64 packed = aig[g];
      u32 lhs = (u32)(packed & 0xFFFFFFFFULL);
      u32 rhs = (u32)(packed >> 32);
      u32 is_ite = 0u;
      u32 ic = 0u;
      u32 it = 0u;
      u32 if_ = 0u;
      if ((lhs & rhs & 1u) != 0u) {
        u32 ln = lhs >> 1;
        u32 rn = rhs >> 1;
        if (ln > A && rn > A) {
          u64 lp = aig[ln];
          u64 rp = aig[rn];
          u32 l0 = (u32)(lp & 0xFFFFFFFFULL);
          u32 l1 = (u32)(lp >> 32);
          u32 r0 = (u32)(rp & 0xFFFFFFFFULL);
          u32 r1 = (u32)(rp >> 32);
          if (l0 == (r0 ^ 1u)) {
            is_ite = 1u; ic = l0; it = l1 ^ 1u; if_ = r1 ^ 1u;
          } else if (l0 == (r1 ^ 1u)) {
            is_ite = 1u; ic = l0; it = l1 ^ 1u; if_ = r0 ^ 1u;
          } else if (l1 == (r0 ^ 1u)) {
            is_ite = 1u; ic = l1; it = l0 ^ 1u; if_ = r1 ^ 1u;
          } else if (l1 == (r1 ^ 1u)) {
            is_ite = 1u; ic = l1; it = l0 ^ 1u; if_ = r0 ^ 1u;
          }
        }
      }
      u32 o = g + 1u;
      if (o > max_var) { max_var = o; }
      if (is_ite != 0u) {
        u32 cv = (ic >> 1) + 1u;
        u32 tv = (it >> 1) + 1u;
        u32 fv = (if_ >> 1) + 1u;
        if (cv > max_var) { max_var = cv; }
        if (tv > max_var) { max_var = tv; }
        if (fv > max_var) { max_var = fv; }
        if ((u64)max_var >= BV_DIMACS_BOUND || (u64)num_clauses >= BV_DIMACS_BOUND - 4ULL) {
          h->oom = 1u;
          h->dimacs_start = 0ULL;
          h->dimacs_len = 0u;
          return false;
        }
        num_clauses = num_clauses + 4u;
        body_bytes = body_bytes + (bv_dec_len(o) << 2) + (bv_dec_len(cv) << 2) +
                                  (bv_dec_len(tv) << 1) + (bv_dec_len(fv) << 1) + 26ULL;
      } else {
        u32 lv = (lhs >> 1) + 1u;
        u32 rv = (rhs >> 1) + 1u;
        if (lv > max_var) { max_var = lv; }
        if (rv > max_var) { max_var = rv; }
        if ((u64)max_var >= BV_DIMACS_BOUND || (u64)num_clauses >= BV_DIMACS_BOUND - 3ULL) {
          h->oom = 1u;
          h->dimacs_start = 0ULL;
          h->dimacs_len = 0u;
          return false;
        }
        num_clauses = num_clauses + 3u;
        u64 olen = bv_dec_len(o);
        body_bytes = body_bytes + (olen + 2ULL + bv_lit_bytes(lhs) + 2ULL);
        body_bytes = body_bytes + (olen + 2ULL + bv_lit_bytes(rhs) + 2ULL);
        body_bytes = body_bytes + (olen + 1ULL + bv_lit_bytes(lhs ^ 1u) +
                                   bv_lit_bytes(rhs ^ 1u) + 2ULL);
      }
    }
    g = g + 1u;
  }
  u64 hdr_bytes = 8ULL + bv_dec_len(max_var) + bv_dec_len(num_clauses);
  u64 total_bytes = hdr_bytes + body_bytes;
  u64 floor_ptr = h->marks_ptr + (u64)len;
  if (total_bytes > 0xFFFFFFFFULL || h->work_end < floor_ptr ||
      total_bytes > h->work_end - floor_ptr) {
    h->oom = 1u;
    h->dimacs_start = 0ULL;
    h->dimacs_len = 0u;
    return false;
  }
  u64 start = h->work_end - total_bytes;
  u64 p = bv_write_dimacs_hdr(start, max_var, num_clauses);
  g = A + 1u;
  while (g < len) {
    if (marks[g] != (u8)0) {
      u64 packed = aig[g];
      u32 lhs = (u32)(packed & 0xFFFFFFFFULL);
      u32 rhs = (u32)(packed >> 32);
      u32 is_ite = 0u;
      u32 ic = 0u;
      u32 it = 0u;
      u32 if_ = 0u;
      if ((lhs & rhs & 1u) != 0u) {
        u32 ln = lhs >> 1;
        u32 rn = rhs >> 1;
        if (ln > A && rn > A) {
          u64 lp = aig[ln];
          u64 rp = aig[rn];
          u32 l0 = (u32)(lp & 0xFFFFFFFFULL);
          u32 l1 = (u32)(lp >> 32);
          u32 r0 = (u32)(rp & 0xFFFFFFFFULL);
          u32 r1 = (u32)(rp >> 32);
          if (l0 == (r0 ^ 1u)) {
            is_ite = 1u; ic = l0; it = l1 ^ 1u; if_ = r1 ^ 1u;
          } else if (l0 == (r1 ^ 1u)) {
            is_ite = 1u; ic = l0; it = l1 ^ 1u; if_ = r0 ^ 1u;
          } else if (l1 == (r0 ^ 1u)) {
            is_ite = 1u; ic = l1; it = l0 ^ 1u; if_ = r1 ^ 1u;
          } else if (l1 == (r1 ^ 1u)) {
            is_ite = 1u; ic = l1; it = l0 ^ 1u; if_ = r0 ^ 1u;
          }
        }
      }
      u32 pos_o = g << 1;
      u32 neg_o = pos_o | 1u;
      if (is_ite != 0u) {
        u32 nc = ic ^ 1u;
        u32 nt = it ^ 1u;
        u32 nf = if_ ^ 1u;
        p = bv_write_lit(p, nc);
        p = bv_write_lit(p, nt);
        p = bv_write_lit(p, pos_o);
        p = bv_write_clause_end(p);
        p = bv_write_lit(p, nc);
        p = bv_write_lit(p, it);
        p = bv_write_lit(p, neg_o);
        p = bv_write_clause_end(p);
        p = bv_write_lit(p, ic);
        p = bv_write_lit(p, nf);
        p = bv_write_lit(p, pos_o);
        p = bv_write_clause_end(p);
        p = bv_write_lit(p, ic);
        p = bv_write_lit(p, if_);
        p = bv_write_lit(p, neg_o);
        p = bv_write_clause_end(p);
      } else {
        p = bv_write_lit(p, neg_o);
        p = bv_write_lit(p, lhs);
        p = bv_write_clause_end(p);
        p = bv_write_lit(p, neg_o);
        p = bv_write_lit(p, rhs);
        p = bv_write_clause_end(p);
        p = bv_write_lit(p, pos_o);
        p = bv_write_lit(p, lhs ^ 1u);
        p = bv_write_lit(p, rhs ^ 1u);
        p = bv_write_clause_end(p);
      }
    }
    g = g + 1u;
  }
  p = bv_write_lit(p, root);
  (void)bv_write_clause_end(p);
  h->dimacs_start = start;
  h->dimacs_len = (u32)total_bytes;
  return true;
}
"

/-- Ordered live functions of `Bitblast/Src/Tseitin.lean` (`8` fns). -/
def fns : List Fn := tseitin_fns

end

public section

theorem bv_coi_mark_wf : Func.Wf bv_coi_mark_body := by bitblast_wf_reify
theorem bv_dec_len_wf : Func.Wf bv_dec_len_body := by bitblast_wf_reify
theorem bv_lit_bytes_wf : Func.Wf bv_lit_bytes_body := by bitblast_wf_reify
theorem bv_write_dec_wf : Func.Wf bv_write_dec_body := by bitblast_wf_reify
theorem bv_write_lit_wf : Func.Wf bv_write_lit_body := by bitblast_wf_reify
theorem bv_write_dimacs_hdr_wf : Func.Wf bv_write_dimacs_hdr_body := by bitblast_wf_reify
theorem bv_write_clause_end_wf : Func.Wf bv_write_clause_end_body := by bitblast_wf_reify
theorem bv_dimacs_write_wf : Func.Wf bv_dimacs_write_body := by bitblast_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, tseitin_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bv_coi_mark_wf
  · exact bv_dec_len_wf
  · exact bv_lit_bytes_wf
  · exact bv_write_dec_wf
  · exact bv_write_lit_wf
  · exact bv_write_dimacs_hdr_wf
  · exact bv_write_clause_end_wf
  · exact bv_dimacs_write_wf

end

end LeanQbe.T.Examples.Bitblast.Src.Tseitin

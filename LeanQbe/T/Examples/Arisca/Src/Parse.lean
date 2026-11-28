/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Arisca.Src.Header
meta import LeanQbe.T.Examples.Arisca.Src.Header

/-!
# ARiSCA Binary AIG & ART Header/Table Parser (`Arisca/Src/Parse.lean`)

Bounds-checked C0 parsers for:
- Binary AIGER (`aig M I L O A\n`, outputs, 7-bit delta varints)
- ART v1 header (magic, version, spec, `n_in`, `n_out`, `n_nets`, `n_gates`, `n_cones`,
  `n_main`, `n_words`) and initial `bind`/`in_net`/`out_ref` tables.

Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Src.Parse

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src

@[expose] public section

arisca_c0! arisca_parse "
#include \"arisca_internal.h\"

extern ar_bool_u32 ar_next_word(ArCtx *cx);
extern u8 *ar_aalloc(ArCtx *cx, u64 bytes);

ar_bool_u64_u32 ar_pnum(const u8 *b, u64 n, u64 pos) {
  u64 p = pos;
  u64 v = 0ULL;
  u32 nd = 0u;
  while (p < n && b[p] >= (u8)48 && b[p] <= (u8)57) {
    v = v * 10ULL + (u64)(b[p] - (u8)48);
    nd = nd + 1u;
    p = p + 1ULL;
    if (nd > 10u || v > 0xFFFFFFFFULL) {
      return C0_TUP3(ar_bool_u64_u32, false, p, 0u);
    }
  }
  if (nd == 0u) {
    return C0_TUP3(ar_bool_u64_u32, false, p, 0u);
  }
  return C0_TUP3(ar_bool_u64_u32, true, p, (u32)v);
}

ar_bool_u64 ar_pch(const u8 *b, u64 n, u64 pos, u8 c) {
  if (pos >= n || b[pos] != c) {
    return C0_TUP2(ar_bool_u64, false, pos);
  }
  return C0_TUP2(ar_bool_u64, true, pos + 1ULL);
}

ar_bool_u64_u32 ar_pvarint(const u8 *b, u64 n, u64 pos) {
  u64 p = pos;
  u64 x = 0ULL;
  u32 i = 0u;
  while (i < 5u) {
    if (p >= n) {
      return C0_TUP3(ar_bool_u64_u32, false, p, 0u);
    }
    u8 c = b[p];
    p = p + 1ULL;
    x = x | ((u64)(c & (u8)0x7F) << (7u * i));
    if ((c & (u8)0x80) == (u8)0) {
      if (x > 0xFFFFFFFFULL) {
        return C0_TUP3(ar_bool_u64_u32, false, p, 0u);
      }
      return C0_TUP3(ar_bool_u64_u32, true, p, (u32)x);
    }
    i = i + 1u;
  }
  return C0_TUP3(ar_bool_u64_u32, false, p, 0u);
}

bool ar_parse_aig(ArCtx *cx, const u8 *b, u64 n) {
  if (n < 4ULL || b[0] != (u8)97 || b[1] != (u8)105 ||
      b[2] != (u8)103 || b[3] != (u8)32) {
    return false;
  }
  u64 p = 4ULL;
  bool ok = false;
  u32 M = 0u, I = 0u, L = 0u, O = 0u, A = 0u;
  C0_TIE3(ok, p, M, ar_pnum(b, n, p)); if (!ok) { return false; }
  C0_TIE2(ok, p, ar_pch(b, n, p, (u8)32)); if (!ok) { return false; }
  C0_TIE3(ok, p, I, ar_pnum(b, n, p)); if (!ok) { return false; }
  C0_TIE2(ok, p, ar_pch(b, n, p, (u8)32)); if (!ok) { return false; }
  C0_TIE3(ok, p, L, ar_pnum(b, n, p)); if (!ok) { return false; }
  C0_TIE2(ok, p, ar_pch(b, n, p, (u8)32)); if (!ok) { return false; }
  C0_TIE3(ok, p, O, ar_pnum(b, n, p)); if (!ok) { return false; }
  C0_TIE2(ok, p, ar_pch(b, n, p, (u8)32)); if (!ok) { return false; }
  C0_TIE3(ok, p, A, ar_pnum(b, n, p)); if (!ok) { return false; }
  C0_TIE2(ok, p, ar_pch(b, n, p, (u8)10)); if (!ok) { return false; }
  if (L != 0u) { return false; }
  if (M > 0x3FFFFFF0u) { return false; }
  if ((u64)I + (u64)A != (u64)M) { return false; }
  u32 maxlit = 2u * M + 1u;
  cx->M = M;
  cx->I = I;
  cx->A = A;
  cx->O = O;
  cx->rhs0 = (u32 *)ar_aalloc(cx, 4ULL * (u64)A);
  cx->rhs1 = (u32 *)ar_aalloc(cx, 4ULL * (u64)A);
  cx->olit = (u32 *)ar_aalloc(cx, 4ULL * (u64)O);
  if (cx->rhs0 == NULL || cx->rhs1 == NULL || cx->olit == NULL) {
    return false;
  }
  u32 j = 0u;
  while (j < O) {
    u32 v = 0u;
    C0_TIE3(ok, p, v, ar_pnum(b, n, p)); if (!ok) { return false; }
    C0_TIE2(ok, p, ar_pch(b, n, p, (u8)10)); if (!ok) { return false; }
    if (v > maxlit) { return false; }
    cx->olit[j] = v;
    j = j + 1u;
  }
  j = 0u;
  while (j < A) {
    u32 lhs = 2u * (I + 1u + j);
    u32 d0 = 0u, d1 = 0u;
    C0_TIE3(ok, p, d0, ar_pvarint(b, n, p)); if (!ok) { return false; }
    C0_TIE3(ok, p, d1, ar_pvarint(b, n, p)); if (!ok) { return false; }
    if (d0 == 0u || d0 > lhs) { return false; }
    u32 r0 = lhs - d0;
    if (d1 > r0) { return false; }
    cx->rhs0[j] = r0;
    cx->rhs1[j] = r0 - d1;
    j = j + 1u;
  }
  return true;
}

bool ar_parse_art_header_and_tables(ArCtx *cx, u8 *art, u64 art_len) {
  if ((art_len & 3ULL) != 0ULL) { return false; }
  cx->art = art;
  cx->nw = art_len >> 2;
  cx->pos = 0ULL;
  bool ok = false;
  u32 h0 = 0u, h1 = 0u, h2 = 0u, h3 = 0u, h4 = 0u;
  u32 h5 = 0u, h6 = 0u, h7 = 0u, h8 = 0u, h9 = 0u;
  C0_TIE2(ok, h0, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h1, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h2, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h3, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h4, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h5, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h6, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h7, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h8, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, h9, ar_next_word(cx)); if (!ok) { return false; }
  if (h0 != AR_ART_MAGIC || h1 != 1u) { return false; }
  if (h2 > 2u) { return false; }
  u32 mw = h4;
  if (h2 == 2u) {
    if (h3 != cx->I) { return false; }
    if (h4 != cx->O || h4 < 2u || (h4 & 1u) != 0u || (h4 >> 1) > 128u) { return false; }
    mw = h4 >> 1;
  } else {
    if (h3 != cx->I || (h3 & 1u) != 0u || h3 < 2u) { return false; }
    if (h4 != cx->O || h4 < 1u || h4 > 128u) { return false; }
  }
  if ((u64)h9 != cx->nw) { return false; }
  if (h5 > 0x3FFFFFFFu) { return false; }
  cx->spec = h2;
  cx->n_in = h3;
  cx->n_out = h4;
  cx->n_nets = h5;
  cx->n_gates = h6;
  cx->n_cones = h7;
  cx->n_main = h8;
  if (mw == 128u) {
    cx->mlo = ~0ULL;
    cx->mhi = ~0ULL;
  } else if (mw > 64u) {
    cx->mlo = ~0ULL;
    cx->mhi = (1ULL << (mw - 64u)) - 1ULL;
  } else if (mw == 64u) {
    cx->mlo = ~0ULL;
    cx->mhi = 0ULL;
  } else {
    cx->mlo = (1ULL << mw) - 1ULL;
    cx->mhi = 0ULL;
  }
  if ((u64)cx->n_nets + (u64)cx->n_in + (u64)cx->n_out > cx->nw - cx->pos) {
    return false;
  }
  cx->bind = (u32 *)ar_aalloc(cx, 4ULL * (u64)cx->n_nets);
  cx->rule_off = (u32 *)ar_aalloc(cx, 4ULL * (u64)cx->n_nets);
  cx->rule_n = (u32 *)ar_aalloc(cx, 4ULL * (u64)cx->n_nets);
  cx->partner = (u32 *)ar_aalloc(cx, 4ULL * (u64)cx->n_nets);
  cx->flipped = ar_aalloc(cx, (u64)cx->n_nets);
  cx->in_net = (u32 *)ar_aalloc(cx, 4ULL * (u64)cx->n_in);
  cx->out_ref = (u32 *)ar_aalloc(cx, 4ULL * (u64)cx->n_out);
  cx->stk_n = (u32 *)ar_aalloc(cx, 4ULL * (u64)AR_TT_STK);
  cx->stk_p = (u32 *)ar_aalloc(cx, 4ULL * (u64)AR_TT_STK);
  cx->memo_n = (u32 *)ar_aalloc(cx, 4ULL * (u64)AR_TT_MAX_AND);
  cx->memo_v = (u64 *)ar_aalloc(cx, 8ULL * (u64)AR_TT_MAX_AND);
  cx->dense = (u64 *)ar_aalloc(cx, 8ULL * 128ULL);
  cx->gsy = (u32 *)ar_aalloc(cx, 4ULL * 85ULL);
  cx->gcl = (u64 *)ar_aalloc(cx, 8ULL * 16ULL);
  cx->gch = (u64 *)ar_aalloc(cx, 8ULL * 16ULL);
  if (cx->bind == NULL || cx->rule_off == NULL || cx->rule_n == NULL ||
      cx->partner == NULL || cx->flipped == NULL || cx->in_net == NULL ||
      cx->out_ref == NULL || cx->stk_n == NULL || cx->stk_p == NULL ||
      cx->memo_n == NULL || cx->memo_v == NULL || cx->dense == NULL ||
      cx->gsy == NULL || cx->gcl == NULL || cx->gch == NULL) {
    return false;
  }
  u32 i = 0u;
  while (i < cx->n_nets) {
    u32 b = 0u;
    C0_TIE2(ok, b, ar_next_word(cx)); if (!ok) { return false; }
    if (b != AR_NONE && b > 2u * cx->M + 1u) { return false; }
    cx->bind[i] = b;
    cx->rule_n[i] = AR_NONE;
    cx->rule_off[i] = 0u;
    cx->partner[i] = AR_NONE;
    cx->flipped[i] = (u8)0;
    i = i + 1u;
  }
  i = 0u;
  while (i < cx->n_in) {
    u32 v = 0u;
    C0_TIE2(ok, v, ar_next_word(cx)); if (!ok) { return false; }
    if (v == AR_NONE) {
      if (cx->spec != 2u) { return false; }
      cx->in_net[i] = AR_NONE;
    } else {
      if (v >= cx->n_nets || cx->bind[v] != 2u * (i + 1u)) { return false; }
      cx->in_net[i] = v;
    }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < cx->n_out) {
    u32 r = 0u;
    C0_TIE2(ok, r, ar_next_word(cx)); if (!ok) { return false; }
    if (r == AR_NONE) {
      if (cx->spec != 2u || cx->olit[j] > 1u) { return false; }
      cx->out_ref[j] = AR_NONE;
    } else {
      if ((r >> 1) >= cx->n_nets) { return false; }
      u32 b = cx->bind[r >> 1];
      if (b == AR_NONE || (b ^ (r & 1u)) != cx->olit[j]) { return false; }
      cx->out_ref[j] = r;
    }
    j = j + 1u;
  }
  return true;
}
"

/-- Ordered live functions of `Arisca/Src/Parse.lean` (`5` fns). -/
def fns : List Fn := arisca_parse_fns

end

public section

theorem ar_pnum_wf : Func.Wf ar_pnum_body := by arisca_wf_reify
theorem ar_pch_wf : Func.Wf ar_pch_body := by arisca_wf_reify
theorem ar_pvarint_wf : Func.Wf ar_pvarint_body := by arisca_wf_reify
theorem ar_parse_aig_wf : Func.Wf ar_parse_aig_body := by arisca_wf_reify
theorem ar_parse_art_header_and_tables_wf : Func.Wf ar_parse_art_header_and_tables_body := by
  arisca_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, arisca_parse_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact ar_pnum_wf
  · exact ar_pch_wf
  · exact ar_pvarint_wf
  · exact ar_parse_aig_wf
  · exact ar_parse_art_header_and_tables_wf

end

end LeanQbe.T.Examples.Arisca.Src.Parse

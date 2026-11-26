/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Syntactic Gate Extraction (AND, XOR, ITE) (`Src/Gates.lean`)

Mirrors upstream `kissat/src/gates.c, ands.c, equivalences.c, ifthenelse.c`
(`13` live functions, DAG level `L0`):
- `full_bve_find_equiv_m7` (R4: `kissat_find_equivalence_gate_fallback`)
- `full_bve_find_and_m7` (R4: `kissat_find_and_gate_fallback`)
- `full_bve_get_tern_m7` (R4: `kissat_get_ternary_clause`)
- `full_bve_match_tern_m7` (R4: `kissat_match_ternary_clause_fallback`)
- `full_bve_find_ite_side_m7` (R4: `kissat_find_ite_gate_side_fallback`)
- `full_bve_find_ite_m7` (R4: `kissat_find_if_then_else_gate_fallback`)
- `full_bve_xor_pat_m7` (R4: `kissat_xor_gate_pattern`)
- `full_bve_find_xor_m7` (R4: `kissat_find_xor_gate`)
- `full_bve_find_equiv_m8` (R4: `kissat_find_equivalence_gate`)
- `full_bve_find_and_m8` (R4: `kissat_find_and_gate`)
- `full_bve_match_tern_m8` (R4: `kissat_match_ternary_clause`)
- `full_bve_find_ite_side_m8` (R4: `kissat_find_ite_gate_side`)
- `full_bve_find_ite_m8` (R4: `kissat_find_if_then_else_gate`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Gates

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! gates "
#include \"kissat_internal.h\"

bool full_bve_find_equiv_m7(FullHdr *h, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 bin_p = 0u;
  u32 i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) {
      u32 ot = wp & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { lm[ot] = (u8)1; bin_p = bin_p + 1u; }
    }
    i = i + 1u;
  }
  if (bin_p == 0u) { return false; }
  u32 match_lit = 0xFFFFFFFFu;
  u32 match_j = 0u;
  u32 j = 0u;
  while (j < nn) {
    u32 wn = scr[512u + j];
    if ((wn & PW_BIN_FLAG) != 0u) {
      u32 ot = wn & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot ^ 1u] != (u8)0) {
        match_lit = ot ^ 1u;
        match_j = j;
        break;
      }
    }
    j = j + 1u;
  }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) { lm[wp & PW_LIT_MASK] = (u8)0; }
    i = i + 1u;
  }
  if (match_lit == 0xFFFFFFFFu) { return false; }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u && (wp & PW_LIT_MASK) == match_lit) {
      scr[1024u + (i >> 5)] = 1u << (i & 31u);
      scr[1040u + (match_j >> 5)] = 1u << (match_j & 31u);
      scr[1056] = 1u;
      scr[1057] = 0u;
      return true;
    }
    i = i + 1u;
  }
  return false;
}

bool full_bve_find_and_m7(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n) {
  u32 pol = lit & 1u;
  u32 lit_off = pol << 9;
  u32 opp_off = 512u - lit_off;
  u32 lit_mask = 1024u + (pol << 4);
  u32 opp_mask = 2064u - lit_mask;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 bin_cnt = 0u;
  u32 j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot] == (u8)0) { lm[ot] = (u8)1; bin_cnt = bin_cnt + 1u; }
    }
    j = j + 1u;
  }
  if (bin_cnt < 1u) {
    j = 0u;
    while (j < opp_n) {
      u32 w = scr[opp_off + j];
      if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
      j = j + 1u;
    }
    return false;
  }
  u32 found_i = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < lit_n) {
    u32 w = scr[lit_off + i];
    if ((w & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true;
      u32 need = 0u;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        if (l != lit) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if (lm[l ^ 1u] == (u8)0) { ok = false; break; }
            need = need + 1u;
          }
        }
        k = k + 1u;
      }
      if (ok && need >= 1u) { found_i = i; break; }
    }
    i = i + 1u;
  }
  j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
    j = j + 1u;
  }
  if (found_i == 0xFFFFFFFFu) { return false; }
  u32 cr = scr[lit_off + found_i];
  u32 sz = ar[(u64)cr + 2ULL];
  u32 uniq_need = 0u;
  u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit && vals[l] == (i8)0 && lm[l ^ 1u] == (u8)0) {
      lm[l ^ 1u] = (u8)1;
      uniq_need = uniq_need + 1u;
    }
    k = k + 1u;
  }
  u32 matched = 0u;
  j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (lm[ot] == (u8)1) {
        lm[ot] = (u8)0;
        u32 midx = opp_mask + (j >> 5);
        scr[midx] = scr[midx] | (1u << (j & 31u));
        matched = matched + 1u;
      }
    }
    j = j + 1u;
  }
  k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit) { lm[l ^ 1u] = (u8)0; }
    k = k + 1u;
  }
  if (matched == uniq_need && uniq_need >= 1u) {
    scr[lit_mask + (found_i >> 5)] = 1u << (found_i & 31u);
    scr[1056] = 1u;
    scr[1057] = 0u;
    return true;
  }
  k = 0u;
  while (k < 16u) { scr[opp_mask + k] = 0u; k = k + 1u; }
  return false;
}

bool full_bve_get_tern_m7(FullHdr *h, u32 v_lit, u32 cr, u32 out_off) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 sz = ar[(u64)cr + 2ULL];
  u32 cnt = 0u;
  u32 l0 = 0u;
  u32 l1 = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) {
      i8 vl = vals[l];
      if (vl > (i8)0) { return false; }
      if (vl == (i8)0) {
        if (cnt == 0u) { l0 = l; }
        else if (cnt == 1u) { l1 = l; }
        else { return false; }
        cnt = cnt + 1u;
      }
    }
    i = i + 1u;
  }
  if (cnt != 2u) { return false; }
  scr[out_off] = l0;
  scr[out_off + 1u] = l1;
  return true;
}

u32 full_bve_match_tern_m7(FullHdr *h, u32 opp_lit, u32 x, u32 y, u32 opp_off, u32 opp_n) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 j = 0u;
  while (j < opp_n && scr[1058] < 2000u) {
    scr[1058] = scr[1058] + 1u;
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (ot == x || ot == y) { return j | 0x80000000u; }
    } else {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true;
      bool sx = false;
      bool sy = false;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        i8 vl = vals[l];
        if (vl > (i8)0) { ok = false; break; }
        if (vl == (i8)0 && l != opp_lit) {
          if (l == x) { sx = true; }
          else if (l == y) { sy = true; }
          else { ok = false; break; }
        }
        k = k + 1u;
      }
      if (ok) {
        if (sx && sy) { return j; }
        if (sx || sy) { return j | 0x80000000u; }
      }
    }
    j = j + 1u;
  }
  return 0xFFFFFFFFu;
}

bool full_bve_find_ite_side_m7(FullHdr *h, u32 v, u32 np, u32 nn, bool neg) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 lit = (v << 1) | (neg ? 1u : 0u);
  u32 opp = lit ^ 1u;
  u32 lit_off = neg ? 512u : 0u;
  u32 lit_n = neg ? nn : np;
  u32 opp_off = neg ? 0u : 512u;
  u32 opp_n = neg ? np : nn;
  u32 lit_mask = neg ? 1040u : 1024u;
  u32 opp_mask = neg ? 1024u : 1040u;
  if (lit_n < 2u || opp_n < 2u) { return false; }
  u64 large_clauses = 0ULL;
  u32 idx = 0u;
  while (idx < lit_n) {
    if ((scr[lit_off + idx] & PW_BIN_FLAG) == 0u) { large_clauses = large_clauses + 1ULL; }
    idx = idx + 1u;
  }
  if (large_clauses < 2ULL || large_clauses * large_clauses > 2000ULL) { return false; }
  scr[1058] = 0u;
  u32 i0 = 0u;
  while (i0 + 1u < lit_n && scr[1058] < 2000u) {
    u32 w0 = scr[lit_off + i0];
    if ((w0 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w0, 1060u)) {
      u32 a0 = scr[1060];
      u32 a1 = scr[1061];
      u32 i1 = i0 + 1u;
      while (i1 < lit_n && scr[1058] < 2000u) {
        u32 w1 = scr[lit_off + i1];
        if ((w1 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w1, 1062u)) {
          u32 b0 = scr[1062];
          u32 b1 = scr[1063];
          bool ok = false;
          u32 cond = 0u;
          u32 u = 0u;
          u32 w = 0u;
          if (a0 == (b0 ^ 1u)) { ok = true; cond = a0; u = a1; w = b1; }
          else if (a0 == (b1 ^ 1u)) { ok = true; cond = a0; u = a1; w = b0; }
          else if (a1 == (b0 ^ 1u)) { ok = true; cond = a1; u = a0; w = b1; }
          else if (a1 == (b1 ^ 1u)) { ok = true; cond = a1; u = a0; w = b0; }
          if (ok && (u >> 1) != (w >> 1)) {
            u32 m0 = full_bve_match_tern_m7(h, opp, cond, u ^ 1u, opp_off, opp_n);
            if (m0 != 0xFFFFFFFFu) {
              u32 m1 = full_bve_match_tern_m7(h, opp, cond ^ 1u, w ^ 1u, opp_off, opp_n);
              if (m1 != 0xFFFFFFFFu) {
                u32 j0 = m0 & 0x7FFFFFFFu;
                u32 j1 = m1 & 0x7FFFFFFFu;
                if (j0 != j1) {
                  u32 k0 = lit_mask + (i0 >> 5);
                  scr[k0] = scr[k0] | (1u << (i0 & 31u));
                  u32 k1 = lit_mask + (i1 >> 5);
                  scr[k1] = scr[k1] | (1u << (i1 & 31u));
                  u32 o0 = opp_mask + (j0 >> 5);
                  scr[o0] = scr[o0] | (1u << (j0 & 31u));
                  u32 o1 = opp_mask + (j1 >> 5);
                  scr[o1] = scr[o1] | (1u << (j1 & 31u));
                  scr[1056] = 1u;
                  scr[1057] = (((m0 | m1) & 0x80000000u) != 0u) ? 1u : 0u;
                  return true;
                }
              }
            }
          }
        }
        i1 = i1 + 1u;
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

bool full_bve_find_ite_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (full_bve_find_ite_side_m7(h, v, np, nn, false)) { return true; }
  return full_bve_find_ite_side_m7(h, v, np, nn, true);
}

u32 full_bve_xor_pat_m7(FullHdr *h, u32 v_lit, u32 cr, u32 k) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 sz = ar[(u64)cr + 2ULL];
  u32 pat = 0u;
  u32 seen = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) {
      i8 vl = vals[l];
      if (vl > (i8)0) { return 0xFFFFFFFFu; }
      if (vl == (i8)0) {
        u8 m = lm[l];
        if (m < (u8)2) { return 0xFFFFFFFFu; }
        u32 mv = (u32)(m - (u8)2);
        u32 idx = mv >> 1;
        u32 sgn = mv & 1u;
        if (idx >= k || ((seen >> idx) & 1u) != 0u) { return 0xFFFFFFFFu; }
        seen = seen | (1u << idx);
        if (sgn != 0u) { pat = pat | (1u << idx); }
      }
    }
    i = i + 1u;
  }
  u32 full_seen = (1u << k) - 1u;
  return (seen == full_seen) ? pat : 0xFFFFFFFFu;
}

bool full_bve_find_xor_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 1096ULL) { return false; }
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 lp = 0u;
  u32 ln = 0u;
  u32 i = 0u;
  while (i < np) {
    if ((scr[i] & PW_BIN_FLAG) == 0u) { lp = lp + 1u; }
    i = i + 1u;
  }
  i = 0u;
  while (i < nn) {
    if ((scr[512u + i] & PW_BIN_FLAG) == 0u) { ln = ln + 1u; }
    i = i + 1u;
  }
  if (lp < 2u || ln < 2u || (u64)lp * (u64)ln > 4096ULL) { return false; }
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 i0 = 0u;
  while (i0 < np) {
    u32 w0 = scr[i0];
    if ((w0 & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w0 + 2ULL];
      bool ok = true;
      u32 k = 0u;
      u32 u = 0u;
      while (u < sz) {
        u32 l = ar[(u64)w0 + 3ULL + (u64)u];
        if (l != pl) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if ((l >> 1) == v || lm[l] != (u8)0 || k >= 4u) { ok = false; break; }
            lm[l] = (u8)(2u + (k << 1));
            lm[l ^ 1u] = (u8)(3u + (k << 1));
            scr[1092u + k] = l;
            k = k + 1u;
          }
        }
        u = u + 1u;
      }
      if (ok && k >= 2u && k <= 4u) {
        u32 etgt = (k == 2u) ? 0x9u : ((k == 3u) ? 0x69u : 0x9669u);
        u32 otgt = (k == 2u) ? 0x6u : ((k == 3u) ? 0x96u : 0x6996u);
        u32 emask = 1u;
        scr[1060] = i0;
        u32 p_idx = 0u;
        while (p_idx < np && emask != etgt) {
          u32 w = scr[p_idx];
          if (p_idx != i0 && (w & PW_BIN_FLAG) == 0u) {
            u32 pat = full_bve_xor_pat_m7(h, pl, w, k);
            if (pat < 16u && ((etgt >> pat) & 1u) != 0u && ((emask >> pat) & 1u) == 0u) {
              emask = emask | (1u << pat);
              scr[1060u + pat] = p_idx;
            }
          }
          p_idx = p_idx + 1u;
        }
        u32 omask = 0u;
        if (emask == etgt) {
          u32 n_idx = 0u;
          while (n_idx < nn && omask != otgt) {
            u32 w = scr[512u + n_idx];
            if ((w & PW_BIN_FLAG) == 0u) {
              u32 pat = full_bve_xor_pat_m7(h, nl, w, k);
              if (pat < 16u && ((otgt >> pat) & 1u) != 0u && ((omask >> pat) & 1u) == 0u) {
                omask = omask | (1u << pat);
                scr[1076u + pat] = n_idx;
              }
            }
            n_idx = n_idx + 1u;
          }
        }
        u32 c = 0u;
        while (c < k) {
          u32 l = scr[1092u + c];
          lm[l] = (u8)0;
          lm[l ^ 1u] = (u8)0;
          c = c + 1u;
        }
        if (emask == etgt && omask == otgt) {
          u32 p = 0u;
          u32 nlim = 1u << k;
          while (p < nlim) {
            if (((etgt >> p) & 1u) != 0u) {
              u32 pi = scr[1060u + p];
              u32 m = 1024u + (pi >> 5);
              scr[m] = scr[m] | (1u << (pi & 31u));
            }
            if (((otgt >> p) & 1u) != 0u) {
              u32 ni = scr[1076u + p];
              u32 m = 1040u + (ni >> 5);
              scr[m] = scr[m] | (1u << (ni & 31u));
            }
            p = p + 1u;
          }
          scr[1056] = 1u;
          scr[1057] = 0u;
          return true;
        }
      } else {
        u32 c = 0u;
        while (c < k) {
          u32 l = scr[1092u + c];
          lm[l] = (u8)0;
          lm[l ^ 1u] = (u8)0;
          c = c + 1u;
        }
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

bool full_bve_find_equiv_m8(FullHdr *h, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 bin_p = 0u;
  u32 i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) {
      u32 ot = wp & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { lm[ot] = (u8)1; bin_p = bin_p + 1u; }
    }
    i = i + 1u;
  }
  if (bin_p == 0u) { return false; }
  u32 match_lit = 0xFFFFFFFFu;
  u32 match_j = 0u;
  u32 j = 0u;
  while (j < nn) {
    u32 wn = scr[M8_NEG_OFF + j];
    if ((wn & PW_BIN_FLAG) != 0u) {
      u32 ot = wn & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot ^ 1u] != (u8)0) {
        match_lit = ot ^ 1u; match_j = j; break;
      }
    }
    j = j + 1u;
  }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) { lm[wp & PW_LIT_MASK] = (u8)0; }
    i = i + 1u;
  }
  if (match_lit == 0xFFFFFFFFu) { return false; }
  i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u && (wp & PW_LIT_MASK) == match_lit) {
      scr[M8_POS_MASK + (i >> 5)] = 1u << (i & 31u);
      scr[M8_NEG_MASK + (match_j >> 5)] = 1u << (match_j & 31u);
      scr[M8_GF_IDX] = 1u;
      scr[M8_RG_IDX] = 0u;
      return true;
    }
    i = i + 1u;
  }
  return false;
}

bool full_bve_find_and_m8(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n) {
  u32 pol = lit & 1u;
  u32 lit_off = (pol != 0u) ? M8_NEG_OFF : 0u;
  u32 opp_off = (pol != 0u) ? 0u : M8_NEG_OFF;
  u32 lit_mask = (pol != 0u) ? M8_NEG_MASK : M8_POS_MASK;
  u32 opp_mask = (pol != 0u) ? M8_POS_MASK : M8_NEG_MASK;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 marked = 0u;
  u32 j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (vals[ot] == (i8)0 && lm[ot] == (u8)0) { lm[ot] = (u8)1; marked = marked + 1u; }
    }
    j = j + 1u;
  }
  if (marked < 2u) {
    j = 0u;
    while (j < opp_n) {
      u32 w = scr[opp_off + j];
      if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
      j = j + 1u;
    }
    return false;
  }
  u32 found_i = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < lit_n) {
    u32 w = scr[lit_off + i];
    if ((w & PW_BIN_FLAG) == 0u) {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true; u32 need = 0u; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        if (l != lit) {
          i8 vl = vals[l];
          if (vl > (i8)0) { ok = false; break; }
          if (vl == (i8)0) {
            if (lm[l ^ 1u] == (u8)0) { ok = false; break; }
            need = need + 1u;
          }
        }
        k = k + 1u;
      }
      if (ok && need >= 1u) { found_i = i; break; }
    }
    i = i + 1u;
  }
  j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) { lm[w & PW_LIT_MASK] = (u8)0; }
    j = j + 1u;
  }
  if (found_i == 0xFFFFFFFFu) { return false; }
  u32 cr = scr[lit_off + found_i];
  u32 sz = ar[(u64)cr + 2ULL];
  u32 uniq_need = 0u; u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit && vals[l] == (i8)0 && lm[l ^ 1u] == (u8)0) {
      lm[l ^ 1u] = (u8)1; uniq_need = uniq_need + 1u;
    }
    k = k + 1u;
  }
  u32 matched = 0u; j = 0u;
  while (j < opp_n) {
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (lm[ot] == (u8)1) {
        lm[ot] = (u8)0;
        u32 midx = opp_mask + (j >> 5);
        scr[midx] = scr[midx] | (1u << (j & 31u));
        matched = matched + 1u;
      }
    }
    j = j + 1u;
  }
  k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if (l != lit) { lm[l ^ 1u] = (u8)0; }
    k = k + 1u;
  }
  if (matched == uniq_need && uniq_need >= 1u) {
    scr[lit_mask + (found_i >> 5)] = 1u << (found_i & 31u);
    scr[M8_GF_IDX] = 1u;
    scr[M8_RG_IDX] = 0u;
    return true;
  }
  k = 0u;
  while (k < 64u) { scr[opp_mask + k] = 0u; k = k + 1u; }
  return false;
}

u32 full_bve_match_tern_m8(FullHdr *h, u32 opp_lit, u32 x, u32 y, u32 opp_off, u32 opp_n) {
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 j = 0u;
  while (j < opp_n && scr[M8_ITE_CNT] < 2000u) {
    scr[M8_ITE_CNT] = scr[M8_ITE_CNT] + 1u;
    u32 w = scr[opp_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (ot == x || ot == y) { return j | 0x80000000u; }
    } else {
      u32 sz = ar[(u64)w + 2ULL];
      bool ok = true; bool sx = false; bool sy = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[(u64)w + 3ULL + (u64)k];
        i8 vl = vals[l];
        if (vl > (i8)0) { ok = false; break; }
        if (vl == (i8)0 && l != opp_lit) {
          if (l == x) { sx = true; }
          else if (l == y) { sy = true; }
          else { ok = false; break; }
        }
        k = k + 1u;
      }
      if (ok) {
        if (sx && sy) { return j; }
        if (sx || sy) { return j | 0x80000000u; }
      }
    }
    j = j + 1u;
  }
  return 0xFFFFFFFFu;
}

bool full_bve_find_ite_side_m8(FullHdr *h, u32 v, u32 np, u32 nn, bool neg) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 lit = (v << 1) | (neg ? 1u : 0u);
  u32 opp = lit ^ 1u;
  u32 lit_off = neg ? M8_NEG_OFF : 0u;
  u32 lit_n = neg ? nn : np;
  u32 opp_off = neg ? 0u : M8_NEG_OFF;
  u32 opp_n = neg ? np : nn;
  u32 lit_mask = neg ? M8_NEG_MASK : M8_POS_MASK;
  u32 opp_mask = neg ? M8_POS_MASK : M8_NEG_MASK;
  if (lit_n < 2u || opp_n < 2u) { return false; }
  u64 large_clauses = 0ULL; u32 idx = 0u;
  while (idx < lit_n) {
    if ((scr[lit_off + idx] & PW_BIN_FLAG) == 0u) { large_clauses = large_clauses + 1ULL; }
    idx = idx + 1u;
  }
  if (large_clauses < 2ULL || large_clauses * large_clauses > 2000ULL) { return false; }
  scr[M8_ITE_CNT] = 0u;
  u32 i0 = 0u;
  while (i0 + 1u < lit_n && scr[M8_ITE_CNT] < 2000u) {
    u32 w0 = scr[lit_off + i0];
    if ((w0 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w0, M8_TMP_OFF)) {
      u32 a0 = scr[M8_TMP_OFF]; u32 a1 = scr[M8_TMP_OFF + 1u];
      u32 i1 = i0 + 1u;
      while (i1 < lit_n && scr[M8_ITE_CNT] < 2000u) {
        u32 w1 = scr[lit_off + i1];
        if ((w1 & PW_BIN_FLAG) == 0u && full_bve_get_tern_m7(h, lit, w1, M8_TMP_OFF + 2u)) {
          u32 b0 = scr[M8_TMP_OFF + 2u]; u32 b1 = scr[M8_TMP_OFF + 3u];
          bool ok = false; u32 cond = 0u; u32 u = 0u; u32 w = 0u;
          if (a0 == (b0 ^ 1u)) { ok = true; cond = a0; u = a1; w = b1; }
          else if (a0 == (b1 ^ 1u)) { ok = true; cond = a0; u = a1; w = b0; }
          else if (a1 == (b0 ^ 1u)) { ok = true; cond = a1; u = a0; w = b1; }
          else if (a1 == (b1 ^ 1u)) { ok = true; cond = a1; u = a0; w = b0; }
          if (ok && (u >> 1) != (w >> 1)) {
            u32 m0 = full_bve_match_tern_m8(h, opp, cond, u ^ 1u, opp_off, opp_n);
            if (m0 != 0xFFFFFFFFu) {
              u32 m1 = full_bve_match_tern_m8(h, opp, cond ^ 1u, w ^ 1u, opp_off, opp_n);
              if (m1 != 0xFFFFFFFFu) {
                u32 j0 = m0 & 0x7FFFFFFFu; u32 j1 = m1 & 0x7FFFFFFFu;
                if (j0 != j1) {
                  scr[lit_mask + (i0 >> 5)] = scr[lit_mask + (i0 >> 5)] | (1u << (i0 & 31u));
                  scr[lit_mask + (i1 >> 5)] = scr[lit_mask + (i1 >> 5)] | (1u << (i1 & 31u));
                  scr[opp_mask + (j0 >> 5)] = scr[opp_mask + (j0 >> 5)] | (1u << (j0 & 31u));
                  scr[opp_mask + (j1 >> 5)] = scr[opp_mask + (j1 >> 5)] | (1u << (j1 & 31u));
                  scr[M8_GF_IDX] = 1u;
                  scr[M8_RG_IDX] = (((m0 | m1) & 0x80000000u) != 0u) ? 1u : 0u;
                  return true;
                }
              }
            }
          }
        }
        i1 = i1 + 1u;
      }
    }
    i0 = i0 + 1u;
  }
  return false;
}

bool full_bve_find_ite_m8(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (full_bve_find_ite_side_m8(h, v, np, nn, false)) { return true; }
  return full_bve_find_ite_side_m8(h, v, np, nn, true);
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Gates

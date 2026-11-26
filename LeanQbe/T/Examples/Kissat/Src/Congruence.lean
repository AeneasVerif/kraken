/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Gate Congruence Closure & Hyper-Binary Resolution (`Src/Congruence.lean`)

Mirrors upstream `kissat/src/congruence.c` (`32` live functions, DAG level `L3`):
- `full_cong_find` (R4: `kissat_congruence_find`)
- `full_cong_merge` (R4: `kissat_congruence_merge`)
- `full_cong_mark_trail` (R4: `kissat_congruence_mark_trail`)
- `full_cong_unit_fold` (R4: `kissat_congruence_unit_fold`)
- `full_cong_equiv_fold` (R4: `kissat_congruence_equiv_fold`)
- `full_cong_emit_xor` (R4: `kissat_congruence_emit_xor`)
- `full_cong_has_clause_k` (R4: `kissat_congruence_has_clause_k`)
- `full_cong_emit_xor4` (R4: `kissat_congruence_emit_xor4`)
- `full_cong_extract_xor_k` (R4: `kissat_congruence_extract_xor_k`)
- `full_cong_try_xor_ite` (R4: `kissat_congruence_try_xor_ite`)
- `full_cong_count_bins` (R4: `kissat_congruence_count_binaries`)
- `full_cong_eb_match` (R4: `kissat_congruence_match_binary`)
- `full_cong_extract_binaries` (R4: `kissat_congruence_extract_binaries`)
- `full_cong_find_units_equivs` (R4: `kissat_congruence_find_units_equivs`)
- `full_cong_extract_and_clause_fid` (R4: `kissat_congruence_extract_and_clause`)
- `full_cong_extract_from_fid` (R4: `kissat_congruence_extract_gates`)
- `full_cong_and_match` (R4: `kissat_congruence_match_and`)
- `full_cong_xor_match` (R4: `kissat_congruence_match_xor`)
- `full_cong_enq_var` (R4: `kissat_congruence_enqueue_var`)
- `full_cong_eval_gate` (R4: `kissat_congruence_eval_gate`)
- `full_cong_worklist` (R4: `kissat_congruence_worklist`)
- `full_cong_sift_pairs_fid` (R4: `kissat_congruence_sift_pairs`)
- `full_cong_sort_pairs_fid` (R4: `kissat_congruence_sort_pairs`)
- `full_cong_fwd_subsume` (R4: `kissat_congruence_forward_subsume`)
- `full_cong_u64_sift_m7` (R4: `kissat_congruence_u64_sift`)
- `full_cong_u64_sort_m7` (R4: `kissat_congruence_u64_sort`)
- `full_cong_bsearch_u64_m7` (R4: `kissat_congruence_bsearch_u64`)
- `full_cong_copy_condbin_m7` (R4: `kissat_congruence_copy_condbin`)
- `full_cong_extract_condeq_m7` (R4: `kissat_congruence_extract_condeq`)
- `full_cong_merge_condeq_m7` (R4: `kissat_congruence_merge_condeq`)
- `full_cong_extract_ite_all_m7` (R4: `kissat_congruence_extract_ites`)
- `full_congruence_dense` (R4: `kissat_congruence`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Congruence

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! congruence "
#include \"kissat_internal.h\"

extern void full_sort_u32(u32 *arr, u32 n);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_add_unit(FullHdr *h, u32 lit);

u32 full_cong_find(u32 *repr, u32 l) {
  u32 r = l;
  while (repr[r] != r) { r = repr[r]; }
  u32 c = l;
  while (repr[c] != r) { u32 n = repr[c]; repr[c] = r; c = n; }
  return r;
}

bool full_cong_merge(FullHdr *h, u32 a, u32 b) {
  u32 *repr = (u32 *)h->repr;
  u32 ra = full_cong_find(repr, a); u32 rb = full_cong_find(repr, b);
  if (ra == rb) { return false; }
  if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return true; }
  if (ra > rb) { u32 t = ra; ra = rb; rb = t; }
  repr[rb] = ra; repr[rb ^ 1u] = ra ^ 1u;
  u64 st1 = full_add_bin(h, ra ^ 1u, rb);
  if (st1 == 20ULL) { h->inconsistent = 1ULL; return true; }
  if (st1 == 2ULL) {
    h->oom = 0ULL; h->ant_sz = 1ULL;
  } else {
    u64 st2 = full_add_bin(h, ra, rb ^ 1u);
    if (st2 == 20ULL) { h->inconsistent = 1ULL; return true; }
    if (st2 == 2ULL) { h->oom = 0ULL; h->ant_sz = 1ULL; }
  }
  h->cong_cnt = h->cong_cnt + 1ULL;
  return true;
}

void full_cong_mark_trail(FullHdr *h, u64 prev_te, u32 ep) {
  u32 *trl = (u32 *)h->trail;
  u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 te = h->trail_end;
  u64 i = prev_te;
  while (i < te) {
    u32 lit = trl[i];
    u32 lv = lit >> 1;
    if ((u64)lv < cv) {
      tmk[lv] = ep;
      u32 r = full_cong_find(repr, lit);
      u32 rv = r >> 1;
      if ((u64)rv < cv) { tmk[rv] = ep; }
    }
    i = i + 1ULL;
  }
}

u64 full_cong_unit_fold(FullHdr *h, u32 lit, u32 next_ep) {
  i8 *vals = (i8 *)h->values;
  if (vals[lit] > (i8)0) { return 0ULL; }
  u64 prev_te = h->trail_end;
  if (!full_add_unit(h, lit)) {
    full_cong_mark_trail(h, prev_te, next_ep);
    return 2ULL;
  }
  h->cong_cnt = h->cong_cnt + 1ULL;
  full_cong_mark_trail(h, prev_te, next_ep);
  return (h->inconsistent != 0ULL) ? 2ULL : 1ULL;
}

u64 full_cong_equiv_fold(FullHdr *h, u32 a, u32 b, u32 next_ep) {
  u64 prev_te = h->trail_end;
  u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 ra = full_cong_find(repr, a);
  u32 rb = full_cong_find(repr, b);
  bool ch = false;
  i8 va = vals[ra];
  i8 vb = vals[rb];
  if (va != (i8)0) {
    u32 target = (va > (i8)0) ? rb : (rb ^ 1u);
    if (vals[target] <= (i8)0) {
      if (!full_add_unit(h, target)) {
        full_cong_mark_trail(h, prev_te, next_ep);
        return 2ULL;
      }
      h->cong_cnt = h->cong_cnt + 1ULL;
      ch = true;
    }
  } else if (vb != (i8)0) {
    u32 target = (vb > (i8)0) ? ra : (ra ^ 1u);
    if (vals[target] <= (i8)0) {
      if (!full_add_unit(h, target)) {
        full_cong_mark_trail(h, prev_te, next_ep);
        return 2ULL;
      }
      h->cong_cnt = h->cong_cnt + 1ULL;
      ch = true;
    }
  }
  if (full_cong_merge(h, ra, rb)) {
    ch = true;
    u64 cv = h->cur_vars;
    u32 av = a >> 1; u32 bv = b >> 1; u32 rav = ra >> 1; u32 rbv = rb >> 1;
    if ((u64)av < cv) { tmk[av] = next_ep; }
    if ((u64)bv < cv) { tmk[bv] = next_ep; }
    if ((u64)rav < cv) { tmk[rav] = next_ep; }
    if ((u64)rbv < cv) { tmk[rbv] = next_ep; }
  }
  if (h->trail_end > prev_te) { full_cong_mark_trail(h, prev_te, next_ep); }
  return (h->inconsistent != 0ULL) ? 2ULL : (ch ? 1ULL : 0ULL);
}

u64 full_cong_emit_xor(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2) {
  u32 lhs = ((x0 ^ 1u) & (~1u)) | (((x0 ^ 1u) ^ x1 ^ x2) & 1u);
  u32 r0 = x1 & (~1u); u32 r1 = x2 & (~1u);
  scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | 2u;
  scr[g_len + 2ULL] = (r0 < r1) ? r0 : r1; scr[g_len + 3ULL] = (r0 < r1) ? r1 : r0;
  return g_len + 4ULL;
}

bool full_cong_has_clause_k(FullHdr *h, u32 k) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *lm = (u8 *)h->lit_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 nlits = h->cur_vars << 1;
  if (k < 3u || k > 5u || (u64)k > h->cur_vars) { return false; }
  u32 min_l = tmp[0]; u32 min_d = wvec[((u64)min_l << 1) + 1ULL];
  u32 i = 0u;
  while (i < k) {
    u32 tl = tmp[i];
    lm[tl] = (u8)(i + 1u);
    u32 d = wvec[((u64)tl << 1) + 1ULL];
    if (d < min_d) { min_d = d; min_l = tl; }
    i = i + 1u;
  }
  bool res = false;
  u64 off = (u64)wvec[(u64)min_l << 1];
  u64 end = off + (u64)wvec[((u64)min_l << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        i8 ov = vals[ot];
        if (ov < (i8)0 || (ov == (i8)0 && lm[ot] != (u8)0)) { res = true; break; }
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u) { continue; }
    bool ok = true; u32 matched_cnt = 0u; u32 j = 0u;
    while (j < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)j];
      i8 cv = vals[cl];
      if (cv > (i8)0) { ok = false; break; }
      if (cv == (i8)0) {
        if (lm[cl] == (u8)0) { ok = false; break; }
        matched_cnt = matched_cnt + 1u;
      }
      j = j + 1u;
    }
    if (ok && matched_cnt >= k) { res = true; break; }
  }
  i = 0u;
  while (i < k) { lm[tmp[i]] = (u8)0; i = i + 1u; }
  return res;
}

u64 full_cong_emit_xor4(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2, u32 x3) {
  u32 lhs = (x0 & (~1u)) | ((1u ^ x0 ^ x1 ^ x2 ^ x3) & 1u);
  u32 r0 = x1 & (~1u); u32 r1 = x2 & (~1u); u32 r2 = x3 & (~1u);
  if (r0 > r1) { u32 t = r0; r0 = r1; r1 = t; }
  if (r1 > r2) { u32 t = r1; r1 = r2; r2 = t; }
  if (r0 > r1) { u32 t = r0; r0 = r1; r1 = t; }
  scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | 3u;
  scr[g_len + 2ULL] = r0; scr[g_len + 3ULL] = r1; scr[g_len + 4ULL] = r2;
  return g_len + 5ULL;
}

u64 full_cong_extract_xor_k(FullHdr *h, u32 k, u32 neg_p, u64 g_len, u64 g_cap) {
  if (k < 3u || k > 5u || (u64)k > h->cur_vars) { return g_len; }
  u64 need_words = (u64)k * (u64)(k + 1u);
  if (g_len + need_words > g_cap) { return g_len; }
  u32 *base = (u32 *)h->work_stk2; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *wvec = (u32 *)h->watch_vec; u32 *nbc = (u32 *)h->work_stk1;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mx = 0u; u32 j = 0u;
  while (j < k) {
    u32 bj = base[j];
    if (bj > mx) { mx = bj; }
    u32 bi = 0u;
    while (bi < j) {
      if ((base[bi] >> 1) == (bj >> 1)) { return g_len; }
      bi = bi + 1u;
    }
    j = j + 1u;
  }
  j = 0u;
  while (j < k) {
    u32 bj = base[j];
    if ((bj & 1u) != 0u && bj != mx) { return g_len; }
    j = j + 1u;
  }
  u32 needed_cl = 1u << (k - 2u);
  j = 0u;
  while (j < k) {
    u32 pl = base[j] & (~1u); u32 nl = pl | 1u;
    u32 wp = wvec[((u64)pl << 1) + 1ULL]; u32 wn = wvec[((u64)nl << 1) + 1ULL];
    u32 bp = nbc[pl ^ 1u]; u32 bn = nbc[nl ^ 1u];
    u32 lp = (wp > bp) ? ((wp - bp) >> 1) : 0u;
    u32 ln = (wn > bn) ? ((wn - bn) >> 1) : 0u;
    if ((u64)lp + (u64)bp < (u64)needed_cl || (u64)ln + (u64)bn < (u64)needed_cl) {
      return g_len;
    }
    j = j + 1u;
  }
  u32 lim = 1u << k;
  u32 mask = 1u;
  while (mask < lim) {
    u32 pop = 0u; u32 b = 0u;
    while (b < k) { pop = pop ^ ((mask >> b) & 1u); b = b + 1u; }
    if (pop == 0u) {
      b = 0u;
      while (b < k) { tmp[b] = base[b] ^ ((mask >> b) & 1u); b = b + 1u; }
      if (!full_cong_has_clause_k(h, k)) { return g_len; }
    }
    mask = mask + 1u;
  }
  if (k == 4u) {
    u32 b0 = base[0]; u32 b1 = base[1]; u32 b2 = base[2]; u32 b3 = base[3];
    g_len = full_cong_emit_xor4(scr, g_len, b0, b1, b2, b3);
    g_len = full_cong_emit_xor4(scr, g_len, b1, b0, b2, b3);
    g_len = full_cong_emit_xor4(scr, g_len, b2, b0, b1, b3);
    g_len = full_cong_emit_xor4(scr, g_len, b3, b0, b1, b2);
    return g_len;
  }
  u32 arity = k - 1u; u32 sign = 1u ^ (neg_p & 1u);
  j = 0u;
  while (j < k) {
    u32 lhs = (base[j] & (~1u)) | sign;
    scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | arity;
    u32 rk = 0u; u32 i = 0u;
    while (i < k) {
      if (i != j) { tmp[rk] = base[i] & (~1u); rk = rk + 1u; }
      i = i + 1u;
    }
    full_sort_u32(tmp, arity);
    i = 0u;
    while (i < arity) { scr[g_len + 2ULL + (u64)i] = tmp[i]; i = i + 1u; }
    g_len = g_len + 2ULL + (u64)arity;
    j = j + 1u;
  }
  return g_len;
}

u64 full_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap) {
  if ((a >> 1) == (b >> 1) || (a >> 1) == (c >> 1) || (b >> 1) == (c >> 1)) { return g_len; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mx = (a > b) ? a : b;
  if (c > mx) { mx = c; }
  if (((a & 1u) == 0u || a == mx) && ((b & 1u) == 0u || b == mx) &&
      ((c & 1u) == 0u || c == mx) &&
      full_has_ternary(h, a, b ^ 1u, c ^ 1u) && full_has_ternary(h, a ^ 1u, b, c ^ 1u) &&
      full_has_ternary(h, a ^ 1u, b ^ 1u, c)) {
    if (g_len + 12ULL <= g_cap) {
      g_len = full_cong_emit_xor(scr, g_len, a, b, c);
      g_len = full_cong_emit_xor(scr, g_len, b, a, c);
      g_len = full_cong_emit_xor(scr, g_len, c, a, b);
    }
    return g_len;
  }
  return g_len;
}

void full_cong_count_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *nbc = (u32 *)h->work_stk1;
  u64 l = 0ULL;
  while (l < nlits) { nbc[l] = 0u; l = l + 1ULL; }
  l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 end = off + (u64)wvec[(l << 1) + 1ULL];
    u64 p = off; u32 bc = 0u;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) { bc = bc + 1u; p = p + 1ULL; }
      else { p = p + 2ULL; }
    }
    nbc[l ^ 1ULL] = bc;
    l = l + 1ULL;
  }
}

bool full_cong_eb_match(FullHdr *h, u32 x, u32 l, u32 k) {
  u32 *nbc = (u32 *)h->work_stk1;
  if (nbc[x] == 0u) { return false; }
  return full_has_bin(h, x ^ 1u, l) || full_has_bin(h, x ^ 1u, k);
}

u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  full_cong_count_bins(h);
  u64 alen = h->arena_len; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 p = 0ULL; u64 ticks = 0ULL;
  while (p < alen && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz == 3u) {
      u32 a = ar[p + 3ULL]; u32 b = ar[p + 4ULL]; u32 c = ar[p + 5ULL];
      if (vals[a] == (i8)0 && vals[b] == (i8)0 && vals[c] == (i8)0) {
        u32 l = 0u; u32 k = 0u; bool found = false;
        if (full_cong_eb_match(h, a, b, c)) { l = b; k = c; found = true; }
        else if (full_cong_eb_match(h, b, a, c)) { l = a; k = c; found = true; }
        else if (full_cong_eb_match(h, c, a, b)) { l = a; k = b; found = true; }
        if (found && !full_has_bin(h, l, k)) {
          ticks = ticks + 2ULL;
          u64 st = full_add_bin(h, l, k);
          if (st == 20ULL) { return 20ULL; }
          if (st == 2ULL) { h->oom = 0ULL; h->ant_sz = 1ULL; break; }
        }
      }
    }
    p = np;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_cong_find_units_equivs(FullHdr *h) {
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u8 *lm = (u8 *)h->lit_mark; i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *fl = (u32 *)h->flags;
  u64 v = 0ULL;
  while (v < cv && h->inconsistent == 0ULL) {
    if ((fl[v] & FL_ACTIVE) == 0u || vals[v << 1] != (i8)0) { v = v + 1ULL; continue; }
    u64 sign = 0ULL;
    while (sign < 2ULL && vals[v << 1] == (i8)0 && h->inconsistent == 0ULL) {
      u32 lit = (u32)((v << 1) | sign);
      u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      bool found_u = false;
      u64 p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits) {
          if (ot == lit || lm[ot ^ 1u] != (u8)0) { found_u = true; break; }
          lm[ot] = (u8)1;
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits) { lm[ot] = (u8)0; }
      }
      if (found_u) {
        if (!full_add_unit(h, lit)) { return 20ULL; }
        h->cong_cnt = h->cong_cnt + 1ULL;
      }
      sign = sign + 1ULL;
    }
    v = v + 1ULL;
  }
  v = 0ULL;
  while (v < cv && h->inconsistent == 0ULL) {
    if ((fl[v] & FL_ACTIVE) == 0u || vals[v << 1] != (i8)0) { v = v + 1ULL; continue; }
    u32 lit = (u32)(v << 1);
    u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
    u64 p = off; bool any = false;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
      p = p + 1ULL;
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits && (u64)(ot >> 1) > v) { lm[ot] = (u8)1; any = true; }
    }
    u64 mcnt = 0ULL;
    if (any) {
      u32 nlit = lit ^ 1u;
      u64 noff = (u64)wvec[(u64)nlit << 1]; u64 nend = noff + (u64)wvec[((u64)nlit << 1) + 1ULL];
      p = noff;
      while (p < nend) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && (u64)(ot >> 1) > v && lm[ot ^ 1u] == (u8)1) {
          lm[ot ^ 1u] = (u8)3;
          if (mcnt < cv) { tmp[mcnt] = ot; mcnt = mcnt + 1ULL; }
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && (u64)(ot >> 1) > v) { lm[ot] = (u8)0; }
      }
      u64 k = 0ULL;
      while (k < mcnt && h->inconsistent == 0ULL) {
        if (full_cong_equiv_fold(h, lit, tmp[k], 1u) == 2ULL) { return 20ULL; }
        k = k + 1ULL;
      }
    }
    v = v + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_cong_extract_and_clause_fid(FullHdr *h, u32 usz, u64 g_len, u64 g_cap, u64 tick_lim) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (usz < 3u || usz > CONG_AND_USZ_MAX || (u64)usz > cv) { return g_len; }
  u32 arity = usz - 1u;
  if (g_len > g_cap || g_cap - g_len < 2ULL + (u64)arity) { return g_len; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *nbc = (u32 *)h->work_stk1;
  u32 *base = (u32 *)h->work_stk2;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u8 *lm = (u8 *)h->lit_mark;
  u32 first_i = usz;
  u32 min_d = 0xFFFFFFFFu;
  u32 m = 0u;
  while (m < usz) {
    u32 bm = base[m];
    u32 nbm = bm ^ 1u;
    if (nbc[bm] >= arity) {
      lm[nbm] = (u8)5;
      u32 d = wvec[((u64)nbm << 1) + 1ULL];
      if (first_i == usz || d < min_d) { min_d = d; first_i = m; }
    } else {
      lm[nbm] = (u8)1;
    }
    m = m + 1u;
  }
  u64 ticks = h->res_sz;
  if (first_i < usz) {
    u32 step = 0u;
    while (step < usz && g_len + 2ULL + (u64)arity <= g_cap && ticks < tick_lim) {
      u32 i = (step == 0u) ? first_i : ((step <= first_i) ? (step - 1u) : step);
      u32 lhs = base[i];
      u32 not_lhs = lhs ^ 1u;
      if ((lm[not_lhs] & (u8)4) != (u8)0) {
        u64 off = (u64)wvec[(u64)not_lhs << 1];
        u64 end = off + (u64)wvec[((u64)not_lhs << 1) + 1ULL];
        u64 wp = off;
        u32 matched = 0u;
        while (wp < end && ticks < tick_lim) {
          u32 w0 = wstk[wp]; wp = wp + 1ULL;
          ticks = ticks + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 ot = w0 & PW_LIT_MASK;
            if ((u64)ot < nlits && ot != not_lhs && (lm[ot] & (u8)3) == (u8)1) {
              lm[ot] = lm[ot] | (u8)2;
              matched = matched + 1u;
            }
          } else {
            if (wp >= end) { break; }
            wp = wp + 1ULL;
          }
        }
        if (matched == arity) {
          scr[g_len] = lhs;
          scr[g_len + 1ULL] = (arity <= 64u) ? arity : ((3u << 28) | arity);
          u32 rk = 0u; u32 j = 0u;
          while (j < usz) {
            if (j != i) { scr[g_len + 2ULL + (u64)rk] = base[j] ^ 1u; rk = rk + 1u; }
            j = j + 1u;
          }
          g_len = g_len + 2ULL + (u64)arity;
        }
        m = 0u;
        while (m < usz) {
          u32 nbm = base[m] ^ 1u;
          u8 mv = lm[nbm];
          if ((mv & (u8)2) != (u8)0) { lm[nbm] = mv & (u8)5; }
          else { lm[nbm] = (u8)1; }
          m = m + 1u;
        }
      }
      step = step + 1u;
    }
  }
  m = 0u;
  while (m < usz) { lm[base[m] ^ 1u] = (u8)0; m = m + 1u; }
  h->res_sz = ticks;
  return g_len;
}

u64 full_cong_extract_from_fid(FullHdr *h, u64 g_start, u64 g_cap, u64 tick_lim) {
  if (g_start > g_cap) { return g_start; }
  full_cong_count_bins(h);
  u32 *ar = (u32 *)h->arena;
  u32 *nbc = (u32 *)h->work_stk1;
  u32 *base = (u32 *)h->work_stk2;
  u32 *rr = (u32 *)h->red_refs;
  i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars;
  u64 rcap = h->red_cap;
  u64 p = 0ULL;
  u64 g_len = g_start;
  u64 ticks = 0ULL;
  u64 wn = 0ULL;
  while (p < h->arena_len && g_len + 4ULL <= g_cap && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 usz = 0u; u32 max_nbc = 0u; u32 min_nbc = 0xFFFFFFFFu;
      u32 neg_p = 0u; bool sat = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        i8 lv = vals[l];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          if (usz >= CONG_AND_USZ_MAX || (u64)usz >= cv) { sat = true; break; }
          base[usz] = l; usz = usz + 1u;
          u32 c_n = nbc[l];
          if (c_n > max_nbc) { max_nbc = c_n; }
          if (c_n < min_nbc) { min_nbc = c_n; }
          if ((l & 1u) != 0u) { neg_p = neg_p ^ 1u; }
        }
        k = k + 1u;
      }
      if (!sat && usz >= 3u && usz <= 65u && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity) {
          h->res_sz = ticks;
          g_len = full_cong_extract_and_clause_fid(h, usz, g_len, g_cap, tick_lim);
          ticks = h->res_sz;
        }
        if (usz == 3u && g_len + 12ULL <= g_cap) {
          g_len = full_cong_try_xor_ite(h, base[0], base[1], base[2], g_len, g_cap);
          ticks = ticks + 4ULL;
        } else if (usz >= 4u && usz <= 5u && g_len + (u64)usz * (u64)(usz + 1u) <= g_cap) {
          g_len = full_cong_extract_xor_k(h, usz, neg_p, g_len, g_cap);
          ticks = ticks + 8ULL;
        }
      } else if (!sat && usz >= 66u && usz <= CONG_AND_USZ_MAX && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity && wn < rcap) {
          rr[wn] = (u32)p; wn = wn + 1ULL;
        }
      }
    }
    p = np;
  }
  u64 wi = 0ULL;
  while (wi < wn && g_len + 4ULL <= g_cap && ticks < tick_lim) {
    u64 wp = (u64)rr[wi];
    u32 hdr = ar[wp]; u32 sz = ar[wp + 2ULL];
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 66u) {
      u32 usz = 0u; u32 max_nbc = 0u; u32 min_nbc = 0xFFFFFFFFu;
      bool sat = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[wp + 3ULL + (u64)k];
        i8 lv = vals[l];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          if (usz >= CONG_AND_USZ_MAX || (u64)usz >= cv) { sat = true; break; }
          base[usz] = l; usz = usz + 1u;
          u32 c_n = nbc[l];
          if (c_n > max_nbc) { max_nbc = c_n; }
          if (c_n < min_nbc) { min_nbc = c_n; }
        }
        k = k + 1u;
      }
      if (!sat && usz >= 66u && usz <= CONG_AND_USZ_MAX && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity) {
          h->res_sz = ticks;
          g_len = full_cong_extract_and_clause_fid(h, usz, g_len, g_cap, tick_lim);
          ticks = h->res_sz;
        }
      }
    }
    wi = wi + 1ULL;
  }
  return g_len;
}

bool full_cong_and_match(FullHdr *h, u32 ent, u32 ua) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (ua < 2u || ua > CONG_AND_ARITY_MAX || (u64)ua > cv) { return false; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u8 *lm = (u8 *)h->lit_mark;
  u32 em = scr[(u64)ent + 1ULL];
  u32 ea = ((em >> 28) == 3u) ? (em & CONG_ARITY_MASK) : (em & 0xFFu);
  if (ea < 2u || ea > CONG_AND_ARITY_MAX || (u64)ea > cv) { return false; }
  u32 distinct_ua = 0u; u32 k = 0u;
  while (k < ua) {
    u32 tl = tmp[k];
    if ((u64)tl >= nlits) {
      u32 c = 0u;
      while (c < k) { lm[tmp[c]] = (u8)0; c = c + 1u; }
      return false;
    }
    if (lm[tl] == (u8)0) { lm[tl] = (u8)1; distinct_ua = distinct_ua + 1u; }
    k = k + 1u;
  }
  bool ok = true; u32 matched = 0u; u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev < (i8)0) { ok = false; break; }
    if (ev == (i8)0) {
      u8 mv = lm[er];
      if (mv == (u8)0) { ok = false; break; }
      if (mv == (u8)1) { lm[er] = (u8)2; matched = matched + 1u; }
    }
    j = j + 1u;
  }
  k = 0u;
  while (k < ua) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  return ok && (matched == distinct_ua);
}

u32 full_cong_xor_match(FullHdr *h, u32 ent, u32 ua) {
  if (ua < 2u || ua > 4u || h->cur_vars < 2ULL || (u64)ua > h->cur_vars) { return 0xFFFFFFFFu; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ep = (u32 *)h->min_clr;
  u32 ea = scr[(u64)ent + 1ULL] & 0xFFu;
  if (ea < 2u || ea > 4u || (u64)ea > h->cur_vars) { return 0xFFFFFFFFu; }
  u32 eflip = 0u; u32 ena = 0u; u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev != (i8)0) {
      if (ev > (i8)0) { eflip = eflip ^ 1u; }
    } else {
      eflip = eflip ^ (er & 1u);
      ep[ena] = er & (~1u);
      ena = ena + 1u;
    }
    j = j + 1u;
  }
  if (ena < ua) { return 0xFFFFFFFFu; }
  if (ena > 1u) { full_sort_u32(ep, ena); }
  u32 eua = 0u; j = 0u;
  while (j < ena) {
    if (j + 1u < ena && ep[j] == ep[j + 1u]) { j = j + 2u; }
    else { ep[eua] = ep[j]; eua = eua + 1u; j = j + 1u; }
  }
  if (eua != ua) { return 0xFFFFFFFFu; }
  j = 0u;
  while (j < ua) { if (ep[j] != tmp[j]) { return 0xFFFFFFFFu; } j = j + 1u; }
  return full_cong_find(repr, scr[ent]) ^ eflip;
}

void full_cong_enq_var(FullHdr *h, u64 ctrl_off, u32 v) {
  if (ctrl_off >= h->scratch_cap || (u64)v >= h->cur_vars) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 occ_bkt = scr[ctrl_off];
  u64 inq_off = (u64)scr[ctrl_off + 2ULL];
  u64 q_off = (u64)scr[ctrl_off + 3ULL];
  u32 b = v & (occ_bkt - 1u);
  if (scr[inq_off + (u64)b] == 0u) {
    u32 q_head = scr[ctrl_off + 4ULL]; u32 q_len = scr[ctrl_off + 5ULL];
    if (q_len < occ_bkt) {
      u32 tail = (q_head + q_len) & (occ_bkt - 1u);
      scr[inq_off + (u64)b] = 1u;
      scr[q_off + (u64)tail] = b;
      scr[ctrl_off + 5ULL] = q_len + 1u;
    }
  }
}

u64 full_cong_eval_gate(FullHdr *h, u64 g, u64 ht_off, u64 ht_sz, u32 next_ep, u64 ctrl_off) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 *tmp = (u32 *)h->tmp_lits; i8 *vals = (i8 *)h->values;
  u32 *trl = (u32 *)h->trail;
  u32 raw_lhs = scr[g]; u32 meta = scr[g + 1ULL];
  u32 tag = meta >> 28;
  u32 arity = (tag == 3u) ? (meta & CONG_ARITY_MASK) : (meta & 0xFFu);
  u32 gtype = (tag == 3u) ? 0u : tag;
  if (arity < 2u || arity > CONG_AND_ARITY_MAX || (u64)arity > h->cur_vars) { return 0ULL; }
  u32 lhs = full_cong_find(repr, raw_lhs);
  u32 i = 0u;
  while (i < arity) { tmp[i] = full_cong_find(repr, scr[g + 2ULL + (u64)i]); i = i + 1u; }
  u64 ht_lim = (ht_sz * 3ULL) >> 2;
  u64 te0 = h->trail_end;
  u32 htag = gtype; u32 harity = arity; bool need_hash = true; bool changed = false;
  if (gtype == 0u) {
    bool has_false = false; u32 na = 0u; i = 0u;
    while (i < arity) {
      u32 r = tmp[i]; i8 rv = vals[r];
      if (rv < (i8)0) { has_false = true; break; }
      if (rv == (i8)0) { tmp[na] = r; na = na + 1u; }
      i = i + 1u;
    }
    if (has_false) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (na == 0u) {
      u64 uf = full_cong_unit_fold(h, lhs, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else {
      if (na > 1u) { full_sort_u32(tmp, na); }
      bool clash = false; u32 ua = 0u; u32 si = 0u;
      while (si < na) {
        u32 cur = tmp[si]; si = si + 1u;
        if (cur == (lhs ^ 1u)) { clash = true; break; }
        if (ua == 0u) { tmp[0] = cur; ua = 1u; }
        else {
          u32 prev = tmp[ua - 1u];
          if (cur == prev) { continue; }
          if (cur == (prev ^ 1u)) { clash = true; break; }
          tmp[ua] = cur; ua = ua + 1u;
        }
      }
      if (clash) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 1u) {
        u32 r0 = tmp[0];
        u64 ef = full_cong_equiv_fold(h, lhs, r0, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, r0 >> 1);
        }
        need_hash = false;
      } else if (vals[lhs] > (i8)0) {
        u32 k = 0u;
        while (k < ua) {
          u64 uf = full_cong_unit_fold(h, tmp[k], next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          k = k + 1u;
        }
        need_hash = false;
      } else {
        harity = ua;
      }
    }
  } else if (gtype == 1u && arity >= 2u && arity <= 4u) {
    u32 flip = 0u; u32 na = 0u; i = 0u;
    while (i < arity) {
      u32 r = tmp[i]; i8 rv = vals[r];
      if (rv != (i8)0) {
        if (rv > (i8)0) { flip = flip ^ 1u; }
      } else {
        flip = flip ^ (r & 1u);
        tmp[na] = r & (~1u); na = na + 1u;
      }
      i = i + 1u;
    }
    lhs = lhs ^ flip;
    if (na > 1u) { full_sort_u32(tmp, na); }
    u32 ua = 0u; i = 0u;
    while (i < na) {
      if (i + 1u < na && tmp[i] == tmp[i + 1u]) { i = i + 2u; }
      else { tmp[ua] = tmp[i]; ua = ua + 1u; i = i + 1u; }
    }
    if (ua > 0u) {
      u32 lhs_v = lhs & (~1u); u32 self_i = ua; i = 0u;
      while (i < ua) {
        if (tmp[i] == lhs_v) { self_i = i; break; }
        i = i + 1u;
      }
      if (self_i < ua) {
        u32 j = self_i;
        while (j + 1u < ua) { tmp[j] = tmp[j + 1u]; j = j + 1u; }
        ua = ua - 1u;
        u32 lsign = lhs & 1u;
        if (ua == 0u) {
          if (lsign != 0u) { h->inconsistent = 1ULL; return 2ULL; }
          need_hash = false;
        } else if (ua == 1u) {
          u32 ul = tmp[0] ^ (1u ^ lsign);
          u64 uf = full_cong_unit_fold(h, ul, next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 2u) {
          u32 a0 = tmp[0] ^ lsign; u32 a1 = tmp[1];
          u64 ef = full_cong_equiv_fold(h, a0, a1, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, a1 >> 1);
          }
          need_hash = false;
        } else {
          need_hash = false;
        }
      }
    }
    if (need_hash) {
      if (ua == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 1u) {
        u32 r0 = tmp[0];
        u64 ef = full_cong_equiv_fold(h, lhs, r0, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, r0 >> 1);
        }
        need_hash = false;
      } else if (ua == 2u && vals[lhs] != (i8)0) {
        u32 a0 = (vals[lhs] > (i8)0) ? (tmp[0] ^ 1u) : tmp[0]; u32 a1 = tmp[1];
        u64 ef = full_cong_equiv_fold(h, a0, a1, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, a1 >> 1);
        }
        need_hash = false;
      } else {
        harity = ua;
      }
    }
  } else if (gtype == 2u && arity == 3u) {
    u32 c = tmp[0]; u32 t = tmp[1]; u32 e = tmp[2];
    i8 vc = vals[c]; i8 vt = vals[t]; i8 ve = vals[e];
    if (vc != (i8)0) {
      u32 br = (vc > (i8)0) ? t : e;
      u64 ef = full_cong_equiv_fold(h, lhs, br, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, br >> 1);
      }
      need_hash = false;
    } else if (t == e) {
      u64 ef = full_cong_equiv_fold(h, lhs, t, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, t >> 1);
      }
      need_hash = false;
    } else if (vt > (i8)0 && ve < (i8)0) {
      u64 ef = full_cong_equiv_fold(h, lhs, c, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, c >> 1);
      }
      need_hash = false;
    } else if (vt < (i8)0 && ve > (i8)0) {
      u64 ef = full_cong_equiv_fold(h, lhs, c ^ 1u, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, c >> 1);
      }
      need_hash = false;
    } else if (vt > (i8)0 && ve > (i8)0) {
      u64 uf = full_cong_unit_fold(h, lhs, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (vt < (i8)0 && ve < (i8)0) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (vt == (i8)0 && ve == (i8)0 && t == (e ^ 1u)) {
      lhs = lhs ^ ((1u ^ c ^ t) & 1u);
      u32 r0 = c & (~1u); u32 r1 = t & (~1u);
      if (r0 == r1) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vals[lhs] != (i8)0) {
        u32 a0 = (vals[lhs] > (i8)0) ? (r0 ^ 1u) : r0;
        u64 ef = full_cong_equiv_fold(h, a0, r1, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, r1 >> 1);
        }
        need_hash = false;
      } else {
        tmp[0] = (r0 < r1) ? r0 : r1; tmp[1] = (r0 < r1) ? r1 : r0;
        htag = 1u; harity = 2u;
      }
    } else {
      bool ite_and = false; u32 a0 = 0u; u32 a1 = 0u;
      if (vt > (i8)0) {
        lhs = lhs ^ 1u; a0 = c ^ 1u; a1 = e ^ 1u; ite_and = true;
      } else if (vt < (i8)0) {
        a0 = c ^ 1u; a1 = e; ite_and = true;
      } else if (ve > (i8)0) {
        lhs = lhs ^ 1u; a0 = c; a1 = t ^ 1u; ite_and = true;
      } else if (ve < (i8)0) {
        a0 = c; a1 = t; ite_and = true;
      } else if (c == t) {
        lhs = lhs ^ 1u; a0 = c ^ 1u; a1 = e ^ 1u; ite_and = true;
      } else if (c == (t ^ 1u)) {
        a0 = c ^ 1u; a1 = e; ite_and = true;
      } else if (c == (e ^ 1u)) {
        lhs = lhs ^ 1u; a0 = c; a1 = t ^ 1u; ite_and = true;
      } else if (c == e) {
        a0 = c; a1 = t; ite_and = true;
      }
      if (ite_and) {
        if (a0 == a1) {
          u64 ef = full_cong_equiv_fold(h, lhs, a0, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, a0 >> 1);
          }
          need_hash = false;
        } else if (a0 == (a1 ^ 1u) || a0 == (lhs ^ 1u) || a1 == (lhs ^ 1u)) {
          u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (vals[lhs] > (i8)0) {
          u64 u0 = full_cong_unit_fold(h, a0, next_ep);
          if (u0 == 2ULL) { return 2ULL; }
          if (u0 == 1ULL) { changed = true; }
          u64 u1 = full_cong_unit_fold(h, a1, next_ep);
          if (u1 == 2ULL) { return 2ULL; }
          if (u1 == 1ULL) { changed = true; }
          need_hash = false;
        } else {
          tmp[0] = (a0 < a1) ? a0 : a1; tmp[1] = (a0 < a1) ? a1 : a0;
          htag = 0u; harity = 2u;
        }
      } else {
        if ((c & 1u) != 0u) { c = c ^ 1u; u32 sw = t; t = e; e = sw; }
        if ((t & 1u) != 0u) { lhs = lhs ^ 1u; t = t ^ 1u; e = e ^ 1u; }
        tmp[0] = c; tmp[1] = t; tmp[2] = e;
      }
    }
  } else {
    need_hash = false;
  }
  bool keep = false;
  if (need_hash && h->inconsistent == 0ULL) {
    keep = true;
    u64 hv = (u64)htag * 0x9E3779B1ULL + (u64)harity;
    i = 0u;
    while (i < harity) { hv = hv * 0x85EBCA77ULL + (u64)tmp[i] + 1ULL; i = i + 1u; }
    u64 slot = hv & (ht_sz - 1ULL); u64 probes = 0ULL; bool seen_self = false;
    while (probes < 128ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) {
        if (!seen_self && htag == gtype && h->res_sz < ht_lim) {
          scr[ht_off + slot] = (u32)g; h->res_sz = h->res_sz + 1ULL;
        }
        break;
      }
      if (ent == (u32)g) {
        seen_self = true; slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
        continue;
      }
      u32 em = scr[(u64)ent + 1ULL]; u32 etag = em >> 28;
      u32 egtype = (etag == 3u) ? 0u : etag;
      if (egtype == htag) {
        bool matched = false; u32 match_lhs = scr[ent];
        if (htag == 0u) {
          matched = full_cong_and_match(h, ent, harity);
        } else if (htag == 1u) {
          u32 ml = full_cong_xor_match(h, ent, harity);
          if (ml != 0xFFFFFFFFu) { matched = true; match_lhs = ml; }
        } else if (htag == 2u && (em & 0xFFu) == 3u) {
          u32 ec = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 et = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          u32 ee = full_cong_find(repr, scr[(u64)ent + 4ULL]);
          if ((ec & 1u) != 0u) { ec = ec ^ 1u; u32 sw = et; et = ee; ee = sw; }
          if ((et & 1u) != 0u) { match_lhs = match_lhs ^ 1u; et = et ^ 1u; ee = ee ^ 1u; }
          matched = (ec == tmp[0] && et == tmp[1] && ee == tmp[2]);
        }
        if (matched) {
          keep = false;
          u64 ef = full_cong_equiv_fold(h, lhs, match_lhs, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, lhs >> 1);
            full_cong_enq_var(h, ctrl_off, match_lhs >> 1);
            full_cong_enq_var(h, ctrl_off, full_cong_find(repr, lhs) >> 1);
            full_cong_enq_var(h, ctrl_off, full_cong_find(repr, match_lhs) >> 1);
          }
          break;
        }
      }
      slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
    }
  }
  while (te0 < h->trail_end) {
    u32 tl = trl[te0];
    full_cong_enq_var(h, ctrl_off, tl >> 1);
    full_cong_enq_var(h, ctrl_off, full_cong_find(repr, tl) >> 1);
    te0 = te0 + 1ULL;
  }
  if (h->inconsistent != 0ULL) { return 2ULL; }
  return (changed ? 1ULL : 0ULL) | (keep ? 4ULL : 0ULL);
}

u64 full_cong_worklist(FullHdr *h, u64 g_len, u64 ctrl_off, u64 tick_lim) {
  if (tick_lim > 0x7FFFFFFFFFFFFFFFULL) { tick_lim = 0x7FFFFFFFFFFFFFFFULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 occ_bkt = scr[ctrl_off]; u64 bkt_off = (u64)scr[ctrl_off + 1ULL];
  u64 inq_off = (u64)scr[ctrl_off + 2ULL]; u64 q_off = (u64)scr[ctrl_off + 3ULL];
  u64 ht_off = (u64)scr[ctrl_off + 6ULL]; u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  u64 i = 0ULL;
  while (i < (u64)occ_bkt) {
    scr[bkt_off + i] = 0xFFFFFFFFu; scr[inq_off + i] = 0u; i = i + 1ULL;
  }
  scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
  u64 occ_end = g_len; u64 ticks = 0ULL; u64 rehashes = 0ULL;
  u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL && ticks < tick_lim) {
    u32 gm = scr[g + 1ULL];
    u32 arity = ((gm >> 28) == 3u) ? (gm & CONG_ARITY_MASK) : (gm & 0xFFu);
    u64 next_g = g + 2ULL + (u64)arity;
    ticks = ticks + 2ULL;
    u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, 2u, ctrl_off);
    if ((er & 2ULL) != 0ULL) { return 20ULL; }
    if ((er & 4ULL) != 0ULL && occ_end + (1ULL + (u64)arity) * 3ULL <= ctrl_off) {
      u32 raw_l = scr[g];
      u32 rl = full_cong_find(repr, raw_l); u32 b0 = (rl >> 1) & (occ_bkt - 1u);
      scr[occ_end] = (u32)g;
      scr[occ_end + 1ULL] = raw_l;
      scr[occ_end + 2ULL] = scr[bkt_off + (u64)b0];
      scr[bkt_off + (u64)b0] = (u32)occ_end;
      occ_end = occ_end + 3ULL;
      u32 s = 0u;
      while (s < arity) {
        u32 raw_r = scr[g + 2ULL + (u64)s];
        u32 rr = full_cong_find(repr, raw_r);
        u32 bs = (rr >> 1) & (occ_bkt - 1u);
        scr[occ_end] = (u32)g;
        scr[occ_end + 1ULL] = raw_r;
        scr[occ_end + 2ULL] = scr[bkt_off + (u64)bs];
        scr[bkt_off + (u64)bs] = (u32)occ_end;
        occ_end = occ_end + 3ULL;
        s = s + 1u;
      }
    }
    g = next_g;
  }
  u32 ep = 3u;
  while ((scr[ctrl_off + 5ULL] > 0u) && h->inconsistent == 0ULL && ticks < tick_lim) {
    u32 q_head = scr[ctrl_off + 4ULL]; u32 q_len = scr[ctrl_off + 5ULL];
    u32 b = scr[q_off + (u64)q_head];
    scr[ctrl_off + 4ULL] = (q_head + 1u) & (occ_bkt - 1u);
    scr[ctrl_off + 5ULL] = q_len - 1u;
    scr[inq_off + (u64)b] = 0u;
    u32 nd = scr[bkt_off + (u64)b]; scr[bkt_off + (u64)b] = 0xFFFFFFFFu;
    while (nd != 0xFFFFFFFFu && h->inconsistent == 0ULL && ticks < tick_lim) {
      u64 gn = (u64)scr[nd];
      u32 raw_lit = scr[(u64)nd + 1ULL];
      u32 nxt = scr[(u64)nd + 2ULL];
      ticks = ticks + 2ULL;
      u64 er = full_cong_eval_gate(h, gn, ht_off, ht_sz, ep, ctrl_off);
      if ((er & 2ULL) != 0ULL) { return 20ULL; }
      if ((er & 4ULL) != 0ULL) {
        u32 dst = full_cong_find(repr, raw_lit);
        u32 b_dst = (dst >> 1) & (occ_bkt - 1u);
        scr[(u64)nd + 2ULL] = scr[bkt_off + (u64)b_dst];
        scr[bkt_off + (u64)b_dst] = nd;
      }
      nd = nxt;
    }
    bool do_grow = (h->res_sz * 2ULL >= ht_sz) && (ht_sz < 1048576ULL) &&
      (ht_off + (ht_sz << 1) <= h->scratch_cap);
    bool do_flush = (!do_grow) && (h->res_sz * 4ULL >= ht_sz * 3ULL) && (rehashes < 4ULL);
    if ((do_grow || do_flush) && ticks < tick_lim) {
      if (do_grow) {
        ht_sz = ht_sz << 1;
        scr[ctrl_off + 7ULL] = (u32)ht_sz;
      } else {
        rehashes = rehashes + 1ULL;
      }
      i = 0ULL; while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
      h->res_sz = 0ULL;
      g = 0ULL;
      while (g < g_len && h->inconsistent == 0ULL && ticks < tick_lim) {
        u32 gm = scr[g + 1ULL];
    u32 arity = ((gm >> 28) == 3u) ? (gm & CONG_ARITY_MASK) : (gm & 0xFFu);
        ticks = ticks + 1ULL;
        u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, ep, ctrl_off);
        if ((er & 2ULL) != 0ULL) { return 20ULL; }
        g = g + 2ULL + (u64)arity;
      }
    }
    ep = ep + 1u;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

void full_cong_sift_pairs_fid(u32 *a, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 child = (root << 1) + 1ULL;
    if (child >= n) { break; }
    u64 sw = root;
    u32 sw_s = a[sw << 1]; u32 sw_r = a[(sw << 1) + 1ULL];
    u32 c_s = a[child << 1]; u32 c_r = a[(child << 1) + 1ULL];
    if (c_s > sw_s || (c_s == sw_s && c_r > sw_r)) {
      sw = child; sw_s = c_s; sw_r = c_r;
    }
    u64 right = child + 1ULL;
    if (right < n) {
      u32 r_s = a[right << 1]; u32 r_r = a[(right << 1) + 1ULL];
      if (r_s > sw_s || (r_s == sw_s && r_r > sw_r)) {
        sw = right; sw_s = r_s; sw_r = r_r;
      }
    }
    if (sw == root) { break; }
    u32 t_s = a[root << 1]; u32 t_r = a[(root << 1) + 1ULL];
    a[root << 1] = sw_s; a[(root << 1) + 1ULL] = sw_r;
    a[sw << 1] = t_s; a[(sw << 1) + 1ULL] = t_r;
    root = sw;
  }
}

void full_cong_sort_pairs_fid(u32 *a, u64 n) {
  if (n <= 1ULL) { return; }
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_cong_sift_pairs_fid(a, start, n);
  }
  u64 end = n;
  while (end > 1ULL) {
    end = end - 1ULL;
    u32 t_s = a[0]; u32 t_r = a[1];
    a[0] = a[end << 1]; a[1] = a[(end << 1) + 1ULL];
    a[end << 1] = t_s; a[(end << 1) + 1ULL] = t_r;
    full_cong_sift_pairs_fid(a, 0ULL, end);
  }
}

u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim) {
  if (h->inconsistent != 0ULL || h->ant_sz != 0ULL) {
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  if (tick_lim > 0x7FFFFFFFFFFFFFFFULL) { tick_lim = 0x7FFFFFFFFFFFFFFFULL; }
  if (tick_lim == 0ULL || h->scratch_cap < 4ULL) { return 1ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *fl = (u32 *)h->flags;
  u32 *mch = (u32 *)h->min_clr; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *occ_head = (u32 *)h->work_stk1; u32 *occ_cnt = (u32 *)h->work_stk2;
  u64 i = 0ULL; while (i < cv) { mch[i] = 0u; i = i + 1ULL; }
  bool has_mch = false; i = 0ULL;
  while (i < cv) {
    if ((fl[i] & FL_ACTIVE) != 0u) {
      u32 lit = (u32)(i << 1); u32 r = full_cong_find(repr, lit);
      if (r != lit) { mch[i] = 1u; mch[r >> 1] = 1u; has_mch = true; }
    }
    i = i + 1ULL;
  }
  if (!has_mch) { return 1ULL; }
  u64 max_cand = h->scratch_cap >> 2;
  u64 ncand = 0ULL; u64 p = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && ticks < tick_lim && h->inconsistent == 0ULL) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & PH_GARB) != 0u || sz < 3u) { p = np; continue; }
    bool sat = false; bool taut = false; bool c_mch = false; bool ovf = false;
    u32 msz = 0u; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k]; i8 lv = vals[l];
      if (lv > (i8)0) { sat = true; break; }
      if (lv < (i8)0) { k = k + 1u; continue; }
      if (mch[l >> 1] != 0u) { c_mch = true; }
      u32 r = full_cong_find(repr, l); i8 rv = vals[r];
      if (rv > (i8)0) { sat = true; break; }
      if (rv < (i8)0) { k = k + 1u; continue; }
      if (lm[r ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[r] == (u8)0) {
        if ((u64)msz < cv) { lm[r] = (u8)1; tmp[msz] = r; msz = msz + 1u; }
        else { ovf = true; break; }
      }
      k = k + 1u;
    }
    k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
    if (sat || taut) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      p = np; continue;
    }
    if (ovf) { p = np; continue; }
    if (msz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (msz == 1u) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, tmp[0])) { return 20ULL; }
      p = np; continue;
    }
    if (!c_mch) { p = np; continue; }
    if (ncand < max_cand) {
      u32 key = (msz << 1) | (((hdr & PH_RED) != 0u) ? 1u : 0u);
      scr[ncand << 1] = key; scr[(ncand << 1) + 1ULL] = (u32)p;
      ncand = ncand + 1ULL;
    }
    p = np;
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (ncand <= 1ULL || ticks >= tick_lim) { return 1ULL; }
  full_cong_sort_pairs_fid(scr, ncand);
  i = 0ULL;
  while (i < nlits) { occ_head[i] = 0xFFFFFFFFu; occ_cnt[i] = 0u; i = i + 1ULL; }
  u64 occ_pos = ncand << 1;
  u64 ci = 0ULL;
  while (ci < ncand && ticks < tick_lim && h->inconsistent == 0ULL) {
    u32 cref = scr[(ci << 1) + 1ULL];
    u32 chdr = ar[cref]; u32 csz = ar[(u64)cref + 2ULL];
    ticks = ticks + 1ULL;
    if ((chdr & PH_GARB) != 0u || csz < 3u) { ci = ci + 1ULL; continue; }
    bool c_red = (chdr & PH_RED) != 0u;
    bool sat = false; bool taut = false; bool ovf = false;
    u32 msz = 0u; u32 k = 0u;
    while (k < csz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)k]; i8 lv = vals[l];
      if (lv > (i8)0) { sat = true; break; }
      if (lv < (i8)0) { k = k + 1u; continue; }
      u32 r = full_cong_find(repr, l); i8 rv = vals[r];
      if (rv > (i8)0) { sat = true; break; }
      if (rv < (i8)0) { k = k + 1u; continue; }
      if (lm[r ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[r] == (u8)0) {
        if ((u64)msz < cv) { lm[r] = (u8)1; tmp[msz] = r; msz = msz + 1u; }
        else { ovf = true; break; }
      }
      k = k + 1u;
    }
    if (sat || taut) {
      k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
      ar[cref] = chdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      ci = ci + 1ULL; continue;
    }
    if (ovf) {
      k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
      ci = ci + 1ULL; continue;
    }
    if (msz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (msz == 1u) {
      lm[tmp[0]] = (u8)0;
      ar[cref] = chdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      if (!full_add_unit(h, tmp[0])) { return 20ULL; }
      ci = ci + 1ULL; continue;
    }
    u32 least_r = tmp[0]; u32 least_cnt = occ_cnt[least_r];
    bool subsumed = false;
    k = 0u;
    while (k < msz && !subsumed && ticks < tick_lim) {
      u32 rk = tmp[k]; u32 cnt = occ_cnt[rk];
      if (cnt < least_cnt) { least_cnt = cnt; least_r = rk; }
      u32 nd = occ_head[rk];
      while (nd != 0xFFFFFFFFu && ticks < tick_lim) {
        ticks = ticks + 1ULL;
        u32 dref = scr[nd]; u32 nxt = scr[(u64)nd + 1ULL];
        u32 dhdr = ar[dref]; u32 dsz = ar[(u64)dref + 2ULL];
        bool d_red = (dhdr & PH_RED) != 0u;
        if ((dhdr & PH_GARB) == 0u && dref != cref && (c_red || !d_red)) {
          bool dok = true; u32 dj = 0u;
          while (dj < dsz) {
            u32 ol = ar[(u64)dref + 3ULL + (u64)dj]; i8 ov = vals[ol];
            if (ov > (i8)0) { dok = false; break; }
            if (ov == (i8)0) {
              u32 ro = full_cong_find(repr, ol); i8 rov = vals[ro];
              if (rov > (i8)0) { dok = false; break; }
              if (rov == (i8)0 && lm[ro] == (u8)0) { dok = false; break; }
            }
            dj = dj + 1u;
          }
          if (dok) { subsumed = true; break; }
        }
        nd = nxt;
      }
      k = k + 1u;
    }
    k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
    if (subsumed) {
      ar[cref] = chdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
    } else if (occ_pos + 2ULL <= h->scratch_cap) {
      scr[occ_pos] = cref;
      scr[occ_pos + 1ULL] = occ_head[least_r];
      occ_head[least_r] = (u32)occ_pos;
      occ_cnt[least_r] = occ_cnt[least_r] + 1u;
      occ_pos = occ_pos + 2ULL;
    }
    ci = ci + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

void full_cong_u64_sift_m7(u64 *a, u64 start, u64 n) {
  u64 root = start;
  while (root < n) {
    u64 child = root * 2ULL + 1ULL;
    if (child >= n) {
      break;
    }
    u64 swp = root;
    if (a[swp] < a[child]) {
      swp = child;
    }
    if (child + 1ULL < n && a[swp] < a[child + 1ULL]) {
      swp = child + 1ULL;
    }
    if (swp == root) {
      break;
    }
    u64 tmp = a[root];
    a[root] = a[swp];
    a[swp] = tmp;
    root = swp;
  }
}

void full_cong_u64_sort_m7(u64 *a, u64 n) {
  if (n <= 1ULL) {
    return;
  }
  u64 start = n >> 1ULL;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_cong_u64_sift_m7(a, start, n);
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u64 tmp = a[end];
    a[end] = a[0];
    a[0] = tmp;
    full_cong_u64_sift_m7(a, 0ULL, end);
    end = end - 1ULL;
  }
}

bool full_cong_bsearch_u64_m7(u64 *a, u64 lo, u64 hi, u64 key) {
  u64 l = lo;
  u64 r = hi;
  while (l < r) {
    u64 mid = l + ((r - l) >> 1ULL);
    u64 v = a[mid];
    if (v == key) {
      return true;
    }
    if (v < key) {
      l = mid + 1ULL;
    } else {
      r = mid;
    }
  }
  return false;
}

u64 full_cong_copy_condbin_m7(FullHdr *h, u32 lit, u64 *dst, u64 cap) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *arena = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 alen = h->arena_len;
  u64 widx = (u64)lit << 1ULL;
  u64 off = (u64)wvec[widx];
  u64 wsz = (u64)wvec[widx + 1ULL];
  u64 p = off; u64 end = off + wsz; u64 cnt = 0ULL;
  while (p < end) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      p = p + 1ULL;
    } else {
      if (p + 1ULL >= end) { break; }
      u32 cr = wstk[p + 1ULL]; p = p + 2ULL;
      if ((u64)cr + 2ULL < alen) {
        u32 hdr = arena[cr]; u32 sz = arena[(u64)cr + 2ULL];
        if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u &&
            (u64)cr + 2ULL + (u64)sz < alen) {
          u32 a = 0u; u32 b = 0u; u32 ocnt = 0u;
          bool found_lit = false; bool ok = true; u32 k = 0u;
          while (k < sz) {
            u32 l = arena[(u64)cr + 3ULL + (u64)k];
            i8 lv = vals[l];
            if (lv > (i8)0) { ok = false; break; }
            if (lv == (i8)0) {
              if (l == lit) { found_lit = true; }
              else if (ocnt == 0u) { a = l; ocnt = 1u; }
              else if (ocnt == 1u) { b = l; ocnt = 2u; }
              else { ok = false; break; }
            }
            k = k + 1u;
          }
          if (ok && found_lit && ocnt == 2u && (a >> 1) != (b >> 1) &&
              (a >> 1) != (lit >> 1) && (b >> 1) != (lit >> 1)) {
            if (cnt >= cap) { return 0ULL; }
            u32 mn = (b < a) ? b : a;
            u32 mx = (b < a) ? a : b;
            dst[cnt] = ((u64)mn << 32ULL) | (u64)mx;
            cnt = cnt + 1ULL;
          }
        }
      }
    }
  }
  if (cnt <= 1ULL) { return cnt; }
  full_cong_u64_sort_m7(dst, cnt);
  u64 u = 1ULL; u64 i = 1ULL;
  while (i < cnt) {
    if (dst[i] != dst[u - 1ULL]) { dst[u] = dst[i]; u = u + 1ULL; }
    i = i + 1ULL;
  }
  return u;
}

u64 full_cong_extract_condeq_m7(u64 *cb, u64 m, u64 *ceq, u64 cap) {
  u64 d = 0ULL;
  u64 i = 0ULL;
  while (i < m) {
    u32 a = (u32)(cb[i] >> 32ULL);
    if ((a & 1u) != 0u) {
      u64 j = i + 1ULL;
      while (j < m && (u32)(cb[j] >> 32ULL) == a) {
        j = j + 1ULL;
      }
      i = j;
    } else {
      u64 pos_start = i;
      u64 pos_end = i + 1ULL;
      while (pos_end < m && (u32)(cb[pos_end] >> 32ULL) == a) {
        pos_end = pos_end + 1ULL;
      }
      u32 opp_a = a | 1u;
      u64 neg_start = pos_end;
      u64 neg_end = pos_end;
      while (neg_end < m && (u32)(cb[neg_end] >> 32ULL) == opp_a) {
        neg_end = neg_end + 1ULL;
      }
      u64 npos = pos_end - pos_start;
      u64 nneg = neg_end - neg_start;
      if (nneg > 0ULL) {
        if (npos <= nneg) {
          u64 k = pos_start;
          while (k < pos_end) {
            u32 b = (u32)cb[k];
            u32 not_b = b ^ 1u;
            u64 key = ((u64)opp_a << 32ULL) | (u64)not_b;
            if (full_cong_bsearch_u64_m7(cb, neg_start, neg_end, key)) {
              if (d + 2ULL <= cap) {
                u32 inv_l = ((not_b & 1u) != 0u) ? b : not_b;
                u32 inv_r = ((not_b & 1u) != 0u) ? opp_a : a;
                ceq[d] = ((u64)a << 32ULL) | (u64)not_b;
                ceq[d + 1ULL] = ((u64)inv_l << 32ULL) | (u64)inv_r;
                d = d + 2ULL;
              }
            }
            k = k + 1ULL;
          }
        } else {
          u64 k = neg_start;
          while (k < neg_end) {
            u32 b = (u32)cb[k];
            u32 not_b = b ^ 1u;
            u64 key = ((u64)a << 32ULL) | (u64)not_b;
            if (full_cong_bsearch_u64_m7(cb, pos_start, pos_end, key)) {
              if (d + 2ULL <= cap) {
                u32 inv_l = ((b & 1u) != 0u) ? not_b : b;
                u32 inv_r = ((b & 1u) != 0u) ? opp_a : a;
                ceq[d] = ((u64)a << 32ULL) | (u64)b;
                ceq[d + 1ULL] = ((u64)inv_l << 32ULL) | (u64)inv_r;
                d = d + 2ULL;
              }
            }
            k = k + 1ULL;
          }
        }
      }
      i = neg_end;
    }
  }
  if (d <= 1ULL) {
    return d;
  }
  full_cong_u64_sort_m7(ceq, d);
  u64 u = 1ULL;
  u64 idx = 1ULL;
  while (idx < d) {
    if (ceq[idx] != ceq[u - 1ULL]) {
      ceq[u] = ceq[idx];
      u = u + 1ULL;
    }
    idx = idx + 1ULL;
  }
  return u;
}

u32 full_cong_merge_condeq_m7(FullHdr *h, u32 cond, u64 pos_n, u64 neg_n,
                              u32 g_len, u32 g_cap) {
  if (pos_n == 0ULL || neg_n == 0ULL || g_len > g_cap ||
      (u64)g_cap > h->scratch_cap) {
    return g_len;
  }
  u64 *pos_eq = (u64 *)h->work_stk1;
  u64 *neg_eq = (u64 *)h->work_stk2;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 gl = g_len; u64 p = 0ULL; u64 q = 0ULL;
  while (p < pos_n && q < neg_n && (u64)gl + 5ULL <= (u64)g_cap) {
    u64 pv = pos_eq[p];
    u32 lhs_p = (u32)(pv >> 32ULL);
    u32 lhs_n = (u32)(neg_eq[q] >> 32ULL);
    if (lhs_p < lhs_n) {
      p = p + 1ULL;
    } else if (lhs_n < lhs_p) {
      q = q + 1ULL;
    } else {
      u64 q2 = q;
      while (q2 < neg_n && (u64)gl + 5ULL <= (u64)g_cap) {
        u64 nv = neg_eq[q2];
        if ((u32)(nv >> 32ULL) != lhs_p) { break; }
        u32 y = lhs_p; u32 t = (u32)pv; u32 e = (u32)nv;
        if (e != (t ^ 1u)) {
          u32 yy = y; u32 tt = t; u32 ee = e;
          if ((t & 1u) != 0u) { yy = y ^ 1u; tt = t ^ 1u; ee = e ^ 1u; }
          scr[gl] = yy;
          scr[(u64)gl + 1ULL] = (2u << 28u) | 3u;
          scr[(u64)gl + 2ULL] = cond;
          scr[(u64)gl + 3ULL] = tt;
          scr[(u64)gl + 4ULL] = ee;
          gl = gl + 5u;
        }
        q2 = q2 + 1ULL;
      }
      p = p + 1ULL;
    }
  }
  return gl;
}

u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap, u64 tick_lim) {
  u64 cv = h->cur_vars; u64 mv = h->max_vars;
  if (g_len > g_cap || (u64)g_cap > h->scratch_cap ||
      cv < 3ULL || cv > mv || tick_lim == 0ULL) {
    return g_len;
  }
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec; u64 *wsort = (u64 *)h->wsort;
  u64 *wk1 = (u64 *)h->work_stk1; u64 *wk2 = (u64 *)h->work_stk2;
  u64 v = 0ULL; u64 ticks = 0ULL; u32 gl = g_len;
  while (v < cv && ticks < tick_lim && (u64)gl + 5ULL <= (u64)g_cap) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1ULL] == (i8)0) {
      u32 lit0 = (u32)(v << 1ULL); u32 lit1 = lit0 | 1u;
      u32 sz0 = wvec[((u64)lit0 << 1ULL) + 1ULL];
      u32 sz1 = wvec[((u64)lit1 << 1ULL) + 1ULL];
      if (sz0 <= 1u || sz1 <= 1u) {
        ticks = ticks + 1ULL;
      } else {
        ticks = ticks + 1ULL + (u64)sz0 + (u64)sz1;
        u32 small_lit = lit0; u32 large_lit = lit1;
        u64 *dst0 = wk2; u64 *dst1 = wk1; bool flipped = false;
        if (sz1 < sz0) {
          small_lit = lit1; large_lit = lit0;
          dst0 = wk1; dst1 = wk2; flipped = true;
        }
        u64 m0 = full_cong_copy_condbin_m7(h, small_lit, wsort, mv);
        if (m0 > 1ULL) {
          u64 n0 = full_cong_extract_condeq_m7(wsort, m0, dst0, mv);
          if (n0 > 0ULL) {
            u64 m1 = full_cong_copy_condbin_m7(h, large_lit, wsort, mv);
            if (m1 > 1ULL) {
              u64 n1 = full_cong_extract_condeq_m7(wsort, m1, dst1, mv);
              if (n1 > 0ULL) {
                if (flipped) {
                  gl = full_cong_merge_condeq_m7(h, lit0, n0, n1, gl, g_cap);
                } else {
                  gl = full_cong_merge_condeq_m7(h, lit0, n1, n0, gl, g_cap);
                }
              }
            }
          }
        }
      }
    }
    v = v + 1ULL;
  }
  return gl;
}

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  h->ant_sz = 0ULL;
  if (full_cong_extract_binaries(h, tick_lim) == 20ULL) { h->ant_sz = 0ULL; return 20ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  if (full_cong_find_units_equivs(h) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  u64 g_cap = h->scratch_cap >> 1;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = (u64)full_cong_extract_ite_all_m7(h, 0u, (u32)(g_cap >> 1), tick_lim);
  if (g_len <= g_cap) {
    g_len = full_cong_extract_from_fid(h, g_len, g_cap, tick_lim);
  }
  if (g_len > 0ULL && g_len <= g_cap) {
    u64 free_scr = h->scratch_cap - g_len;
    u64 ht_max = 64ULL;
    while (ht_max * 4ULL <= free_scr && ht_max < 1048576ULL) { ht_max = ht_max << 1; }
    u64 ht_off = h->scratch_cap - ht_max;
    u64 rem_occ = ht_off - g_len;
    u64 occ_bkt = 16ULL;
    while ((occ_bkt << 1) <= 1048576ULL && (occ_bkt << 1) < nlits &&
           (occ_bkt << 1) * 16ULL <= rem_occ) {
      occ_bkt = occ_bkt << 1;
    }
    u64 bkt_off = ht_off - occ_bkt;
    u64 inq_off = bkt_off - occ_bkt;
    u64 q_off = inq_off - occ_bkt;
    u64 ctrl_off = q_off - 8ULL;
    u64 ht_sz = 64ULL;
    while (ht_sz < g_len && (ht_sz << 1) <= ht_max) { ht_sz = ht_sz << 1; }
    i = 0ULL;
    while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    h->res_sz = 0ULL;
    scr[ctrl_off] = (u32)occ_bkt; scr[ctrl_off + 1ULL] = (u32)bkt_off;
    scr[ctrl_off + 2ULL] = (u32)inq_off; scr[ctrl_off + 3ULL] = (u32)q_off;
    scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
    scr[ctrl_off + 6ULL] = (u32)ht_off; scr[ctrl_off + 7ULL] = (u32)ht_sz;
    if (full_cong_worklist(h, g_len, ctrl_off, tick_lim) == 20ULL) {
      i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
      h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
    }
  }
  if (full_cong_fwd_subsume(h, tick_lim) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL; h->ant_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Congruence

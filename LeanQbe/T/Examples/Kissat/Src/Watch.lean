/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Watch Lists, Compact Vectors & Binary/Ternary Lookup (`Src/Watch.lean`)

Mirrors upstream `kissat/src/watch.c, vector.c` (`15` live functions, DAG level `L0`):
- `full_wsort_sift` (R4: `kissat_vector_sift`)
- `full_wstack_radix_sort_m6` (R4: `kissat_vector_radix_sort`)
- `full_wstack_defrag_m6` (R4: `kissat_defrag_vectors_impl`)
- `full_watch_push_slow_m6` (R4: `kissat_push_watch_slow`)
- `full_watch_push_m6` (R4: `kissat_push_watch_impl`)
- `full_wstack_defrag` (R4: `kissat_defrag_vectors`)
- `full_watch_push` (R4: `kissat_push_watch`)
- `full_watch_pop_c0` (R4: `kissat_pop_watch`)
- `full_unwatch_large` (R4: `kissat_unwatch_large`)
- `full_has_bin` (R4: `kissat_has_binary`)
- `full_delete_bin_side` (R4: `kissat_remove_binary_watch`)
- `full_delete_binary` (R4: `kissat_delete_binary`)
- `full_prioritize_binaries_m6` (R4: `kissat_prioritize_binaries`)
- `full_sort_bin_watches_fid` (R4: `kissat_sort_binary_watches`)
- `full_has_ternary` (R4: `kissat_has_ternary`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Watch

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! watch "
#include \"kissat_internal.h\"

void full_wsort_sift(u32 *wvec, u32 *ws, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 cl = ws[ch];
    u32 co = wvec[(u64)cl << 1];
    if (ch + 1ULL < n) {
      u32 sl = ws[ch + 1ULL];
      u32 so = wvec[(u64)sl << 1];
      if (so > co) { ch = ch + 1ULL; co = so; }
    }
    u32 rl = ws[root];
    if (wvec[(u64)rl << 1] >= co) { break; }
    ws[root] = ws[ch];
    ws[ch] = rl;
    root = ch;
  }
}

void full_wstack_radix_sort_m6(u32 *wvec, u32 *ws, u32 *tmp, u32 *cnt,
                               u64 n, u64 max_off) {
  u64 shift = 0ULL;
  while (shift < 32ULL && (max_off >> shift) != 0ULL) {
    u64 b = 0ULL;
    while (b < 256ULL) { cnt[b] = 0u; b = b + 1ULL; }
    u64 j = 0ULL;
    while (j < n) {
      u32 lit = ws[j];
      u64 bkt = ((u64)wvec[(u64)lit << 1] >> shift) & 255ULL;
      cnt[bkt] = cnt[bkt] + 1u;
      j = j + 1ULL;
    }
    u64 sum = 0ULL;
    b = 0ULL;
    while (b < 256ULL) {
      u64 c = (u64)cnt[b];
      cnt[b] = (u32)sum;
      sum = sum + c;
      b = b + 1ULL;
    }
    j = 0ULL;
    while (j < n) {
      u32 lit = ws[j];
      u64 bkt = ((u64)wvec[(u64)lit << 1] >> shift) & 255ULL;
      u64 pos = (u64)cnt[bkt];
      cnt[bkt] = (u32)(pos + 1ULL);
      tmp[pos] = lit;
      j = j + 1ULL;
    }
    j = 0ULL;
    while (j < n) { ws[j] = tmp[j]; j = j + 1ULL; }
    shift = shift + 8ULL;
  }
}

void full_wstack_defrag_m6(FullHdr *h) {
  if (h->wlen <= 1ULL) { h->wusable = 0ULL; return; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u64 n = 0ULL;
  u64 l = 0ULL;
  u64 max_off = 0ULL;
  u64 prev_off = 0ULL;
  bool sorted = true;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    if (wvec[(l << 1) + 1ULL] == 0u) {
      wvec[l << 1] = 0u;
    } else {
      if (off < prev_off) { sorted = false; }
      prev_off = off;
      if (off > max_off) { max_off = off; }
      ws[n] = (u32)l;
      n = n + 1ULL;
    }
    l = l + 1ULL;
  }
  if (n == 0ULL) { wstk[0] = 0u; h->wlen = 1ULL; h->wusable = 0ULL; return; }
  if (!sorted && n > 1ULL) {
    if ((n << 1) + 256ULL <= (h->max_vars << 1)) {
      full_wstack_radix_sort_m6(wvec, ws, ws + n, ws + (n << 1), n, max_off);
    } else if (h->wcap - h->wlen >= n + 256ULL) {
      full_wstack_radix_sort_m6(wvec, ws, wstk + h->wlen, wstk + h->wlen + n,
                                n, max_off);
    } else {
      u64 start = n >> 1;
      while (start > 0ULL) {
        start = start - 1ULL; full_wsort_sift(wvec, ws, start, n);
      }
      u64 end = n - 1ULL;
      while (end > 0ULL) {
        u32 tmp = ws[0]; ws[0] = ws[end]; ws[end] = tmp;
        full_wsort_sift(wvec, ws, 0ULL, end);
        end = end - 1ULL;
      }
    }
  }
  u64 p = 1ULL;
  u64 i = 0ULL;
  while (i < n) {
    u32 lit = ws[i];
    u64 off = (u64)wvec[(u64)lit << 1];
    u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    if (off != p) {
      u64 k = 0ULL;
      while (k < sz) { wstk[p + k] = wstk[off + k]; k = k + 1ULL; }
      wvec[(u64)lit << 1] = (u32)p;
    }
    p = p + sz;
    i = i + 1ULL;
  }
  h->wlen = p;
  h->wusable = 0ULL;
}

bool full_watch_push_slow_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  bool retry_fast = false;
  if (h->wlen == 0ULL) {
    if (h->wcap < 1ULL) { return false; }
    u32 *wstk0 = (u32 *)h->watch_stk;
    wstk0[0] = 0u;
    h->wlen = 1ULL;
    retry_fast = true;
  }
  if (h->wlen * 4ULL >= h->wcap * 3ULL && h->wusable * 4ULL >= h->wlen * 3ULL) {
    full_wstack_defrag_m6(h);
    retry_fast = true;
  }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (sz == 0ULL && off == 0ULL) {
    if (c > wcap - h->wlen && h->wusable > 0ULL) { full_wstack_defrag_m6(h); }
    if (c > wcap - h->wlen) { return false; }
    u64 pos = h->wlen;
    wstk[pos] = w0;
    if (cnt == 2u) { wstk[pos + 1ULL] = w1; }
    wvec[(u64)lit << 1] = (u32)pos;
    wvec[((u64)lit << 1) + 1ULL] = cnt;
    h->wlen = pos + c;
    return true;
  }
  if (retry_fast) {
    u64 end = off + sz;
    if (end == h->wlen && c <= wcap - h->wlen) {
      wstk[end] = w0;
      if (cnt == 2u) { wstk[end + 1ULL] = w1; }
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
      h->wlen = end + c;
      return true;
    }
    if (end + c <= h->wlen && wstk[end] == 0xFFFFFFFFu &&
        (cnt == 1u || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
      wstk[end] = w0;
      if (cnt == 2u) { wstk[end + 1ULL] = w1; }
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
      if (h->wusable >= c) { h->wusable = h->wusable - c; }
      return true;
    }
  }
  u64 ncap = (sz == 0ULL) ? 2ULL : (sz << 1);
  if (ncap < sz + c) { ncap = sz + c; }
  if (ncap > wcap - h->wlen) {
    if (h->wusable > 0ULL) {
      full_wstack_defrag_m6(h);
      off = (u64)wvec[(u64)lit << 1];
      sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    }
    if (ncap > wcap - h->wlen) { ncap = sz + c; }
    if (ncap > wcap - h->wlen) { return false; }
  }
  u64 dst = h->wlen;
  u64 k = 0ULL;
  while (k < sz) {
    wstk[dst + k] = wstk[off + k];
    wstk[off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wstk[dst + sz] = w0;
  if (cnt == 2u) { wstk[dst + sz + 1ULL] = w1; }
  k = sz + c;
  while (k < ncap) { wstk[dst + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[(u64)lit << 1] = (u32)dst;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
  h->wusable = h->wusable + sz + (ncap - (sz + c));
  h->wlen = dst + ncap;
  return true;
}

bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  u64 c = (u64)cnt;
  u64 wlen = h->wlen;
  if (wlen != 0ULL && (wlen * 4ULL < h->wcap * 3ULL || h->wusable * 4ULL < wlen * 3ULL)) {
    u64 l2 = (u64)lit << 1;
    u32 *wvec0 = (u32 *)h->watch_vec;
    u64 off = (u64)wvec0[l2];
    u64 sz = (u64)wvec0[l2 + 1ULL];
    u64 end = off + sz;
    if (end > 0ULL) {
      u32 *wstk = (u32 *)h->watch_stk;
      if (end + c <= wlen && wstk[end] == 0xFFFFFFFFu &&
          (c == 1ULL || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        u32 *wvec = (u32 *)h->watch_vec;
        wvec[l2 + 1ULL] = wvec[l2 + 1ULL] + (u32)c;
        if (h->wusable >= c) { h->wusable = h->wusable - c; }
        return true;
      }
      if (end == wlen && c <= h->wcap - wlen) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        u32 *wvec = (u32 *)h->watch_vec;
        wvec[l2 + 1ULL] = wvec[l2 + 1ULL] + (u32)c;
        h->wlen = end + c;
        return true;
      }
    } else if (c <= h->wcap - wlen) {
      u32 *wstk = (u32 *)h->watch_stk;
      wstk[wlen] = w0;
      if (c == 2ULL) { wstk[wlen + 1ULL] = w1; }
      u32 *wvec = (u32 *)h->watch_vec;
      wvec[l2] = (u32)wlen;
      wvec[l2 + 1ULL] = (u32)c;
      h->wlen = wlen + c;
      return true;
    }
  }
  return full_watch_push_slow_m6(h, lit, w0, w1, (u32)c);
}

void full_wstack_defrag(FullHdr *h) {
  full_wstack_defrag_m6(h);
}

bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  return full_watch_push_m6(h, lit, w0, w1, cnt);
}

void full_watch_pop_c0(FullHdr *h, u32 lit, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1)) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (c == 0ULL || sz < c || off + sz > h->wlen) { return; }
  u64 k = sz - c;
  while (k < sz) { wstk[off + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - c);
  h->wusable = h->wusable + c;
}

void full_unwatch_large(FullHdr *h, u32 lit, u32 cref) {
  if ((u64)lit >= (h->cur_vars << 1) || (cref & PW_BIN_FLAG) != 0u) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz < 2ULL) { return; }
  u64 end = off + sz;
  u64 off2 = off + 2ULL;
  u64 p = end;
  while (p >= off2) {
    u32 w = wstk[p - 1ULL];
    if (w == cref) {
      u64 q = p - 2ULL;
      if ((p & 1ULL) != 0ULL && p < end) {
        wstk[q] = wstk[p];
        q = q + 1ULL;
        p = p + 1ULL;
      }
      while (p + 4ULL <= end) {
        u64 *sp4 = (u64 *)(wstk + p);
        u64 *dp4 = (u64 *)(wstk + q);
        u64 v0 = sp4[0];
        u64 v1 = sp4[1];
        dp4[0] = v0;
        dp4[1] = v1;
        q = q + 4ULL;
        p = p + 4ULL;
      }
      if (p + 2ULL <= end) {
        u64 *sp2 = (u64 *)(wstk + p);
        u64 *dp2 = (u64 *)(wstk + q);
        dp2[0] = sp2[0];
        q = q + 2ULL;
        p = p + 2ULL;
      }
      if (p < end) {
        wstk[q] = wstk[p];
      }
      wstk[end - 2ULL] = 0xFFFFFFFFu;
      wstk[end - 1ULL] = 0xFFFFFFFFu;
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - 2ULL);
      h->wusable = h->wusable + 2ULL;
      return;
    }
    p = p - 2ULL + (u64)(w >> 31);
  }
}

bool full_has_bin(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == b || a == (b ^ 1u)) { return false; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 sa = (u64)wvec[((u64)a << 1) + 1ULL];
  u64 sb = (u64)wvec[((u64)b << 1) + 1ULL];
  u32 src = (sa <= sb) ? a : b;
  u32 tgt = (sa <= sb) ? b : a;
  u64 off = (u64)wvec[(u64)src << 1];
  u64 end = off + (u64)wvec[((u64)src << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if ((w0 & PW_LIT_MASK) == tgt) { return true; }
      p = p + 1ULL;
    } else { p = p + 2ULL; }
  }
  return false;
}

void full_delete_bin_side(FullHdr *h, u32 lit, u32 other) {
  if ((u64)lit >= (h->cur_vars << 1)) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz == 0ULL) { return; }
  u64 p = off;
  u64 end = off + sz;
  bool removed = false;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if ((w0 & PW_LIT_MASK) == other) { removed = true; break; }
    } else if (p < end) {
      p = p + 1ULL;
    }
  }
  if (!removed) { return; }
  while (p < end) {
    wstk[p - 1ULL] = wstk[p];
    p = p + 1ULL;
  }
  wstk[end - 1ULL] = 0xFFFFFFFFu;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - 1ULL);
  h->wusable = h->wusable + 1ULL;
}

void full_delete_binary(FullHdr *h, u32 a, u32 b) {
  full_delete_bin_side(h, a, b);
  full_delete_bin_side(h, b, a);
  if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
}

bool full_prioritize_binaries_m6(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 scap = h->scratch_cap;
  bool all_prio = true;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 1ULL) {
      if (sz > scap) {
        all_prio = false;
      } else {
        u64 end = off + sz;
        u64 p = off;
        u64 q = off;
        u64 ln = 0ULL;
        while (p < end) {
          u32 w0 = wstk[p]; p = p + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) {
            wstk[q] = w0; q = q + 1ULL;
          } else if (p < end) {
            u32 cr = wstk[p]; p = p + 1ULL;
            scr[ln] = w0; scr[ln + 1ULL] = cr; ln = ln + 2ULL;
          }
        }
        u64 k = 0ULL;
        while (k < ln) { wstk[q + k] = scr[k]; k = k + 1ULL; }
      }
    }
    l = l + 1ULL;
  }
  return all_prio;
}

void full_sort_bin_watches_fid(FullHdr *h) {
  u64 nl = h->cur_vars << 1;
  u32 *wv = (u32 *)h->watch_vec;
  u32 *ws = (u32 *)h->watch_stk;
  u64 l = 0ULL;
  while (l < nl) {
    u64 off = (u64)wv[l << 1];
    u64 sz = (u64)wv[(l << 1) + 1ULL];
    u64 bn = 0ULL;
    while (bn < sz && (ws[off + bn] & 0x80000000u) != 0u) {
      bn = bn + 1ULL;
    }
    if (bn > 1ULL) {
      u64 gap = 1ULL;
      u64 lim = bn / 3ULL;
      while (gap < lim) {
        gap = 3ULL * gap + 1ULL;
      }
      while (gap > 0ULL) {
        u64 i = gap;
        while (i < bn) {
          u32 x = ws[off + i];
          u32 xo = x & 0x7FFFFFFFu;
          u64 j = i;
          while (j >= gap && (ws[off + j - gap] & 0x7FFFFFFFu) > xo) {
            ws[off + j] = ws[off + j - gap];
            j = j - gap;
          }
          ws[off + j] = x;
          i = i + 1ULL;
        }
        gap = gap / 3ULL;
      }
    }
    l = l + 1ULL;
  }
}

bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c) {
  i8 *vals = (i8 *)h->values;
  if (vals[a] != (i8)0) { return false; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 scan = a;
  u32 min_sz = wvec[((u64)a << 1) + 1ULL];
  if ((u64)b < nlits) {
    if (vals[b] != (i8)0) { return false; }
    u32 b_sz = wvec[((u64)b << 1) + 1ULL];
    if (b_sz < min_sz) { scan = b; min_sz = b_sz; }
  }
  if ((u64)c < nlits) {
    if (vals[c] != (i8)0) { return false; }
    u32 c_sz = wvec[((u64)c << 1) + 1ULL];
    if (c_sz < min_sz) { scan = c; min_sz = c_sz; }
  }
  if (min_sz == 0u) { return false; }
  bool distinct = (a != b) && (a != c) && (b != c);
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)scan << 1];
  u64 end = off + (u64)min_sz;
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { continue; }
    u32 nf = 0u;
    u32 mask = 0u;
    u64 ci = (u64)cr + 3ULL;
    u64 cend = ci + (u64)sz;
    while (ci < cend) {
      u32 l = ar[ci]; ci = ci + 1ULL;
      i8 lv = vals[l];
      if (lv > (i8)0) { mask = 8u; break; }
      if (lv == (i8)0) {
        nf = nf + 1u;
        if (nf > 3u) { mask = 8u; break; }
        u32 hit = 0u;
        if (l == a) { hit = 1u; }
        if (l == b) { hit = hit | 2u; }
        if (l == c) { hit = hit | 4u; }
        if (hit == 0u && distinct) { mask = 8u; break; }
        mask = mask | hit;
      }
    }
    if (nf == 3u && mask == 7u) { return true; }
  }
  return false;
}
"

/-- Ordered live functions of `Src/Watch.lean` (`15` fns). -/
def fns : List Fn := watch_fns

end

public section

theorem full_wsort_sift_wf : Func.Wf full_wsort_sift_body := by kissat_wf_reify
theorem full_wstack_radix_sort_m6_wf : Func.Wf full_wstack_radix_sort_m6_body := by kissat_wf_reify
theorem full_wstack_defrag_m6_wf : Func.Wf full_wstack_defrag_m6_body := by kissat_wf_reify
theorem full_watch_push_slow_m6_wf : Func.Wf full_watch_push_slow_m6_body := by kissat_wf_reify
theorem full_watch_push_m6_wf : Func.Wf full_watch_push_m6_body := by kissat_wf_reify
theorem full_wstack_defrag_wf : Func.Wf full_wstack_defrag_body := by kissat_wf_reify
theorem full_watch_push_wf : Func.Wf full_watch_push_body := by kissat_wf_reify
theorem full_watch_pop_c0_wf : Func.Wf full_watch_pop_c0_body := by kissat_wf_reify
theorem full_unwatch_large_wf : Func.Wf full_unwatch_large_body := by kissat_wf_reify
theorem full_has_bin_wf : Func.Wf full_has_bin_body := by kissat_wf_reify
theorem full_delete_bin_side_wf : Func.Wf full_delete_bin_side_body := by kissat_wf_reify
theorem full_delete_binary_wf : Func.Wf full_delete_binary_body := by kissat_wf_reify
theorem full_prioritize_binaries_m6_wf : Func.Wf full_prioritize_binaries_m6_body := by
  kissat_wf_reify
theorem full_sort_bin_watches_fid_wf : Func.Wf full_sort_bin_watches_fid_body := by kissat_wf_reify
theorem full_has_ternary_wf : Func.Wf full_has_ternary_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, watch_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact full_wsort_sift_wf
  · exact full_wstack_radix_sort_m6_wf
  · exact full_wstack_defrag_m6_wf
  · exact full_watch_push_slow_m6_wf
  · exact full_watch_push_m6_wf
  · exact full_wstack_defrag_wf
  · exact full_watch_push_wf
  · exact full_watch_pop_c0_wf
  · exact full_unwatch_large_wf
  · exact full_has_bin_wf
  · exact full_delete_bin_side_wf
  · exact full_delete_binary_wf
  · exact full_prioritize_binaries_m6_wf
  · exact full_sort_bin_watches_fid_wf
  · exact full_has_ternary_wf

end

end LeanQbe.T.Examples.Kissat.Src.Watch

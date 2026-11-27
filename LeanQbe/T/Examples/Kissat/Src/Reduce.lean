/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Learned Clause Database Reduction & OOM Purge (`Src/Reduce.lean`)

Mirrors upstream `kissat/src/reduce.c` (`5` live functions, DAG level `L3`):
- `full_red_less` (R4: `kissat_reducible_less`)
- `full_red_sift` (R4: `kissat_reducible_sift`)
- `full_sort_reds` (R4: `kissat_sort_reducibles`)
- `full_reduce_m6` (R4: `kissat_reduce`)
- `full_reduce_purge_c0` (R4: `kissat_reduce_purge`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Reduce

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! reduce "
#include \"kissat_internal.h\"

extern u64 full_isqrt(u64 x);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern bool full_compact_needed(FullHdr *h);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 f64u_log10_u64(u64 x);
extern u64 f64u_sub(u64 a, u64 b);
extern u64 f64u_div(u64 a, u64 b);
extern u64 f64u_to_u64(u64 a);
extern u64 f64u_mul(u64 a, u64 b);
extern u64 f64u_from_u64(u64 x);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_compact(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern void full_update_classify_fid(FullHdr *h);

bool full_red_less(u32 *ar, u32 a, u32 b) {
  u32 ga = ar[a] & PH_GLUE_MASK;
  u32 gb = ar[b] & PH_GLUE_MASK;
  if (ga != gb) { return ga > gb; }
  return ar[a + 2u] > ar[b + 2u];
}

void full_red_sift(u32 *ar, u32 *rr, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    if (ch + 1ULL < n && !full_red_less(ar, rr[ch + 1ULL], rr[ch])) { ch = ch + 1ULL; }
    if (!full_red_less(ar, rr[root], rr[ch])) { break; }
    u32 t = rr[root]; rr[root] = rr[ch]; rr[ch] = t;
    root = ch;
  }
}

void full_sort_reds(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  if (n < 32ULL) {
    u64 i = 1ULL;
    while (i < n) {
      u32 x = rr[i];
      u64 kx = ((u64)(~(ar[x] & PH_GLUE_MASK)) << 32) | (u64)(~ar[(u64)x + 2ULL]);
      u64 j = i;
      while (j > 0ULL) {
        u32 y = rr[j - 1ULL];
        u64 ky = ((u64)(~(ar[y] & PH_GLUE_MASK)) << 32) | (u64)(~ar[(u64)y + 2ULL]);
        if (ky <= kx) { break; }
        rr[j] = y;
        j = j - 1ULL;
      }
      rr[j] = x;
      i = i + 1ULL;
    }
    return;
  }
  if (4ULL * n + 512ULL <= h->scratch_cap) {
    u64 *ranks = (u64 *)h->scratch_buf;
    u32 *idx0 = ((u32 *)h->scratch_buf) + (2ULL * n);
    u32 *idx1 = idx0 + n;
    u64 *cnt = ((u64 *)h->scratch_buf) + (2ULL * n);
    u64 i = 0ULL;
    while (i < n) {
      u32 r = rr[i];
      u32 g = ar[r] & PH_GLUE_MASK;
      u32 sz = ar[(u64)r + 2ULL];
      ranks[i] = ((u64)(0xFFFFFFFFu - g) << 32) | (u64)(0xFFFFFFFFu - sz);
      idx0[i] = (u32)i;
      i = i + 1ULL;
    }
    u32 *src = idx0;
    u32 *dst = idx1;
    u64 shift = 0ULL;
    while (shift < 64ULL) {
      u64 b = 0ULL;
      while (b < 256ULL) { cnt[b] = 0ULL; b = b + 1ULL; }
      u64 lo = 255ULL;
      u64 hi = 0ULL;
      i = 0ULL;
      while (i < n) {
        u64 byte = (ranks[src[i]] >> shift) & 255ULL;
        cnt[byte] = cnt[byte] + 1ULL;
        if (byte < lo) { lo = byte; }
        if (byte > hi) { hi = byte; }
        i = i + 1ULL;
      }
      if (lo != hi) {
        u64 pos = 0ULL;
        b = 0ULL;
        while (b < 256ULL) {
          u64 c = cnt[b];
          cnt[b] = pos;
          pos = pos + c;
          b = b + 1ULL;
        }
        i = 0ULL;
        while (i < n) {
          u32 id = src[i];
          u64 byte = (ranks[id] >> shift) & 255ULL;
          dst[cnt[byte]] = id;
          cnt[byte] = cnt[byte] + 1ULL;
          i = i + 1ULL;
        }
        u32 *t = src; src = dst; dst = t;
      }
      shift = shift + 8ULL;
    }
    u32 *tmp_rr = (src == idx0) ? idx1 : idx0;
    i = 0ULL;
    while (i < n) { tmp_rr[i] = rr[src[i]]; i = i + 1ULL; }
    i = 0ULL;
    while (i < n) { rr[i] = tmp_rr[i]; i = i + 1ULL; }
    return;
  }
  u64 start = n >> 1;
  while (start > 0ULL) { start = start - 1ULL; full_red_sift(ar, rr, start, n); }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = rr[0]; rr[0] = rr[end]; rr[end] = t;
    full_red_sift(ar, rr, 0ULL, end);
    end = end - 1ULL;
  }
}

u64 full_reduce_m6(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + full_isqrt(h->reductions * 1000000ULL);
  u64 ret = 1ULL;
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { ret = 20ULL; }
    else if (pr != 0ULL) { ret = 0ULL; }
    else { h->unflushed = 0ULL; }
  }
  bool do_compact = false;
  if (ret == 1ULL) {
    do_compact = (!force && h->cur_level == 0ULL && full_compact_needed(h));
    m6_hdr_recompute_tiers(h);
    full_mark_reasons(h, true);
    u32 *ar = (u32 *)h->arena;
    u32 *rr = (u32 *)h->red_refs;
    u64 rc = 0ULL;
    u64 alen = h->arena_len;
    u64 p = 0ULL;
    u64 t1 = h->tier1;
    u64 t2 = h->tier2;
    while (p < alen) {
      u32 hdr = ar[p];
      u32 n = full_arena_next(h, (u32)p);
      if ((hdr & PH_RED) != 0u && (hdr & PH_GARB) == 0u) {
        u32 old_u = (hdr >> 27) & 31u;
        if (old_u > 0u) { ar[p] = (hdr & 0x07FFFFFFu) | ((old_u - 1u) << 27); }
        if ((hdr & PH_RSN) == 0u) {
          u64 glue = (u64)(hdr & PH_GLUE_MASK);
          bool keep = (glue <= t1 && old_u > 0u) || (glue <= t2 && old_u >= 30u);
          if (!keep && rc < h->red_cap) { rr[rc] = (u32)p; rc = rc + 1ULL; }
        }
      }
      p = (u64)n;
    }
    if (rc > 0ULL) {
      full_sort_reds(h, rc);
      u64 arg = (h->reductions > (~0ULL) - 9ULL) ? (~0ULL) : (h->reductions + 9ULL);
      u64 lg = f64u_log10_u64(arg);
      if (lg < 0x3FF0000000000000ULL) { lg = 0x3FF0000000000000ULL; }
      u64 pct = f64u_sub(0x4056800000000000ULL, f64u_div(0x4044000000000000ULL, lg));
      u64 frac = f64u_div(pct, 0x4059000000000000ULL);
      u64 target = f64u_to_u64(f64u_mul(f64u_from_u64(rc), frac));
      u64 i = 0ULL;
      while (i < target && i < rc) {
        u64 cref = (u64)rr[i];
        u32 hdr = ar[cref];
        if ((hdr & PH_GARB) == 0u) {
          ar[cref] = hdr | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[cref + 2ULL];
        }
        i = i + 1ULL;
      }
    }
    if (force || do_compact ||
        (h->unflushed == 0ULL && (h->arena_garbage > 0ULL || h->cur_level == 0ULL))) {
      while (true) {
        u64 sr = full_arena_sweep(h);
        if (sr == 2ULL) { ret = 20ULL; break; }
        if (sr == 3ULL) { ret = 0ULL; break; }
        if (sr == 0ULL) { break; }
        u64 pr = full_propagate(h);
        if (pr == 1ULL) { ret = 20ULL; break; }
        if (pr != 0ULL) { ret = 0ULL; break; }
        h->unflushed = 0ULL;
      }
    } else {
      full_mark_reasons(h, false);
    }
    if (ret == 1ULL && do_compact) {
      u64 cr = full_compact(h);
      if (cr == 20ULL) { ret = 20ULL; }
      else if (cr != 1ULL) { ret = 0ULL; }
    }
  }
  m6_hdr_set_watermark(h, M6_WM_REDUCE_CONFL, h->conflicts);
  m6_hdr_set_watermark(h, M6_WM_REDUCE_TICKS, h->search_ticks);
  full_update_classify_fid(h);
  return ret;
}

u64 full_reduce_purge_c0(FullHdr *h) {
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  full_mark_reasons(h, true);
  u32 *ar = (u32 *)h->arena;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 n = full_arena_next(h, (u32)p);
    if (p + 3ULL <= h->arena_len && (hdr & PH_RED) != 0u &&
        (hdr & (PH_GARB | PH_RSN)) == 0u) {
      ar[p] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[p + 2ULL];
    }
    if ((u64)n <= p) { break; }
    p = (u64)n;
  }
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (sr == 0ULL) { break; }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  return 1ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Reduce

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Variable Queue & Score Reordering (`Src/Reorder.lean`)

Mirrors upstream `kissat/src/reorder.c` (`3` live functions, DAG level `L2`):
- `full_reorder_sift_fid` (R4: `kissat_reorder_sift`)
- `full_reorder_queue_m7` (R4: `kissat_reorder_impl`)
- `full_reorder_m6` (R4: `kissat_reorder`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Reorder

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! reorder "
#include \"kissat_internal.h\"

extern u64 f64u_add(u64 a, u64 b);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 f64u_mul(u64 a, u64 b);
extern void full_rescale(FullHdr *h);
extern void full_heap_up(FullHdr *h, u32 v);

void full_reorder_sift_fid(FullHdr *h, u64 start, u64 n) {
  if (n == 0ULL || start >= n || n > h->cur_vars) { return; }
  u32 *ws = (u32 *)h->wsort;
  u64 *wl = (u64 *)h->tarjan_mark;
  u32 *qs = (u32 *)h->q_stamp;
  u64 root = start;
  while (true) {
    u64 child = (root << 1) + 1ULL;
    if (child >= n) { break; }
    u64 best = root;
    u32 bv = ws[best];
    u64 bw = wl[bv];
    u32 bs = qs[bv];
    u32 cv = ws[child];
    u64 cw = wl[cv];
    u32 cs = qs[cv];
    if (cw > bw || (cw == bw && cs > bs)) { best = child; bv = cv; bw = cw; bs = cs; }
    u64 rch = child + 1ULL;
    if (rch < n) {
      u32 rv = ws[rch];
      u64 rw = wl[rv];
      u32 rs = qs[rv];
      if (rw > bw || (rw == bw && rs > bs)) { best = rch; bv = rv; }
    }
    if (best == root) { break; }
    u32 tmp = ws[root];
    ws[root] = bv;
    ws[best] = tmp;
    root = best;
  }
}

u64 full_reorder_queue_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  u64 alen = h->arena_len;
  u64 wlen = h->wlen;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u64 *wl = (u64 *)h->tarjan_mark;
  u64 *wr = (u64 *)h->tarjan_reach;
  u64 w2 = 0x3FF0000000000000ULL;
  u64 z = 0ULL;
  while (z < cv) {
    wl[z] = 0ULL;
    wr[z] = 0ULL;
    z = z + 1ULL;
  }
  u64 p = 0ULL;
  while (p < alen) {
    if (p + 3ULL > alen) { break; }
    u32 hdr = ar[p];
    u32 csz = ar[p + 2ULL];
    u64 clen = (u64)csz;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && clen <= alen - (p + 3ULL)) {
      bool sat = false;
      u64 sz = 0ULL;
      u64 ci = 0ULL;
      while (ci < clen) {
        u32 lit = ar[p + 3ULL + ci];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) { sz = sz + 1ULL; }
        }
        ci = ci + 1ULL;
      }
      if (!sat && sz >= 2ULL) {
        if (sz > 100ULL) { sz = 100ULL; }
        u64 w = (1025ULL - sz) << 52;
        ci = 0ULL;
        while (ci < clen) {
          u32 lit = ar[p + 3ULL + ci];
          if ((u64)lit < nlits) {
            u32 av = lit >> 1;
            if ((lit & 1u) == 0u) { wl[av] = f64u_add(wl[av], w); }
            else { wr[av] = f64u_add(wr[av], w); }
          }
          ci = ci + 1ULL;
        }
      }
    }
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (np <= p) { break; }
    p = np;
  }
  u64 lit = 0ULL;
  while (lit < nlits) {
    u64 lvar = lit >> 1;
    if ((fl[lvar] & FL_ACTIVE) != 0u && vals[lit] == (i8)0) {
      u64 off = (u64)wvec[lit << 1];
      u64 wsz = (u64)wvec[(lit << 1) + 1ULL];
      if (wsz > 0ULL && off < wlen && wsz <= wlen - off) {
        u64 wp = off;
        u64 wend = off + wsz;
        while (wp < wend) {
          u32 w0 = wstk[wp];
          if ((w0 & PW_BIN_FLAG) == 0u) {
            if (wp + 1ULL < wend) { wp = wp + 2ULL; continue; }
            break;
          }
          u32 other = w0 & PW_LIT_MASK;
          if ((u64)other > lit && (u64)other < nlits) {
            u64 ov = (u64)(other >> 1);
            if ((fl[ov] & FL_ACTIVE) != 0u && vals[other] == (i8)0) {
              if ((lit & 1ULL) == 0ULL) { wl[lvar] = f64u_add(wl[lvar], w2); }
              else { wr[lvar] = f64u_add(wr[lvar], w2); }
              if ((other & 1u) == 0u) { wl[ov] = f64u_add(wl[ov], w2); }
              else { wr[ov] = f64u_add(wr[ov], w2); }
            }
          }
          wp = wp + 1ULL;
        }
      }
    }
    lit = lit + 1ULL;
  }
  u64 fv = 0ULL;
  while (fv < cv) {
    u64 a = wl[fv];
    u64 b = wr[fv];
    wl[fv] = (a >= b) ? f64u_add(a, f64u_mul(b, 0x4000000000000000ULL))
                      : f64u_add(b, f64u_mul(a, 0x4000000000000000ULL));
    fv = fv + 1ULL;
  }
  if (h->stable != 0ULL) {
    full_rescale(h);
    u64 *sc = (u64 *)h->score;
    u64 n_s = 0ULL;
    u64 sv = 0ULL;
    while (sv < cv) {
      if ((fl[sv] & FL_ACTIVE) != 0u) { ws[n_s] = (u32)sv; n_s = n_s + 1ULL; }
      sv = sv + 1ULL;
    }
    if (n_s > 1ULL) {
      u64 s = n_s >> 1;
      while (s > 0ULL) {
        s = s - 1ULL;
        u64 root = s;
        while (true) {
          u64 ch = (root << 1) + 1ULL;
          if (ch >= n_s) { break; }
          u64 best = root;
          u32 bv = ws[best]; u64 bw = wl[bv]; u64 bs = sc[bv];
          u32 cv1 = ws[ch]; u64 cw = wl[cv1]; u64 cs = sc[cv1];
          if (cw > bw || (cw == bw && (cs > bs || (cs == bs && cv1 < bv)))) {
            best = ch; bv = cv1; bw = cw; bs = cs;
          }
          u64 rch = ch + 1ULL;
          if (rch < n_s) {
            u32 rv1 = ws[rch]; u64 rw = wl[rv1]; u64 rs = sc[rv1];
            if (rw > bw || (rw == bw && (rs > bs || (rs == bs && rv1 < bv)))) {
              best = rch; bv = rv1;
            }
          }
          if (best == root) { break; }
          u32 t = ws[root]; ws[root] = bv; ws[best] = t;
          root = best;
        }
      }
      u64 e = n_s;
      while (e > 1ULL) {
        e = e - 1ULL;
        u32 sw = ws[0]; ws[0] = ws[e]; ws[e] = sw;
        u64 root = 0ULL;
        while (true) {
          u64 ch = (root << 1) + 1ULL;
          if (ch >= e) { break; }
          u64 best = root;
          u32 bv = ws[best]; u64 bw = wl[bv]; u64 bs = sc[bv];
          u32 cv1 = ws[ch]; u64 cw = wl[cv1]; u64 cs = sc[cv1];
          if (cw > bw || (cw == bw && (cs > bs || (cs == bs && cv1 < bv)))) {
            best = ch; bv = cv1; bw = cw; bs = cs;
          }
          u64 rch = ch + 1ULL;
          if (rch < e) {
            u32 rv1 = ws[rch]; u64 rw = wl[rv1]; u64 rs = sc[rv1];
            if (rw > bw || (rw == bw && (rs > bs || (rs == bs && rv1 < bv)))) {
              best = rch; bv = rv1;
            }
          }
          if (best == root) { break; }
          u32 t = ws[root]; ws[root] = bv; ws[best] = t;
          root = best;
        }
      }
    }
    u64 rem_s = n_s;
    while (rem_s > 0ULL) {
      rem_s = rem_s - 1ULL;
      u32 idx = ws[rem_s];
      sc[idx] = f64u_add(sc[idx], wl[idx]);
      full_heap_up(h, idx);
    }
    return n_s;
  }
  u64 n = 0ULL;
  u64 av = 0ULL;
  while (av < cv) {
    if ((fl[av] & FL_ACTIVE) != 0u) { ws[n] = (u32)av; n = n + 1ULL; }
    av = av + 1ULL;
  }
  if (n > 1ULL) {
    u64 s = n >> 1;
    while (s > 0ULL) {
      s = s - 1ULL;
      full_reorder_sift_fid(h, s, n);
    }
    u64 e = n;
    while (e > 1ULL) {
      e = e - 1ULL;
      u32 tmp = ws[0];
      ws[0] = ws[e];
      ws[e] = tmp;
      full_reorder_sift_fid(h, 0ULL, e);
    }
  }
  u64 rv = 0ULL;
  while (rv < cv) {
    qp[rv] = 0xFFFFFFFFu;
    qn[rv] = 0xFFFFFFFFu;
    qs[rv] = 0u;
    rv = rv + 1ULL;
  }
  if (n == 0ULL) {
    h->q_first = 0xFFFFFFFFULL;
    h->q_last = 0xFFFFFFFFULL;
    h->q_search_idx = 0xFFFFFFFFULL;
    h->q_cur_stamp = 0ULL;
    h->q_search_stamp = 0ULL;
    return 0ULL;
  }
  u64 sidx = 0xFFFFFFFFULL;
  u64 sstamp = 0ULL;
  u64 qi = 0ULL;
  while (qi < n) {
    u32 cur = ws[qi];
    qp[cur] = (qi > 0ULL) ? ws[qi - 1ULL] : 0xFFFFFFFFu;
    qn[cur] = (qi + 1ULL < n) ? ws[qi + 1ULL] : 0xFFFFFFFFu;
    qs[cur] = (u32)(qi + 1ULL);
    if (vals[(u64)cur << 1] == (i8)0) { sidx = (u64)cur; sstamp = qi + 1ULL; }
    qi = qi + 1ULL;
  }
  h->q_first = (u64)ws[0];
  h->q_last = (u64)ws[n - 1ULL];
  h->q_cur_stamp = n;
  if (sidx >= cv) { sidx = (u64)ws[n - 1ULL]; sstamp = n; }
  h->q_search_idx = sidx;
  h->q_search_stamp = sstamp;
  return n;
}

u64 full_reorder_m6(FullHdr *h, u64 budget) {
  (void)budget;
  if (h->cur_level != 0ULL) { return 0ULL; }
  return full_reorder_queue_m7(h);
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Reorder

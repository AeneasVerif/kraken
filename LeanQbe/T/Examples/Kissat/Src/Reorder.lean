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
- `full_reorder_m6` (R4: `kissat_reorder`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Reorder

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! reorder "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_heap_up(FullHdr *h, u32 v);
extern void full_rescale(FullHdr *h);

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
  u64 w2 = 1ULL << 40;
  u64 wcap = 1ULL << 60;
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
      if (!sat && sz >= 2ULL && sz <= 100ULL) {
        u64 w = (sz >= 2ULL && sz <= 42ULL) ? ((1ULL << 40) >> (sz - 2ULL)) : 0ULL;
        if (w > 0ULL) {
          ci = 0ULL;
          while (ci < clen) {
            u32 lit = ar[p + 3ULL + ci];
            if ((u64)lit < nlits) {
              u32 av = lit >> 1;
              if ((lit & 1u) == 0u) {
                u64 cur = wl[av];
                wl[av] = (cur > wcap - w) ? wcap : (cur + w);
              } else {
                u64 cur = wr[av];
                wr[av] = (cur > wcap - w) ? wcap : (cur + w);
              }
            }
            ci = ci + 1ULL;
          }
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
              if ((lit & 1ULL) == 0ULL) {
                u64 c1 = wl[lvar];
                wl[lvar] = (c1 > wcap - w2) ? wcap : (c1 + w2);
              } else {
                u64 c1 = wr[lvar];
                wr[lvar] = (c1 > wcap - w2) ? wcap : (c1 + w2);
              }
              if ((other & 1u) == 0u) {
                u64 c2 = wl[ov];
                wl[ov] = (c2 > wcap - w2) ? wcap : (c2 + w2);
              } else {
                u64 c2 = wr[ov];
                wr[ov] = (c2 > wcap - w2) ? wcap : (c2 + w2);
              }
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
    wl[fv] = (a >= b) ? (a + (b << 1)) : (b + (a << 1));
    fv = fv + 1ULL;
  }
  if (h->stable != 0ULL) {
    full_rescale(h);
    u64 *sc = (u64 *)h->score;
    u64 sv = 0ULL;
    u64 maxw = 0ULL;
    while (sv < cv) {
      if ((fl[sv] & FL_ACTIVE) != 0u && wl[sv] > maxw) { maxw = wl[sv]; }
      sv = sv + 1ULL;
    }
    u64 scale_ref = h->scinc;
    if (scale_ref < (1ULL << 20)) { scale_ref = 1ULL << 20; }
    sv = 0ULL;
    while (sv < cv) {
      if ((fl[sv] & FL_ACTIVE) != 0u && wl[sv] > 0ULL) {
        u64 add = (maxw > 0ULL) ? ((wl[sv] >> 20) * (scale_ref >> 20)) : 0ULL;
        if (add > (1ULL << 52)) { add = 1ULL << 52; }
        u64 cur = sc[sv];
        u64 nsc = (cur > (1ULL << 60) - add) ? (1ULL << 60) : (cur + add);
        sc[sv] = nsc;
        full_heap_up(h, (u32)sv);
      }
      sv = sv + 1ULL;
    }
    return cv;
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

/-- Ordered live functions of `Src/Reorder.lean` (`3` fns). -/
def fns : List Fn := reorder_fns

end

public section

theorem full_reorder_sift_fid_wf : Func.Wf full_reorder_sift_fid_body := by kissat_wf_reify
theorem full_reorder_queue_m7_wf : Func.Wf full_reorder_queue_m7_body := by kissat_wf_reify
theorem full_reorder_m6_wf : Func.Wf full_reorder_m6_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, reorder_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact full_reorder_sift_fid_wf
  · exact full_reorder_queue_m7_wf
  · exact full_reorder_m6_wf

end

end LeanQbe.T.Examples.Kissat.Src.Reorder

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Variable Score Bumping & VMTF Decision Queue (`Src/Bump.lean`)

Mirrors upstream `kissat/src/bump.c, queue.c` (`9` live functions, DAG level `L1`):
- `full_rescale_m6` (R4: `kissat_rescale_scores_impl`)
- `full_rescale` (R4: `kissat_rescale_scores`)
- `full_bump_var` (R4: `kissat_bump_variable`)
- `full_bump_decay` (R4: `kissat_bump_score_increment`)
- `full_queue_renumber` (R4: `kissat_reassign_queue_stamps`)
- `full_queue_mtf` (R4: `kissat_move_to_front`)
- `full_ana_sift_m6` (R4: `kissat_bump_queue_sift`)
- `full_sort_ana_qs_m6` (R4: `kissat_sort_bump_queue`)
- `full_bump_analyzed_mode_fid`-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Bump

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! bump "
#include \"kissat_internal.h\"

extern u64 f64u_div(u64 a, u64 b);
extern u64 f64u_mul(u64 a, u64 b);
extern u64 f64u_add(u64 a, u64 b);
extern void full_heap_up(FullHdr *h, u32 v);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool m6_hdr_dr_allow(FullHdr *h);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);

void full_rescale_m6(FullHdr *h) {
  u64 *sc = (u64 *)h->score;
  u64 cv = h->cur_vars;
  u64 mx = 0ULL;
  u64 m = 0ULL;
  while (m < cv) { if (sc[m] > mx) { mx = sc[m]; } m = m + 1ULL; }
  u64 inc = h->scinc;
  u64 rescale = (mx > inc) ? mx : inc;
  u64 factor = f64u_div(0x3FF0000000000000ULL, rescale);
  u64 v = 0ULL;
  while (v < cv) { sc[v] = f64u_mul(sc[v], factor); v = v + 1ULL; }
  h->scinc = f64u_mul(inc, factor);
}

void full_rescale(FullHdr *h) {
  full_rescale_m6(h);
}

void full_bump_var(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u64 *sc = (u64 *)h->score;
  u64 nsc = f64u_add(sc[v], h->scinc);
  sc[v] = nsc;
  if (h->stable != 0ULL) { full_heap_up(h, v); }
  if (nsc > 0x5F18EA1BD2031214ULL) { full_rescale(h); }
}

void full_bump_decay(FullHdr *h) {
  u64 factor = 0x3FF0D79435E50D79ULL; /* 1.0 / (1.0 - 0.05) */
  u64 ninc = f64u_mul(h->scinc, factor);
  h->scinc = ninc;
  if (ninc > 0x5F18EA1BD2031214ULL) { full_rescale(h); }
}

void full_queue_renumber(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 st = 0u;
  u64 cur = h->q_first;
  u64 steps = 0ULL;
  while (cur < cv && steps < cv) {
    st = st + 1u;
    qs[cur] = st;
    cur = (u64)qn[cur];
    steps = steps + 1ULL;
  }
  h->q_cur_stamp = (u64)st;
  if (h->q_search_idx < cv) { h->q_search_stamp = (u64)qs[h->q_search_idx]; }
}

void full_queue_mtf(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv || (u64)v == h->q_last) { return; }
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  i8 *vals = (i8 *)h->values;
  if (vals[(u64)v << 1] != (i8)0 && (u64)v == h->q_search_idx) {
    u32 pv = qp[v];
    if ((u64)pv < cv) { h->q_search_idx = (u64)pv; h->q_search_stamp = (u64)qs[pv]; }
    else {
      u32 nv = qn[v];
      if ((u64)nv < cv) { h->q_search_idx = (u64)nv; h->q_search_stamp = (u64)qs[nv]; }
    }
  }
  u32 pv = qp[v];
  u32 nv = qn[v];
  qp[v] = 0xFFFFFFFFu; qn[v] = 0xFFFFFFFFu;
  if ((u64)pv >= cv) { h->q_first = (u64)nv; } else { qn[pv] = nv; }
  if ((u64)nv >= cv) { h->q_last = (u64)pv; } else { qp[nv] = pv; }
  u32 old_last = (u32)h->q_last;
  qp[v] = old_last; h->q_last = (u64)v;
  if ((u64)old_last >= cv) { h->q_first = (u64)v; } else { qn[old_last] = v; }
  if (h->q_cur_stamp >= 0xFFFFFFFFULL) { full_queue_renumber(h); }
  else { h->q_cur_stamp = h->q_cur_stamp + 1ULL; qs[v] = (u32)h->q_cur_stamp; }
  if (vals[(u64)v << 1] == (i8)0) {
    h->q_search_idx = (u64)v; h->q_search_stamp = (u64)qs[v];
  }
}

void full_ana_sift_m6(u32 *qs, u32 *ana, u64 cv, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 ac = ana[ch];
    u32 qc = ((u64)ac < cv) ? qs[ac] : 0u;
    if (ch + 1ULL < n) {
      u32 ac1 = ana[ch + 1ULL];
      u32 qc1 = ((u64)ac1 < cv) ? qs[ac1] : 0u;
      if (qc < qc1) { ch = ch + 1ULL; qc = qc1; }
    }
    u32 ar = ana[root];
    u32 qr = ((u64)ar < cv) ? qs[ar] : 0u;
    if (qr >= qc) { break; }
    ana[root] = ana[ch]; ana[ch] = ar;
    root = ch;
  }
}

void full_sort_ana_qs_m6(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u64 cv = h->cur_vars;
  if (n > cv) { return; }
  u32 *qs = (u32 *)h->q_stamp;
  u32 *ana = (u32 *)h->work_stk1;
  u64 *rk = (u64 *)h->repr;
  u64 *tmp = (u64 *)h->wsort;
  if (n < 32ULL) {
    u64 i = 0ULL;
    while (i < n) {
      u32 a = ana[i];
      u32 q = ((u64)a < cv) ? qs[a] : 0u;
      rk[i] = ((u64)q << 32) | (u64)a;
      i = i + 1ULL;
    }
    i = 1ULL;
    while (i < n) {
      u64 x = rk[i];
      u64 kx = x >> 32;
      u64 j = i;
      while (j > 0ULL && (rk[j - 1ULL] >> 32) > kx) {
        rk[j] = rk[j - 1ULL];
        j = j - 1ULL;
      }
      rk[j] = x;
      i = i + 1ULL;
    }
    i = 0ULL;
    while (i < n) { ana[i] = (u32)rk[i]; i = i + 1ULL; }
    return;
  }
  if (h->scratch_cap >= 512ULL) {
    u64 i = 0ULL;
    while (i < n) {
      u32 a = ana[i];
      u32 q = ((u64)a < cv) ? qs[a] : 0u;
      rk[i] = ((u64)q << 32) | (u64)a;
      i = i + 1ULL;
    }
    u64 *cnt = (u64 *)h->scratch_buf;
    u64 *s_arr = rk;
    u64 *d_arr = tmp;
    u64 shift = 32ULL;
    while (shift < 64ULL) {
      u64 b = 0ULL;
      while (b < 256ULL) { cnt[b] = 0ULL; b = b + 1ULL; }
      u64 lo = 256ULL;
      u64 hi = 0ULL;
      i = 0ULL;
      while (i < n) {
        u64 bv = (s_arr[i] >> shift) & 255ULL;
        cnt[bv] = cnt[bv] + 1ULL;
        if (bv < lo) { lo = bv; }
        if (bv > hi) { hi = bv; }
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
          u64 x = s_arr[i];
          u64 bv = (x >> shift) & 255ULL;
          u64 p = cnt[bv];
          cnt[bv] = p + 1ULL;
          d_arr[p] = x;
          i = i + 1ULL;
        }
        u64 *sw = s_arr;
        s_arr = d_arr;
        d_arr = sw;
      }
      shift = shift + 8ULL;
    }
    i = 0ULL;
    while (i < n) { ana[i] = (u32)s_arr[i]; i = i + 1ULL; }
    return;
  }
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_ana_sift_m6(qs, ana, cv, start, n);
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = ana[0]; ana[0] = ana[end]; ana[end] = t;
    full_ana_sift_m6(qs, ana, cv, 0ULL, end);
    end = end - 1ULL;
  }
}

void full_bump_analyzed_mode_fid(FullHdr *h, bool allow_reasons) {
  if (h->probing != 0ULL) { return; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  if (allow_reasons && !m6_hdr_delaying(h, 0ULL) && m6_hdr_dr_allow(h)) {
    u64 lim = saved * 10ULL;
    u64 i = 0ULL;
    u64 tlen = h->tmp_len;
    if (tlen > cv) { tlen = cv; }
    while (i < tlen && h->min_clr_len <= lim) {
      u32 uv = tmp[i] >> 1;
      u32 rsn = ((u64)uv < cv) ? rsns[uv] : 0xFFFFFFFFu;
      if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) != 0u) {
        u32 ov = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
          mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
          h->min_clr_len = h->min_clr_len + 1ULL;
        }
      } else if (rsn != 0xFFFFFFFFu && (u64)rsn + 3ULL <= h->arena_len) {
        u32 sz = ar[(u64)rsn + 2ULL];
        if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len) {
          h->search_ticks = h->search_ticks + 1ULL;
          u32 j = 0u;
          while (j < sz && h->min_clr_len <= lim) {
            u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
            if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
              mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
              h->min_clr_len = h->min_clr_len + 1ULL;
            }
            j = j + 1u;
          }
        }
      }
      i = i + 1ULL;
    }
    if (h->min_clr_len > lim) {
      while (h->min_clr_len > saved) {
        h->min_clr_len = h->min_clr_len - 1ULL;
        u32 rv = ana[h->min_clr_len];
        if ((u64)rv < cv) { mrk[rv] = (u8)0; }
      }
      m6_hdr_bump_delay(h, 0ULL);
    } else {
      m6_hdr_reduce_delay(h, 0ULL);
    }
  }
  u64 cnt = h->min_clr_len;
  if (h->stable == 0ULL) {
    if (cnt <= cv) { full_sort_ana_qs_m6(h, cnt); }
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_queue_mtf(h, bv);
      }
      k = k + 1ULL;
    }
  } else {
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_bump_var(h, bv);
      }
      k = k + 1ULL;
    }
    full_bump_decay(h);
  }
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Bump

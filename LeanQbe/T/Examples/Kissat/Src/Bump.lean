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

Mirrors upstream `kissat/src/bump.c, queue.c` (`13` live functions, DAG level `L1`):
- `full_rescale_m6` (R4: `kissat_rescale_scores_impl`)
- `full_rescale` (R4: `kissat_rescale_scores`)
- `full_bump_var` (R4: `kissat_bump_variable`)
- `full_bump_decay` (R4: `kissat_bump_score_increment`)
- `full_queue_renumber` (R4: `kissat_reassign_queue_stamps`)
- `full_queue_mtf` (R4: `kissat_move_to_front`)
- `full_ana_sift_m6` (R4: `kissat_bump_queue_sift`)
- `full_sort_ana_qs_m6` (R4: `kissat_sort_bump_queue`)
- `full_bump_analyzed_m6_hdr` (R4: `kissat_bump_analyzed`)
- `full_bump_sift_m7` (R4: `kissat_bump_stamp_sift`)
- `full_bump_sort_stamps_m7` (R4: `kissat_bump_sort_stamps`)
- `full_bump_reasons_m7` (R4: `kissat_bump_reason_literals`)
- `full_bump_analyzed` (R4: `kissat_bump_analyzed_basic`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Bump

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! bump "
#include \"kissat_internal.h\"

extern void full_heap_up(FullHdr *h, u32 v);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern bool m6_hdr_dr_allow(FullHdr *h);

void full_rescale_m6(FullHdr *h) {
  u64 *sc = (u64 *)h->score;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  while (v < cv) { sc[v] = sc[v] >> 16ULL; v = v + 1ULL; }
  h->scinc = h->scinc >> 16ULL;
  if (h->scinc < (1ULL << 20)) { h->scinc = 1ULL << 20; }
}

void full_rescale(FullHdr *h) {
  full_rescale_m6(h);
}

void full_bump_var(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u64 *sc = (u64 *)h->score;
  u64 cur = sc[v];
  u64 inc = h->scinc;
  u64 nsc = (cur > (1ULL << 61) || inc > (1ULL << 61)) ? (1ULL << 60) : (cur + inc);
  sc[v] = nsc;
  if (h->stable != 0ULL) { full_heap_up(h, v); }
  if (nsc >= (1ULL << 60)) { full_rescale(h); }
}

void full_bump_decay(FullHdr *h) {
  u64 inc = h->scinc;
  if (inc < (1ULL << 20)) { inc = 1ULL << 20; }
  if (inc >= (1ULL << 56)) { full_rescale(h); inc = h->scinc; }
  u64 ninc = (inc * 20ULL) / 19ULL;
  h->scinc = ninc;
  if (ninc >= (1ULL << 56)) { full_rescale(h); }
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

void full_bump_analyzed_m6_hdr(FullHdr *h) {
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
  if (!m6_hdr_delaying(h, 0ULL) && m6_hdr_dr_allow(h)) {
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

void full_bump_sift_m7(FullHdr *h, u64 start, u64 n) {
  u64 cv = h->cur_vars;
  if (n == 0ULL || start >= n || n > cv || cv > h->max_vars) { return; }
  u32 *ws = (u32 *)h->work_stk1;
  u32 *qs = (u32 *)h->q_stamp;
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 cl = ws[ch];
    u32 cq = ((u64)cl < cv) ? qs[cl] : 0u;
    if (ch + 1ULL < n) {
      u32 sl = ws[ch + 1ULL];
      u32 sq = ((u64)sl < cv) ? qs[sl] : 0u;
      if (sq > cq || (sq == cq && sl > cl)) {
        ch = ch + 1ULL;
        cl = sl;
        cq = sq;
      }
    }
    u32 rl = ws[root];
    u32 rq = ((u64)rl < cv) ? qs[rl] : 0u;
    if (rq > cq || (rq == cq && rl >= cl)) { break; }
    ws[root] = cl;
    ws[ch] = rl;
    root = ch;
  }
}

void full_bump_sort_stamps_m7(FullHdr *h, u64 n) {
  u64 cv = h->cur_vars;
  if (n <= 1ULL || n > cv || cv > h->max_vars) { return; }
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_bump_sift_m7(h, start, n);
  }
  u64 end = n;
  u32 *ws = (u32 *)h->work_stk1;
  while (end > 1ULL) {
    end = end - 1ULL;
    u32 tmp = ws[0];
    ws[0] = ws[end];
    ws[end] = tmp;
    full_bump_sift_m7(h, 0ULL, end);
  }
}

void full_bump_reasons_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv > h->max_vars) { cv = h->max_vars; }
  u64 tl = h->tmp_len;
  if (tl > cv) { tl = cv; }
  u64 saved = h->min_clr_len;
  if (saved >= cv || tl == 0ULL) { return; }
  u64 lim = (saved > 0x1999999999999999ULL) ? 0xFFFFFFFFFFFFFFFFULL : (saved * 10ULL);
  u64 alen = h->arena_len;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *rsns = (u32 *)h->reason;
  u32 *lvl = (u32 *)h->level;
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  while (i < tl) {
    u32 lit = tmp[i];
    u32 uv = lit >> 1;
    if ((u64)uv < cv) {
      u32 rsn = rsns[uv];
      if (rsn != 0xFFFFFFFFu) {
        if ((rsn & PW_BIN_FLAG) != 0u) {
          u32 olit = rsn & PW_LIT_MASK;
          u32 ov = olit >> 1;
          if ((u64)ov < cv && ov != uv && lvl[ov] > 0u && mrk[ov] == (u8)0) {
            if (h->min_clr_len < cv) {
              mrk[ov] = (u8)1;
              ana[h->min_clr_len] = ov;
              h->min_clr_len = h->min_clr_len + 1ULL;
            }
          }
        } else if (alen >= 3ULL && (u64)rsn <= alen - 3ULL) {
          u32 sz = ar[(u64)rsn + 2ULL];
          if (sz >= 3u && (u64)sz <= alen - ((u64)rsn + 3ULL)) {
            u64 k = 0ULL;
            while (k < (u64)sz) {
              u32 olit = ar[(u64)rsn + 3ULL + k];
              u32 ov = olit >> 1;
              if ((u64)ov < cv && ov != uv && lvl[ov] > 0u && mrk[ov] == (u8)0) {
                if (h->min_clr_len < cv) {
                  mrk[ov] = (u8)1;
                  ana[h->min_clr_len] = ov;
                  h->min_clr_len = h->min_clr_len + 1ULL;
                }
              }
              k = k + 1ULL;
            }
          }
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
  }
}

void full_bump_analyzed(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  full_bump_reasons_m7(h);
  u64 cnt = h->min_clr_len;
  u64 cv = h->cur_vars;
  if (cv > h->max_vars) { return; }
  if (cnt > cv) { cnt = cv; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *fl = (u32 *)h->flags;
  if (h->stable == 0ULL) {
    full_bump_sort_stamps_m7(h, cnt);
    u64 iv = 0ULL;
    while (iv < cnt) {
      u32 bv = ana[iv];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_queue_mtf(h, bv);
      }
      iv = iv + 1ULL;
    }
  } else {
    u64 iv = 0ULL;
    while (iv < cnt) {
      u32 bv = ana[iv];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_bump_var(h, bv);
      }
      iv = iv + 1ULL;
    }
    full_bump_decay(h);
  }
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Bump

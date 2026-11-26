/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Bounded Variable Addition (BVA / Factorization) (`Src/Factor.lean`)

Mirrors upstream `kissat/src/factor.c` (`14` live functions, DAG level `L5`):
- `full_bva_steps_cap_fid` (R4: `kissat_factor_steps_cap`)
- `full_bva_clines_fid` (R4: `kissat_factor_clause_lines`)
- `full_fheap_up_fid` (R4: `kissat_factor_heap_up`)
- `full_fheap_down_fid` (R4: `kissat_factor_heap_down`)
- `full_bva_count_lit_deg_fid` (R4: `kissat_factor_count_literal_degree`)
- `full_bva_connect_clauses_fid` (R4: `kissat_factor_connect_clauses`)
- `full_bva_match_large_bva_fid` (R4: `kissat_factor_match_large`)
- `full_bva_scan_cands` (R4: `kissat_factor_scan_candidates`)
- `full_bva_pick_cand` (R4: `kissat_factor_pick_candidate`)
- `full_bva_filter_row` (R4: `kissat_factor_filter_row`)
- `full_bva_commit` (R4: `kissat_factor_commit`)
- `full_bva_try_lit` (R4: `kissat_factor_try_literal`)
- `full_bva_upd_lit_fid` (R4: `kissat_factor_update_literal`)
- `full_factor` (R4: `kissat_factor`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Factor

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! factor "
#include \"kissat_internal.h\"

extern void full_fill_u64_m7(u64 *dst, u64 n, u64 val);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern void full_fwd_flush_large_m7(FullHdr *h);

u32 full_bva_steps_cap_fid(u64 cap) {
  if (cap >= 8192ULL) { return 256u; }
  if (cap >= 1024ULL) { return 64u; }
  if (cap >= 256ULL) { return 32u; }
  if (cap >= 64ULL) { return 8u; }
  return 0u;
}

u64 full_bva_clines_fid(u64 n) {
  if (n == 0ULL) { return 0ULL; }
  return (n + 31ULL) >> 5;
}

void full_fheap_up_fid(u32 *hp, u32 *ps, u32 *deg, u32 p) {
  u32 l = hp[p];
  u32 d = deg[l];
  while (p > 0u) {
    u32 par = (p - 1u) >> 1;
    u32 pl = hp[par];
    if (deg[pl] >= d) { break; }
    hp[p] = pl;
    ps[pl] = p;
    p = par;
  }
  hp[p] = l;
  ps[l] = p;
}

void full_fheap_down_fid(u32 *hp, u32 *ps, u32 *deg, u32 p, u32 n) {
  u32 l = hp[p];
  u32 d = deg[l];
  while (true) {
    u32 lc = (p << 1) + 1u;
    if (lc >= n) { break; }
    u32 best = lc;
    u32 bd = deg[hp[lc]];
    u32 rc = lc + 1u;
    if (rc < n) {
      u32 rd = deg[hp[rc]];
      if (rd > bd) { best = rc; bd = rd; }
    }
    if (d >= bd) { break; }
    u32 bl = hp[best];
    hp[p] = bl;
    ps[bl] = p;
    p = best;
  }
  hp[p] = l;
  ps[l] = p;
}

u32 full_bva_count_lit_deg_fid(FullHdr *h, u32 lit) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 p = off;
  u32 cnt = 0u;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      cnt = cnt + 1u;
    } else if (p < end) {
      p = p + 1ULL;
      cnt = cnt + 1u;
    }
  }
  return cnt;
}

void full_bva_connect_clauses_fid(FullHdr *h) {
  full_fwd_flush_large_m7(h);
  u64 nlits = h->cur_vars << 1;
  u32 *bc = (u32 *)h->tarjan_mark;
  u32 *lc = (u32 *)h->work_stk1;
  u32 *nlc = (u32 *)h->work_stk2;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *deg = (u32 *)h->repr;
  u64 i = 0ULL;
  while (i < nlits) {
    bc[i] = 0u;
    lc[i] = 0u;
    i = i + 1ULL;
  }
  i = 0ULL;
  while (i < nlits) {
    if ((fl[i >> 1] & FL_ACTIVE) != 0u && vals[i] == (i8)0) {
      u64 off = (u64)wvec[i << 1];
      u64 end = off + (u64)wvec[(i << 1) + 1ULL];
      u64 p = off;
      u32 bcnt = 0u;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 other = w0 & PW_LIT_MASK;
          if (vals[other] == (i8)0 && (fl[other >> 1] & FL_ACTIVE) != 0u) {
            if (bcnt < 0xFFFFFFFFu) { bcnt = bcnt + 1u; }
          }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      bc[i] = bcnt;
    }
    i = i + 1ULL;
  }
  u64 cands = 0ULL;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
      bool sat = false;
      u32 k = 0u;
      while (k < sz) {
        if (vals[ar[p + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
        k = k + 1u;
      }
      if (!sat) {
        k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (lc[l] < 0xFFFFFFFFu) { lc[l] = lc[l] + 1u; }
          k = k + 1u;
        }
        cands = cands + 1ULL;
      }
    }
    p = np;
  }
  u32 rnd = 0u;
  while (rnd < 2u && cands > 0ULL) {
    i = 0ULL;
    while (i < nlits) { nlc[i] = 0u; i = i + 1ULL; }
    u64 ncands = 0ULL;
    p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
        bool keep = true;
        u32 k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (vals[l] > (i8)0 || (u64)bc[l] + (u64)lc[l] < 2ULL) {
            keep = false; break;
          }
          k = k + 1u;
        }
        if (keep) {
          k = 0u;
          while (k < sz) {
            u32 l = ar[p + 3ULL + (u64)k];
            if (nlc[l] < 0xFFFFFFFFu) { nlc[l] = nlc[l] + 1u; }
            k = k + 1u;
          }
          ncands = ncands + 1ULL;
        }
      }
      p = np;
    }
    i = 0ULL;
    while (i < nlits) { lc[i] = nlc[i]; i = i + 1ULL; }
    if (ncands == cands) { break; }
    cands = ncands;
    rnd = rnd + 1u;
  }
  p = 0ULL;
  while (p < h->arena_len && h->oom == 0ULL) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
      bool keep = true;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        if (vals[l] > (i8)0 || (u64)bc[l] + (u64)lc[l] < 2ULL) {
          keep = false; break;
        }
        k = k + 1u;
      }
      if (keep) {
        k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (!full_watch_push(h, l, sz & PW_LIT_MASK, (u32)p, 2u)) {
            h->oom = 1ULL;
            break;
          }
          k = k + 1u;
        }
      }
    }
    p = np;
  }
  u64 dl = 0ULL;
  while (dl < nlits) {
    deg[dl] = full_bva_count_lit_deg_fid(h, (u32)dl);
    dl = dl + 1ULL;
  }
}

bool full_bva_match_large_bva_fid(FullHdr *h, u32 cur_cr, u32 next_lit, u32 d_ref) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark;
  u32 sz = ar[(u64)cur_cr + 2ULL];
  if (ar[(u64)d_ref + 2ULL] != sz || (ar[d_ref] & (PH_GARB | PH_RED | PH_BVA_Q)) != 0u) {
    return false;
  }
  u32 j = 0u; bool seen_next = false;
  while (j < sz) {
    u32 dl = ar[(u64)d_ref + 3ULL + (u64)j];
    if ((lm[dl] & (u8)2) == (u8)0) {
      if (dl == next_lit && !seen_next) { seen_next = true; } else { return false; }
    }
    j = j + 1u;
  }
  return seen_next;
}

u32 full_bva_scan_cands(FullHdr *h, u32 row_off, u32 cur_qn, u64 init_lits) {
  i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *cntd = (u32 *)h->work_stk1;
  u32 *fl = (u32 *)h->flags; u32 *ql = (u32 *)h->work_stk2;
  u32 *deg = (u32 *)h->repr;
  u32 nql = 0u; u32 ncntd = 0u; u32 qi = 0u;
  u64 ticks = 1ULL + full_bva_clines_fid((u64)cur_qn);
  while (qi < cur_qn) {
    u32 qw = scr[row_off + qi];
    if ((qw & PW_BIN_FLAG) != 0u) {
      u32 q = qw & PW_LIT_MASK;
      u64 qoff = (u64)wvec[(u64)q << 1];
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      u64 qend = qoff + qsz;
      ticks = ticks + 1ULL + full_bva_clines_fid((u64)deg[q]);
      u64 qp = qoff;
      while (qp < qend) {
        u32 nw = wstk[qp];
        if ((nw & PW_BIN_FLAG) != 0u) {
          u32 cand = nw & PW_LIT_MASK;
          if ((u64)cand < init_lits && (lm[cand] & (u8)1) == (u8)0 &&
              (fl[cand >> 1] & FL_ACTIVE) != 0u && vals[cand] == (i8)0) {
            if (cnt[cand] == 0u) {
              if ((u64)ncntd < init_lits) { cntd[ncntd] = cand; ncntd = ncntd + 1u; }
            }
            if (cnt[cand] < 0xFFFFFFFFu) { cnt[cand] = cnt[cand] + 1u; }
          }
          qp = qp + 1ULL;
        } else { qp = qp + 2ULL; }
      }
    } else {
      u32 csz = ar[(u64)qw + 2ULL]; u32 min_l = 0xFFFFFFFFu; u32 min_d = 0xFFFFFFFFu;
      u32 fc = 0u; u32 j = 0u;
      ticks = ticks + 1ULL;
      while (j < csz) {
        u32 l = ar[(u64)qw + 3ULL + (u64)j];
        if ((lm[l] & (u8)1) != (u8)0) { fc = fc + 1u; if (fc > 1u) { break; } }
        else {
          lm[l] = lm[l] | (u8)2;
          u32 d = deg[l];
          if (min_l == 0xFFFFFFFFu || d < min_d) { min_l = l; min_d = d; }
        }
        j = j + 1u;
      }
      if (fc == 1u && min_l != 0xFFFFFFFFu) {
        u64 moff = (u64)wvec[(u64)min_l << 1];
        u64 msz = (u64)wvec[((u64)min_l << 1) + 1ULL];
        u64 mend = moff + msz; u64 mp = moff;
        u64 mxv = h->max_vars; u32 nnou = 0u;
        ticks = ticks + 1ULL + full_bva_clines_fid((u64)min_d);
        while (mp < mend) {
          u32 mw = wstk[mp]; mp = mp + 1ULL;
          if ((mw & PW_BIN_FLAG) != 0u) { continue; }
          if (mp >= mend) { break; }
          u32 dr = wstk[mp]; mp = mp + 1ULL;
          if (dr == qw) { continue; }
          ticks = ticks + 1ULL;
          if ((ar[dr] & (PH_GARB | PH_RED | PH_BVA_Q)) != 0u ||
              ar[(u64)dr + 2ULL] != csz) { continue; }
          u32 cand = 0xFFFFFFFFu; bool ok = true; u32 dj = 0u;
          while (dj < csz) {
            u32 dl = ar[(u64)dr + 3ULL + (u64)dj]; u8 m = lm[dl];
            if ((m & (u8)2) == (u8)0) {
              if ((m & (u8)5) != (u8)0 || cand != 0xFFFFFFFFu) { ok = false; break; }
              cand = dl;
            }
            dj = dj + 1u;
          }
          if (ok && cand != 0xFFFFFFFFu && (u64)cand < init_lits &&
              (fl[cand >> 1] & FL_ACTIVE) != 0u && vals[cand] == (i8)0) {
            if ((u64)nnou < mxv) {
              lm[cand] = lm[cand] | (u8)4;
              ql[mxv + (u64)nnou] = cand;
              nnou = nnou + 1u;
            }
            if ((u64)nql < mxv) {
              ar[dr] = ar[dr] | PH_BVA_Q;
              ql[nql] = dr;
              nql = nql + 1u;
            }
            if (cnt[cand] == 0u) {
              if ((u64)ncntd < init_lits) { cntd[ncntd] = cand; ncntd = ncntd + 1u; }
            }
            if (cnt[cand] < 0xFFFFFFFFu) { cnt[cand] = cnt[cand] + 1u; }
          }
        }
        j = 0u;
        while (j < nnou) {
          u32 cl = ql[mxv + (u64)j]; lm[cl] = lm[cl] & (u8)0xFB; j = j + 1u;
        }
      }
      j = 0u;
      while (j < csz) {
        u32 cj = ar[(u64)qw + 3ULL + (u64)j]; lm[cj] = lm[cj] & (u8)0xFD; j = j + 1u;
      }
    }
    h->ant_sz = (h->ant_sz > ticks) ? (h->ant_sz - ticks) : 0ULL;
    ticks = 0ULL;
    if (h->ant_sz == 0ULL) { break; }
    qi = qi + 1u;
  }
  u32 ci = 0u; while (ci < nql) { ar[ql[ci]] = ar[ql[ci]] & (~PH_BVA_Q); ci = ci + 1u; }
  return ncntd;
}

u32 full_bva_pick_cand(FullHdr *h, u32 ncntd, u32 f0) {
  (void)f0;
  u32 *deg = (u32 *)h->repr;
  u32 *cnt = (u32 *)h->wsort;
  u32 *cntd = (u32 *)h->work_stk1;
  u32 best_c = 0u;
  u32 best_deg = 0u;
  u32 best_lit = 0xFFFFFFFFu;
  u32 ci = 0u;
  while (ci < ncntd) {
    u32 clit = cntd[ci];
    u32 cc = cnt[clit];
    if (cc >= 2u) {
      if (cc > best_c) {
        best_c = cc;
        best_deg = deg[clit];
        best_lit = clit;
      } else if (cc == best_c) {
        u32 d = deg[clit];
        if (d > best_deg) {
          best_deg = d;
          best_lit = clit;
        }
      }
    }
    ci = ci + 1u;
  }
  ci = 0u;
  while (ci < ncntd) {
    cnt[cntd[ci]] = 0u;
    ci = ci + 1u;
  }
  return (best_c < 2u) ? 0xFFFFFFFFu : best_lit;
}

u32 full_bva_filter_row(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off,
                        u32 cur_qn, u32 best_lit) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 *deg = (u32 *)h->repr;
  u32 max_new = par_off - nrow_off;
  u32 new_qn = 0u; u32 qi = 0u;
  u64 ticks = 1ULL + full_bva_clines_fid((u64)cur_qn);
  while (qi < cur_qn && new_qn < max_new) {
    u32 qw = scr[row_off + qi];
    if ((qw & PW_BIN_FLAG) != 0u) {
      u32 q = qw & PW_LIT_MASK;
      u64 qoff = (u64)wvec[(u64)q << 1];
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      u64 qend = qoff + qsz;
      ticks = ticks + 1ULL + full_bva_clines_fid((u64)deg[q]);
      u64 qp = qoff;
      while (qp < qend) {
        u32 nw = wstk[qp];
        if ((nw & PW_BIN_FLAG) != 0u) {
          if ((nw & PW_LIT_MASK) == best_lit) {
            scr[nrow_off + new_qn] = qw; scr[par_off + new_qn] = qi;
            new_qn = new_qn + 1u; break;
          }
          qp = qp + 1ULL;
        } else { qp = qp + 2ULL; }
      }
    } else {
      u32 csz = ar[(u64)qw + 2ULL]; u32 min_l = 0xFFFFFFFFu; u32 min_d = 0xFFFFFFFFu;
      u32 fc = 0u; u32 j = 0u;
      ticks = ticks + 1ULL;
      while (j < csz) {
        u32 l = ar[(u64)qw + 3ULL + (u64)j];
        if ((lm[l] & (u8)1) != (u8)0) {
          fc = fc + 1u; if (fc > 1u) { break; }
        } else {
          lm[l] = lm[l] | (u8)2;
          u32 d = deg[l];
          if (min_l == 0xFFFFFFFFu || d < min_d) { min_l = l; min_d = d; }
        }
        j = j + 1u;
      }
      if (fc == 1u && min_l != 0xFFFFFFFFu) {
        u64 moff = (u64)wvec[(u64)min_l << 1];
        u64 msz = (u64)wvec[((u64)min_l << 1) + 1ULL];
        u64 mend = moff + msz; u64 mp = moff;
        ticks = ticks + 1ULL + full_bva_clines_fid((u64)min_d);
        while (mp < mend) {
          u32 mw = wstk[mp]; mp = mp + 1ULL;
          if ((mw & PW_BIN_FLAG) != 0u) { continue; }
          if (mp >= mend) { break; }
          u32 dr = wstk[mp]; mp = mp + 1ULL;
          if (dr == qw) { continue; }
          ticks = ticks + 1ULL;
          if (full_bva_match_large_bva_fid(h, qw, best_lit, dr)) {
            ar[dr] = ar[dr] | PH_BVA_Q;
            scr[nrow_off + new_qn] = dr; scr[par_off + new_qn] = qi;
            new_qn = new_qn + 1u; break;
          }
        }
      }
      j = 0u;
      while (j < csz) {
        u32 cj = ar[(u64)qw + 3ULL + (u64)j]; lm[cj] = lm[cj] & (u8)0xFD; j = j + 1u;
      }
    }
    qi = qi + 1u;
  }
  u32 ci = 0u;
  while (ci < new_qn) {
    u32 e = scr[nrow_off + ci];
    if ((e & PW_BIN_FLAG) == 0u) { ar[e] = ar[e] & (~PH_BVA_Q); }
    ci = ci + 1u;
  }
  h->ant_sz = (h->ant_sz > ticks) ? (h->ant_sz - ticks) : 0ULL;
  return new_qn;
}

bool full_bva_commit(FullHdr *h, u32 best_k) {
  if (h->oom != 0ULL) { return false; }
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (sc == 0u || best_k >= sc) { return false; }
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *fl = (u32 *)h->flags;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 dm = best_k + 1u;
  u32 brow_off = scr[sc + best_k];
  u32 mn = scr[2u * sc + best_k];
  u64 need_ar = 16ULL;
  u64 need_w = (((u64)dm + (u64)mn + 8ULL) << 3);
  u32 si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 fsz = (u64)wvec[((u64)fs << 1) + 1ULL];
    need_w = need_w + (fsz << 1) + 2ULL;
    si = si + 1u;
  }
  u32 m = 0u;
  while (m < mn) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      need_w = need_w + (qsz << 1) + 2ULL;
    } else {
      u32 csz = ar[(u64)c_top + 2ULL];
      need_ar = need_ar + 3ULL + (u64)csz;
      u32 flit = scr[best_k]; u32 j = 0u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) {
          u64 lsz = (u64)wvec[((u64)l << 1) + 1ULL];
          need_w = need_w + (lsz << 1) + 2ULL;
        }
        j = j + 1u;
      }
    }
    m = m + 1u;
  }
  if (h->cur_vars >= h->max_vars || h->arena_cap < h->arena_len ||
      h->arena_cap - h->arena_len < need_ar) { return false; }
  bool defrag_dirty = false;
  if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); defrag_dirty = true; }
    if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
      if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
      return false;
    }
  }
  u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
  full_init_fresh_var(h, fv);
  u32 *deg = (u32 *)h->repr;
  deg[fv << 1] = 0u; deg[(fv << 1) | 1u] = 0u;
  cnt[fv << 1] = 0u; cnt[(fv << 1) | 1u] = 0u;
  u32 fresh = fv << 1; u32 *tmp = (u32 *)h->tmp_lits;
  bool ok = true;
  u64 garb_add = 0ULL;
  u64 irred_add = 0ULL;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    if (!defrag_dirty) {
      u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
      u64 sza = (u64)wvec[((u64)fresh << 1) + 1ULL];
      u64 szb = (u64)wvec[((u64)fs << 1) + 1ULL];
      u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
      u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
      if (wl_c == 0ULL || fresh == fs || wc_c < wl_c || wl_c + na + nb > wc_c ||
          ((wl_c + na) * 4ULL >= wc_c * 3ULL && (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
        defrag_dirty = true;
      }
    }
    u64 br = full_add_bin(h, fresh, fs);
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    fl[fs >> 1] = fl[fs >> 1] | (((fs & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
    fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_P;
    si = si + 1u;
  }
  m = 0u;
  while (m < mn && ok) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      if (!defrag_dirty) {
        u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
        u32 nf = fresh ^ 1u;
        u64 sza = (u64)wvec[((u64)nf << 1) + 1ULL];
        u64 szb = (u64)wvec[((u64)q << 1) + 1ULL];
        u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
        u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
        if (wl_c == 0ULL || nf == q || wc_c < wl_c || wl_c + na + nb > wc_c ||
            ((wl_c + na) * 4ULL >= wc_c * 3ULL && (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      u64 br = full_add_bin(h, fresh ^ 1u, q);
      fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_N;
      fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      if (!defrag_dirty) {
        u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
        u32 nf = fresh ^ 1u;
        u64 sz0 = (u64)wvec[((u64)nf << 1) + 1ULL];
        u64 sum_nw = (sz0 == 0ULL) ? 2ULL : ((sz0 == 1ULL) ? 3ULL : (sz0 << 1));
        u32 dj = 0u;
        while (dj < csz) {
          u32 dl = ar[(u64)c_top + 3ULL + (u64)dj];
          if (dl != flit) {
            u64 szl = (u64)wvec[((u64)dl << 1) + 1ULL];
            sum_nw = sum_nw + ((szl == 0ULL) ? 2ULL : ((szl == 1ULL) ? 3ULL : (szl << 1)));
          }
          dj = dj + 1u;
        }
        if (wl_c == 0ULL || wc_c < wl_c || wl_c + sum_nw > wc_c ||
            ((wl_c + sum_nw) * 4ULL >= wc_c * 3ULL &&
             (wu_c + sum_nw) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr == 0xFFFFFFFFULL) { ok = false; break; }
      u32 *dst_cl = ar + (ncr + 3ULL);
      if ((ncr & 1ULL) != 0ULL) {
        j = 0u;
        while (j + 2u <= tk) {
          u64 *dp = (u64 *)(dst_cl + (u64)j);
          u64 *sp = (u64 *)(tmp + (u64)j);
          dp[0] = sp[0];
          j = j + 2u;
        }
        if (j < tk) { dst_cl[j] = tmp[j]; }
      } else {
        j = 0u;
        while (j < tk) { dst_cl[j] = tmp[j]; j = j + 1u; }
      }
      j = 0u;
      while (j < tk) {
        if (!full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u)) {
          u32 uk = 0u;
          while (uk < j) { full_unwatch_large(h, tmp[uk], (u32)ncr); uk = uk + 1u; }
          ar[ncr] = ar[ncr] | PH_GARB;
          garb_add = garb_add + 3ULL + (u64)tk;
          ok = false; break;
        }
        u32 tv = tmp[j] >> 1;
        fl[tv] = fl[tv] | (((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        j = j + 1u;
      }
      if (ok) { irred_add = irred_add + 1ULL; }
    }
    m = m + 1u;
  }
  if (!ok) {
    if (garb_add > 0ULL) { h->arena_garbage = h->arena_garbage + garb_add; }
    if (irred_add > 0ULL) { h->num_irred = h->num_irred + irred_add; }
    if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
    return false;
  }
  u32 fs_i = best_k;
  while (fs_i > 0u) {
    u32 ro_prev = scr[sc + (fs_i - 1u)];
    u32 po_s = scr[3u * sc + fs_i];
    u32 po_prev = (fs_i > 1u) ? scr[3u * sc + (fs_i - 1u)] : 0u;
    u32 fi = 0u;
    while (fi < mn) {
      u32 fj = scr[po_s + fi];
      if (fs_i > 1u) { scr[po_prev + fi] = scr[po_prev + fj]; }
      scr[ro_prev + fi] = scr[ro_prev + fj];
      fi = fi + 1u;
    }
    scr[2u * sc + (fs_i - 1u)] = mn;
    fs_i = fs_i - 1u;
  }
  u32 qs = best_k + 1u;
  while (qs > 0u) {
    qs = qs - 1u;
    u32 ro = scr[sc + qs];
    u32 fs = scr[qs];
    m = 0u;
    while (m < mn) {
      u32 cs = scr[ro + m];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          full_unwatch_large(h, dl, cs);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB;
        garb_add = garb_add + 3ULL + (u64)csz;
      }
      m = m + 1u;
    }
  }
  if (garb_add > 0ULL) { h->arena_garbage = h->arena_garbage + garb_add; }
  if (irred_add > 0ULL) { h->num_irred = h->num_irred + irred_add; }
  if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
  deg[fresh] = dm; deg[fresh ^ 1u] = mn;
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv) {
  u64 cap = h->scratch_cap;
  u32 sc = full_bva_steps_cap_fid(cap);
  if (h->cur_vars >= h->max_vars || sc == 0u) { return false; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *arena = (u32 *)h->arena;
  u8 *counted = (u8 *)h->lit_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  if (vals[f0] != (i8)0) { return false; }
  u64 init_lits = (init_cv <= h->cur_vars) ? (init_cv << 1) : (h->cur_vars << 1);
  u32 hdr_sz = sc << 2;
  u32 row0_max = (u32)((cap - (u64)hdr_sz) / 3ULL);
  if (row0_max < 2u) { return false; }
  u64 off0 = (u64)wvec[(u64)f0 << 1];
  u64 sz0 = (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 wi = 0ULL;
  u32 r0n = 0u;
  u64 fticks = 0ULL;
  while (wi < sz0 && r0n < row0_max) {
    u32 w0 = wstk[off0 + wi]; wi = wi + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      fticks = fticks + 1ULL;
      u32 other = w0 & PW_LIT_MASK;
      if (vals[other] == (i8)0) {
        scr[hdr_sz + r0n] = w0;
        r0n = r0n + 1u;
      }
    } else if (wi < sz0) {
      u32 cr = wstk[off0 + wi]; wi = wi + 1ULL;
      fticks = fticks + 1ULL;
      u32 csz = arena[(u64)cr + 2ULL];
      u32 cfl = arena[(u64)cr];
      if ((cfl & (PH_GARB | PH_RED)) == 0u && csz >= 3u && csz <= 5u) {
        u32 j = 0u; bool has_f0 = false; bool sat = false;
        while (j < csz) {
          u32 l = arena[(u64)cr + 3ULL + (u64)j];
          if (vals[l] > (i8)0) { sat = true; break; }
          if (l == f0) { has_f0 = true; }
          j = j + 1u;
        }
        if (!sat && has_f0) {
          scr[hdr_sz + r0n] = cr;
          r0n = r0n + 1u;
        }
      }
    }
  }
  h->ant_sz = (h->ant_sz > fticks) ? (h->ant_sz - fticks) : 0ULL;
  if (r0n < 2u) { return false; }
  u64 elim_bound = h->elim_bound;
  scr[0] = f0;
  scr[sc] = hdr_sz;
  scr[2u * sc] = r0n;
  scr[3u * sc] = hdr_sz;
  u32 bump = hdr_sz + r0n;
  counted[f0] = (u8)1;
  u32 step = 1u;
  u32 cur_qn = r0n;
  u32 best_k = 0u;
  u64 best_red = 0ULL;
  while (step < sc && cur_qn >= 2u && h->ant_sz > 0ULL) {
    u32 row_off = scr[sc + step - 1u];
    u32 ncntd = full_bva_scan_cands(h, row_off, cur_qn, init_lits);
    u32 best_lit = full_bva_pick_cand(h, ncntd, f0);
    if (best_lit == 0xFFFFFFFFu || h->ant_sz == 0ULL) { break; }
    u32 rem = (u32)(cap - (u64)bump);
    u32 max_new = rem >> 1;
    if (max_new > cur_qn) { max_new = cur_qn; }
    if (max_new < 2u) { break; }
    u32 nrow_off = bump;
    u32 par_off = bump + max_new;
    cur_qn = full_bva_filter_row(h, row_off, nrow_off, par_off, cur_qn, best_lit);
    if (cur_qn < 2u) { break; }
    scr[step] = best_lit;
    scr[sc + step] = nrow_off;
    scr[2u * sc + step] = cur_qn;
    scr[3u * sc + step] = par_off;
    bump = par_off + cur_qn;
    counted[best_lit] = (u8)1;
    step = step + 1u;
    u64 dm = (u64)step;
    u64 mn = (u64)cur_qn;
    u64 prod = dm * mn;
    u64 sum = dm + mn;
    if (prod > sum) {
      u64 red = prod - sum;
      if (red > elim_bound && red > best_red) {
        best_red = red;
        best_k = step - 1u;
      }
    }
  }
  u32 ci = 0u;
  while (ci < step) {
    counted[scr[ci]] = (u8)0;
    ci = ci + 1u;
  }
  if (best_k == 0u) { return false; }
  h->res_sz = (u64)best_k;
  return full_bva_commit(h, best_k);
}

u32 full_bva_upd_lit_fid(FullHdr *h, u32 *fheap, u32 *fpos,
    u32 *deg, u64 cur_nl, u64 hsz_tl) {
  u32 hsz = (u32)(hsz_tl >> 32);
  u32 tl = (u32)(hsz_tl & 0xFFFFFFFFULL);
  u32 nd = full_bva_count_lit_deg_fid(h, tl);
  u32 od = deg[tl];
  if (nd > 1u) {
    if (nd != od) {
      deg[tl] = nd;
      u32 p = fpos[tl];
      if (p < hsz) {
        if (nd > od) { full_fheap_up_fid(fheap, fpos, deg, p); }
        else { full_fheap_down_fid(fheap, fpos, deg, p, hsz); }
      }
    }
    if (fpos[tl] == 0xFFFFFFFFu && (u64)hsz < cur_nl) {
      fheap[hsz] = tl; fpos[tl] = hsz;
      full_fheap_up_fid(fheap, fpos, deg, hsz);
      hsz = hsz + 1u;
    }
  } else {
    deg[tl] = nd;
    u32 p = fpos[tl];
    if (p < hsz) {
      hsz = hsz - 1u;
      u32 last = fheap[hsz];
      fpos[last] = 0xFFFFFFFFu;
      fpos[tl] = 0xFFFFFFFFu;
      if (p < hsz) {
        fheap[p] = last; fpos[last] = p;
        full_fheap_up_fid(fheap, fpos, deg, p);
        u32 lp = fpos[last];
        if (lp < hsz) { full_fheap_down_fid(fheap, fpos, deg, lp, hsz); }
      }
    }
  }
  return hsz;
}

u64 full_factor(FullHdr *h, u64 budget) {
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (h->cur_vars >= h->max_vars || sc == 0u || budget == 0ULL) {
    return 1ULL;
  }
  full_bva_connect_clauses_fid(h);
  if (h->oom != 0ULL) { return 1ULL; }
  h->ant_sz = budget;
  u64 init_cv = h->cur_vars;
  u64 max_nl = h->max_vars << 1;
  u32 *tmark = (u32 *)h->wsort;
  u32 *fheap = (u32 *)h->tarjan_mark;
  u32 *fpos = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags;
  u32 *deg = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u64 zi = 0ULL;
  while (zi < max_nl) {
    tmark[zi] = 0u; fheap[zi] = 0u; fpos[zi] = 0xFFFFFFFFu;
    zi = zi + 1ULL;
  }
  u32 hsz = 0u;
  u64 v = 0ULL;
  while (v < init_cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 pl = (u32)(v << 1);
      u32 nl = pl | 1u;
      if ((fl[v] & FL_FACT_P) != 0u && deg[pl] > 1u) {
        fheap[hsz] = pl; fpos[pl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
      if ((fl[v] & FL_FACT_N) != 0u && deg[nl] > 1u) {
        fheap[hsz] = nl; fpos[nl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
    }
    v = v + 1ULL;
  }
  while (hsz > 0u && h->cur_vars < h->max_vars && h->ant_sz > 0ULL && h->oom == 0ULL) {
    u32 f0 = fheap[0];
    hsz = hsz - 1u;
    fpos[f0] = 0xFFFFFFFFu;
    if (hsz > 0u) {
      fheap[0] = fheap[hsz];
      fpos[fheap[0]] = 0u;
      full_fheap_down_fid(fheap, fpos, deg, 0u, hsz);
    }
    u32 fv = f0 >> 1;
    u32 fbit = ((f0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    if ((fl[fv] & FL_ACTIVE) == 0u) { continue; }
    if ((fl[fv] & fbit) == 0u) { continue; }
    if (vals[f0] != (i8)0) { continue; }
    fl[fv] = fl[fv] & (~fbit);
    if (deg[f0] <= 1u) { continue; }
    if (full_bva_try_lit(h, f0, init_cv)) {
      u32 *scr_b = (u32 *)h->scratch_buf;
      u32 *ar_b = (u32 *)h->arena;
      u32 sc_b = full_bva_steps_cap_fid(h->scratch_cap);
      u32 bk = (u32)h->res_sz;
      u64 cur_nl = h->cur_vars << 1;
      u8 *tmk = (u8 *)h->lit_mark;
      u32 *tlits = (u32 *)h->work_stk2;
      u64 nt = 0ULL;
      u32 qs_idx = bk + 1u;
      while (qs_idx > 0u) {
        qs_idx = qs_idx - 1u;
        u32 factor = scr_b[qs_idx];
        u32 fneg = factor ^ 1u;
        if ((u64)factor < cur_nl && tmk[factor] == (u8)0 && nt < cur_nl) {
          tmk[factor] = (u8)1; tlits[nt] = factor; nt = nt + 1ULL;
        }
        if ((u64)fneg < cur_nl && tmk[fneg] == (u8)0 && nt < cur_nl) {
          tmk[fneg] = (u8)1; tlits[nt] = fneg; nt = nt + 1ULL;
        }
        u32 ro = scr_b[sc_b + qs_idx];
        u32 qn = scr_b[2u * sc_b + qs_idx];
        u32 qi = 0u;
        while (qi < qn) {
          u32 cw = scr_b[ro + qi];
          if ((cw & PW_BIN_FLAG) != 0u) {
            u32 ol = cw & PW_LIT_MASK;
            if ((u64)ol < cur_nl && tmk[ol] == (u8)0 && nt < cur_nl) {
              tmk[ol] = (u8)1; tlits[nt] = ol; nt = nt + 1ULL;
            }
          } else {
            u32 csz = ar_b[(u64)cw + 2ULL];
            u32 lj = 0u;
            while (lj < csz) {
              u32 l = ar_b[(u64)cw + 3ULL + (u64)lj];
              if (l != factor && (u64)l < cur_nl && tmk[l] == (u8)0 && nt < cur_nl) {
                tmk[l] = (u8)1; tlits[nt] = l; nt = nt + 1ULL;
              }
              lj = lj + 1u;
            }
          }
          qi = qi + 1u;
        }
      }
      u64 ui = 0ULL;
      while (ui < nt) {
        tmk[tlits[ui]] = (u8)0;
        ui = ui + 1ULL;
      }
      ui = 0ULL;
      while (ui < nt) {
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
          ((u64)hsz << 32) | (u64)tlits[ui]);
        ui = ui + 1ULL;
      }
    }
  }
  u64 end_nlits = h->cur_vars << 1;
  u64 ci = 0ULL;
  while (ci < end_nlits) {
    fheap[ci] = 0u; fpos[ci] = 0u;
    ci = ci + 1ULL;
  }
  if (h->cur_vars > init_cv) {
    u64 cv = h->cur_vars;
    u32 *qn = (u32 *)h->q_next;
    u32 *qs = (u32 *)h->q_stamp;
    u64 p = h->q_first;
    u64 s = 0ULL;
    while (p < cv && s < cv) {
      s = s + 1ULL;
      qs[p] = (u32)s;
      p = (u64)qn[p];
    }
    h->q_cur_stamp = s;
    if (h->q_search_idx < cv) {
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  return 1ULL;
}
"

/-- Ordered live functions of `Src/Factor.lean` (`14` fns). -/
def fns : List Fn := factor_fns

end

public section

theorem full_bva_steps_cap_fid_wf : Func.Wf full_bva_steps_cap_fid_body := by kissat_wf_reify
theorem full_bva_clines_fid_wf : Func.Wf full_bva_clines_fid_body := by kissat_wf_reify
theorem full_fheap_up_fid_wf : Func.Wf full_fheap_up_fid_body := by kissat_wf_reify
theorem full_fheap_down_fid_wf : Func.Wf full_fheap_down_fid_body := by kissat_wf_reify
theorem full_bva_count_lit_deg_fid_wf : Func.Wf full_bva_count_lit_deg_fid_body := by
  kissat_wf_reify
theorem full_bva_connect_clauses_fid_wf : Func.Wf full_bva_connect_clauses_fid_body := by
  kissat_wf_reify
theorem full_bva_match_large_bva_fid_wf : Func.Wf full_bva_match_large_bva_fid_body := by
  kissat_wf_reify
theorem full_bva_scan_cands_wf : Func.Wf full_bva_scan_cands_body := by kissat_wf_reify
theorem full_bva_pick_cand_wf : Func.Wf full_bva_pick_cand_body := by kissat_wf_reify
theorem full_bva_filter_row_wf : Func.Wf full_bva_filter_row_body := by kissat_wf_reify
theorem full_bva_commit_wf : Func.Wf full_bva_commit_body := by kissat_wf_reify
theorem full_bva_try_lit_wf : Func.Wf full_bva_try_lit_body := by kissat_wf_reify
theorem full_bva_upd_lit_fid_wf : Func.Wf full_bva_upd_lit_fid_body := by kissat_wf_reify
theorem full_factor_wf : Func.Wf full_factor_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, factor_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bva_steps_cap_fid_wf
  · exact full_bva_clines_fid_wf
  · exact full_fheap_up_fid_wf
  · exact full_fheap_down_fid_wf
  · exact full_bva_count_lit_deg_fid_wf
  · exact full_bva_connect_clauses_fid_wf
  · exact full_bva_match_large_bva_fid_wf
  · exact full_bva_scan_cands_wf
  · exact full_bva_pick_cand_wf
  · exact full_bva_filter_row_wf
  · exact full_bva_commit_wf
  · exact full_bva_try_lit_wf
  · exact full_bva_upd_lit_fid_wf
  · exact full_factor_wf

end

end LeanQbe.T.Examples.Kissat.Src.Factor

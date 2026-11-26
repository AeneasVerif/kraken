/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Sparse Garbage Collection, Rewatching & Reason Marking (`Src/Collect.lean`)

Mirrors upstream `kissat/src/collect.c, trail.c` (`15` live functions, DAG level `L2`):
- `full_lit_rank_m6` (R4: `kissat_collect_lit_rank`)
- `full_sweep_bins_range_m6` (R4: `kissat_flush_binary_watches_range`)
- `full_rewatch_range_m6` (R4: `kissat_rewatch_clauses_range`)
- `full_rewatch_arena_m6` (R4: `kissat_rewatch_arena_impl`)
- `full_sweep_bins_m6cf` (R4: `kissat_flush_binary_watches_impl`)
- `full_sweep_bins` (R4: `kissat_flush_binary_watches`)
- `full_sweep_copy` (R4: `kissat_sparse_sweep_clause`)
- `full_rewatch_arena` (R4: `kissat_rewatch_arena`)
- `full_move_red_pass2_m6` (R4: `kissat_move_redundant_pass2`)
- `full_move_red_end_buf_m6` (R4: `kissat_move_redundant_buffered`)
- `full_move_red_end_m6` (R4: `kissat_move_redundant_clauses_to_end`)
- `full_arena_sweep_m6` (R4: `kissat_sparse_collect_impl`)
- `full_mark_reasons_m6` (R4: `kissat_mark_reason_clauses_impl`)
- `full_arena_sweep` (R4: `kissat_sparse_collect`)
- `full_mark_reasons` (R4: `kissat_mark_reason_clauses`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Collect

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! collect "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag_m6(FullHdr *h);
extern bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_watch_pop_c0(FullHdr *h, u32 lit, u32 cnt);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);

u64 full_lit_rank_m6(i8 *vals, u32 *lvl, u32 l) {
  i8 v = vals[l];
  if (v > (i8)0) { return 0x200000000ULL | (u64)(~lvl[l >> 1]); }
  if (v == (i8)0) { return 0x100000000ULL; }
  return (u64)lvl[l >> 1];
}

void full_sweep_bins_range_m6(FullHdr *h, u64 keep_large_before) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *seen = (u32 *)h->wsort;
  bool prop_done = (h->propagated >= h->trail_end);
  u64 s0 = 0ULL;
  while (s0 < nlits) { seen[s0] = 0xFFFFFFFFu; s0 = s0 + 1ULL; }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    bool lfix = (lvl[l >> 1] == 0u &&
      (vals[l] > (i8)0 || (prop_done && vals[l] < (i8)0)));
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        bool ofix = ((u64)ot < nlits && lvl[ot >> 1] == 0u &&
          (vals[ot] > (i8)0 || (prop_done && vals[ot] < (i8)0)));
        if (lfix || ofix) {
          if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
        } else if (!lfix) {
          if ((u64)ot < nlits && seen[ot] == (u32)l) {
            if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
              h->num_binary = h->num_binary - 1ULL;
            }
          } else {
            if ((u64)ot < nlits) { seen[ot] = (u32)l; }
            wstk[q] = w0; q = q + 1ULL;
          }
        }
        p = p + 1ULL;
      } else {
        if (p + 1ULL < end) {
          u32 cr = wstk[p + 1ULL];
          if (keep_large_before > 0ULL && (u64)cr < keep_large_before) {
            wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL;
          }
        }
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off);
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  full_wstack_defrag_m6(h);
}

bool full_rewatch_range_m6(FullHdr *h, u64 start, u64 dst) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool at_root = (h->cur_level == 0ULL);
  u64 p = start;
  while (p < dst) {
    u32 sz = ar[p + 2ULL];
    if (!at_root && sz >= 3u) {
      u32 i0 = 0u; u64 r0 = full_lit_rank_m6(vals, lvl, ar[p + 3ULL]);
      u32 i = 1u;
      while (i < sz) {
        u64 rk = full_lit_rank_m6(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r0) { r0 = rk; i0 = i; }
        i = i + 1u;
      }
      if (i0 != 0u) {
        u32 t = ar[p + 3ULL]; ar[p + 3ULL] = ar[p + 3ULL + (u64)i0];
        ar[p + 3ULL + (u64)i0] = t;
      }
      u32 i1 = 1u; u64 r1 = full_lit_rank_m6(vals, lvl, ar[p + 4ULL]);
      i = 2u;
      while (i < sz) {
        u64 rk = full_lit_rank_m6(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r1) { r1 = rk; i1 = i; }
        i = i + 1u;
      }
      if (i1 != 1u) {
        u32 t = ar[p + 4ULL]; ar[p + 4ULL] = ar[p + 3ULL + (u64)i1];
        ar[p + 3ULL + (u64)i1] = t;
      }
    }
    ar[p + 1ULL] = 2u;
    u32 l0 = ar[p + 3ULL]; u32 l1 = ar[p + 4ULL];
    if (!full_watch_push_m6(h, l0, l1 & PW_LIT_MASK, (u32)p, 2u) ||
        !full_watch_push_m6(h, l1, l0 & PW_LIT_MASK, (u32)p, 2u)) {
      h->oom = 1ULL; return false;
    }
    p = p + 3ULL + (u64)sz;
  }
  return true;
}

bool full_rewatch_arena_m6(FullHdr *h, u64 dst) {
  return full_rewatch_range_m6(h, 0ULL, dst);
}

void full_sweep_bins_m6cf(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *seen = (u32 *)h->wsort;
  bool prop_done = (h->propagated >= h->trail_end);
  u64 si = 0ULL;
  while (si < nlits) { seen[si] = 0xFFFFFFFFu; si = si + 1ULL; }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) {
      wvec[l << 1] = 0u;
      l = l + 1ULL;
      continue;
    }
    bool lsat = (lvl[l >> 1] == 0u && vals[l] > (i8)0);
    bool lfix = lsat || (prop_done && lvl[l >> 1] == 0u && vals[l] < (i8)0);
    u32 ltag = (u32)l;
    u32 lneg = ltag ^ 1u;
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        bool osat = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] > (i8)0);
        bool ofix = osat ||
          (prop_done && (u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] < (i8)0);
        bool drop = lfix || ofix || ot == lneg ||
          ((u64)ot < nlits && seen[ot] == ltag);
        if (drop) {
          if (l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
        } else {
          if ((u64)ot < nlits) { seen[ot] = ltag; }
          wstk[q] = w0; q = q + 1ULL;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    if (q == off) {
      wvec[l << 1] = 0u;
      wvec[(l << 1) + 1ULL] = 0u;
    } else {
      wvec[(l << 1) + 1ULL] = (u32)(q - off);
    }
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  full_wstack_defrag(h);
}

void full_sweep_bins(FullHdr *h) {
  full_sweep_bins_m6cf(h);
}

u64 full_sweep_copy(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u64 cv = h->cur_vars;
  if (!at_root) {
    u32 i = 0u;
    while (i < old_sz) { ar[dst + 3ULL + (u64)i] = ar[src + 3ULL + (u64)i]; i = i + 1u; }
    return (u64)old_sz;
  }
  bool is_red = (ar[src] & PH_RED) != 0u;
  u32 new_sz = 0u;
  u32 i = 0u;
  while (i < old_sz) {
    u32 lit = ar[src + 3ULL + (u64)i];
    u32 v = lit >> 1;
    if ((u64)v < cv && is_red && (fl[v] & FL_ACTIVE) == 0u) {
      return 0xFFFFFFFFULL;
    }
    if ((u64)v < cv && lvl[v] == 0u && vals[lit] != (i8)0) {
      if (vals[lit] > (i8)0) { return 0xFFFFFFFFULL; }
    } else {
      ar[dst + 3ULL + (u64)new_sz] = lit;
      new_sz = new_sz + 1u;
    }
    i = i + 1u;
  }
  if (new_sz == 0u) { return 0xFFFFFFFEULL; }
  if (new_sz == 1u) {
    u32 ulit = ar[dst + 3ULL];
    if (vals[ulit] < (i8)0) { return 0xFFFFFFFEULL; }
    if (vals[ulit] == (i8)0) { full_assign_lvl(h, ulit, 0xFFFFFFFFu, 0u); return 1ULL; }
    return 0xFFFFFFFFULL;
  }
  if (new_sz == 2u) {
    u32 l0 = ar[dst + 3ULL]; u32 l1 = ar[dst + 4ULL];
    u32 b0 = (l1 & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (l0 & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, l0, b0, 0u, 1u)) { h->oom = 1ULL; return 0xFFFFFFFDULL; }
    if (!full_watch_push(h, l1, b1, 0u, 1u)) {
      full_watch_pop_c0(h, l0, 1u);
      h->oom = 1ULL; return 0xFFFFFFFDULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFFULL;
  }
  return (u64)new_sz;
}

bool full_rewatch_arena(FullHdr *h, u64 dst) {
  return full_rewatch_arena_m6(h, dst);
}

void full_move_red_pass2_m6(FullHdr *h, u64 mid, u64 rlen, u64 dst, u32 *buf) {
  u32 *ar = (u32 *)h->arena;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 rpos = 0ULL;
  while (rpos < rlen) {
    u32 hdr = buf[rpos];
    u32 sz = buf[rpos + 2ULL];
    u64 clen = 3ULL + (u64)sz;
    u64 od = mid + rpos;
    u64 k = 0ULL;
    while (k < clen) { ar[od + k] = buf[rpos + k]; k = k + 1ULL; }
    if ((hdr & PH_RSN) != 0u) {
      u32 v = buf[rpos + 1ULL];
      if ((u64)v < cv) { rsns[v] = (u32)od; }
    }
    ar[od] = hdr & (~PH_RSN);
    ar[od + 1ULL] = 2u;
    rpos = rpos + clen;
  }
  h->first_reducible = (mid < dst) ? mid : 0xFFFFFFFFULL;
}

void full_move_red_end_buf_m6(FullHdr *h, u64 first_red, u64 dst, u32 *buf) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 src = first_red;
  u64 idst = first_red;
  u64 rlen = 0ULL;
  while (src < dst) {
    u32 hdr = ar[src];
    u32 sz = ar[src + 2ULL];
    u64 clen = 3ULL + (u64)sz;
    if ((hdr & PH_RED) != 0u) {
      u64 k = 0ULL;
      while (k < clen) { buf[rlen + k] = ar[src + k]; k = k + 1ULL; }
      if ((hdr & PH_RSN) != 0u) {
        u32 i = 0u;
        bool found = false;
        while (i < sz) {
          u32 lit = ar[src + 3ULL + (u64)i]; u32 v = lit >> 1;
          if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
            buf[rlen + 1ULL] = v; found = true; break;
          }
          i = i + 1u;
        }
        if (!found) { buf[rlen] = hdr & (~PH_RSN); }
      }
      rlen = rlen + clen;
    } else {
      if (idst != src) {
        u64 k = 0ULL;
        while (k < clen) { ar[idst + k] = ar[src + k]; k = k + 1ULL; }
        if ((hdr & PH_RSN) != 0u) {
          u32 i = 0u;
          while (i < sz) {
            u32 lit = ar[idst + 3ULL + (u64)i]; u32 v = lit >> 1;
            if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
              rsns[v] = (u32)idst; break;
            }
            i = i + 1u;
          }
        }
      }
      ar[idst] = hdr & (~PH_RSN);
      idst = idst + clen;
    }
    src = src + clen;
  }
  full_move_red_pass2_m6(h, idst, rlen, dst, buf);
}

void full_move_red_end_m6(FullHdr *h, u64 first_red, u64 dst) {
  u32 *ar = (u32 *)h->arena;
  u64 p = first_red;
  u64 red_words = 0ULL;
  while (p < dst) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    u64 clen = 3ULL + (u64)sz;
    if ((hdr & PH_RED) != 0u) { red_words = red_words + clen; }
    p = p + clen;
  }
  if (red_words == 0ULL) { h->first_reducible = 0xFFFFFFFFULL; return; }
  if (red_words <= h->scratch_cap) {
    full_move_red_end_buf_m6(h, first_red, dst, (u32 *)h->scratch_buf);
    return;
  }
  if (dst + red_words <= h->arena_cap) {
    full_move_red_end_buf_m6(h, first_red, dst, ar + dst);
    return;
  }
  p = first_red;
  while (p < dst) {
    u32 sz = ar[p + 2ULL];
    ar[p] = ar[p] & (~PH_RSN);
    p = p + 3ULL + (u64)sz;
  }
  h->first_reducible = first_red;
}

u64 full_arena_sweep_m6(FullHdr *h) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  bool at_root = (h->cur_level == 0ULL);
  u64 start = 0ULL;
  u64 pre_irred = 0ULL;
  if (!at_root && h->unflushed == 0ULL && h->first_reducible > 0ULL &&
      h->first_reducible < alen) {
    u64 fp = h->first_reducible;
    u64 p = 0ULL;
    u64 cnt = 0ULL;
    bool pre_ok = true;
    while (p < fp) {
      if (p + 3ULL > fp) { pre_ok = false; break; }
      u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
      if ((hdr & (PH_GARB | PH_SHRK | PH_RED)) != 0u || sz < 3u ||
          p + 3ULL + (u64)sz > fp) {
        pre_ok = false; break;
      }
      p = p + 3ULL + (u64)sz;
      cnt = cnt + 1ULL;
    }
    if (pre_ok && p == fp) {
      u64 cp0 = 0ULL;
      while (cp0 < fp) {
        u32 hdr = ar[cp0]; u32 sz = ar[cp0 + 2ULL];
        if ((hdr & PH_RSN) != 0u) { ar[cp0] = hdr & (~PH_RSN); }
        cp0 = cp0 + 3ULL + (u64)sz;
      }
      start = fp;
      pre_irred = cnt;
    }
  }
  full_sweep_bins_range_m6(h, start);
  u64 src = start;
  u64 dst = start;
  u64 first_red = 0xFFFFFFFFULL;
  u64 irred = pre_irred;
  u64 redd = 0ULL;
  bool has_irred_after_red = false;
  bool unsat = false;
  bool new_unit = false;
  while (src < alen) {
    if (src + 3ULL > alen) { break; }
    u32 hdr = ar[src]; u32 old_sz = ar[src + 2ULL];
    u64 nsrc = (u64)full_arena_next(h, (u32)src);
    if ((hdr & PH_GARB) != 0u || old_sz < 3u ||
        src + 3ULL + (u64)old_sz > alen) {
      src = nsrc; continue;
    }
    u64 st = full_sweep_copy(h, src, dst, old_sz, at_root);
    if (st == 0xFFFFFFFEULL) { unsat = true; break; }
    if (st == 0xFFFFFFFDULL) { break; }
    if (st == 1ULL) { new_unit = true; src = nsrc; continue; }
    if (st == 0xFFFFFFFFULL) { src = nsrc; continue; }
    u32 new_sz = (u32)st;
    u32 nhdr = hdr & (~(PH_SHRK | PH_RSN));
    ar[dst] = nhdr;
    ar[dst + 1ULL] = 2u;
    ar[dst + 2ULL] = new_sz;
    if ((hdr & PH_RSN) != 0u) {
      u32 i = 0u;
      while (i < new_sz) {
        u32 lit = ar[dst + 3ULL + (u64)i]; u32 v = lit >> 1;
        if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
          rsns[v] = (u32)dst;
          if (!at_root && (first_red != 0xFFFFFFFFULL || (hdr & PH_RED) != 0u)) {
            ar[dst] = nhdr | PH_RSN;
          }
          break;
        }
        i = i + 1u;
      }
    }
    if ((hdr & PH_RED) != 0u) {
      if (first_red == 0xFFFFFFFFULL) { first_red = dst; }
      redd = redd + 1ULL;
    } else {
      if (first_red != 0xFFFFFFFFULL) { has_irred_after_red = true; }
      irred = irred + 1ULL;
    }
    dst = dst + 3ULL + (u64)new_sz;
    src = nsrc;
  }
  if (!unsat && h->oom == 0ULL && has_irred_after_red && first_red < dst) {
    full_move_red_end_m6(h, first_red, dst);
  } else {
    h->first_reducible = first_red;
    if (!at_root && first_red < dst) {
      u64 cp = first_red;
      while (cp < dst) {
        u32 sz = ar[cp + 2ULL];
        ar[cp] = ar[cp] & (~PH_RSN);
        cp = cp + 3ULL + (u64)sz;
      }
    }
  }
  h->arena_len = dst;
  h->arena_garbage = 0ULL;
  h->num_irred = irred;
  h->num_redundant = redd;
  u32 *ll = (u32 *)h->last_learned;
  u64 li = 0ULL;
  while (li < 16ULL) { ll[li] = 0xFFFFFFFFu; li = li + 1ULL; }
  if (unsat) { return 2ULL; }
  if (h->oom != 0ULL) { return 3ULL; }
  if (!full_rewatch_range_m6(h, start, dst)) { return 3ULL; }
  return new_unit ? 1ULL : 0ULL;
}

void full_mark_reasons_m6(FullHdr *h, bool set_flag) {
  if (h->cur_level == 0ULL) { return; }
  u32 *trl = (u32 *)h->trail;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u32 *ftrl = (u32 *)h->frame_trail;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  u64 i = (u64)ftrl[1];
  while (i < h->trail_end) {
    u32 v = trl[i] >> 1;
    if ((u64)v < cv && lvl[v] > 0u) {
      u32 r = rsns[v];
      if (r < 0x80000000u && (u64)r + 3ULL <= alen) {
        if (set_flag) { ar[r] = ar[r] | PH_RSN; }
        else { ar[r] = ar[r] & (~PH_RSN); }
      }
    }
    i = i + 1ULL;
  }
}

u64 full_arena_sweep(FullHdr *h) {
  return full_arena_sweep_m6(h);
}

void full_mark_reasons(FullHdr *h, bool set_flag) {
  full_mark_reasons_m6(h, set_flag);
}
"

/-- Ordered live functions of `Src/Collect.lean` (`15` fns). -/
def fns : List Fn := collect_fns

end

public section

theorem full_lit_rank_m6_wf : Func.Wf full_lit_rank_m6_body := by kissat_wf_reify
theorem full_sweep_bins_range_m6_wf : Func.Wf full_sweep_bins_range_m6_body := by kissat_wf_reify
theorem full_rewatch_range_m6_wf : Func.Wf full_rewatch_range_m6_body := by kissat_wf_reify
theorem full_rewatch_arena_m6_wf : Func.Wf full_rewatch_arena_m6_body := by kissat_wf_reify
theorem full_sweep_bins_m6cf_wf : Func.Wf full_sweep_bins_m6cf_body := by kissat_wf_reify
theorem full_sweep_bins_wf : Func.Wf full_sweep_bins_body := by kissat_wf_reify
theorem full_sweep_copy_wf : Func.Wf full_sweep_copy_body := by kissat_wf_reify
theorem full_rewatch_arena_wf : Func.Wf full_rewatch_arena_body := by kissat_wf_reify
theorem full_move_red_pass2_m6_wf : Func.Wf full_move_red_pass2_m6_body := by kissat_wf_reify
theorem full_move_red_end_buf_m6_wf : Func.Wf full_move_red_end_buf_m6_body := by kissat_wf_reify
theorem full_move_red_end_m6_wf : Func.Wf full_move_red_end_m6_body := by kissat_wf_reify
theorem full_arena_sweep_m6_wf : Func.Wf full_arena_sweep_m6_body := by kissat_wf_reify
theorem full_mark_reasons_m6_wf : Func.Wf full_mark_reasons_m6_body := by kissat_wf_reify
theorem full_arena_sweep_wf : Func.Wf full_arena_sweep_body := by kissat_wf_reify
theorem full_mark_reasons_wf : Func.Wf full_mark_reasons_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, collect_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact full_lit_rank_m6_wf
  · exact full_sweep_bins_range_m6_wf
  · exact full_rewatch_range_m6_wf
  · exact full_rewatch_arena_m6_wf
  · exact full_sweep_bins_m6cf_wf
  · exact full_sweep_bins_wf
  · exact full_sweep_copy_wf
  · exact full_rewatch_arena_wf
  · exact full_move_red_pass2_m6_wf
  · exact full_move_red_end_buf_m6_wf
  · exact full_move_red_end_m6_wf
  · exact full_arena_sweep_m6_wf
  · exact full_mark_reasons_m6_wf
  · exact full_arena_sweep_wf
  · exact full_mark_reasons_wf

end

end LeanQbe.T.Examples.Kissat.Src.Collect

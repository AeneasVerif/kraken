/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Transitive Binary Implication Reduction (`Src/Transitive.lean`)

Mirrors upstream `kissat/src/transitive.c` (`3` live functions, DAG level `L3`):
- `full_trans_lit_m6` (R4: `kissat_transitive_reduce_literal`)
- `full_trans_sort_m6` (R4: `kissat_transitive_sort_candidates`)
- `full_transitive_m6` (R4: `kissat_transitive_reduction`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Transitive

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! transitive "
#include \"kissat_internal.h\"

extern void full_wstack_defrag(FullHdr *h);
extern void full_delete_bin_side(FullHdr *h, u32 lit, u32 other);
extern bool full_prioritize_binaries_m6(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_propagate(FullHdr *h);

bool full_trans_lit_m6(FullHdr *h, u32 src, bool stop_early) {
  i8 *vals = (i8 *)h->values;
  if (vals[src] != (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *trl = (u32 *)h->trail; u64 nlits = h->cur_vars << 1;
  u64 off = (u64)wvec[(u64)src << 1]; u64 sz = (u64)wvec[((u64)src << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u32 not_src = src ^ 1u; bool failed = false; u64 reduced = 0ULL;
  u64 p = off; u64 end = off + sz;
  while (p < end && !failed && h->ant_sz > 0ULL) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) == 0u) {
      if (stop_early) { break; }
      p = p + 2ULL; continue;
    }
    u32 dst = w0 & PW_LIT_MASK;
    if ((u64)dst >= nlits || dst <= src || vals[dst] != (i8)0) { p = p + 1ULL; continue; }
    u64 ticks = h->ant_sz - 1ULL;
    u64 saved = h->trail_end; u64 prop = saved; bool trans = false;
    vals[not_src] = (i8)1; vals[src] = (i8)(-1); trl[saved] = not_src;
    h->trail_end = saved + 1ULL;
    while (!trans && !failed && prop < h->trail_end && ticks > 0ULL) {
      u32 lit = trl[prop]; prop = prop + 1ULL; u32 nl = lit ^ 1u;
      u64 loff = (u64)wvec[(u64)nl << 1];
      u64 lend = loff + (u64)wvec[((u64)nl << 1) + 1ULL];
      ticks = ticks - 1ULL;
      u64 q = loff;
      while (q < lend) {
        u32 qw = wstk[q];
        if (qw == 0xFFFFFFFFu) { q = q + 1ULL; continue; }
        if ((qw & PW_BIN_FLAG) == 0u) {
          if (stop_early) { break; }
          q = q + 2ULL;
          if (((q - loff) & 15ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
          continue;
        }
        if (nl == src && q == p) { q = q + 1ULL; continue; }
        q = q + 1ULL;
        if (((q - loff) & 15ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
        u32 ot = qw & PW_LIT_MASK;
        if (ot == dst) { trans = true; break; }
        if ((u64)ot < nlits) {
          if (vals[ot] < (i8)0) { failed = true; break; }
          if (vals[ot] == (i8)0 && h->trail_end < h->max_vars) {
            vals[ot] = (i8)1; vals[ot ^ 1u] = (i8)(-1);
            trl[h->trail_end] = ot; h->trail_end = h->trail_end + 1ULL;
          }
        }
      }
    }
    h->ant_sz = ticks;
    while (h->trail_end > saved) {
      h->trail_end = h->trail_end - 1ULL; u32 ul = trl[h->trail_end];
      vals[ul] = (i8)0; vals[ul ^ 1u] = (i8)0;
    }
    if (trans) {
      full_delete_bin_side(h, dst, src);
      wstk[p] = 0xFFFFFFFFu; reduced = reduced + 1ULL;
      h->trans_cnt = h->trans_cnt + 1ULL;
    }
    p = p + 1ULL;
  }
  if (reduced > 0ULL) {
    u64 q = off; p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if (w0 == 0xFFFFFFFFu) { p = p + 1ULL; }
      else if ((w0 & PW_BIN_FLAG) != 0u) { wstk[q] = w0; q = q + 1ULL; p = p + 1ULL; }
      else if (p + 1ULL < end) {
        wstk[q] = w0; wstk[q + 1ULL] = wstk[p + 1ULL]; q = q + 2ULL; p = p + 2ULL;
      } else { p = p + 1ULL; }
    }
    while (q < end) { wstk[q] = 0xFFFFFFFFu; q = q + 1ULL; }
    wvec[((u64)src << 1) + 1ULL] = (u32)((end - off) - reduced);
    h->wusable = h->wusable + reduced;
    if (h->num_binary >= reduced) { h->num_binary = h->num_binary - reduced; }
  }
  if (failed) { h->trans_cnt = h->trans_cnt + 1ULL; return full_add_unit(h, src); }
  return true;
}

void full_trans_sort_m6(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u32 *probes = (u32 *)h->work_stk1;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  bool stab = (h->stable != 0ULL);
  u64 gap = 1ULL;
  u64 n3 = n / 3ULL;
  while (gap < n3) { gap = 3ULL * gap + 1ULL; }
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < n) {
      u32 v = probes[si];
      u64 kv = stab ? sc[v] : (u64)qs[v];
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pv = probes[pj];
        u64 kpv = stab ? sc[pv] : (u64)qs[pv];
        if (kpv > kv || (kpv == kv && pv <= v)) { break; }
        probes[sj] = pv;
        sj = pj;
      }
      probes[sj] = v;
      si = si + 1ULL;
    }
    gap = gap / 3ULL;
  }
}

u64 full_transitive_m6(FullHdr *h, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  if (h->num_binary == 0ULL || tick_lim == 0ULL || cv == 0ULL) {
    h->probing = 0ULL; return 1ULL;
  }
  h->probing = 1ULL;
  bool stop_early = full_prioritize_binaries_m6(h);
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *probes = (u32 *)h->work_stk1;
  u64 pn = 0ULL; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_TRANS)) == (FL_ACTIVE | FL_TRANS) &&
        vals[v << 1] == (i8)0) {
      probes[pn] = (u32)v; pn = pn + 1ULL;
    }
    v = v + 1ULL;
  }
  if (pn > 1ULL) { full_trans_sort_m6(h, pn); }
  h->ant_sz = tick_lim;
  u64 res = 1ULL; u64 pi = 0ULL;
  while (pi < pn && h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u32 pv = probes[pi];
    if ((fl[pv] & FL_ACTIVE) != 0u && vals[(u64)pv << 1] == (i8)0) {
      if (!full_trans_lit_m6(h, pv << 1, stop_early)) { res = 20ULL; break; }
      u64 p0 = full_propagate(h);
      if (p0 == 1ULL) { res = 20ULL; break; }
      if (p0 == 2ULL) { break; }
      if (h->ant_sz == 0ULL || h->oom != 0ULL || h->fuel == 0ULL) { break; }
      if (!full_trans_lit_m6(h, (pv << 1) | 1u, stop_early)) { res = 20ULL; break; }
      u64 p1 = full_propagate(h);
      if (p1 == 1ULL) { res = 20ULL; break; }
      if (p1 == 2ULL) { break; }
      if (h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
        fl[pv] = fl[pv] & (~FL_TRANS);
      }
    } else {
      fl[pv] = fl[pv] & (~FL_TRANS);
    }
    pi = pi + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
  h->probing = 0ULL;
  return res;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Transitive

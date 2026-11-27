/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Equivalence Substitution & Tarjan SCC (`Src/Substitute.lean`)

Mirrors upstream `kissat/src/substitute.c` (`6` live functions, DAG level `L3`):
- `full_tarjan_pop_scc` (R4: `kissat_tarjan_pop_scc`)
- `full_tarjan_scc` (R4: `kissat_determine_representatives`)
- `full_subst_elim_vars` (R4: `kissat_substitute_eliminate_vars`)
- `full_subst_rewrite_bins` (R4: `kissat_substitute_binaries`)
- `full_subst_rewrite_ar` (R4: `kissat_substitute_clauses`)
- `full_substitute` (R4: `kissat_substitute`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Substitute

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! substitute "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern u64 full_propagate(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);

bool full_tarjan_pop_scc(FullHdr *h, u32 root_lit, u32 lit, u32 mark_root) {
  u32 *scc = (u32 *)h->work_stk1; u32 *repr = (u32 *)h->repr;
  u32 *trc = (u32 *)h->tarjan_reach; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *units = (u32 *)h->shrink_stk;
  u64 scc_top = h->tmp_cnt;
  u64 k = scc_top;
  u32 min_lit = lit;
  while (k > 0ULL) {
    k = k - 1ULL; u32 x = scc[k];
    if (x < min_lit) { min_lit = x; }
    if (x == lit) { break; }
  }
  bool failed = (mark_root == 0xFFFFFFFFu);
  u64 j = k;
  while (j < scc_top) {
    u32 other = scc[j]; repr[other] = min_lit; trc[other] = 0xFFFFFFFFu;
    u32 ro = repr[other ^ 1u];
    if (ro == min_lit) {
      if (h->res_sz < h->max_vars) { units[h->res_sz] = min_lit; h->res_sz = h->res_sz + 1ULL; }
      h->inconsistent = 1ULL; break;
    }
    if (ro != 0xFFFFFFFFu && !failed && mark_root <= tmk[other ^ 1u]) {
      if (h->res_sz < h->max_vars) {
        units[h->res_sz] = root_lit ^ 1u; h->res_sz = h->res_sz + 1ULL;
      }
      failed = true;
    }
    j = j + 1ULL;
  }
  h->tmp_cnt = k;
  return failed;
}

u64 full_tarjan_scc(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach; u32 *scc = (u32 *)h->work_stk1;
  u32 *dv = (u32 *)h->work_stk2; u32 *dpos = (u32 *)h->wsort;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *fl = (u32 *)h->flags;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = 0xFFFFFFFFu; tmk[i] = 0u; trc[i] = 0u; i = i + 1ULL; }
  u32 reached = 0u; h->tmp_cnt = 0ULL; h->res_sz = 0ULL;
  u64 root = 0ULL;
  while (root < nlits && h->inconsistent == 0ULL) {
    if (tmk[root] == 0u && (fl[root >> 1] & FL_ACTIVE) != 0u) {
      bool failed = false; u32 mroot = reached + 1u;
      u64 dsp = 1ULL; dv[0] = (u32)root; dpos[0] = 0u;
      reached = reached + 1u; tmk[root] = reached; trc[root] = reached;
      scc[h->tmp_cnt] = (u32)root; h->tmp_cnt = h->tmp_cnt + 1ULL;
      while (dsp > 0ULL && h->inconsistent == 0ULL) {
        u32 lit = dv[dsp - 1ULL]; u32 nl = lit ^ 1u; u32 pos = dpos[dsp - 1ULL];
        u64 off = (u64)wvec[(u64)nl << 1]; u32 sz = wvec[((u64)nl << 1) + 1ULL];
        if (pos < sz) {
          u32 w0 = wstk[off + (u64)pos];
          if ((w0 & PW_BIN_FLAG) == 0u) { dpos[dsp - 1ULL] = pos + 2u; continue; }
          dpos[dsp - 1ULL] = pos + 1u;
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && (fl[ot >> 1] & FL_ACTIVE) != 0u) {
            if (tmk[ot] == 0u) {
              reached = reached + 1u; tmk[ot] = reached; trc[ot] = reached;
              scc[h->tmp_cnt] = ot; h->tmp_cnt = h->tmp_cnt + 1ULL;
              dv[dsp] = ot; dpos[dsp] = 0u; dsp = dsp + 1ULL;
            } else if (trc[ot] < trc[lit]) {
              trc[lit] = trc[ot];
            }
          }
          continue;
        }
        u32 rlit = trc[lit];
        dsp = dsp - 1ULL;
        if (rlit != tmk[lit]) {
          trc[lit] = rlit;
          if (dsp > 0ULL) {
            u32 par = dv[dsp - 1ULL];
            if (rlit < trc[par]) { trc[par] = rlit; }
          }
        } else {
          u32 mr = failed ? 0xFFFFFFFFu : mroot;
          if (full_tarjan_pop_scc(h, (u32)root, lit, mr)) { failed = true; }
        }
      }
    }
    root = root + 1ULL;
  }
  i = 0ULL;
  while (i < nlits) {
    if (repr[i] == 0xFFFFFFFFu) { repr[i] = (u32)i; }
    tmk[i] = 0u; trc[i] = 0u; i = i + 1ULL;
  }
  return h->res_sz;
}

bool full_subst_elim_vars(FullHdr *h, u64 ucnt) {
  u32 *units = (u32 *)h->shrink_stk;
  u64 k = 0ULL;
  while (k < ucnt) {
    if (!full_add_unit(h, units[k])) { return false; }
    k = k + 1ULL;
  }
  if (full_propagate(h) == 1ULL || h->inconsistent != 0ULL) { return false; }
  u32 *repr = (u32 *)h->repr; u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u) {
      u32 lit = (u32)(v << 1); u32 rep = repr[lit];
      if (rep != lit) {
        if (h->extend_len + 4ULL <= h->extend_cap) {
          full_extend_push2(h, lit ^ 1u, rep);
          full_extend_push2(h, lit, rep ^ 1u);
          full_set_inactive(h, (u32)v, FL_SUBST);
          h->subst_cnt = h->subst_cnt + 1ULL;
        } else {
          repr[lit] = lit; repr[lit ^ 1u] = lit ^ 1u;
        }
      }
    }
    v = v + 1ULL;
  }
  return true;
}

bool full_subst_rewrite_bins(FullHdr *h) {
  if (h->oom != 0ULL) { return true; }
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u8 *lm = (u8 *)h->lit_mark;
  u32 *pa = (u32 *)h->work_stk1; u32 *pb = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    u32 rl = repr[l]; u64 pn = 0ULL; bool ovf = false;
    u64 p = off; u64 q = off; u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) == 0u) {
        if (p < end) { wstk[q] = w0; wstk[q + 1ULL] = wstk[p]; q = q + 2ULL; p = p + 1ULL; }
        continue;
      }
      u32 ot = w0 & PW_LIT_MASK; u32 rot = ((u64)ot < nlits) ? repr[ot] : ot;
      if (rl == (u32)l && rot == ot) {
        if ((lm[ot] & (u8)1) == (u8)0) {
          lm[ot] = lm[ot] | (u8)1; wstk[q] = w0; q = q + 1ULL;
        } else if (l < (u64)ot && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
      } else {
        if (l < (u64)ot) {
          if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
          if (rl != (rot ^ 1u)) {
            if ((u64)rot < nlits) {
              if ((lm[rot] & (u8)2) == (u8)0) {
                if (pn < nlits) {
                  lm[rot] = lm[rot] | (u8)2; pa[pn] = rl; pb[pn] = rot; pn = pn + 1ULL;
                } else { ovf = true; }
              }
            } else { ovf = true; }
          }
        }
      }
    }
    u64 c = off;
    while (c < q) {
      if ((wstk[c] & PW_BIN_FLAG) != 0u) { lm[wstk[c] & PW_LIT_MASK] = (u8)0; }
      c = c + 1ULL;
    }
    c = 0ULL;
    while (c < pn) { lm[pb[c]] = (u8)0; c = c + 1ULL; }
    c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off); h->wusable = h->wusable + (end - q);
    if (ovf) { h->oom = 1ULL; return true; }
    c = 0ULL;
    while (c < pn) {
      if (pa[c] == pb[c]) { if (!full_add_unit(h, pa[c])) { return false; } }
      else {
        u64 br = full_add_bin(h, pa[c], pb[c]);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
      c = c + 1ULL;
    }
    l = l + 1ULL;
  }
  return true;
}

bool full_subst_rewrite_ar(FullHdr *h) {
  if (h->oom != 0ULL) { return true; }
  u32 *ar = (u32 *)h->arena; u32 *repr = (u32 *)h->repr;
  u8 *lm = (u8 *)h->lit_mark; u64 nlits = h->cur_vars << 1;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) != 0u || sz < 3u) { p = np; continue; }
    bool chg = false; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k];
      if ((u64)l < nlits && repr[l] != l) { chg = true; break; }
      k = k + 1u;
    }
    if (!chg) { p = np; continue; }
    bool taut = false; u32 nsz = 0u; k = 0u;
    while (k < sz) {
      u32 rl = repr[ar[p + 3ULL + (u64)k]];
      if (lm[rl ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rl] == (u8)0) { lm[rl] = (u8)1; ar[p + 3ULL + (u64)nsz] = rl; nsz = nsz + 1u; }
      k = k + 1u;
    }
    k = 0u; while (k < nsz) { lm[ar[p + 3ULL + (u64)k]] = (u8)0; k = k + 1u; }
    if (taut || nsz <= 2u) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
      if (!taut && nsz == 1u && !full_add_unit(h, ar[p + 3ULL])) { return false; }
      if (!taut && nsz == 2u) {
        u64 br = full_add_bin(h, ar[p + 3ULL], ar[p + 4ULL]);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
    } else if (nsz < sz) {
      ar[p + 2ULL] = nsz; ar[p + 1ULL] = 2u;
      if ((hdr & PH_SHRK) == 0u) {
        ar[p] = hdr | PH_SHRK; ar[p + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
      }
    }
    p = np;
  }
  return true;
}

u64 full_substitute(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->num_binary == 0ULL || h->oom != 0ULL) { return 1ULL; }
  u64 round = 0ULL;
  while (round < 2ULL && h->inconsistent == 0ULL && h->oom == 0ULL) {
    u64 before = h->subst_cnt;
    u64 ucnt = full_tarjan_scc(h);
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (!full_subst_elim_vars(h, ucnt)) { return 20ULL; }
    if (ucnt == 0ULL && h->subst_cnt == before) { break; }
    if (!full_subst_rewrite_bins(h)) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    if (!full_subst_rewrite_ar(h)) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL || h->oom != 0ULL) { return 1ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    round = round + 1ULL;
  }
  return 1ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Substitute

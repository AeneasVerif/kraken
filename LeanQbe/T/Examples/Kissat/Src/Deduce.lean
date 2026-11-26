/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 1-UIP Conflict Deduction & On-the-Fly Strengthening (OTFS) (`Src/Deduce.lean`)

Mirrors upstream `kissat/src/deduce.c, strengthen.c` (`10` live functions, DAG level `L1`):
- `full_analyze_lit` (R4: `kissat_analyze_literal`)
- `full_analyze_rsn` (R4: `kissat_analyze_reason_basic`)
- `full_analyze_rsn_m6_hdr` (R4: `kissat_analyze_reason`)
- `full_clear_ana` (R4: `kissat_reset_analyzed`)
- `full_otfs_large` (R4: `kissat_large_on_the_fly_strengthen`)
- `full_otfs_bin` (R4: `kissat_binary_on_the_fly_strengthen`)
- `full_otfs_subsume` (R4: `kissat_on_the_fly_subsume`)
- `full_deduce_1uip_m6` (R4: `kissat_deduce_first_uip_basic_impl`)
- `full_deduce_1uip` (R4: `kissat_deduce_first_uip_basic`)
- `full_deduce_1uip_m6_hdr` (R4: `kissat_deduce_first_uip_clause`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Deduce

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! deduce "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void m6_hdr_record_used(FullHdr *h, u64 glue);

bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var) {
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ana = (u32 *)h->work_stk1;
  u32 cur_lvl = (u32)h->cur_level;
  u32 v = l >> 1;
  if ((u64)v >= h->cur_vars) { return false; }
  u32 vlvl = lvl[v];
  if (vlvl == 0u) { return true; }
  if (vlvl > cur_lvl) { return false; }
  h->ant_sz = h->ant_sz + 1ULL;
  if (v != skip_var && mrk[v] == (u8)0) {
    mrk[v] = (u8)1;
    if (h->min_clr_len < h->cur_vars) {
      ana[h->min_clr_len] = v;
      h->min_clr_len = h->min_clr_len + 1ULL;
    }
    h->res_sz = h->res_sz + 1ULL;
    if (vlvl == cur_lvl) {
      h->tmp_cnt = h->tmp_cnt + 1ULL;
    } else {
      if (h->tmp_len >= h->cur_vars) { return false; }
      tmp[h->tmp_len] = l;
      h->tmp_len = h->tmp_len + 1ULL;
    }
  }
  return true;
}

bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    if (glue > 1ULL) {
      u64 lim = glue - 1ULL;
      if (lim > h->tier2) { lim = h->tier2; }
      if (lim > 32ULL) { lim = 32ULL; }
      u32 *lv = (u32 *)h->level;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL; u64 lo = 0ULL; bool more = true;
      while (more && ng <= lim) {
        u64 best = 0xFFFFFFFFFFFFFFFFULL; u32 k = 0u;
        while (k < sz) {
          u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
          if (kv < cv) {
            u64 kl = (u64)lv[kv];
            if (kl >= lo && kl < best) { best = kl; }
          }
          k = k + 1u;
        }
        if (best == 0xFFFFFFFFFFFFFFFFULL) { more = false; }
        else { ng = ng + 1ULL; lo = best + 1ULL; }
      }
      if (!more && ng > 0ULL && ng < glue) {
        hdr = (hdr & (~PH_GLUE_MASK)) | (u32)ng;
        ar[rsn] = hdr;
        glue = ng;
      }
    }
    u32 *gu = (u32 *)h->glue_used;
    if (glue < 36ULL) {
      if (gu[glue] < 0xFFFFFFFFu) { gu[glue] = gu[glue] + 1u; }
    }
    u32 old_u = (hdr >> 27) & 31u;
    if (31u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (31u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

bool full_analyze_rsn_m6_hdr(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    if (glue > 1ULL) {
      u64 lim = glue - 1ULL;
      u32 *lv = (u32 *)h->level;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL; u64 lo = 0ULL; bool more = true;
      while (more && ng <= lim) {
        u64 best = 0xFFFFFFFFFFFFFFFFULL; u32 k = 0u;
        while (k < sz) {
          u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
          if (kv < cv) {
            u64 kl = (u64)lv[kv];
            if (kl >= lo && kl < best) { best = kl; }
          }
          k = k + 1u;
        }
        if (best == 0xFFFFFFFFFFFFFFFFULL) { more = false; }
        else { ng = ng + 1ULL; lo = best + 1ULL; }
      }
      if (!more && ng > 0ULL && ng < glue) {
        hdr = (hdr & (~PH_GLUE_MASK)) | (u32)ng;
        ar[rsn] = hdr;
        glue = ng;
      }
    }
    if (h->probing == 0ULL) { m6_hdr_record_used(h, glue); }
    u32 old_u = (hdr >> 27) & 31u;
    if (31u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (31u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

void full_clear_ana(FullHdr *h) {
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u64 cv = h->cur_vars;
  u64 i = 0ULL;
  while (i < h->min_clr_len) {
    u32 v = ana[i];
    if ((u64)v < cv) { mrk[v] = (u8)0; }
    i = i + 1ULL;
  }
  h->min_clr_len = 0ULL;
}

bool full_otfs_large(FullHdr *h, u32 cref, u32 uip) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u64 cb = (u64)cref + 3ULL;
  u32 l0 = ar[cb]; u32 l1 = ar[cb + 1ULL];
  if (l0 == uip) { l0 = l1; }
  else if (l1 != uip) { return false; }
  u32 old_sz = ar[(u64)cref + 2ULL];
  u32 cnt = 1u; u32 i = 2u;
  while (i < old_sz) {
    if (lvl[ar[cb + (u64)i] >> 1] > 0u) {
      cnt = cnt + 1u;
      if (cnt >= 3u) { break; }
    }
    i = i + 1u;
  }
  if (cnt < 3u) { return false; }
  u32 hl_pre = 0u; u32 nl1_pre = uip;
  i = 2u;
  while (i < old_sz) {
    u32 ot = ar[cb + (u64)i];
    u32 cl = lvl[ot >> 1];
    if (cl > hl_pre) { hl_pre = cl; nl1_pre = ot; }
    i = i + 1u;
  }
  if (h->wcap - h->wlen < 2ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
  }
  if (!full_watch_push(h, nl1_pre, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL; return false;
  }
  ar[cb] = l0; ar[cb + 1ULL] = uip;
  full_unwatch_large(h, uip, cref);
  u32 new_sz = 1u; u32 hp = 1u; u32 hl = 0u;
  i = 2u;
  while (i < old_sz) {
    u32 ot = ar[cb + (u64)i];
    u32 cl = lvl[ot >> 1];
    if (cl > 0u) {
      ar[cb + (u64)new_sz] = ot;
      if (cl > hl) { hl = cl; hp = new_sz; }
      new_sz = new_sz + 1u;
    }
    i = i + 1u;
  }
  u32 hdr = ar[cref];
  ar[(u64)cref + 2ULL] = new_sz; ar[(u64)cref + 1ULL] = 2u;
  if ((hdr & PH_SHRK) == 0u) {
    ar[cref] = hdr | PH_SHRK;
    ar[cb + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
  }
  if (hp != 1u) {
    u32 t = ar[cb + 1ULL]; ar[cb + 1ULL] = ar[cb + (u64)hp];
    ar[cb + (u64)hp] = t;
  }
  u32 nl1 = ar[cb + 1ULL];
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  if ((cref & PW_BIN_FLAG) == 0u) {
    u64 off = (u64)wvec[(u64)l0 << 1];
    u64 sz = (u64)wvec[((u64)l0 << 1) + 1ULL];
    if (sz >= 2ULL) {
      u64 p = off + sz;
      u64 off2 = off + 2ULL;
      while (p >= off2) {
        u32 w = wstk[p - 1ULL];
        if (w == cref) { wstk[p - 2ULL] = nl1 & PW_LIT_MASK; break; }
        p = p - 2ULL + (u64)(w >> 31);
      }
    }
  }
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

bool full_otfs_bin(FullHdr *h, u32 cref, u32 uip) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 old_sz = ar[(u64)cref + 2ULL];
  u32 f0 = 0xFFFFFFFFu; u32 f1 = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < old_sz) {
    u32 ot = ar[(u64)cref + 3ULL + (u64)i];
    if (ot != uip && lvl[ot >> 1] > 0u) {
      if (f0 == 0xFFFFFFFFu) { f0 = ot; } else { f1 = ot; break; }
    }
    i = i + 1u;
  }
  if (f0 == 0xFFFFFFFFu || f1 == 0xFFFFFFFFu) { return false; }
  bool has_bin = false;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 sa = (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 sb = (u64)wvec[((u64)f1 << 1) + 1ULL];
  u32 src = (sa <= sb) ? f0 : f1;
  u32 tgt = (sa <= sb) ? f1 : f0;
  u64 p = (u64)wvec[(u64)src << 1];
  u64 pend = p + (u64)wvec[((u64)src << 1) + 1ULL];
  while (p < pend) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if ((w0 & PW_LIT_MASK) == tgt) { has_bin = true; break; }
      p = p + 1ULL;
    } else {
      p = p + 2ULL;
    }
  }
  if (!has_bin) {
    if (h->wcap - h->wlen < 2ULL) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
    }
    u32 b0 = (f1 & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (f0 & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, f0, b0, 0u, 1u) ||
        !full_watch_push(h, f1, b1, 0u, 1u)) {
      h->oom = 1ULL; return false;
    }
    h->num_binary = h->num_binary + 1ULL;
  }
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u64 gsz = (u64)full_arena_next(h, cref) - (u64)cref;
  ar[cref] = ar[cref] | PH_GARB;
  h->arena_garbage = h->arena_garbage + gsz;
  h->confl_type = 1ULL; h->confl_lit0 = (u64)f0; h->confl_lit1 = (u64)f1;
  h->confl_ref = 0xFFFFFFFFULL;
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

void full_otfs_subsume(FullHdr *h, u32 new_confl, u64 old_ctype, u64 old_cref, bool to_bin) {
  if (old_ctype != 2ULL || old_cref == 0xFFFFFFFFULL) { return; }
  u32 *ar = (u32 *)h->arena;
  u32 dhdr = ar[old_cref];
  if ((dhdr & PH_GARB) != 0u) { return; }
  ar[old_cref] = dhdr | PH_GARB;
  h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[old_cref + 2ULL];
  if ((dhdr & PH_RED) != 0u) {
    if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    if (!to_bin) {
      u32 chdr = ar[new_confl];
      if ((chdr & PH_RED) != 0u) {
        u32 cg = chdr & PH_GLUE_MASK;
        u32 dg = dhdr & PH_GLUE_MASK;
        if (cg > dg) { ar[new_confl] = (chdr & (~PH_GLUE_MASK)) | dg; }
      }
    }
  } else {
    if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    if (!to_bin && (ar[new_confl] & PH_RED) != 0u) {
      ar[new_confl] = ar[new_confl] & (~PH_RED);
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
      h->num_irred = h->num_irred + 1ULL;
    }
  }
}

u64 full_deduce_1uip_m6(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  u64 tcnt = h->tmp_cnt;
  if (!seed_ok || tcnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (tcnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= cv) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      tcnt = tcnt - 1ULL;
      h->tmp_cnt = tcnt;
      if (tcnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      tcnt = h->tmp_cnt;
      u64 rsz = h->res_sz;
      if (rsz > 0ULL) { rsz = rsz - 1ULL; h->res_sz = rsz; }
      u64 asz = h->ant_sz;
      if (asz >= 3ULL && rsz < asz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (asz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            u32 *ar = (u32 *)h->arena;
            bool rsn_red = ((ar[rsn] & PH_RED) != 0u);
            if (rsn_red) {
              if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
            } else {
              if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
            }
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}

u64 full_deduce_1uip(FullHdr *h) {
  return full_deduce_1uip_m6(h);
}

u64 full_deduce_1uip_m6_hdr(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn_m6_hdr(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  u64 tcnt = h->tmp_cnt;
  if (!seed_ok || tcnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (tcnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= cv) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      tcnt = tcnt - 1ULL;
      h->tmp_cnt = tcnt;
      if (tcnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn_m6_hdr(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      tcnt = h->tmp_cnt;
      u64 rsz = h->res_sz;
      if (rsz > 0ULL) { rsz = rsz - 1ULL; h->res_sz = rsz; }
      u64 asz = h->ant_sz;
      if (asz >= 3ULL && rsz < asz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (asz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            u32 *ar = (u32 *)h->arena;
            bool rsn_red = ((ar[rsn] & PH_RED) != 0u);
            if (rsn_red) {
              if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
            } else {
              if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
            }
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}
"

/-- Ordered live functions of `Src/Deduce.lean` (`10` fns). -/
def fns : List Fn := deduce_fns

end

public section

theorem full_analyze_lit_wf : Func.Wf full_analyze_lit_body := by kissat_wf_reify
theorem full_analyze_rsn_wf : Func.Wf full_analyze_rsn_body := by kissat_wf_reify
theorem full_analyze_rsn_m6_hdr_wf : Func.Wf full_analyze_rsn_m6_hdr_body := by kissat_wf_reify
theorem full_clear_ana_wf : Func.Wf full_clear_ana_body := by kissat_wf_reify
theorem full_otfs_large_wf : Func.Wf full_otfs_large_body := by kissat_wf_reify
theorem full_otfs_bin_wf : Func.Wf full_otfs_bin_body := by kissat_wf_reify
theorem full_otfs_subsume_wf : Func.Wf full_otfs_subsume_body := by kissat_wf_reify
theorem full_deduce_1uip_m6_wf : Func.Wf full_deduce_1uip_m6_body := by kissat_wf_reify
theorem full_deduce_1uip_wf : Func.Wf full_deduce_1uip_body := by kissat_wf_reify
theorem full_deduce_1uip_m6_hdr_wf : Func.Wf full_deduce_1uip_m6_hdr_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, deduce_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_analyze_lit_wf
  · exact full_analyze_rsn_wf
  · exact full_analyze_rsn_m6_hdr_wf
  · exact full_clear_ana_wf
  · exact full_otfs_large_wf
  · exact full_otfs_bin_wf
  · exact full_otfs_subsume_wf
  · exact full_deduce_1uip_m6_wf
  · exact full_deduce_1uip_wf
  · exact full_deduce_1uip_m6_hdr_wf

end

end LeanQbe.T.Examples.Kissat.Src.Deduce

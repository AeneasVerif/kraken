/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Clause Vivification & Watch Sorting (`Src/Vivify.lean`)

Mirrors upstream `kissat/src/vivify.c` (`28` live functions, DAG level `L3`):
- `full_viv_unreason_m6` (R4: `kissat_vivify_unreason`)
- `full_viv_watch_rank_m6` (R4: `kissat_vivify_watch_rank`)
- `full_viv_best_watch_m6` (R4: `kissat_vivify_best_watch`)
- `full_viv_simplify_m6` (R4: `kissat_vivify_simplify`)
- `full_viv_commit_m6` (R4: `kissat_vivify_commit`)
- `full_viv_mark_garb_m6` (R4: `kissat_vivify_mark_garbage`)
- `full_viv_subsumes_bin_m6` (R4: `kissat_vivify_subsumes_binary`)
- `full_viv_subsumes_cl_m6` (R4: `kissat_vivify_subsumes_clause`)
- `full_viv_deduce_m6` (R4: `kissat_vivify_deduce`)
- `full_viv_best_implied_m6` (R4: `kissat_vivify_best_implied`)
- `full_viv_reestablish_m6` (R4: `kissat_vivify_reestablish`)
- `full_viv_inst_check_m6` (R4: `kissat_vivify_instantiate_check`)
- `full_viv_inst_m6` (R4: `kissat_vivify_instantiate`)
- `full_viv_finish_m6` (R4: `kissat_vivify_finish`)
- `full_viv_sift_counts_m6` (R4: `kissat_vivify_sift_counts`)
- `full_viv_sort_counts_m6` (R4: `kissat_vivify_sort_by_counts`)
- `full_viv_has_l0_m6` (R4: `kissat_vivify_has_root_lit`)
- `full_viv_l0_simp_m6` (R4: `kissat_vivify_root_simplify`)
- `full_viv_reuse_prefix_m6` (R4: `kissat_vivify_reuse_prefix`)
- `full_viv_clause_m6` (R4: `kissat_vivify_clause`)
- `full_viv_tier_match_m6` (R4: `kissat_vivify_tier_match`)
- `full_viv_clear_tier_m6` (R4: `kissat_vivify_clear_tier`)
- `full_viv_collect_fid` (R4: `kissat_vivify_collect`)
- `full_viv_count_fid` (R4: `kissat_vivify_count`)
- `full_viv_sort2_fid` (R4: `kissat_vivify_sort_sift`)
- `full_viv_sort_fid` (R4: `kissat_vivify_sort_schedule`)
- `full_vivify_tier_m6_hdr` (R4: `kissat_vivify_tier`)
- `full_vivify_m6_hdr` (R4: `kissat_vivify`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Vivify

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! vivify "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_add_bin_m6(FullHdr *h, u32 a, u32 b);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);
extern u64 m6_hdr_get_tier1(FullHdr *h, bool vivify_mode);
extern u64 m6_hdr_get_tier2(FullHdr *h, bool vivify_mode);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref);
extern u64 full_propagate(FullHdr *h);

void full_viv_unreason_m6(FullHdr *h, u32 cref) {
  if (h->cur_level == 0ULL) { return; }
  u32 *trl = (u32 *)h->trail;
  u32 *rsns = (u32 *)h->reason;
  u64 te = h->trail_end;
  u64 i = 0ULL;
  while (i < te) {
    u32 rsn = rsns[trl[i] >> 1];
    if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) == 0u && rsn == cref) {
      full_backtrack(h, 0ULL);
      return;
    }
    i = i + 1ULL;
  }
}

u64 full_viv_watch_rank_m6(FullHdr *h, u32 lit) {
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  i8 v = vals[lit];
  if (v > (i8)0) { return 0x200000000ULL + (0xFFFFFFFFULL - (u64)lvl[lit >> 1]); }
  if (v == (i8)0) { return 0x100000000ULL; }
  return (u64)lvl[lit >> 1];
}

void full_viv_best_watch_m6(FullHdr *h, u32 olen) {
  u32 *out = (u32 *)h->work_stk2;
  u32 pos = 0u;
  while (pos < 2u && pos < olen) {
    u32 best = pos;
    u64 brank = full_viv_watch_rank_m6(h, out[pos]);
    u32 k = pos + 1u;
    while (k < olen) {
      u64 r = full_viv_watch_rank_m6(h, out[k]);
      if (r > brank) { best = k; brank = r; }
      k = k + 1u;
    }
    if (best != pos) {
      u32 tmp = out[pos];
      out[pos] = out[best];
      out[best] = tmp;
    }
    pos = pos + 1u;
  }
}

u64 full_viv_simplify_m6(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u32 hdr = ar[cref]; u32 old_sz = ar[(u64)cref + 2ULL];
  u32 k = 0u; u32 i = 0u;
  while (i < old_sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[lit] > (i8)0) {
      full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
      full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
      if ((hdr & PH_RED) != 0u) {
        if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
      } else {
        if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
      }
      return 1ULL;
    }
    if (vals[lit] == (i8)0) { k = k + 1u; }
    i = i + 1u;
  }
  if (k == old_sz) { return 0ULL; }
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u32 nsz = 0u; i = 0u;
  while (i < old_sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[lit] == (i8)0) { ar[(u64)cref + 3ULL + (u64)nsz] = lit; nsz = nsz + 1u; }
    i = i + 1u;
  }
  if (nsz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
  if (nsz == 1u) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    if ((hdr & PH_RED) != 0u) {
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    } else {
      if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    }
    return full_add_unit(h, ar[(u64)cref + 3ULL]) ? 1ULL : 20ULL;
  }
  if (nsz == 2u) {
    u64 br = full_add_bin_m6(h, ar[(u64)cref + 3ULL], ar[(u64)cref + 4ULL]);
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    if ((hdr & PH_RED) != 0u) {
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    } else {
      if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    }
    if (br == 20ULL) { return 20ULL; }
    if (br == 2ULL) { return 2ULL; }
    return 1ULL;
  }
  ar[(u64)cref + 2ULL] = nsz; ar[(u64)cref + 1ULL] = 2u;
  u32 nhdr = hdr;
  if ((nhdr & PH_RED) != 0u) {
    u32 glue = nhdr & PH_GLUE_MASK;
    if (glue >= nsz) {
      nhdr = (nhdr & (~PH_GLUE_MASK)) | ((nsz - 1u) & PH_GLUE_MASK);
    }
  }
  if ((nhdr & PH_SHRK) == 0u) {
    ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
    nhdr = nhdr | PH_SHRK;
  }
  ar[cref] = nhdr;
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, cref, 2u) ||
      !full_watch_push(h, l1, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL; return 2ULL;
  }
  return 0ULL;
}

u64 full_viv_commit_m6(FullHdr *h, u32 cref, u32 olen, u32 implied) {
  u32 *ar = (u32 *)h->arena; u32 *out = (u32 *)h->work_stk2;
  u32 hdr = ar[cref]; u32 old_sz = ar[(u64)cref + 2ULL];
  if (olen >= old_sz) { return 1ULL; }
  h->viv_cnt = h->viv_cnt + 1ULL;
  if (olen == 0u) {
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (olen <= 2u) {
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
    full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    if ((hdr & PH_RED) != 0u) {
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    } else {
      if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    }
    if (olen == 1u) { return full_add_unit(h, out[0]) ? 1ULL : 20ULL; }
    u64 br = full_add_bin_m6(h, out[0], out[1]);
    if (br == 20ULL) { return 20ULL; }
    if (br == 2ULL) { return 2ULL; }
    return 1ULL;
  }
  if (implied == 0xFFFFFFFFu) {
    u64 target = (u64)(olen - 2u);
    if (h->cur_level > target) { full_backtrack(h, target); }
  }
  full_viv_unreason_m6(h, cref);
  full_viv_best_watch_m6(h, olen);
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u32 i = 0u;
  while (i < olen) { ar[(u64)cref + 3ULL + (u64)i] = out[i]; i = i + 1u; }
  ar[(u64)cref + 2ULL] = olen; ar[(u64)cref + 1ULL] = 2u;
  u32 nhdr = hdr;
  if ((nhdr & PH_RED) != 0u) {
    u32 glue = nhdr & PH_GLUE_MASK;
    if (glue >= olen) {
      nhdr = (nhdr & (~PH_GLUE_MASK)) | ((olen - 1u) & PH_GLUE_MASK);
    }
  }
  if ((nhdr & PH_SHRK) == 0u) {
    ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
    nhdr = nhdr | PH_SHRK;
  }
  ar[cref] = nhdr;
  u32 l0 = out[0]; u32 l1 = out[1];
  if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, cref, 2u) ||
      !full_watch_push(h, l1, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL;
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    return 2ULL;
  }
  return 1ULL;
}

void full_viv_mark_garb_m6(FullHdr *h, u32 cref) {
  full_viv_unreason_m6(h, cref);
  u32 *ar = (u32 *)h->arena;
  u32 hdr = ar[cref];
  if ((hdr & PH_GARB) != 0u) { return; }
  u32 sz = ar[(u64)cref + 2ULL];
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  ar[cref] = hdr | PH_GARB;
  h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
  if ((hdr & PH_RED) != 0u) {
    if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
  } else {
    if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
  }
  h->viv_cnt = h->viv_cnt + 1ULL;
}

bool full_viv_subsumes_bin_m6(FullHdr *h, u32 a, u32 b) {
  u8 *lm = (u8 *)h->lit_mark; i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  bool oka = (lm[a] != (u8)0) || (vals[a] < (i8)0 && lvl[a >> 1] == 0u);
  bool okb = (lm[b] != (u8)0) || (vals[b] < (i8)0 && lvl[b >> 1] == 0u);
  return oka && okb;
}

bool full_viv_subsumes_cl_m6(FullHdr *h, u32 rcr, u32 sz) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 rsz = ar[(u64)rcr + 2ULL];
  if (rsz > sz) { return false; }
  u32 j = 0u;
  while (j < rsz) {
    u32 sl = ar[(u64)rcr + 3ULL + (u64)j];
    if (lm[sl] == (u8)0 && !(vals[sl] < (i8)0 && lvl[sl >> 1] == 0u)) { return false; }
    j = j + 1u;
  }
  return true;
}

u32 full_viv_deduce_m6(FullHdr *h, u32 cref, u32 sz, u32 implied) {
  u32 *ar = (u32 *)h->arena; u8 *mrk = (u8 *)h->mark; u8 *lm = (u8 *)h->lit_mark;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *qstk = (u32 *)h->work_stk1; u32 *out = (u32 *)h->work_stk2; u64 cv = h->cur_vars;
  u32 mk = 0u;
  while (mk < sz) { lm[tmp[mk]] = (u8)1; mk = mk + 1u; }
  u64 qlen = 0ULL; u64 qi = 0ULL; u32 olen = 0u; bool taut = false;
  h->ant_sz = 0xFFFFFFFFFFFFFFFFULL; h->res_sz = 0ULL;
  if (implied != 0xFFFFFFFFu) {
    u32 iv = implied >> 1;
    if ((u64)iv < cv && lvl[iv] > 0u) { mrk[iv] = (u8)1; qstk[qlen] = iv; qlen = qlen + 1ULL; }
    out[olen] = implied; olen = olen + 1u;
  } else {
    u32 src_cr = (h->confl_type == 2ULL) ? (u32)h->confl_ref : cref;
    if (h->confl_type == 1ULL) {
      u32 a = (u32)h->confl_lit0; u32 b = (u32)h->confl_lit1;
      if (full_viv_subsumes_bin_m6(h, a, b)) { h->ant_sz = 0xFFFFFFFFFFFFFFFEULL; }
      if (lvl[a >> 1] > 0u && mrk[a >> 1] == (u8)0 && qlen < cv) {
        mrk[a >> 1] = (u8)1; qstk[qlen] = a >> 1; qlen = qlen + 1ULL;
      }
      if (lvl[b >> 1] > 0u && mrk[b >> 1] == (u8)0 && qlen < cv) {
        mrk[b >> 1] = (u8)1; qstk[qlen] = b >> 1; qlen = qlen + 1ULL;
      }
    } else if ((u64)src_cr + 3ULL <= h->arena_len) {
      if (src_cr != cref) {
        if ((ar[src_cr] & PH_RED) != 0u) { h->res_sz = 1ULL; }
        if (full_viv_subsumes_cl_m6(h, src_cr, sz)) { h->ant_sz = (u64)src_cr; }
      }
      u32 csz = ar[(u64)src_cr + 2ULL]; u32 i = 0u;
      while (i < csz) {
        u32 lv = ar[(u64)src_cr + 3ULL + (u64)i] >> 1;
        if ((u64)lv < cv && lvl[lv] > 0u && mrk[lv] == (u8)0 && qlen < cv) {
          mrk[lv] = (u8)1; qstk[qlen] = lv; qlen = qlen + 1ULL;
        }
        i = i + 1u;
      }
    }
  }
  u32 *trl = (u32 *)h->trail; u32 *tpos = (u32 *)h->trail_pos;
  while (qi < qlen) {
    u32 v = qstk[qi]; qi = qi + 1ULL;
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) {
      u32 tl = trl[tpos[v]];
      if (tl == implied) { taut = true; }
      else if ((u64)olen < cv) { out[olen] = tl ^ 1u; olen = olen + 1u; }
    } else if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ot = rsn & PW_LIT_MASK;
      if (h->ant_sz == 0xFFFFFFFFFFFFFFFFULL) {
        u32 tl = trl[tpos[v]];
        if (full_viv_subsumes_bin_m6(h, tl, ot)) { h->ant_sz = 0xFFFFFFFFFFFFFFFEULL; }
      }
      u32 ov = ot >> 1;
      if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
        mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
      }
    } else if ((u64)rsn + 3ULL <= h->arena_len) {
      if ((ar[rsn] & PH_RED) != 0u) { h->res_sz = 1ULL; }
      if (h->ant_sz == 0xFFFFFFFFFFFFFFFFULL && rsn != cref &&
          full_viv_subsumes_cl_m6(h, rsn, sz)) {
        h->ant_sz = (u64)rsn;
      }
      u32 rsz = ar[(u64)rsn + 2ULL]; u32 j = 0u;
      while (j < rsz && (u64)rsn + 3ULL + (u64)rsz <= h->arena_len) {
        u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
        if (ov != v && (u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
          mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
        }
        j = j + 1u;
      }
    }
  }
  qi = 0ULL; while (qi < qlen) { mrk[qstk[qi]] = (u8)0; qi = qi + 1ULL; }
  mk = 0u; while (mk < sz) { lm[tmp[mk]] = (u8)0; mk = mk + 1u; }
  if (taut) { h->ant_sz = 0xFFFFFFFFFFFFFFFFULL; return 0xFFFFFFFFu; }
  return olen;
}

u32 full_viv_best_implied_m6(FullHdr *h, u32 sz) {
  u32 *tmp = (u32 *)h->tmp_lits;
  i8 *vals = (i8 *)h->values;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 best = 0xFFFFFFFFu;
  u32 best_pos = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < sz) {
    u32 l = tmp[i];
    if (vals[l] > (i8)0) {
      u32 tp = tpos[l >> 1];
      if (best == 0xFFFFFFFFu || tp < best_pos) {
        best = l; best_pos = tp;
      }
    }
    i = i + 1u;
  }
  return best;
}

void full_viv_reestablish_m6(FullHdr *h, u32 cref) {
  if (h->cur_level == 0ULL) { return; }
  u32 *ar = (u32 *)h->arena;
  if ((ar[cref] & PH_GARB) != 0u) { return; }
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  i8 v0 = vals[l0]; i8 v1 = vals[l1];
  u64 lvl0 = (v0 != (i8)0) ? (u64)lvl[l0 >> 1] : 0ULL;
  u64 lvl1 = (v1 != (i8)0) ? (u64)lvl[l1 >> 1] : 0ULL;
  u64 new_lvl = 0ULL;
  if (v0 < (i8)0) {
    if (v1 < (i8)0) { new_lvl = (lvl0 < lvl1) ? lvl0 : lvl1; }
    else if (v1 == (i8)0) { new_lvl = lvl0; }
    else if (lvl0 < lvl1) { new_lvl = lvl0; }
  } else if (v1 < (i8)0) {
    if (v0 == (i8)0) { new_lvl = lvl1; }
    else if (lvl1 < lvl0) { new_lvl = lvl1; }
  }
  if (new_lvl > 0ULL && new_lvl - 1ULL < h->cur_level) {
    full_backtrack(h, new_lvl - 1ULL);
  }
}

bool full_viv_inst_check_m6(FullHdr *h, u32 sz, u32 iolen, u32 not_lit) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *out = (u32 *)h->work_stk2;
  u8 *lm = (u8 *)h->lit_mark;
  u32 k = 0u;
  while (k + 1u < sz) { lm[tmp[k]] = (u8)1; k = k + 1u; }
  bool ok = true;
  u32 i = 0u;
  while (i < iolen) {
    u32 x = out[i];
    if (x != not_lit && lm[x] == (u8)0) { ok = false; break; }
    i = i + 1u;
  }
  k = 0u;
  while (k + 1u < sz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  return ok;
}

u64 full_viv_inst_m6(FullHdr *h, u32 cref, u32 sz) {
  if (h->cur_level == 0ULL || sz < 3u) { return 0ULL; }
  u32 *tmp = (u32 *)h->tmp_lits; i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 lit = tmp[sz - 1u];
  if (!(vals[lit] < (i8)0 && (u64)lvl[lit >> 1] == h->cur_level &&
        rsns[lit >> 1] == 0xFFFFFFFFu)) {
    return 0ULL;
  }
  full_backtrack(h, h->cur_level - 1ULL);
  if (vals[lit] != (i8)0) { return 0ULL; }
  u64 nlvl = h->cur_level + 1ULL;
  if (nlvl > h->max_vars) { return 0ULL; }
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
  full_assign(h, lit, 0xFFFFFFFFu);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  u64 pr = full_propagate_ignore(h, (u64)cref);
  if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
  if (pr != 1ULL) {
    full_backtrack(h, h->cur_level - 1ULL);
    return 0ULL;
  }
  u32 iolen = full_viv_deduce_m6(h, cref, sz, 0xFFFFFFFFu);
  if (iolen == 0xFFFFFFFFu || !full_viv_inst_check_m6(h, sz, iolen, lit ^ 1u)) {
    full_backtrack(h, h->cur_level - 1ULL);
    return 0ULL;
  }
  u32 *out = (u32 *)h->work_stk2;
  u32 nsz = sz - 1u;
  u32 k = 0u;
  while (k < nsz) { out[k] = tmp[k]; k = k + 1u; }
  return full_viv_commit_m6(h, cref, nsz, 0xFFFFFFFFu);
}

u64 full_viv_finish_m6(FullHdr *h, u32 cref, u32 sz,
                       bool confl, u32 implied, bool all_done) {
  u32 *ar = (u32 *)h->arena;
  u32 olen = sz;
  bool has_ded = false;
  h->ant_sz = 0xFFFFFFFFFFFFFFFFULL;
  h->res_sz = 0ULL;
  if (confl || implied != 0xFFFFFFFFu || all_done) {
    olen = full_viv_deduce_m6(h, cref, sz, confl ? 0xFFFFFFFFu : implied);
    has_ded = (olen != 0xFFFFFFFFu);
  }
  bool used_red = (h->res_sz != 0ULL);
  u64 sub_ref = h->ant_sz;
  u32 hdr = ar[cref];
  bool is_red = ((hdr & PH_RED) != 0u);
  if (sub_ref != 0xFFFFFFFFFFFFFFFFULL) {
    if (sub_ref < h->arena_len) {
      u32 shdr = ar[sub_ref];
      if (!is_red && (shdr & PH_RED) != 0u) {
        ar[sub_ref] = shdr & (~PH_RED);
        if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
        h->num_irred = h->num_irred + 1ULL;
      } else if (is_red && (shdr & PH_RED) != 0u) {
        u32 cgl = hdr & PH_GLUE_MASK;
        u32 sgl = shdr & PH_GLUE_MASK;
        if (cgl < sgl) { ar[sub_ref] = (shdr & (~PH_GLUE_MASK)) | cgl; }
      }
    }
    full_viv_mark_garb_m6(h, cref);
    if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
    return 1ULL;
  }
  if (has_ded && olen < sz) {
    u64 cr = full_viv_commit_m6(h, cref, olen, confl ? 0xFFFFFFFFu : implied);
    if (cr == 1ULL) { full_viv_reestablish_m6(h, cref); }
    return cr;
  }
  if (has_ded && (confl || implied != 0xFFFFFFFFu) && (is_red || !used_red)) {
    full_viv_mark_garb_m6(h, cref);
    if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
    return 1ULL;
  }
  if (!confl && implied == 0xFFFFFFFFu && all_done) {
    u64 ir = full_viv_inst_m6(h, cref, sz);
    if (ir != 0ULL) {
      if (ir == 1ULL) { full_viv_reestablish_m6(h, cref); }
      return ir;
    }
  }
  if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
  full_viv_reestablish_m6(h, cref);
  return 1ULL;
}

void full_viv_sift_counts_m6(FullHdr *h, u64 start, u64 n) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 r = start;
  while ((r << 1) + 1ULL < n) {
    u64 c1 = (r << 1) + 1ULL;
    u64 worst = c1;
    u32 wlit = tmp[c1];
    u32 wc = cnt[wlit];
    u64 c2 = c1 + 1ULL;
    if (c2 < n) {
      u32 lit2 = tmp[c2];
      u32 c2_val = cnt[lit2];
      if (c2_val < wc || (c2_val == wc && lit2 > wlit)) {
        worst = c2;
        wlit = lit2;
        wc = c2_val;
      }
    }
    u32 rlit = tmp[r];
    u32 rc = cnt[rlit];
    if (wc < rc || (wc == rc && wlit > rlit)) {
      tmp[r] = wlit;
      tmp[worst] = rlit;
      r = worst;
    } else {
      return;
    }
  }
}

void full_viv_sort_counts_m6(FullHdr *h, u32 sz) {
  if (sz <= 1u) { return; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 n = (u64)sz;
  u64 i = n >> 1;
  while (i > 0ULL) {
    i = i - 1ULL;
    full_viv_sift_counts_m6(h, i, n);
  }
  u64 m = n;
  while (m > 1ULL) {
    m = m - 1ULL;
    u32 top = tmp[0];
    tmp[0] = tmp[m];
    tmp[m] = top;
    full_viv_sift_counts_m6(h, 0ULL, m);
  }
}

bool full_viv_has_l0_m6(FullHdr *h, u32 cref, u32 sz) {
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[l] != (i8)0 && lvl[l >> 1] == 0u) { return true; }
    i = i + 1u;
  }
  return false;
}

u64 full_viv_l0_simp_m6(FullHdr *h, u32 cref, u32 sz) {
  if (!full_viv_has_l0_m6(h, cref, sz)) { return 0ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  return full_viv_simplify_m6(h, cref);
}

void full_viv_reuse_prefix_m6(FullHdr *h, u32 cref, u32 sz) {
  if (h->cur_level == 0ULL) { return; }
  u32 *tmp = (u32 *)h->tmp_lits; u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u64 clvl = h->cur_level; u64 keep_lvl = 0ULL; u32 i = 0u;
  while (i < sz && keep_lvl < clvl) {
    u32 l = tmp[i];
    if (l == (fdec[keep_lvl + 1ULL] ^ 1u)) { keep_lvl = keep_lvl + 1ULL; }
    else if (!(vals[l] < (i8)0 && (u64)lvl[l >> 1] <= keep_lvl)) { break; }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < sz && keep_lvl > 0ULL) {
    u32 l = tmp[j];
    if (vals[l] > (i8)0 && rsns[l >> 1] == cref) {
      u64 rl = (u64)lvl[l >> 1];
      if (rl == 0ULL) { keep_lvl = 0ULL; }
      else if (rl - 1ULL < keep_lvl) { keep_lvl = rl - 1ULL; }
    }
    j = j + 1u;
  }
  if (keep_lvl < clvl) { full_backtrack(h, keep_lvl); }
}

u64 full_viv_clause_m6(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((ar[cref] & PH_GARB) != 0u) { return 1ULL; }
  u32 sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u64 l0r = full_viv_l0_simp_m6(h, cref, sz);
  if (l0r != 0ULL) { return l0r; }
  sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u;
  while (i < sz) { tmp[i] = ar[(u64)cref + 3ULL + (u64)i]; i = i + 1u; }
  full_viv_sort_counts_m6(h, sz);
  full_viv_reuse_prefix_m6(h, cref, sz);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  bool confl = false; u32 implied = 0xFFFFFFFFu;
  i = 0u;
  while (i < sz) {
    u32 lit = tmp[i]; i8 lv = vals[lit];
    if (lv > (i8)0) { implied = full_viv_best_implied_m6(h, sz); break; }
    if (lv == (i8)0) {
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { break; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
      full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
      u64 pr = full_propagate_ignore(h, (u64)cref);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) { confl = true; break; }
      u32 bi = full_viv_best_implied_m6(h, sz);
      if (bi != 0xFFFFFFFFu) { implied = bi; break; }
    }
    i = i + 1u;
  }
  u64 fr = full_viv_finish_m6(h, cref, sz, confl, implied, i == sz);
  if (fr != 2ULL && fr != 20ULL && (ar[cref] & PH_GARB) == 0u) {
    ar[cref] = ar[cref] & (~PH_VIV);
  }
  return fr;
}

bool full_viv_tier_match_m6(FullHdr *h, u32 hdr, u64 tier_mode) {
  bool is_red = ((hdr & PH_RED) != 0u);
  u64 glue = (u64)(hdr & PH_GLUE_MASK);
  if (tier_mode == 0ULL) { return !is_red; }
  if (tier_mode == 1ULL) { return is_red && glue <= h->tier1; }
  if (tier_mode == 2ULL) { return is_red && glue > h->tier1 && glue <= h->tier2; }
  return is_red && glue > h->tier2;
}

void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u64 q = 0ULL;
  while (q < h->arena_len) {
    u32 hdr = ar[q];
    if ((hdr & (PH_GARB | PH_VIV)) == PH_VIV) {
      if (full_viv_tier_match_m6(h, hdr, tier_mode)) { ar[q] = hdr & (~PH_VIV); }
    }
    q = (u64)full_arena_next(h, (u32)q);
  }
}

u64 full_viv_collect_fid(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = 0ULL;
  bool any_prio = false;
  u64 pass = 0ULL;
  while (pass < 2ULL && bn < bmax) {
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_GARB) == 0u) {
        bool want = (pass == 0ULL) ? ((hdr & PH_VIV) == 0u) : ((hdr & PH_VIV) != 0u);
        if (want && full_viv_tier_match_m6(h, hdr, tier_mode) && bn < bmax) {
          rr[bn] = (u32)p;
          bn = bn + 1ULL;
          if (pass != 0ULL) { any_prio = true; }
        }
      }
      p = np;
    }
    pass = pass + 1ULL;
  }
  if (!any_prio) {
    u64 k = 0ULL;
    while (k < bn) {
      u32 cref = rr[k];
      ar[cref] = ar[cref] | PH_VIV;
      k = k + 1ULL;
    }
  }
  return bn;
}

void full_viv_count_fid(FullHdr *h, u64 bn) {
  u64 nlits = h->cur_vars << 1;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 l = 0ULL;
  while (l < nlits) { cnt[l] = 0u; l = l + 1ULL; }
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k = 0u;
    while (k < sz) {
      u32 lit = ar[(u64)cr + 3ULL + (u64)k];
      if ((u64)lit < nlits && cnt[lit] < 0xFFFFFFFFu) { cnt[lit] = cnt[lit] + 1u; }
      k = k + 1u;
    }
    bi = bi + 1ULL;
  }
}

void full_viv_sort2_fid(FullHdr *h, u64 bn, u64 mode) {
  if (bn <= 1ULL) { return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 nlits = h->cur_vars << 1;
  u32 *keys = (mode == 1ULL) ? (rr + bn) : ((u32 *)h->scratch_buf);
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k0 = 0xFFFFFFFFu; u32 d0 = 0u;
    u32 k1 = 0xFFFFFFFFu; u32 d1 = 0u;
    u32 j = 0u;
    while (j < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)j];
      u32 dl = ((u64)l < nlits) ? cnt[l] : 0u;
      if (k0 == 0xFFFFFFFFu || dl > d0 || (dl == d0 && l < k0)) {
        k1 = k0; d1 = d0; k0 = l; d0 = dl;
      } else if (k1 == 0xFFFFFFFFu || dl > d1 || (dl == d1 && l < k1)) {
        k1 = l; d1 = dl;
      }
      j = j + 1u;
    }
    keys[bi << 1] = k0;
    keys[(bi << 1) + 1ULL] = k1;
    bi = bi + 1ULL;
  }
  u64 bn3 = bn / 3ULL;
  u64 gap = 1ULL;
  while (gap < bn3) {
    gap = gap * 3ULL + 1ULL;
  }
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < bn) {
      u32 cr = rr[si];
      u32 k0 = keys[si << 1]; u32 k1 = keys[(si << 1) + 1ULL];
      bool v0 = ((ar[cr] & PH_VIV) != 0u);
      u32 dk0 = ((u64)k0 < nlits) ? cnt[k0] : 0u;
      u32 dk1 = ((u64)k1 < nlits) ? cnt[k1] : 0u;
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pcr = rr[pj];
        u32 pk0 = keys[pj << 1]; u32 pk1 = keys[(pj << 1) + 1ULL];
        bool pv0 = ((ar[pcr] & PH_VIV) != 0u);
        u32 dpk0 = ((u64)pk0 < nlits) ? cnt[pk0] : 0u;
        u32 dpk1 = ((u64)pk1 < nlits) ? cnt[pk1] : 0u;
        if (pv0 && !v0) { break; }
        if (pv0 == v0) {
          if (dpk0 > dk0) { break; }
          if (dpk0 == dk0) {
            if (pk0 < k0) { break; }
            if (pk0 == k0) {
              if (dpk1 > dk1) { break; }
              if (dpk1 == dk1) {
                if (pk1 < k1 || (pk1 == k1 && pcr <= cr)) { break; }
              }
            }
          }
        }
        rr[sj] = pcr;
        keys[sj << 1] = pk0; keys[(sj << 1) + 1ULL] = pk1;
        sj = pj;
      }
      rr[sj] = cr;
      keys[sj << 1] = k0; keys[(sj << 1) + 1ULL] = k1;
      si = si + 1ULL;
    }
    gap = gap / 3ULL;
  }
}

void full_viv_sort_fid(FullHdr *h, u64 bn) {
  if (bn <= 1ULL) { return; }
  u64 rcap = h->red_cap;
  u64 scap = h->scratch_cap;
  if (bn <= rcap / 3ULL) { full_viv_sort2_fid(h, bn, 1ULL); return; }
  if (bn <= (scap >> 1)) { full_viv_sort2_fid(h, bn, 2ULL); return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  if (bn > (rcap >> 1) && bn > scap) {
    u64 lo = 0ULL;
    u64 hi = bn - 1ULL;
    while (lo < hi) {
      u32 lcr = rr[lo];
      if ((ar[lcr] & PH_VIV) != 0u) {
        lo = lo + 1ULL;
      } else {
        u32 hcr = rr[hi];
        if ((ar[hcr] & PH_VIV) == 0u) {
          hi = hi - 1ULL;
        } else {
          rr[lo] = hcr; rr[hi] = lcr;
          lo = lo + 1ULL;
          hi = hi - 1ULL;
        }
      }
    }
    return;
  }
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 nlits = h->cur_vars << 1;
  u32 *keys1 = (bn <= (rcap >> 1)) ? (rr + bn) : ((u32 *)h->scratch_buf);
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k0 = 0xFFFFFFFFu; u32 d0 = 0u;
    u32 j = 0u;
    while (j < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)j];
      u32 dl = ((u64)l < nlits) ? cnt[l] : 0u;
      if (k0 == 0xFFFFFFFFu || dl > d0 || (dl == d0 && l < k0)) { k0 = l; d0 = dl; }
      j = j + 1u;
    }
    keys1[bi] = k0;
    bi = bi + 1ULL;
  }
  u64 bn3 = bn / 3ULL;
  u64 gap = 1ULL;
  while (gap < bn3) {
    gap = gap * 3ULL + 1ULL;
  }
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < bn) {
      u32 cr = rr[si]; u32 k0 = keys1[si];
      bool v0 = ((ar[cr] & PH_VIV) != 0u);
      u32 dk0 = ((u64)k0 < nlits) ? cnt[k0] : 0u;
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pcr = rr[pj]; u32 pk0 = keys1[pj];
        bool pv0 = ((ar[pcr] & PH_VIV) != 0u);
        u32 dpk0 = ((u64)pk0 < nlits) ? cnt[pk0] : 0u;
        if (pv0 && !v0) { break; }
        if (pv0 == v0) {
          if (dpk0 > dk0) { break; }
          if (dpk0 == dk0 && (pk0 < k0 || (pk0 == k0 && pcr <= cr))) { break; }
        }
        rr[sj] = pcr; keys1[sj] = pk0;
        sj = pj;
      }
      rr[sj] = cr; keys1[sj] = k0;
      si = si + 1ULL;
    }
    gap = gap / 3ULL;
  }
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = full_viv_collect_fid(h, tier_mode);
  bool do_sort = (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant);
  if (do_sort) {
    full_viv_count_fid(h, bn);
    full_viv_sort_fid(h, bn);
  }
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         h->search_ticks < tick_lim) {
    u32 cr = rr[do_sort ? bi : (bn - 1ULL - bi)];
    budget = budget - 1ULL;
    u64 vc = full_viv_clause_m6(h, cr);
    if (vc == 20ULL) { res = 20ULL; break; }
    if (vc == 2ULL) { break; }
    if (h->cur_level == 0ULL && full_propagate(h) == 1ULL) { res = 20ULL; break; }
    bi = bi + 1ULL;
  }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (res == 1ULL && bi >= bn && bn < bmax) {
    full_viv_clear_tier_m6(h, tier_mode);
  }
  h->res_sz = bi;
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_m6_hdr(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->tier1 = m6_hdr_get_tier1(h, true);
  h->tier2 = m6_hdr_get_tier2(h, true);
  u64 w0 = m6_hdr_delaying(h, M6_DELAY_VIVIFYIRR) ? 0ULL : 3ULL;
  u64 w1 = (h->num_redundant == 0ULL) ? 0ULL : 3ULL;
  u64 w2 = (h->num_redundant == 0ULL) ? 0ULL : 3ULL;
  u64 w3 = (h->num_redundant == 0ULL) ? 0ULL : 1ULL;
  u64 sum = w0 + w1 + w2 + w3;
  if (sum == 0ULL) { h->probing = 0ULL; return 1ULL; }
  u64 start = h->search_ticks;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 delta = (start > last_p) ? (start - last_p) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  if (w1 > 0ULL && w2 > 0ULL && h->tier1 >= h->tier2) { w1 = w1 + w2; w2 = 0ULL; }
  u64 res = 1ULL;
  u64 lim = start;
  if (w1 > 0ULL) {
    u64 a1 = (total * w1) / sum;
    lim = (lim > (~0ULL) - a1) ? (~0ULL) : (lim + a1);
    res = full_vivify_tier_m6_hdr(h, 1ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w2 > 0ULL) {
    u64 a2 = (total * w2) / sum;
    lim = (lim > (~0ULL) - a2) ? (~0ULL) : (lim + a2);
    res = full_vivify_tier_m6_hdr(h, 2ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w3 > 0ULL) {
    u64 a3 = (total * w3) / sum;
    lim = (lim > (~0ULL) - a3) ? (~0ULL) : (lim + a3);
    res = full_vivify_tier_m6_hdr(h, 3ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w0 > 0ULL) {
    u64 a0 = (total * w0) / sum;
    lim = (lim > (~0ULL) - a0) ? (~0ULL) : (lim + a0);
    u64 vb = h->viv_cnt;
    u64 ub = h->unassigned;
    res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim);
    u64 tried = h->res_sz;
    if (res != 20ULL) {
      u64 y = (h->viv_cnt - vb) + ((ub > h->unassigned) ? (ub - h->unassigned) : 0ULL);
      if (tried == 0ULL || y * 100ULL < tried) { m6_hdr_bump_delay(h, M6_DELAY_VIVIFYIRR); }
      else { m6_hdr_reduce_delay(h, M6_DELAY_VIVIFYIRR); }
    }
  }
  m6_hdr_sync_legacy_tiers(h);
  h->search_ticks = start;
  return res;
}
"

/-- Ordered live functions of `Src/Vivify.lean` (`28` fns). -/
def fns : List Fn := vivify_fns

end

public section

theorem full_viv_unreason_m6_wf : Func.Wf full_viv_unreason_m6_body := by kissat_wf_reify
theorem full_viv_watch_rank_m6_wf : Func.Wf full_viv_watch_rank_m6_body := by kissat_wf_reify
theorem full_viv_best_watch_m6_wf : Func.Wf full_viv_best_watch_m6_body := by kissat_wf_reify
theorem full_viv_simplify_m6_wf : Func.Wf full_viv_simplify_m6_body := by kissat_wf_reify
theorem full_viv_commit_m6_wf : Func.Wf full_viv_commit_m6_body := by kissat_wf_reify
theorem full_viv_mark_garb_m6_wf : Func.Wf full_viv_mark_garb_m6_body := by kissat_wf_reify
theorem full_viv_subsumes_bin_m6_wf : Func.Wf full_viv_subsumes_bin_m6_body := by kissat_wf_reify
theorem full_viv_subsumes_cl_m6_wf : Func.Wf full_viv_subsumes_cl_m6_body := by kissat_wf_reify
theorem full_viv_deduce_m6_wf : Func.Wf full_viv_deduce_m6_body := by kissat_wf_reify
theorem full_viv_best_implied_m6_wf : Func.Wf full_viv_best_implied_m6_body := by kissat_wf_reify
theorem full_viv_reestablish_m6_wf : Func.Wf full_viv_reestablish_m6_body := by kissat_wf_reify
theorem full_viv_inst_check_m6_wf : Func.Wf full_viv_inst_check_m6_body := by kissat_wf_reify
theorem full_viv_inst_m6_wf : Func.Wf full_viv_inst_m6_body := by kissat_wf_reify
theorem full_viv_finish_m6_wf : Func.Wf full_viv_finish_m6_body := by kissat_wf_reify
theorem full_viv_sift_counts_m6_wf : Func.Wf full_viv_sift_counts_m6_body := by kissat_wf_reify
theorem full_viv_sort_counts_m6_wf : Func.Wf full_viv_sort_counts_m6_body := by kissat_wf_reify
theorem full_viv_has_l0_m6_wf : Func.Wf full_viv_has_l0_m6_body := by kissat_wf_reify
theorem full_viv_l0_simp_m6_wf : Func.Wf full_viv_l0_simp_m6_body := by kissat_wf_reify
theorem full_viv_reuse_prefix_m6_wf : Func.Wf full_viv_reuse_prefix_m6_body := by kissat_wf_reify
theorem full_viv_clause_m6_wf : Func.Wf full_viv_clause_m6_body := by kissat_wf_reify
theorem full_viv_tier_match_m6_wf : Func.Wf full_viv_tier_match_m6_body := by kissat_wf_reify
theorem full_viv_clear_tier_m6_wf : Func.Wf full_viv_clear_tier_m6_body := by kissat_wf_reify
theorem full_viv_collect_fid_wf : Func.Wf full_viv_collect_fid_body := by kissat_wf_reify
theorem full_viv_count_fid_wf : Func.Wf full_viv_count_fid_body := by kissat_wf_reify
theorem full_viv_sort2_fid_wf : Func.Wf full_viv_sort2_fid_body := by kissat_wf_reify
theorem full_viv_sort_fid_wf : Func.Wf full_viv_sort_fid_body := by kissat_wf_reify
theorem full_vivify_tier_m6_hdr_wf : Func.Wf full_vivify_tier_m6_hdr_body := by kissat_wf_reify
theorem full_vivify_m6_hdr_wf : Func.Wf full_vivify_m6_hdr_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, vivify_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_viv_unreason_m6_wf
  · exact full_viv_watch_rank_m6_wf
  · exact full_viv_best_watch_m6_wf
  · exact full_viv_simplify_m6_wf
  · exact full_viv_commit_m6_wf
  · exact full_viv_mark_garb_m6_wf
  · exact full_viv_subsumes_bin_m6_wf
  · exact full_viv_subsumes_cl_m6_wf
  · exact full_viv_deduce_m6_wf
  · exact full_viv_best_implied_m6_wf
  · exact full_viv_reestablish_m6_wf
  · exact full_viv_inst_check_m6_wf
  · exact full_viv_inst_m6_wf
  · exact full_viv_finish_m6_wf
  · exact full_viv_sift_counts_m6_wf
  · exact full_viv_sort_counts_m6_wf
  · exact full_viv_has_l0_m6_wf
  · exact full_viv_l0_simp_m6_wf
  · exact full_viv_reuse_prefix_m6_wf
  · exact full_viv_clause_m6_wf
  · exact full_viv_tier_match_m6_wf
  · exact full_viv_clear_tier_m6_wf
  · exact full_viv_collect_fid_wf
  · exact full_viv_count_fid_wf
  · exact full_viv_sort2_fid_wf
  · exact full_viv_sort_fid_wf
  · exact full_vivify_tier_m6_hdr_wf
  · exact full_vivify_m6_hdr_wf

end

end LeanQbe.T.Examples.Kissat.Src.Vivify

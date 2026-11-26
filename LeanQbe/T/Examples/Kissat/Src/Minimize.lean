/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Recursive Clause Minimization & Block Shrinking (`Src/Minimize.lean`)

Mirrors upstream `kissat/src/minimize.c, shrink.c` (`7` live functions, DAG level `L0`):
- `full_min_mark` (R4: `kissat_minimize_mark`)
- `full_sort_tmp` (R4: `kissat_sort_deduced_clause`)
- `full_min_lit_dfs_m8` (R4: `kissat_minimize_literal`)
- `full_shrink_lower_m8` (R4: `kissat_shrink_lower_literal`)
- `full_shrink_blk_bool_m8` (R4: `kissat_shrink_block`)
- `full_min_shrink_m6` (R4: `kissat_shrink_and_minimize_impl`)
- `full_min_shrink` (R4: `kissat_shrink_and_minimize`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Minimize

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! minimize "
#include \"kissat_internal.h\"

void full_min_mark(FullHdr *h, u32 v, u8 tag) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[v] & tag) != (u8)0) { return; }
  if (mrk[v] == (u8)0) {
    if (h->min_clr_len < cv) {
      u32 *mclr = (u32 *)h->min_clr;
      mclr[h->min_clr_len] = v;
      h->min_clr_len = h->min_clr_len + 1ULL;
    } else { h->min_clr_full = 1ULL; }
  }
  mrk[v] = mrk[v] | tag;
}

void full_sort_tmp(FullHdr *h) {
  u64 tlen = h->tmp_len;
  u64 mv = h->max_vars;
  if (tlen <= 2ULL || tlen > mv) {
    return;
  }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  if (tlen <= 32ULL) {
    u64 i = 2ULL;
    while (i < tlen) {
      u32 x = tmp[i];
      u32 lx = lvl[((u64)x) >> 1];
      u64 j = i;
      while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] > lx) {
        tmp[j] = tmp[j - 1ULL];
        j = j - 1ULL;
      }
      tmp[j] = x;
      i = i + 1ULL;
    }
    return;
  }
  u32 *sh = (u32 *)h->wsort;
  u32 x1 = tmp[1];
  sh[1] = x1;
  u32 l1 = lvl[((u64)x1) >> 1];
  u32 min_l = l1;
  u32 max_l = l1;
  u64 k = 2ULL;
  while (k < tlen) {
    u32 x = tmp[k];
    sh[k] = x;
    u32 lx = lvl[((u64)x) >> 1];
    if (lx < min_l) { min_l = lx; }
    if (lx > max_l) { max_l = lx; }
    k = k + 1ULL;
  }
  u64 span = (u64)max_l - (u64)min_l + 1ULL;
  u64 n = tlen - 1ULL;
  if (span == 1ULL) {
    return;
  }
  if (span <= mv && span <= (n << 2)) {
    u64 b = 0ULL;
    while (b < span) {
      sh[mv + b] = 0u;
      b = b + 1ULL;
    }
    k = 1ULL;
    while (k < tlen) {
      u32 x = sh[k];
      u64 bi = (u64)lvl[((u64)x) >> 1] - (u64)min_l;
      sh[mv + bi] = sh[mv + bi] + 1u;
      k = k + 1ULL;
    }
    u64 pos = 1ULL;
    b = 0ULL;
    while (b < span) {
      u32 c = sh[mv + b];
      sh[mv + b] = (u32)pos;
      pos = pos + (u64)c;
      b = b + 1ULL;
    }
    k = 1ULL;
    while (k < tlen) {
      u32 x = sh[k];
      u64 bi = (u64)lvl[((u64)x) >> 1] - (u64)min_l;
      u64 dst = (u64)sh[mv + bi];
      sh[mv + bi] = (u32)(dst + 1ULL);
      tmp[dst] = x;
      k = k + 1ULL;
    }
    return;
  }
  u64 w = 1ULL;
  while (w < n) {
    u64 lo = 1ULL;
    while (lo < tlen) {
      u64 mid = (lo + w < tlen) ? (lo + w) : tlen;
      u64 hi = (lo + (w << 1) < tlen) ? (lo + (w << 1)) : tlen;
      u64 i0 = lo;
      u64 i1 = mid;
      u64 dst = lo;
      while (i0 < mid && i1 < hi) {
        if (lvl[((u64)tmp[i0]) >> 1] <= lvl[((u64)tmp[i1]) >> 1]) {
          sh[dst] = tmp[i0]; i0 = i0 + 1ULL;
        } else {
          sh[dst] = tmp[i1]; i1 = i1 + 1ULL;
        }
        dst = dst + 1ULL;
      }
      while (i0 < mid) { sh[dst] = tmp[i0]; i0 = i0 + 1ULL; dst = dst + 1ULL; }
      while (i1 < hi) { sh[dst] = tmp[i1]; i1 = i1 + 1ULL; dst = dst + 1ULL; }
      u64 cp = lo;
      while (cp < hi) { tmp[cp] = sh[cp]; cp = cp + 1ULL; }
      lo = hi;
    }
    w = w << 1;
  }
}

bool full_min_lit_dfs_m8(FullHdr *h, u32 root_lit, bool minimizing, bool check_used) {
  u64 cv = h->cur_vars;
  u32 root_v = root_lit >> 1;
  if ((u64)root_v >= cv || h->min_depth == 0ULL) { return false; }
  u32 *rsns = (u32 *)h->reason;
  if (rsns[root_v] == 0xFFFFFFFFu) { return false; }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena; u32 *stk = (u32 *)h->wsort;
  u32 *used = (u32 *)h->shrink_stk;
  u32 rlvl = lvl[root_v];
  if (minimizing && check_used && (u64)rlvl < cv && (u64)rlvl < h->cur_level &&
      used[rlvl] <= 1u) {
    return false;
  }
  stk[0] = root_v; stk[1] = 0u;
  u64 sp = 0ULL; u64 cur_depth = 0ULL; bool ok = false; u64 steps = 0ULL;
  u64 max_steps = (h->arena_len + cv) * 4ULL + 64ULL;
  while (steps < max_steps) {
    steps = steps + 1ULL;
    u32 v = stk[sp << 1]; u32 pword = stk[(sp << 1) + 1ULL];
    u32 pos = pword & 0x7FFFFFFFu;
    if ((u64)v >= cv) { break; }
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) { break; }
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    if (is_bin) {
      if (pos == 0u) {
        stk[(sp << 1) + 1ULL] = pword | 1u;
        u32 u = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)u >= cv) { break; }
        u32 ul = lvl[u];
        if (u == v || ul == 0u) { continue; }
        u8 mu = mrk[u];
        if ((mu & (u8)2) != (u8)0) { continue; }
        if ((mu & (u8)4) != (u8)0) { break; }
        if (rsns[u] == 0xFFFFFFFFu) { full_min_mark(h, u, (u8)4); break; }
        if (check_used && (u64)ul < cv && (u64)ul < h->cur_level && used[ul] == 0u) { break; }
        if (sp + 1ULL >= h->max_vars) { break; }
        sp = sp + 1ULL; stk[sp << 1] = u; stk[(sp << 1) + 1ULL] = 0u;
        continue;
      }
      if (sp == 0ULL) { ok = true; break; }
      full_min_mark(h, v, (u8)2);
      if ((pword & 0x80000000u) != 0u && cur_depth > 0ULL) { cur_depth = cur_depth - 1ULL; }
      sp = sp - 1ULL;
      continue;
    }
    if ((u64)rsn + 3ULL > h->arena_len) { break; }
    u32 sz = ar[(u64)rsn + 2ULL];
    if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { break; }
    if (pos == 0u) { h->search_ticks = h->search_ticks + 1ULL; }
    if (pos < sz) {
      stk[(sp << 1) + 1ULL] = (pword & 0x80000000u) | (pos + 1u);
      u32 l = ar[(u64)rsn + 3ULL + (u64)pos];
      u32 u = l >> 1;
      if ((u64)u >= cv) { break; }
      u32 ul = lvl[u];
      if (u == v || ul == 0u) { continue; }
      u8 mu = mrk[u];
      if ((mu & (u8)2) != (u8)0) { continue; }
      if ((mu & (u8)4) != (u8)0) { break; }
      if (rsns[u] == 0xFFFFFFFFu) { full_min_mark(h, u, (u8)4); break; }
      if (check_used && (u64)ul < cv && (u64)ul < h->cur_level && used[ul] == 0u) { break; }
      if (cur_depth + 1ULL >= h->min_depth || sp + 1ULL >= h->max_vars) { break; }
      cur_depth = cur_depth + 1ULL;
      sp = sp + 1ULL; stk[sp << 1] = u; stk[(sp << 1) + 1ULL] = 0x80000000u;
      continue;
    }
    if (sp == 0ULL) { ok = true; break; }
    full_min_mark(h, v, (u8)2);
    if ((pword & 0x80000000u) != 0u && cur_depth > 0ULL) { cur_depth = cur_depth - 1ULL; }
    sp = sp - 1ULL;
  }
  if (!ok) {
    u64 j = 1ULL;
    while (j <= sp) { full_min_mark(h, stk[j << 1], (u8)4); j = j + 1ULL; }
    return false;
  }
  return true;
}

bool full_shrink_lower_m8(FullHdr *h, u32 ot, u32 ov) {
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[ov] & (u8)2) != (u8)0) { return true; }
  if ((mrk[ov] & (u8)4) != (u8)0 || !full_min_lit_dfs_m8(h, ot, false, false)) {
    full_min_mark(h, ov, (u8)4);
    return false;
  }
  full_min_mark(h, ov, (u8)2);
  return true;
}

bool full_shrink_blk_bool_m8(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *sstk = (u32 *)h->shrink_stk;
  u32 *ar = (u32 *)h->arena; u64 cv = h->cur_vars;
  u64 open = end_b - beg; u64 slen = 0ULL; u64 k = beg;
  while (k < end_b) {
    u32 v = tmp[k] >> 1; mrk[v] = mrk[v] | (u8)8;
    sstk[slen] = v; slen = slen + 1ULL; k = k + 1ULL;
  }
  bool failed = false; u32 uip = 0xFFFFFFFFu; u64 t = max_tr;
  while (!failed) {
    while (true) {
      if (t >= h->trail_end) { failed = true; break; }
      u32 lit = trl[t];
      if ((mrk[lit >> 1] & (u8)8) != (u8)0) { uip = lit; break; }
      if (t == 0ULL) { failed = true; break; }
      t = t - 1ULL;
    }
    if (failed || open == 1ULL || t == 0ULL) {
      if (open != 1ULL) { failed = true; }
      break;
    }
    t = t - 1ULL;
    u32 rsn = rsns[uip >> 1];
    if (rsn == 0xFFFFFFFFu) { failed = true; break; }
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    u32 csz = 1u;
    if (!is_bin) {
      if ((u64)rsn + 3ULL > h->arena_len) { failed = true; break; }
      csz = ar[(u64)rsn + 2ULL];
      if (csz < 3u || (u64)rsn + 3ULL + (u64)csz > h->arena_len) { failed = true; break; }
      h->search_ticks = h->search_ticks + 1ULL;
    }
    u32 i = 0u;
    while (i < csz && !failed) {
      u32 ot = is_bin ? (rsn & PW_LIT_MASK) : ar[(u64)rsn + 3ULL + (u64)i];
      u32 ov = ot >> 1;
      if (ot != uip && (u64)ov < cv && lvl[ov] > 0u && (mrk[ov] & (u8)8) == (u8)0) {
        if (lvl[ov] < blvl) {
          if (!full_shrink_lower_m8(h, ot, ov)) { failed = true; }
        } else if (lvl[ov] == blvl && slen < cv) {
          mrk[ov] = mrk[ov] | (u8)8; sstk[slen] = ov;
          slen = slen + 1ULL; open = open + 1ULL;
        } else { failed = true; }
      }
      i = i + 1u;
    }
    if (!failed) { open = open - 1ULL; }
  }
  if (failed || uip == 0xFFFFFFFFu) {
    u64 i = 0ULL;
    while (i < slen) { u32 sv = sstk[i]; mrk[sv] = mrk[sv] & (u8)0xF7; i = i + 1ULL; }
    return false;
  }
  k = beg;
  while (k < end_b) { tmp[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  tmp[beg] = uip ^ 1u;
  u64 i = 0ULL;
  while (i < slen) {
    u32 sv = sstk[i]; mrk[sv] = mrk[sv] & (u8)0xF7;
    full_min_mark(h, sv, (u8)2); i = i + 1ULL;
  }
  return true;
}

void full_min_shrink_m6(FullHdr *h) {
  u64 cv = h->cur_vars; u64 orig_tlen = h->tmp_len;
  if (h->probing == 0ULL) { h->conflicts = h->conflicts + 1ULL; }
  if (orig_tlen <= 1ULL || orig_tlen > cv) {
    h->learned_lits = h->learned_lits + orig_tlen; return;
  }
  full_sort_tmp(h);
  u32 *tmp = (u32 *)h->tmp_lits; u32 *lvl = (u32 *)h->level; u32 *tpos = (u32 *)h->trail_pos;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  u64 i = 0ULL;
  while (i < orig_tlen) { full_min_mark(h, tmp[i] >> 1, (u8)2); i = i + 1ULL; }
  u64 tlen = orig_tlen;
  u64 beg = 1ULL;
  while (beg < tlen) {
    u32 blvl = lvl[tmp[beg] >> 1]; u64 max_tr = (u64)tpos[tmp[beg] >> 1];
    u64 end_b = beg + 1ULL;
    while (end_b < tlen && lvl[tmp[end_b] >> 1] == blvl) {
      u64 tp = (u64)tpos[tmp[end_b] >> 1];
      if (tp > max_tr) { max_tr = tp; }
      end_b = end_b + 1ULL;
    }
    if (end_b - beg >= 2ULL) {
      if (!full_shrink_blk_bool_m8(h, beg, end_b, blvl, max_tr)) {
        u64 mk2 = beg;
        while (mk2 < end_b) {
          if (full_min_lit_dfs_m8(h, tmp[mk2], false, false)) { tmp[mk2] = 0xFFFFFFFFu; }
          mk2 = mk2 + 1ULL;
        }
      }
    }
    beg = end_b;
  }
  u64 keep = 1ULL; u64 k = 1ULL;
  while (k < tlen) {
    if (tmp[k] != 0xFFFFFFFFu) { tmp[keep] = tmp[k]; keep = keep + 1ULL; }
    k = k + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  if (h->min_clr_full != 0ULL) {
    u64 v = 0ULL; while (v < cv) { mrk[v] = (u8)0; v = v + 1ULL; }
  } else {
    u32 *mclr = (u32 *)h->min_clr; u64 z = 0ULL;
    while (z < h->min_clr_len) {
      u32 z_v = mclr[z]; if ((u64)z_v < cv) { mrk[z_v] = (u8)0; }
      z = z + 1ULL;
    }
  }
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL; h->tmp_len = keep;
  h->min_removed = h->min_removed + (orig_tlen - keep);
  h->learned_lits = h->learned_lits + keep;
}

void full_min_shrink(FullHdr *h) {
  full_min_shrink_m6(h);
}
"

/-- Ordered live functions of `Src/Minimize.lean` (`7` fns). -/
def fns : List Fn := minimize_fns

end

public section

theorem full_min_mark_wf : Func.Wf full_min_mark_body := by kissat_wf_reify
theorem full_sort_tmp_wf : Func.Wf full_sort_tmp_body := by kissat_wf_reify
theorem full_min_lit_dfs_m8_wf : Func.Wf full_min_lit_dfs_m8_body := by kissat_wf_reify
theorem full_shrink_lower_m8_wf : Func.Wf full_shrink_lower_m8_body := by kissat_wf_reify
theorem full_shrink_blk_bool_m8_wf : Func.Wf full_shrink_blk_bool_m8_body := by kissat_wf_reify
theorem full_min_shrink_m6_wf : Func.Wf full_min_shrink_m6_body := by kissat_wf_reify
theorem full_min_shrink_wf : Func.Wf full_min_shrink_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, minimize_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_min_mark_wf
  · exact full_sort_tmp_wf
  · exact full_min_lit_dfs_m8_wf
  · exact full_shrink_lower_m8_wf
  · exact full_shrink_blk_bool_m8_wf
  · exact full_min_shrink_m6_wf
  · exact full_min_shrink_wf

end

end LeanQbe.T.Examples.Kissat.Src.Minimize

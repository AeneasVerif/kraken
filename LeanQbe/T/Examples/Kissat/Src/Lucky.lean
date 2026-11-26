/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Lucky Phase-Satisfying Assignment Checks (`Src/Lucky.lean`)

Mirrors upstream `kissat/src/lucky.c` (`4` live functions, DAG level `L6`):
- `full_lucky_ord_fid` (R4: `kissat_lucky_order`)
- `full_lucky_scan` (R4: `kissat_lucky_scan`)
- `full_lucky_polar_m7` (R4: `kissat_lucky_polar`)
- `full_lucky_late_m7` (R4: `kissat_lucky`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Lucky

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! lucky "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern u64 full_analyze(FullHdr *h);

u64 full_lucky_ord_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 mx = h->max_vars;
  u32 *ord = (u32 *)h->tarjan_reach;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *ext = (u32 *)h->extend_stk;
  u64 len = h->extend_len;
  bool has_perm = false;
  u64 orig_mv = 0ULL;
  if (len > 0ULL && len <= h->extend_cap) {
    u32 h0 = ext[0];
    if ((h0 & (EXT_BLK_FLAG | EXT_COMPACT_FLAG | EXT_PERM_FLAG)) ==
        (EXT_BLK_FLAG | EXT_PERM_FLAG)) {
      orig_mv = (u64)(h0 & EXT_PERM_MASK);
      if (orig_mv <= mx && 1ULL + orig_mv <= len) {
        has_perm = true;
      }
    }
  }
  if (!has_perm) {
    u64 v = 0ULL;
    while (v < cv) {
      ord[v] = (u32)v;
      v = v + 1ULL;
    }
    return cv;
  }
  u64 e = 0ULL;
  while (e < orig_mv) {
    ord[e] = ext[1ULL + e];
    e = e + 1ULL;
  }
  u64 p = 1ULL + orig_mv;
  while (p < len) {
    u32 head = ext[p];
    if ((head & (EXT_BLK_FLAG | EXT_COMPACT_FLAG)) == (EXT_BLK_FLAG | EXT_COMPACT_FLAG)) {
      u64 ncv = (u64)(head & EXT_CNT_MASK);
      if (ncv <= mx && p + 1ULL + ncv <= len) {
        u64 z = 0ULL;
        while (z < mx) { tmk[z] = EXT_UNMAPPED; z = z + 1ULL; }
        u64 k = 0ULL;
        while (k < ncv) {
          u32 ov = ext[p + 1ULL + k];
          if ((u64)ov < mx) { tmk[ov] = (u32)k; }
          k = k + 1ULL;
        }
        e = 0ULL;
        while (e < orig_mv) {
          u32 cur = ord[e];
          ord[e] = ((u64)cur < mx) ? tmk[cur] : EXT_UNMAPPED;
          e = e + 1ULL;
        }
        p = p + 1ULL + ncv;
      } else {
        p = p + 1ULL;
      }
    } else {
      p = p + 1ULL;
      while (p < len && (ext[p] & EXT_BLK_FLAG) == 0u) {
        p = p + 1ULL;
      }
    }
  }
  u64 z = 0ULL;
  while (z < cv) { tmk[z] = 0u; z = z + 1ULL; }
  u64 n = 0ULL;
  e = 0ULL;
  while (e < orig_mv) {
    u32 iv = ord[e];
    if ((u64)iv < cv && tmk[iv] == 0u && n < cv) {
      tmk[iv] = 1u;
      ord[n] = iv;
      n = n + 1ULL;
    }
    e = e + 1ULL;
  }
  u64 v = 0ULL;
  while (v < cv) {
    if (tmk[v] == 0u && n < cv) {
      ord[n] = (u32)v;
      n = n + 1ULL;
    }
    v = v + 1ULL;
  }
  return n;
}

u64 full_lucky_scan(FullHdr *h, bool pos_mode, bool fwd) {
  u64 cv = h->cur_vars;
  u64 n = full_lucky_ord_fid(h);
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  u32 *ord = (u32 *)h->tarjan_reach;
  u64 i = 0ULL;
  while (i < n) {
    u64 j = fwd ? i : (n - 1ULL - i);
    u64 v = (u64)ord[j];
    if (v < cv && (fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      h->fuel = h->fuel - 1ULL;
      u32 lit = pos_mode ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
      full_assign(h, lit, 0xFFFFFFFFu);
      u64 pr = full_propagate(h);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) {
        if (h->cur_level > 1ULL) {
          full_backtrack(h, h->cur_level - 1ULL);
          if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          h->fuel = h->fuel - 1ULL;
          nlvl = h->cur_level + 1ULL;
          if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
          ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
          full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
          u64 pr2 = full_propagate(h);
          if (pr2 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          if (pr2 == 1ULL) { full_backtrack(h, 0ULL); return 0ULL; }
        } else {
          u64 ast = full_analyze(h);
          if (ast == 20ULL) { return 20ULL; }
          if (ast != 1ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          u64 pr3 = full_propagate(h);
          if (pr3 == 1ULL) { return 20ULL; }
          if (pr3 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
        }
      }
    }
    i = i + 1ULL;
  }
  return 10ULL;
}

u64 full_lucky_polar_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  bool has_neg = false;
  bool has_pos = false;
  u64 p = 0ULL;
  while (p < h->arena_len && (!has_neg || !has_pos)) {
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (p + 3ULL <= h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) == 0u &&
          sz >= 3u && p + 3ULL + (u64)sz <= h->arena_len) {
        bool sat = false;
        bool ap = false;
        bool an = false;
        u32 k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if ((u64)l < nlits) {
            i8 vl = vals[l];
            if (vl > (i8)0) { sat = true; break; }
            if (vl >= (i8)0) {
              if ((l & 1u) == 0u) { ap = true; } else { an = true; }
            }
          }
          k = k + 1u;
        }
        if (!sat) {
          if (!ap) { has_neg = true; }
          if (!an) { has_pos = true; }
        }
      }
    }
    if (np <= p) { break; }
    p = np;
  }
  u64 v = 0ULL;
  while (v < cv && (!has_neg || !has_pos)) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 nl = (u32)((v << 1) | 1ULL);
      u64 off = (u64)wvec[(u64)nl << 1];
      u64 sz = (u64)wvec[((u64)nl << 1) + 1ULL];
      if (off <= h->wlen && sz <= h->wlen - off) {
        u64 end = off + sz;
        while (off < end && !has_neg) {
          u32 w0 = wstk[off];
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 ot = w0 & PW_LIT_MASK;
            if ((u64)ot < nlits) {
              i8 vo = vals[ot];
              if (vo < (i8)0 || (vo == (i8)0 && (ot & 1u) != 0u)) {
                has_neg = true;
              }
            }
            off = off + 1ULL;
          } else {
            off = off + 2ULL;
          }
        }
      }
      u32 pl = (u32)(v << 1);
      u64 off2 = (u64)wvec[(u64)pl << 1];
      u64 sz2 = (u64)wvec[((u64)pl << 1) + 1ULL];
      if (off2 <= h->wlen && sz2 <= h->wlen - off2) {
        u64 end2 = off2 + sz2;
        while (off2 < end2 && !has_pos) {
          u32 w0 = wstk[off2];
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 ot = w0 & PW_LIT_MASK;
            if ((u64)ot < nlits) {
              i8 vo = vals[ot];
              if (vo < (i8)0 || (vo == (i8)0 && (ot & 1u) == 0u)) {
                has_pos = true;
              }
            }
            off2 = off2 + 1ULL;
          } else {
            off2 = off2 + 2ULL;
          }
        }
      }
    }
    v = v + 1ULL;
  }
  if (has_neg && has_pos) { return 0ULL; }
  return has_neg ? 2ULL : 1ULL;
}

u64 full_lucky_late_m7(FullHdr *h) {
  if (h->inconsistent != 0ULL) { h->probing = 0ULL; return 20ULL; }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (h->propagated < h->trail_end) {
    u64 pr0 = full_propagate(h);
    if (pr0 == 1ULL) { h->inconsistent = 1ULL; h->probing = 0ULL; return 20ULL; }
    if (pr0 == 2ULL) { h->probing = 0ULL; return 2ULL; }
  }
  h->probing = 1ULL;
  u64 pol = full_lucky_polar_m7(h);
  if (pol != 0ULL) {
    bool set_pos = (pol == 1ULL);
    i8 *vals = (i8 *)h->values;
    u32 *fl = (u32 *)h->flags;
    u32 *ftrl = (u32 *)h->frame_trail;
    u32 *fdec = (u32 *)h->frame_dec;
    u64 v = 0ULL;
    while (v < h->cur_vars) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        if (h->fuel == 0ULL) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 2ULL;
        }
        h->fuel = h->fuel - 1ULL;
        u32 lit = set_pos ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
        u64 nlvl = h->cur_level + 1ULL;
        if (nlvl > h->max_vars) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL;
        }
        ftrl[nlvl] = (u32)h->trail_end;
        fdec[nlvl] = lit;
        h->cur_level = nlvl;
        full_assign(h, lit, 0xFFFFFFFFu);
        u64 pr = full_propagate(h);
        if (pr == 2ULL) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 2ULL;
        }
        if (pr == 1ULL) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL;
        }
      }
      v = v + 1ULL;
    }
    h->probing = 0ULL;
    return 10ULL;
  }
  u64 r = full_lucky_scan(h, false, true);
  if (r == 0ULL) { r = full_lucky_scan(h, true, true); }
  if (r == 0ULL) { r = full_lucky_scan(h, false, false); }
  if (r == 0ULL) { r = full_lucky_scan(h, true, false); }
  h->probing = 0ULL;
  return r;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Lucky

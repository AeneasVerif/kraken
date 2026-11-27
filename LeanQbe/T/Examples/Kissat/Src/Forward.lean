/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Forward Subsumption & Strengthening (`Src/Forward.lean`)

Mirrors upstream `kissat/src/forward.c` (`9` live functions, DAG level `L4`):
- `full_fwd_dedup_bins` (R4: `kissat_remove_duplicated_binaries`)
- `full_fwd_flush_large_m7` (R4: `kissat_forward_flush_large`)
- `full_dense_bin_roundtrip_fid`
- `full_fwd_reconnect_irred_m7` (R4: `kissat_forward_reconnect_irredundant`)
- `full_fwd_scan_lit_m7` (R4: `kissat_forward_scan_literal`)
- `full_fwd_check_cl_m7` (R4: `kissat_forward_check_clause`)
- `full_fwd_connect_subsumer_m7` (R4: `kissat_forward_connect_subsumer`)
- `full_fwd_collect_sort_m7` (R4: `kissat_forward_collect_and_sort`)
- `full_forward_sub_m7` (R4: `kissat_forward_subsume_during_elimination`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Forward

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! forward "
#include \"kissat_internal.h\"

extern bool full_add_unit(FullHdr *h, u32 lit);
extern void full_wstack_defrag(FullHdr *h);
extern void full_sweep_bins(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_dense_occ_cnt_fid(FullHdr *h, u32 lit, u64 cap);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);

bool full_fwd_dedup_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u8 *lm = (u8 *)h->lit_mark; u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    u64 p = off; u64 q = off; u64 end = off + sz; bool unit_l = false;
    while (p < end) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) == 0u) {
        if (p < end) { wstk[q] = w0; wstk[q + 1ULL] = wstk[p]; q = q + 2ULL; p = p + 1ULL; }
        continue;
      }
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits && lm[ot] != (u8)0) {
        if (l < (u64)ot && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
      } else {
        if ((u64)ot < nlits && lm[ot ^ 1u] != (u8)0) { unit_l = true; }
        if ((u64)ot < nlits) { lm[ot] = (u8)1; }
        wstk[q] = w0; q = q + 1ULL;
      }
    }
    u64 c = off;
    while (c < q) {
      if ((wstk[c] & PW_BIN_FLAG) != 0u) { lm[wstk[c] & PW_LIT_MASK] = (u8)0; }
      c = c + 1ULL;
    }
    c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off); h->wusable = h->wusable + (end - q);
    if (unit_l && !full_add_unit(h, (u32)l)) { return false; }
    l = l + 1ULL;
  }
  return true;
}

void full_fwd_flush_large_m7(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 0ULL) {
      u64 p = off;
      u64 q = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          wstk[q] = w0;
          q = q + 1ULL;
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      u64 c = q;
      while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
      wvec[(l << 1) + 1ULL] = (u32)(q - off);
      h->wusable = h->wusable + (end - q);
    }
    l = l + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
}

void full_dense_bin_roundtrip_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (nlits == 0ULL) { return; }
  full_fwd_flush_large_m7(h);
  if (h->num_binary == 0ULL || h->wcap == 0ULL) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  i8 *vals = (i8 *)h->values;
  u8 *lm = (u8 *)h->lit_mark;
  u32 *pairs = (u32 *)h->scratch_buf;
  u64 scap_pairs = h->scratch_cap >> 1;
  u64 nb = 0ULL;
  bool overflow = false;
  u64 l = 0ULL;
  while (l < nlits && !overflow) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 0ULL) {
      i8 lv = vals[l];
      u64 p = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && lm[ot] == (u8)0) {
            lm[ot] = (u8)1;
            if (lv <= (i8)0 && vals[ot] <= (i8)0 && l < (u64)ot) {
              if (nb < scap_pairs) {
                pairs[nb << 1] = (u32)l;
                pairs[(nb << 1) + 1ULL] = ot;
                nb = nb + 1ULL;
              } else {
                overflow = true;
                break;
              }
            }
          }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits) { lm[ot] = (u8)0; }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
    }
    l = l + 1ULL;
  }
  if (overflow) {
    full_sweep_bins(h);
    return;
  }
  l = 0ULL;
  while (l < nlits) {
    wvec[l << 1] = 0u;
    wvec[(l << 1) + 1ULL] = 0u;
    l = l + 1ULL;
  }
  wstk[0] = 0u;
  h->wlen = 1ULL;
  h->wusable = 0ULL;
  h->num_binary = nb;
  u64 k = 0ULL;
  while (k < nb) {
    u32 a = pairs[k << 1];
    u32 b = pairs[(k << 1) + 1ULL];
    full_watch_push(h, a, (b & PW_LIT_MASK) | PW_BIN_FLAG, 0u, 1u);
    full_watch_push(h, b, (a & PW_LIT_MASK) | PW_BIN_FLAG, 0u, 1u);
    k = k + 1ULL;
  }
}

void full_fwd_reconnect_irred_m7(FullHdr *h) {
  full_fwd_flush_large_m7(h);
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 p = 0ULL;
  while (p < h->arena_len && h->oom == 0ULL) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      bool sat = false;
      u32 k = 0u;
      while (k < sz) {
        if (vals[ar[p + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
        k = k + 1u;
      }
      if (sat) {
        ar[p] = hdr | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      } else {
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
}

u32 full_fwd_scan_lit_m7(FullHdr *h, u32 cref, u32 sz, u32 scan_lit, bool check_bins) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)scan_lit << 1];
  u64 wsz = (u64)wvec[((u64)scan_lit << 1) + 1ULL];
  if (wsz == 0ULL || full_dense_occ_cnt_fid(h, scan_lit, 1001ULL) > 1000ULL) {
    return 0xFFFFFFFFu;
  }
  u64 end = off + wsz;
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if (check_bins) {
        u32 ot = w0 & PW_LIT_MASK;
        if (lm[ot] != (u8)0) { return 0xFFFFFFFEu; }
        if ((ot ^ 1u) != scan_lit && lm[ot ^ 1u] != (u8)0) { return ot ^ 1u; }
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    if (cr == cref || (ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
    u32 dsz = ar[(u64)cr + 2ULL];
    if (dsz > sz) { continue; }
    u32 miss = 0u;
    u32 cand = 0xFFFFFFFFu;
    u32 j = 0u;
    while (j < dsz) {
      u32 dl = ar[(u64)cr + 3ULL + (u64)j];
      if (lm[dl] == (u8)0 && vals[dl] >= (i8)0) {
        if (lm[dl ^ 1u] != (u8)0 && cand == 0xFFFFFFFFu) { cand = dl ^ 1u; }
        else { miss = 1u; break; }
      }
      j = j + 1u;
    }
    if (miss == 0u) {
      if (cand == 0xFFFFFFFFu) { return 0xFFFFFFFEu; }
      return cand;
    }
  }
  return 0xFFFFFFFFu;
}

bool full_fwd_check_cl_m7(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return true; }
  while (true) {
    bool sat = false;
    u32 drop = 0xFFFFFFFFu;
    u32 i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      i8 vl = vals[l];
      if (vl > (i8)0) { sat = true; break; }
      if (vl < (i8)0 && drop == 0xFFFFFFFFu) { drop = l; }
      i = i + 1u;
    }
    if (sat) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      return true;
    }
    bool subsumed = false;
    if (drop == 0xFFFFFFFFu) {
      u32 min_l = ar[(u64)cref + 3ULL];
      u32 min_deg = wvec[((u64)min_l << 1) + 1ULL];
      i = 0u;
      while (i < sz) {
        u32 l = ar[(u64)cref + 3ULL + (u64)i];
        lm[l] = (u8)1;
        u32 d = wvec[((u64)l << 1) + 1ULL];
        if (d < min_deg) { min_deg = d; min_l = l; }
        i = i + 1u;
      }
      i = 0u;
      while (i < sz && !subsumed && drop == 0xFFFFFFFFu) {
        u32 l = (i == 0u) ? min_l : ar[(u64)cref + 3ULL + (u64)i];
        if (i > 0u && l == min_l) { l = ar[(u64)cref + 3ULL]; }
        u32 r1 = full_fwd_scan_lit_m7(h, cref, sz, l, true);
        if (r1 == 0xFFFFFFFEu) { subsumed = true; break; }
        if (r1 != 0xFFFFFFFFu) { drop = r1; break; }
        u32 r2 = full_fwd_scan_lit_m7(h, cref, sz, l ^ 1u, false);
        if (r2 == 0xFFFFFFFEu) { subsumed = true; break; }
        if (r2 != 0xFFFFFFFFu) { drop = r2; break; }
        i = i + 1u;
      }
      i = 0u;
      while (i < sz) { lm[ar[(u64)cref + 3ULL + (u64)i]] = (u8)0; i = i + 1u; }
    }
    if (subsumed) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      h->fwd_sub_cnt = h->fwd_sub_cnt + 1ULL;
      return true;
    }
    if (drop == 0xFFFFFFFFu) { return true; }
    h->fwd_str_cnt = h->fwd_str_cnt + 1ULL;
    full_unwatch_large(h, drop, cref);
    u32 nsz = 0u;
    i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      if (l != drop) { tmp[nsz] = l; nsz = nsz + 1u; }
      i = i + 1u;
    }
    if (nsz >= sz) { return true; }
    if (nsz == 0u) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      h->inconsistent = 1ULL;
      return false;
    }
    if (nsz == 1u) {
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, tmp[0])) { return false; }
      return full_dense_flush_units_m7(h);
    }
    if (nsz == 2u) {
      u32 b0 = tmp[0];
      u32 b1 = tmp[1];
      u64 br = full_add_bin(h, b0, b1);
      if (br == 20ULL) { return false; }
      if (br == 2ULL) { return true; }
      ar[cref] = hdr | PH_GARB | PH_SUBSUME;
      ar[(u64)cref + 3ULL] = b0;
      ar[(u64)cref + 4ULL] = b1;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      return full_dense_flush_units_m7(h);
    }
    i = 0u;
    while (i < nsz) { ar[(u64)cref + 3ULL + (u64)i] = tmp[i]; i = i + 1u; }
    ar[(u64)cref + 2ULL] = nsz;
    ar[(u64)cref + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[(u64)cref + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
      hdr = hdr | PH_SHRK;
      ar[cref] = hdr;
    }
    hdr = hdr | PH_SUBSUME;
    ar[cref] = hdr;
    sz = nsz;
  }
  return true;
}

void full_fwd_connect_subsumer_m7(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *fl = (u32 *)h->flags;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return; }
  u32 best_l = ar[(u64)cref + 3ULL];
  u32 best_d = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if ((fl[l >> 1] & FL_SUBSUME) != 0u) {
      u32 d = (u32)full_dense_occ_cnt_fid(h, l, 1001ULL);
      if (d < best_d) { best_d = d; best_l = l; }
    }
    i = i + 1u;
  }
  if (best_d == 0xFFFFFFFFu) {
    best_d = (u32)full_dense_occ_cnt_fid(h, best_l, 1001ULL);
    i = 1u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      u32 d = (u32)full_dense_occ_cnt_fid(h, l, 1001ULL);
      if (d < best_d) { best_d = d; best_l = l; }
      i = i + 1u;
    }
  }
  if (best_d <= 1000u) {
    if (!full_watch_push(h, best_l, sz & PW_LIT_MASK, cref, 2u)) { h->oom = 1ULL; }
  }
}

u64 full_fwd_collect_sort_m7(FullHdr *h) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *rr = (u32 *)h->red_refs;
  u64 half = h->red_cap >> 1;
  u64 ncand = 0ULL;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      if ((hdr & PH_SUBSUME) != 0u) {
        hdr = hdr & (~PH_SUBSUME);
        ar[p] = hdr;
      }
      bool sat = false;
      u32 scnt = 0u;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        i8 vl = vals[l];
        if (vl > (i8)0) { sat = true; break; }
        if (vl == (i8)0 && (fl[l >> 1] & FL_SUBSUME) != 0u) { scnt = scnt + 1u; }
        k = k + 1u;
      }
      if (sat) {
        ar[p] = hdr | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      } else if (sz <= 1000u && scnt >= 2u && ncand < half) {
        rr[ncand] = (u32)p;
        ncand = ncand + 1ULL;
      }
    }
    p = np;
  }
  if (ncand > 1ULL && h->scratch_cap >= 1008ULL) {
    u32 *scr = (u32 *)h->scratch_buf;
    u64 b = 0ULL;
    while (b <= 1000ULL) { scr[b] = 0u; b = b + 1ULL; }
    u64 i = 0ULL;
    while (i < ncand) {
      u32 cr = rr[i];
      rr[half + i] = cr;
      u32 sz = ar[(u64)cr + 2ULL];
      if (sz <= 1000u) { scr[sz] = scr[sz] + 1u; }
      i = i + 1ULL;
    }
    u32 sum = 0u;
    b = 0ULL;
    while (b <= 1000ULL) {
      u32 cnt = scr[b];
      scr[b] = sum;
      sum = sum + cnt;
      b = b + 1ULL;
    }
    i = 0ULL;
    while (i < ncand) {
      u32 cr = rr[i];
      u32 sz = ar[(u64)cr + 2ULL];
      if (sz <= 1000u) {
        u64 pos = (u64)scr[sz];
        if (pos < ncand) {
          rr[half + pos] = cr;
          scr[sz] = (u32)(pos + 1ULL);
        }
      }
      i = i + 1ULL;
    }
    i = 0ULL;
    while (i < ncand) { rr[i] = rr[half + i]; i = i + 1ULL; }
  }
  return ncand;
}

u64 full_forward_sub_m7(FullHdr *h, u64 budget) {
  if (budget == 0ULL) { full_fwd_reconnect_irred_m7(h); return 1ULL; }
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  u64 saved_prop = h->propagated;
  u64 ncand = full_fwd_collect_sort_m7(h);
  if (ncand == 0ULL) {
    full_fwd_reconnect_irred_m7(h);
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  full_fwd_flush_large_m7(h);
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  u64 rem = budget;
  while (i < ncand && rem > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 cr = rr[i];
    rem = rem - 1ULL;
    if (!full_fwd_check_cl_m7(h, cr)) { return 20ULL; }
    if (h->oom == 0ULL && h->inconsistent == 0ULL && (ar[cr] & PH_GARB) == 0u) {
      full_fwd_connect_subsumer_m7(h, cr);
    }
    i = i + 1ULL;
  }
  if (i == ncand && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 *fl = (u32 *)h->flags;
    u64 cv = h->cur_vars;
    u64 v = 0ULL;
    while (v < cv) { fl[v] = fl[v] & (~FL_SUBSUME); v = v + 1ULL; }
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_SUBSUME) != 0u) {
        ar[p] = hdr & (~PH_SUBSUME);
        if ((hdr & PH_GARB) == 0u) {
          u32 k = 0u;
          while (k < sz) {
            u32 lv = ar[p + 3ULL + (u64)k] >> 1;
            if ((u64)lv < cv) { fl[lv] = fl[lv] | FL_SUBSUME | FL_ELIM_C; }
            k = k + 1u;
          }
        } else if (sz >= 2u) {
          u32 v0 = ar[p + 3ULL] >> 1;
          u32 v1 = ar[p + 4ULL] >> 1;
          if ((u64)v0 < cv) { fl[v0] = fl[v0] | FL_SUBSUME | FL_ELIM_C; }
          if ((u64)v1 < cv) { fl[v1] = fl[v1] | FL_SUBSUME | FL_ELIM_C; }
        }
      }
      p = np;
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  full_fwd_reconnect_irred_m7(h);
  if (saved_prop < h->propagated && saved_prop <= h->trail_end) {
    h->propagated = saved_prop;
  }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Forward

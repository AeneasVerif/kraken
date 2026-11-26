/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Extended Header Tiers, Delays, Watermarks & Decision Rate (`Src/Tiers.lean`)

Mirrors upstream `kissat/src/tiers.c` (`18` live functions, DAG level `L0`):
- `m6_hdr_init` (R4: `kissat_tiers_init`)
- `m6_ext_ensure_init` (R4: `kissat_tiers_ensure_init`)
- `m6_hdr_sync_legacy_tiers` (R4: `kissat_sync_tier_limits`)
- `m6_hdr_recompute_tiers_mode` (R4: `kissat_compute_tier_limits_mode`)
- `m6_hdr_recompute_tiers` (R4: `kissat_compute_and_set_tier_limits`)
- `m6_hdr_update_tier_limits` (R4: `kissat_update_tier_limits`)
- `m6_hdr_record_used` (R4: `kissat_record_glue_used`)
- `m6_hdr_get_tier1` (R4: `kissat_get_tier1_limit`)
- `m6_hdr_get_tier2` (R4: `kissat_get_tier2_limit`)
- `m6_hdr_delaying` (R4: `kissat_delaying`)
- `m6_hdr_bump_delay` (R4: `kissat_bump_delay`)
- `m6_hdr_reduce_delay` (R4: `kissat_reduce_delay`)
- `m6_hdr_get_watermark` (R4: `kissat_get_watermark`)
- `m6_hdr_set_watermark` (R4: `kissat_set_watermark`)
- `m6_hdr_dr_init` (R4: `kissat_decision_rate_init`)
- `m6_hdr_dr_update` (R4: `kissat_decision_rate_update`)
- `m6_hdr_dr_allow` (R4: `kissat_decision_rate_allow`)
- `full_recompute_tiers` (R4: `kissat_recompute_tiers_legacy`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Tiers

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! tiers "
#include \"kissat_internal.h\"

void m6_hdr_init(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 i = 0ULL;
  while (i < M6_EXT_WORDS) {
    e[i] = 0ULL;
    i = i + 1ULL;
  }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_SE] = 1ULL << 32;
  e[M6W_DR_SE + 1ULL] = 1ULL << 32;
  e[M6W_TIER1] = 2ULL;
  e[M6W_TIER1 + 1ULL] = 2ULL;
  e[M6W_TIER2] = 6ULL;
  e[M6W_TIER2 + 1ULL] = 6ULL;
  e[M6W_GLUE_INTV] = 2ULL;
  e[M6W_WM_BASE] = h->fwd_sub_cnt;
  e[M6W_WM_BASE + 1ULL] = 0ULL;
  e[M6W_MAGIC] = M6_HDR_MAGIC;
}

void m6_ext_ensure_init(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if (e[M6W_MAGIC] != M6_HDR_MAGIC) {
    m6_hdr_init(h);
  }
}

void m6_hdr_sync_legacy_tiers(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 t1 = e[M6W_TIER1];
  u64 t2 = e[M6W_TIER2 + 1ULL];
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1;
  h->tier2 = t2;
}

void m6_hdr_recompute_tiers_mode(FullHdr *h, u64 st) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 mode = (st != 0ULL) ? 1ULL : 0ULL;
  u64 base = (mode == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < M6_GLUE_BINS) {
    u64 u = e[base + g];
    if (total <= 0xFFFFFFFFFFFFFFFFULL - u) { total = total + u; }
    else { total = 0xFFFFFFFFFFFFFFFFULL; }
    g = g + 1ULL;
  }
  e[M6W_TOTAL_USED + mode] = total;
  u64 t1 = 2ULL; u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total == 1ULL) ? 1ULL : (total >> 1);
    u64 lim2 = (total == 1ULL) ? 1ULL :
      ((total / 10ULL) * 9ULL + (((total % 10ULL) * 9ULL) / 10ULL));
    u64 acc = 0ULL; bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < M6_GLUE_BINS) {
      u64 u = e[base + g];
      if (acc <= 0xFFFFFFFFFFFFFFFFULL - u) { acc = acc + u; }
      else { acc = 0xFFFFFFFFFFFFFFFFULL; }
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  e[M6W_TIER1 + mode] = t1;
  e[M6W_TIER2 + mode] = t2;
  m6_hdr_sync_legacy_tiers(h);
}

void m6_hdr_recompute_tiers(FullHdr *h) {
  m6_hdr_recompute_tiers_mode(h, (h->stable != 0ULL) ? 1ULL : 0ULL);
}

void m6_hdr_update_tier_limits(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 next_c = e[M6W_GLUE_NEXT];
  if (h->conflicts > next_c) {
    m6_hdr_recompute_tiers(h);
    u64 iv = e[M6W_GLUE_INTV];
    if (iv == 0ULL) { iv = 2ULL; }
    else if (iv < M6_GLUE_INTERVAL_MAX) { iv = iv << 1; }
    e[M6W_GLUE_INTV] = iv;
    e[M6W_GLUE_NEXT] = h->conflicts + iv;
  }
}

void m6_hdr_record_used(FullHdr *h, u64 glue) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 gi = (glue >= M6_GLUE_BINS) ? (M6_GLUE_BINS - 1ULL) : glue;
  u64 base = (st == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 u = e[base + gi];
  if (u < 0xFFFFFFFFFFFFFFFFULL) { e[base + gi] = u + 1ULL; }
  u64 tu = e[M6W_TOTAL_USED + st];
  if (tu < 0xFFFFFFFFFFFFFFFFULL) { e[M6W_TOTAL_USED + st] = tu + 1ULL; }
}

u64 m6_hdr_get_tier1(FullHdr *h, bool vivify_mode) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = vivify_mode ? 0ULL : ((h->stable != 0ULL) ? 1ULL : 0ULL);
  return e[M6W_TIER1 + st];
}

u64 m6_hdr_get_tier2(FullHdr *h, bool vivify_mode) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 t1 = e[M6W_TIER1];
  u64 st = vivify_mode ? 0ULL : 1ULL;
  u64 t2 = e[M6W_TIER2 + st];
  return (t2 < t1) ? t1 : t2;
}

bool m6_hdr_delaying(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return false; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cnt = e[M6W_DELAY_CNT + id];
  if (cnt > 0ULL) {
    e[M6W_DELAY_CNT + id] = cnt - 1ULL;
    return true;
  }
  return false;
}

void m6_hdr_bump_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cur = e[M6W_DELAY_CUR + id];
  if (cur < 0xFFFFFFFFULL) { cur = cur + 1ULL; }
  e[M6W_DELAY_CUR + id] = cur;
  e[M6W_DELAY_CNT + id] = cur;
}

void m6_hdr_reduce_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cur = e[M6W_DELAY_CUR + id] >> 1;
  e[M6W_DELAY_CUR + id] = cur;
  e[M6W_DELAY_CNT + id] = cur;
}

u64 m6_hdr_get_watermark(FullHdr *h, u64 kind) {
  if (kind >= 8ULL) { return 0ULL; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  return e[M6W_WM_BASE + kind];
}

void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val) {
  if (kind >= 8ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  e[M6W_WM_BASE + kind] = val;
}

void m6_hdr_dr_init(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if ((e[M6W_DR_STATE] >> 63) != 0ULL) { return; }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_PREV] = 0ULL;
  e[M6W_DR_PREV + 1ULL] = 0ULL;
  e[M6W_DR_SB] = 0ULL;
  e[M6W_DR_SB + 1ULL] = 0ULL;
  e[M6W_DR_SE] = 1ULL << 32;
  e[M6W_DR_SE + 1ULL] = 1ULL << 32;
}

void m6_hdr_dr_update(FullHdr *h) {
  m6_hdr_dr_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 cur = st & mask56;
  u64 last_sw = (st >> 56) & 127ULL;
  u64 cur_sw = h->switched & 127ULL;
  u64 mode = (h->stable != 0ULL) ? 1ULL : 0ULL;
  if (cur_sw != last_sw) {
    e[M6W_DR_STATE] = (1ULL << 63) | (cur_sw << 56) | cur;
    e[M6W_DR_PREV + mode] = cur;
    e[M6W_DR_SB + mode] = 0ULL;
    e[M6W_DR_SE + mode] = 1ULL << 32;
    return;
  }
  u64 prev = e[M6W_DR_PREV + mode];
  e[M6W_DR_PREV + mode] = cur;
  u64 d = (cur >= prev) ? (cur - prev) : 0ULL;
  if (d > 16383ULL) { d = 16383ULL; }
  u64 ys = d << 32;
  u64 sb = e[M6W_DR_SB + mode];
  u64 se = e[M6W_DR_SE + mode];
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  if (se > 0ULL) {
    u64 ds = se / 100000ULL;
    se = (ds == 0ULL) ? 0ULL : (se - ds);
  }
  e[M6W_DR_SB + mode] = sb;
  e[M6W_DR_SE + mode] = se;
}

bool m6_hdr_dr_allow(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if ((e[M6W_DR_STATE] >> 63) == 0ULL) { return true; }
  u64 mode = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 sb = e[M6W_DR_SB + mode];
  u64 se = e[M6W_DR_SE + mode];
  u64 scale = 1ULL << 32;
  u64 sd = (scale > se) ? (scale - se) : 0ULL;
  if (sd == 0ULL) { return true; }
  return sb < (sd * 10ULL);
}

void full_recompute_tiers(FullHdr *h) {
  u32 *gu = (u32 *)h->glue_used;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < 64ULL) { total = total + (u64)gu[g]; g = g + 1ULL; }
  u64 t1 = 2ULL;
  u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total + 1ULL) >> 1;
    u64 lim2 = (total * 9ULL + 9ULL) / 10ULL;
    u64 acc = 0ULL;
    bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < 64ULL) {
      acc = acc + (u64)gu[g];
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1; h->tier2 = t2;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Tiers

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Probing Orchestrator (`Src/Probe.lean`)

Mirrors upstream `kissat/src/probe.c` (`2` live functions, DAG level `L6`):
- `full_probe_dticks_m6_hdr` (R4: `kissat_probe_delta_ticks`)
- `full_probe_m6` (R4: `kissat_probe`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Probe

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! probe "
#include \"kissat_internal.h\"

extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern void full_dense_bin_roundtrip_fid(FullHdr *h);
extern u64 full_rebuild_watches_nosort_fid(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64 full_substitute(FullHdr *h);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern bool full_has_factor_cands_fid(FullHdr *h);
extern bool full_enter_dense_ex_fid(FullHdr *h, bool connect_large);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);
extern void full_update_classify_fid(FullHdr *h);
extern u64 f64u_mul(u64 a, u64 b);
extern u64 f64u_nlogpown(u64 count, u64 exponent);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern u64 f64u_to_u64(u64 a);

u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial) {
  if (initial) { return 10000000ULL; }
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 raw = (h->search_ticks > last_p) ? (h->search_ticks - last_p) : 0ULL;
  return (raw > 10000000ULL) ? raw : 10000000ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  h->probings = h->probings + 1ULL;
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  if (initial) {
    bool subst_at_end = true;
    if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
      if (full_enter_dense(h)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, 0xFFFFFFFFFFFFFFFFULL) == 20ULL) {
          full_dense_bin_roundtrip_fid(h);
          full_rebuild_watches_nosort_fid(h);
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        full_dense_bin_roundtrip_fid(h);
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if (ca > cb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
      h->probing = saved_prob;
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
      if (full_enter_dense(h)) {
        u32 *gu_sw = (u32 *)h->glue_used;
        gu_sw[SWP_GU_SWEPT] = 0u;
        u64 sb = h->sweep_cnt;
        if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 sa = h->sweep_cnt;
        u64 swept = (u64)gu_sw[SWP_GU_SWEPT];
        if (sa > sb && swept > 0ULL && (sa - sb) * 1000ULL >= swept) {
          m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if (sa > sb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (subst_at_end && h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      h->probing = saved_prob;
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    u64 fr = 1ULL; u64 fp = 10ULL; u64 fa = h->unassigned / 10ULL;
    while (fa >= fp && fr < 19ULL) { fr = fr + 1ULL; fp = fp * 10ULL; }
    u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
    if (h->unassigned > 0ULL && fr <= fe4 && full_has_factor_cands_fid(h)) {
      if (full_enter_dense_ex_fid(h, false)) {
        u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
        m6_hdr_set_watermark(h, 1ULL, nfact);
        u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
        full_factor(h, fbud);
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      } else if (h->inconsistent != 0ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
  } else {
    u64 round = 0ULL;
    while (round < 2ULL) {
      u32 *fl_a = (u32 *)h->flags;
      u64 before_act = 0ULL;
      u64 ai = 0ULL;
      while (ai < h->cur_vars) {
        if ((fl_a[ai] & 1u) != 0u) { before_act = before_act + 1ULL; }
        ai = ai + 1ULL;
      }
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        if (full_enter_dense(h)) {
          u64 cb = h->cong_cnt;
          if (full_congruence_dense(h, 0xFFFFFFFFFFFFFFFFULL) == 20ULL) {
            full_dense_bin_roundtrip_fid(h);
            full_rebuild_watches_nosort_fid(h);
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 ca = h->cong_cnt;
          if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
          }
          full_dense_bin_roundtrip_fid(h);
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        } else if (h->inconsistent != 0ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (full_vivify_m6_hdr(h) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
        if (full_enter_dense(h)) {
          u32 *gu_sw = (u32 *)h->glue_used;
          gu_sw[SWP_GU_SWEPT] = 0u;
          u64 sb = h->sweep_cnt;
          if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 swept = (u64)gu_sw[SWP_GU_SWEPT];
          if (h->sweep_cnt > sb && swept > 0ULL && (h->sweep_cnt - sb) * 1000ULL >= swept) {
            m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        } else if (h->inconsistent != 0ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 tr_lim = dticks / 50ULL;
      if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, dticks / 50ULL) == 20ULL) {
        h->probing = saved_prob;
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 fr = 1ULL; u64 fp = 10ULL; u64 fa = h->unassigned / 10ULL;
      while (fa >= fp && fr < 19ULL) { fr = fr + 1ULL; fp = fp * 10ULL; }
      u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
      if (h->unassigned > 0ULL && fr <= fe4 && full_has_factor_cands_fid(h)) {
        if (full_enter_dense_ex_fid(h, false)) {
          u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
          m6_hdr_set_watermark(h, 1ULL, nfact);
          u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
          full_factor(h, fbud);
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            h->probing = saved_prob;
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        } else if (h->inconsistent != 0ULL) {
          h->probing = saved_prob;
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      fl_a = (u32 *)h->flags;
      u64 after_act = 0ULL;
      ai = 0ULL;
      while (ai < h->cur_vars) {
        if ((fl_a[ai] & 1u) != 0u) { after_act = after_act + 1ULL; }
        ai = ai + 1ULL;
      }
      if (before_act == after_act) { break; }
      round = round + 1ULL;
    }
  }
  full_update_classify_fid(h);
  if (!initial) {
    u64 nlogp = f64u_mul(0x4059000000000000ULL, f64u_nlogpown(h->probings, 1ULL));
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, f64u_to_u64(nlogp));
  }
  h->probing = saved_prob;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Probe

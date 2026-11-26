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
- `full_probe_m6` (R4: `kissat_probe`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Probe

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! probe "
#include \"kissat_internal.h\"

extern u64 full_log10_q16_m7(u64 x);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern void full_sort_bin_watches_fid(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches_nosort_fid(FullHdr *h);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_factor(FullHdr *h, u64 budget);

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
  if (!initial) {
    u64 parg = (h->probings > (~0ULL) - 9ULL) ? (~0ULL) : (h->probings + 9ULL);
    u64 qlog = full_log10_q16_m7(parg);
    u64 pc = (h->probings > 100000000ULL) ? 100000000ULL : h->probings;
    u64 nlogp = (100ULL * pc * qlog) >> 16;
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
  }
  bool bin_dirty = false;
  if (initial) {
    bool subst_at_end = true;
    if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
      if (full_enter_dense(h)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches_nosort_fid(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        bin_dirty = true;
        if (ca > cb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
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
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        bin_dirty = true;
        if (sa > sb) {
          subst_at_end = false;
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
        }
      } else if (h->inconsistent != 0ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    }
    if (subst_at_end && h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    u64 round = 0ULL;
    while (round < 2ULL) {
      u64 before_unass = h->unassigned;
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        if (full_enter_dense(h)) {
          u64 cb = h->cong_cnt;
          if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
            full_rebuild_watches_nosort_fid(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          u64 ca = h->cong_cnt;
          if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
          }
          if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          bin_dirty = true;
        } else if (h->inconsistent != 0ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (full_vivify_m6_hdr(h) == 20ULL) {
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
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          bin_dirty = true;
        } else if (h->inconsistent != 0ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
      if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      u64 tr_lim = (dticks / 50ULL) + 100000ULL;
      if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->num_binary > 0ULL &&
          full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
      if (h->unassigned >= before_unass) { break; }
      round = round + 1ULL;
    }
  }
  u64 fr = 1ULL;
  u64 fp = 10ULL;
  u64 fa = h->unassigned / 10ULL;
  while (fa >= fp && fr < 19ULL) {
    fr = fr + 1ULL;
    fp = fp * 10ULL;
  }
  u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
  if (h->unassigned > 0ULL && fr <= fe4 && full_enter_dense(h)) {
    u64 nfact = m6_hdr_get_watermark(h, 1ULL) + 1ULL;
    m6_hdr_set_watermark(h, 1ULL, nfact);
    u64 fbud = (nfact <= 1ULL) ? 700000000ULL : (dticks / 20ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches_nosort_fid(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    bin_dirty = true;
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  if (bin_dirty) { full_sort_bin_watches_fid(h); }
  h->search_ticks = saved_st;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}
"

/-- Ordered live functions of `Src/Probe.lean` (`2` fns). -/
def fns : List Fn := probe_fns

end

public section

theorem full_probe_dticks_m6_hdr_wf : Func.Wf full_probe_dticks_m6_hdr_body := by kissat_wf_reify
theorem full_probe_m6_wf : Func.Wf full_probe_m6_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, probe_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact full_probe_dticks_m6_hdr_wf
  · exact full_probe_m6_wf

end

end LeanQbe.T.Examples.Kissat.Src.Probe

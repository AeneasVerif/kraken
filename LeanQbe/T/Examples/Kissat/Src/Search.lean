/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Preprocessing, Main CDCL Search Loop & Top-Level Entry (`Src/Search.lean`)

Mirrors upstream `kissat/src/preprocess.c, search.c, internal.c`
(`5` live functions, DAG level `L7`):
- `full_preprocess_m6` (R4: `kissat_preprocess`)
- `full_simplify_m6` (R4: `kissat_simplify`)
- `full_search_m6` (R4: `kissat_search`)
- `kissat_solve_bytes_m6` (R4: `kissat_solve_bytes_impl`)
- `kissat_solve_bytes` (R4: `kissat_solve_bytes`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Search

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! search "
#include \"kissat_internal.h\"

extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d, i8 *vals, u64 mv_max);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_m6_mem_init(u64 cnf_ptr, u64 cnf_end, u64 work_base, u64 avail, u64 fuel);
extern u64 full_propagate(FullHdr *h);
extern u64 full_parse_body(FullHdr *h, u64 cnf_end);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern u64 m6_hdr_decide_fid(FullHdr *h);
extern void full_rephase(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern void full_switch_mode_m7(FullHdr *h);
extern void full_extend(FullHdr *h);
extern u64 full_lucky_late_m7(FullHdr *h);
extern u64 full_eliminate_m6(FullHdr *h, bool initial);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);
extern u64 full_reorder_m6(FullHdr *h, u64 budget);
extern u64 full_probe_m6(FullHdr *h, bool initial);

u64 full_preprocess_m6(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  u64 saved_lk_ticks = h->search_ticks;
  u64 lk = full_lucky_late_m7(h);
  h->search_ticks = saved_lk_ticks;
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL || h->trail_end > 0ULL) {
    while (true) {
      u64 sr2 = full_arena_sweep(h);
      if (sr2 == 2ULL) { return 20ULL; }
      if (sr2 == 3ULL || h->oom != 0ULL) { break; }
      u64 pr2 = full_propagate(h);
      if (pr2 == 1ULL) { return 20ULL; }
      if (pr2 == 2ULL) { break; }
      if (sr2 == 0ULL && h->propagated >= h->trail_end) { break; }
    }
    h->unflushed = 0ULL;
  }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  if (full_probe_m6(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  return 1ULL;
}

u64 full_simplify_m6(FullHdr *h, bool do_probe, bool do_elim) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (do_probe && full_probe_m6(h, false) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (do_elim && full_eliminate_m6(h, false) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  return 1ULL;
}

u64 full_search_m6(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  u64 reordered = 0ULL;
  u64 last_reduce_cfl = 0xFFFFFFFFFFFFFFFFULL;
  u64 lkr = full_lucky_late_m7(h);
  if (lkr == 10ULL || lkr == 20ULL) { return lkr; }
  h->search_ticks = 0ULL; h->mode_saved_ticks = 0ULL;
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, 0ULL); h->fwd_str_cnt = 0ULL;
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
    } else if (h->unassigned == 0ULL) {
      return 10ULL;
    } else if (h->fuel == 0ULL) {
      return 0ULL;
    } else if (h->conflicts >= h->reduce_limit) {
      last_reduce_cfl = h->conflicts;
      h->fuel = h->fuel - 1ULL;
      u64 rr = full_reduce_m6(h, false);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
    } else if ((h->stable == 0ULL) ? (h->conflicts >= h->mode_confl_lim)
                                   : (h->search_ticks >= h->mode_tick_lim)) {
      h->fuel = h->fuel - 1ULL;
      full_switch_mode_m7(h);
    } else if (full_restart_due(h) != 0ULL) {
      h->fuel = h->fuel - 1ULL;
      full_restart(h);
    } else if (h->cur_level == 0ULL && h->conflicts >= reorder_limit) {
      reordered = reordered + 1ULL;
      reorder_limit = h->conflicts + 10000ULL * reordered;
      h->fuel = h->fuel - 1ULL;
      full_reorder_m6(h, 256ULL);
    } else if (h->stable != 0ULL && h->conflicts >= h->rephase_limit) {
      h->fuel = h->fuel - 1ULL;
      full_rephase(h);
    } else if (h->conflicts != last_reduce_cfl && h->conflicts > h->probe_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, true, false);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else if (h->conflicts != last_reduce_cfl && h->conflicts >= h->elim_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, false, true);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else {
      if (m6_hdr_decide_fid(h) == 0ULL) {
        return (h->unassigned == 0ULL) ? 10ULL : 0ULL;
      }
    }
  }
}

u64 kissat_solve_bytes_m6(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + M6_HDR_TOTAL_BYTES) { return 0ULL; }
  u64 work_base = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  u64 hdr_addr = full_m6_mem_init(cnf_ptr, cnf_end, work_base, avail, fuel);
  if (hdr_addr == 0ULL) { return 0ULL; }
  FullHdr *h = (FullHdr *)hdr_addr;
  u64 pb = full_parse_body(h, cnf_end);
  if (pb != 1ULL) { return pb; }
  u64 orig_mv = h->d.mv;
  u64 pp = full_preprocess_m6(h);
  if (pp == 20ULL) { return 20ULL; }
  u64 r = (pp == 10ULL) ? 10ULL : ((pp == 0ULL) ? 0ULL : full_search_m6(h));
  if (r == 10ULL) {
    full_extend(h);
    h->d.mv = orig_mv;
    h->bva_cap = h->max_vars - orig_mv;
    u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, orig_mv);
    return (ok == 1ULL) ? 10ULL : 0ULL;
  }
  return r;
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  return kissat_solve_bytes_m6(cnf_ptr, cnf_len, work_ptr, work_cap, fuel);
}
"

/-- Ordered live functions of `Src/Search.lean` (`5` fns). -/
def fns : List Fn := search_fns

end

public section

theorem full_preprocess_m6_wf : Func.Wf full_preprocess_m6_body := by kissat_wf_reify
theorem full_simplify_m6_wf : Func.Wf full_simplify_m6_body := by kissat_wf_reify
theorem full_search_m6_wf : Func.Wf full_search_m6_body := by kissat_wf_reify
theorem kissat_solve_bytes_m6_wf : Func.Wf kissat_solve_bytes_m6_body := by kissat_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, search_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_preprocess_m6_wf
  · exact full_simplify_m6_wf
  · exact full_search_m6_wf
  · exact kissat_solve_bytes_m6_wf
  · exact kissat_solve_bytes_wf

end

end LeanQbe.T.Examples.Kissat.Src.Search

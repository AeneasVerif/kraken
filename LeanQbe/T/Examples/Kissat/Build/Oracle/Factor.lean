module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Factor

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_bva_connect_clauses_fid", ["full_bva_count_lit_deg_fid", "full_arena_next",
      "full_watch_push"]),
  ("full_bva_scan_cands", ["full_bva_clines_fid"]),
  ("full_bva_filter_row", ["full_bva_clines_fid", "full_bva_match_large_bva_fid"]),
  ("full_bva_commit", ["full_add_bin", "full_wstack_defrag", "full_bva_steps_cap_fid",
      "full_fill_u64_m7", "full_alloc_cl", "full_watch_push"]),
  ("full_bva_try_lit", ["full_bva_steps_cap_fid", "full_bva_pick_cand"]),
  ("full_bva_upd_lit_fid", ["full_bva_count_lit_deg_fid", "full_fheap_up_fid",
      "full_fheap_down_fid"]),
  ("full_factor", ["full_bva_steps_cap_fid", "full_fheap_up_fid", "full_fheap_down_fid"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Factor

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Forward

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_fwd_flush_large_m7", ["full_wstack_defrag"]),
  ("full_dense_bin_roundtrip_fid", ["full_sweep_bins", "full_watch_push"]),
  ("full_fwd_reconnect_irred_m7", ["full_arena_next", "full_watch_push"]),
  ("full_fwd_scan_lit_m7", ["full_dense_occ_cnt_fid"]),
  ("full_fwd_check_cl_m7", ["full_add_bin", "full_dense_flush_units_m7",
      "full_fwd_scan_lit_m7"]),
  ("full_fwd_connect_subsumer_m7", ["full_dense_occ_cnt_fid", "full_watch_push"]),
  ("full_fwd_collect_sort_m7", ["full_arena_next"]),
  ("full_forward_sub_m7", ["full_dense_flush_units_m7", "full_arena_next"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Forward

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Definition

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_k6_prop_m7", ["full_k6_assign_m7"]),
  ("full_k6_analyze_m7", ["full_k6_watch_m7", "full_k6_assign_m7", "full_k6_backtrack_m7"]),
  ("full_k6_solve_m7", ["full_k6_assign_m7", "full_k6_backtrack_m7"]),
  ("full_bve_def_k6_m7", ["full_k6_watch_m7"]),
  ("full_bve_gates_m7", ["full_bve_find_ite_m7"]),
  ("full_k6_prop_fid", ["full_fid_k6_add_ticks", "full_k6_assign_fid"]),
  ("full_k6_analyze_fid", ["full_k6_watch_fid", "full_k6_assign_fid", "full_k6_backtrack_fid",
      "full_k6_mtf_fid"]),
  ("full_k6_solve_fid", ["full_k6_assign_fid", "full_k6_backtrack_fid"]),
  ("full_k6_extract_and_solve_fid", ["full_bve_k6_mv_fid", "full_k6_watch_fid"]),
  ("full_bve_certify_unit_fid", ["full_m6_max_v", "full_assign_lvl"]),
  ("full_bve_def_k6_fid", ["full_bve_k6_mv_fid"]),
  ("full_bve_gates_fid", ["full_bve_find_ite_m8"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Definition

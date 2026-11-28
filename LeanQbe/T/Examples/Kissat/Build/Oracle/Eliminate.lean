module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_bve_weaken", ["full_extend_push2"]),
  ("full_bve_commit_res", ["full_add_bin", "full_alloc_cl", "full_watch_push"]),
  ("full_bve_var_m7", ["full_wstack_defrag", "full_bve_ext_need", "full_dense_flush_units_m7",
      "full_bve_collect_m7", "full_assign_lvl"]),
  ("full_bve_var_key_m7", ["f64u_to_u64", "full_dense_occ_cnt_fid"]),
  ("full_bve_heap_push_m7", ["full_bve_heap_up_m7", "full_bve_heap_down_m7"]),
  ("full_bve_heap_pop_m7", ["full_bve_heap_down_m7"]),
  ("full_elim_bve_m7", ["full_dense_flush_units_m7", "full_bve_heap_pop_m7"]),
  ("full_eliminate_m6", ["full_rebuild_watches", "f64u_to_u64", "full_elim_dticks",
      "full_has_elim_cands_fid", "full_update_classify_fid"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_m6_sweep_cone", ["full_m6_max_v"]),
  ("full_m6_sweep_refine_sig", ["full_m6_max_v"]),
  ("full_m6_sweep_rand_phases", ["full_m6_max_v"]),
  ("full_m6_sweep_solve", ["full_m6_sweep_rand_phases"]),
  ("full_m6_sweep_flip_round", ["full_m6_max_v", "full_k6_flip"]),
  ("full_m6_sweep_sim", ["full_m6_max_v", "full_m6_sweep_refine_sig", "full_m6_sweep_solve"]),
  ("full_m6_sweep_build_pht", ["full_m6_max_v"]),
  ("full_m6_extract_pht", ["full_m6_max_v"]),
  ("full_m6_refine_partition", ["full_m6_max_v"]),
  ("full_m6_sweep_units", ["full_m6_max_v", "full_m6_sweep_refine_sig", "full_m6_sweep_solve",
      "full_m6_sweep_rearm", "full_k6_flip"]),
  ("full_m6_sweep_classes", ["full_m6_max_v", "full_m6_sweep_refine_sig",
      "full_m6_sweep_solve", "full_m6_sweep_rearm", "full_k6_flip"]),
  ("full_m6_els_ar", ["full_add_bin", "full_cong_find", "full_watch_push"]),
  ("full_m6_els_lit", ["full_add_bin"]),
  ("full_m6_dense_els", ["full_add_bin", "full_cong_find", "full_m6_dense_prop"]),
  ("full_m6_sweep_var", ["full_m6_max_v", "full_cong_find"]),
  ("full_m6_collect_cands", ["full_dense_occ_cnt_fid", "full_m6_cand_sift"]),
  ("full_m6_sweep_vars", ["full_m6_max_v", "full_cong_find", "full_m6_dense_prop",
      "full_dense_occ_cnt_fid"]),
  ("full_sweep_dense_m6", ["full_m6_max_v"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep

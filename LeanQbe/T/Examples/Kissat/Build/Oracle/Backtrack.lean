module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_assign", ["full_assign_lvl"]),
  ("full_backtrack_raw_m5", ["full_save_target_best", "full_heap_push"]),
  ("full_backtrack", ["full_save_target_best"]),
  ("full_backtrack_ac_fid", ["full_save_target_best"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack

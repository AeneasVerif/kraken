module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_min_lit_dfs_m8", ["full_min_mark"]),
  ("full_shrink_lower_m8", ["full_min_mark"]),
  ("full_shrink_blk_bool_m8", ["full_min_mark", "full_shrink_lower_m8"]),
  ("full_min_shrink_m6", ["full_min_mark"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize

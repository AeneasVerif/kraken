module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Clause

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_add_clause", ["full_alloc_cl", "full_watch_pop_c0", "full_watch_push"]),
  ("full_add_bin_m6", ["full_has_bin", "full_assign_lvl", "full_watch_push"]),
  ("full_add_unit", ["full_assign_lvl"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Clause

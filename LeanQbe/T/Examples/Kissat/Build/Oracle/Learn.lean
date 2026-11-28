module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Learn

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_one_lit_confl", ["full_wstack_defrag", "full_det_new_level", "full_assign_lvl",
      "full_watch_push"]),
  ("full_learn_clause_m6", ["full_wstack_defrag", "full_det_new_level", "full_assign_lvl"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Learn

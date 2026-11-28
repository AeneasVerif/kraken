module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_k6_init", ["full_m6_max_v"]),
  ("full_k6_add_clause", ["full_m6_max_v", "full_k6_add_ticks", "full_k6_watch",
      "full_k6_assign"]),
  ("full_k6_analyze", ["full_k6_watch", "full_k6_assign", "full_k6_backtrack",
      "full_k6_ana_clause", "full_k6_mtf"]),
  ("full_k6_solve", ["full_m6_max_v", "full_k6_assign", "full_k6_backtrack"]),
  ("full_k6_flip", ["full_m6_max_v", "full_k6_add_ticks"]),
  ("full_k512_add_live_m6", ["full_m6_max_v", "full_k6_watch", "full_k6_assign",
      "full_k6_backtrack"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten

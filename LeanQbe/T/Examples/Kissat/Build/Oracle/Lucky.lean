module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_lucky_scan", ["full_propagate", "full_analyze_m6_hdr", "full_assign"]),
  ("full_lucky_polar_m7", ["full_arena_next"]),
  ("full_lucky_late_m7", ["full_propagate", "full_assign"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky

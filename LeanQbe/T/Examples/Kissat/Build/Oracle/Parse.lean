module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Parse

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_activate_lit_fid", ["full_heap_push"]),
  ("full_ingest_cl", ["full_assign_lvl", "kissat_next_lit"]),
  ("full_parse_body_m6", ["full_propagate", "full_wstack_defrag", "full_tumble_finish_fid",
      "kissat_skip_ws_comments"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Parse

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("kissat_skip_ws_comments", ["kissat_is_ws"]),
  ("kissat_skip_ws1", ["kissat_is_ws"]),
  ("kissat_read_nat", ["kissat_is_digit", "kissat_is_ws"]),
  ("kissat_parse_header", ["kissat_skip_ws_comments", "kissat_skip_ws1", "kissat_read_nat"]),
  ("kissat_next_lit", ["kissat_skip_ws_comments", "kissat_read_nat"]),
  ("kissat_check_model", ["kissat_skip_ws_comments", "kissat_next_lit"]),
  ("full_skip_cl", ["kissat_next_lit"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs

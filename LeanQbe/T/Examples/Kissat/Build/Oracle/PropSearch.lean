module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_prop_lit_ovf_hot", ["full_watch_push"]),
  ("full_prop_flush_slow_fid", ["full_watch_push"]),
  ("full_propagate_ignore_hot", ["m6_wm4_get"]),
  ("full_propagate_ignore", ["m6_wm4_get"]),
  ("full_flush_trail", ["full_propagate"]),
  ("full_propagate_beyond_m7", ["m6_wm4_get"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Watch

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_wstack_defrag_m6", ["full_wsort_sift"]),
  ("full_watch_push", ["full_watch_push_m6"]),
  ("full_delete_binary", ["full_delete_bin_side"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Watch

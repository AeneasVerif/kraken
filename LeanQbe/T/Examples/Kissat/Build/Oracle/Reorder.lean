module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_reorder_queue_m7", ["full_rescale", "full_arena_next", "full_heap_up",
      "full_reorder_sift_fid"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder

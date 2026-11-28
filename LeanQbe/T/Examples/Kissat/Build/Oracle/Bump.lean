module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Bump

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_bump_var", ["full_rescale", "full_heap_up"]),
  ("full_bump_decay", ["full_rescale"]),
  ("full_queue_mtf", ["full_queue_renumber"]),
  ("full_sort_ana_qs_m6", ["full_ana_sift_m6"]),
  ("full_bump_analyzed_mode_fid", ["full_bump_decay", "m6_hdr_delaying", "m6_hdr_reduce_delay",
      "m6_hdr_bump_delay", "m6_hdr_dr_allow", "full_bump_var", "full_queue_mtf"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Bump

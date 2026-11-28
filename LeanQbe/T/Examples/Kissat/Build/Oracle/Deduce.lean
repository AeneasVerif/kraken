module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_analyze_rsn_m6_hdr", ["m6_hdr_record_used", "full_analyze_lit"]),
  ("full_otfs_large", ["full_wstack_defrag", "full_watch_push"]),
  ("full_otfs_bin", ["full_wstack_defrag", "full_arena_next", "full_watch_push"]),
  ("full_deduce_1uip_m6_hdr", ["full_clear_ana", "full_analyze_lit", "full_otfs_subsume",
      "full_analyze_rsn_m6_hdr"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce

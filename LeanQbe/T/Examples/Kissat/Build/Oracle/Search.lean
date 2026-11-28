module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Search

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_preprocess_m6", ["full_arena_sweep", "full_propagate", "full_compact_needed"]),
  ("full_simplify_m6", ["full_compact_needed"]),
  ("full_search_m6", ["full_propagate", "full_reorder_m6", "full_analyze_m6_hdr",
      "m6_hdr_set_watermark", "full_update_classify_fid", "full_restart_due"]),
  ("kissat_solve_bytes_seeded", ["full_parse_body", "full_extend"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Search

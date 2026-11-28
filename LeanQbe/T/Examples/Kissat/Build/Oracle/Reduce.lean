module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_red_sift", ["full_red_less"]),
  ("full_sort_reds", ["full_red_sift"]),
  ("full_reduce_m6", ["full_arena_sweep", "full_propagate", "m6_hdr_recompute_tiers",
      "m6_hdr_set_watermark", "f64u_to_u64", "full_compact_needed", "full_isqrt",
      "full_update_classify_fid", "full_arena_next", "full_mark_reasons", "f64u_from_u64"]),
  ("full_reduce_purge_c0", ["full_arena_sweep", "full_propagate", "full_arena_next",
      "full_mark_reasons"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce

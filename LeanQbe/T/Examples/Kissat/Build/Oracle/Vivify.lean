module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Vivify

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_viv_best_watch_m6", ["full_viv_watch_rank_m6"]),
  ("full_viv_simplify_m6", ["full_watch_push"]),
  ("full_viv_commit_m6", ["full_viv_unreason_m6", "full_viv_best_watch_m6", "full_watch_push"]),
  ("full_viv_mark_garb_m6", ["full_viv_unreason_m6"]),
  ("full_viv_deduce_m6", ["full_viv_subsumes_cl_m6", "full_viv_subsumes_bin_m6"]),
  ("full_viv_inst_m6", ["full_viv_inst_check_m6", "full_assign"]),
  ("full_viv_sort_counts_m6", ["full_viv_sift_counts_m6"]),
  ("full_viv_l0_simp_m6", ["full_viv_has_l0_m6"]),
  ("full_viv_clause_m6", ["full_viv_best_implied_m6", "full_viv_l0_simp_m6",
      "full_viv_reuse_prefix_m6", "full_assign"]),
  ("full_viv_clear_tier_m6", ["full_viv_tier_match_m6", "full_arena_next"]),
  ("full_viv_collect_fid", ["full_viv_tier_match_m6", "full_arena_next"]),
  ("full_vivify_tier_m6_hdr", ["full_propagate", "m6_hdr_get_watermark", "full_arena_next"]),
  ("full_vivify_m6_hdr", ["m6_hdr_get_watermark", "m6_hdr_delaying",
      "m6_hdr_sync_legacy_tiers", "m6_hdr_reduce_delay", "m6_hdr_bump_delay"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Vivify

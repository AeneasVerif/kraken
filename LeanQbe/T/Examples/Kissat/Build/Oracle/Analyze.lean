module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_ana_failed_lit_m6_hdr", ["full_clear_ana", "full_tick_rel", "full_assign_lvl"]),
  ("full_restore_bump_ana_mode_fid", ["full_clear_ana"]),
  ("full_analyze_reasons_fid", ["m6_hdr_delaying", "m6_hdr_reduce_delay", "m6_hdr_bump_delay",
      "m6_hdr_dr_allow"]),
  ("full_analyze_core_m6", ["full_clear_ana", "m6_hdr_update_tier_limits", "full_tick_rel"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze

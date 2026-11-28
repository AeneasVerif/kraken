module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("m6_hdr_add_ticks", ["m6_ext_ensure_init"]),
  ("m6_hdr_sync_legacy_tiers", ["m6_ext_ensure_init"]),
  ("m6_hdr_recompute_tiers_mode", ["m6_ext_ensure_init", "f64u_to_u64",
      "m6_hdr_sync_legacy_tiers", "f64u_from_u64"]),
  ("m6_hdr_update_tier_limits", ["m6_hdr_recompute_tiers", "m6_ext_ensure_init"]),
  ("m6_hdr_record_used", ["m6_ext_ensure_init"]),
  ("m6_hdr_get_tier1", ["m6_ext_ensure_init"]),
  ("m6_hdr_get_tier2", ["m6_ext_ensure_init"]),
  ("m6_hdr_delaying", ["m6_ext_ensure_init"]),
  ("m6_hdr_bump_delay", ["m6_ext_ensure_init"]),
  ("m6_hdr_reduce_delay", ["m6_ext_ensure_init"]),
  ("m6_hdr_get_watermark", ["m6_ext_ensure_init"]),
  ("m6_hdr_set_watermark", ["m6_ext_ensure_init"]),
  ("m6_hdr_dr_init", ["m6_ext_ensure_init"]),
  ("m6_hdr_dr_update", ["m6_hdr_dr_init", "f64u_from_u64"]),
  ("m6_hdr_dr_allow", ["m6_ext_ensure_init"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers

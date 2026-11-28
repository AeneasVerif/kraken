module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Probe

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_probe_dticks_m6_hdr", ["m6_hdr_get_watermark"]),
  ("full_probe_m6", ["full_enter_dense", "m6_hdr_set_watermark", "m6_hdr_get_watermark",
      "m6_hdr_delaying", "m6_hdr_reduce_delay", "m6_hdr_bump_delay"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Probe

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Limits

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_scale_delta_m5", ["f64u_to_u64", "f64u_from_u64"]),
  ("full_ema_update", ["f64u_from_u64"]),
  ("full_scale_delta", ["f64u_to_u64", "f64u_from_u64"]),
  ("full_elim_dticks", ["full_max_u64"]),
  ("full_m7_state_init", ["full_m7_set64", "full_m7_get64"]),
  ("full_ema_swap_m7", ["full_m7_set64", "full_m7_get64"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Limits

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Restart

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_restart_due", ["f64u_to_u64"]),
  ("full_switch_mode_m7", ["full_ilog10", "m6_wm4_set", "m6_wm4_get", "full_m7_set64",
      "full_m7_get64", "f64u_to_u64", "m6_hdr_dr_init", "full_heap_up", "full_heap_down",
      "full_heap_push"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Restart

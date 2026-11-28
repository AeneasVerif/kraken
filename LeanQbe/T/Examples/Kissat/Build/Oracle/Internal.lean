module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Internal

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_calc_max_v", ["full_fixed_bytes"]),
  ("full_init_arenas", ["full_init_ptrs"]),
  ("full_init_state_m5", ["full_calc_ext_cap_m5", "full_calc_scr_cap_m5", "full_fixed_bytes",
      "full_calc_max_v", "full_zero_tables2"]),
  ("full_m6_mem_init", ["full_init_state"]),
  ("full_set_inactive", ["full_heap_up", "full_heap_down"]),
  ("full_init_fresh_var", ["full_heap_push"]),
  ("full_update_classify_fid", ["m6_wm4_set", "m6_wm4_get"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Internal

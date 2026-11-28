module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Decide

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_next_dec_var", ["full_heap_pop"]),
  ("full_randec_var_lvl_fid", ["full_lcg_next_m7", "full_m7_set64", "full_m7_get64",
      "f64u_to_u64"]),
  ("full_decide_m7", ["full_randec_var_m7", "full_assign"]),
  ("m6_hdr_decide_fid", ["m6_hdr_dr_init", "full_decide_m7"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Decide

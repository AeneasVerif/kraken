module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Gates

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_bve_find_ite_side_m7", ["full_bve_get_tern_m7"]),
  ("full_bve_find_xor_m7", ["full_bve_xor_pat_m7"]),
  ("full_bve_find_ite_side_m8", ["full_bve_get_tern_m7", "full_bve_match_tern_m8"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Gates

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_trans_lit_m6", ["full_delete_bin_side"]),
  ("full_transitive_m6", ["full_propagate", "full_wstack_defrag"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_backbone_round_m6", ["full_backbone_unwind_m6"]),
  ("full_backbone_m6", ["full_propagate", "m6_wm4_set", "m6_wm4_get"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone

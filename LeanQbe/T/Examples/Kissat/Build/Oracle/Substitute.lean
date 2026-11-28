module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_tarjan_scc", ["full_tarjan_pop_scc"]),
  ("full_subst_elim_vars", ["full_propagate", "full_extend_push2"]),
  ("full_subst_rewrite_bins", ["full_add_bin"]),
  ("full_subst_rewrite_ar", ["full_add_bin", "full_arena_next"]),
  ("full_substitute", ["full_arena_sweep", "full_propagate"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute

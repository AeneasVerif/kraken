module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Dense

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_enter_dense_ex_fid", ["full_arena_sweep", "full_sweep_bins", "full_propagate",
      "full_flush_trail", "full_arena_next", "full_watch_push"]),
  ("full_rebuild_watches_nosort_fid", ["full_arena_sweep", "full_propagate"]),
  ("full_rebuild_watches", ["full_sort_bin_watches_fid"]),
  ("full_m6_dense_prop_lit", ["full_assign_lvl"]),
  ("full_watch_large_clauses_fid", ["full_lit_rank_m6", "full_arena_next",
      "full_watch_push_m6"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Dense

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Collect

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_rewatch_range_m6", ["full_lit_rank_m6", "full_watch_push_m6"]),
  ("full_sweep_bins_m6cf", ["full_wstack_defrag"]),
  ("full_sweep_copy", ["full_watch_pop_c0", "full_assign_lvl", "full_watch_push"]),
  ("full_rewatch_arena", ["full_rewatch_arena_m6"]),
  ("full_move_red_end_buf_m6", ["full_move_red_pass2_m6"]),
  ("full_arena_sweep_m6", ["full_arena_next"]),
  ("full_mark_reasons", ["full_mark_reasons_m6"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Collect

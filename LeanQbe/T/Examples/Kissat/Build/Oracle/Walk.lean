module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Walk

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_walk_cb_inv_m7", ["f64u_from_u64"]),
  ("full_walk_collect_m7", ["full_arena_next"]),
  ("full_walk_pick_m7", ["full_walk_break_m7", "f64u_from_u64"]),
  ("full_walk_m7", ["full_walk_effort_m7", "full_walk_save_min_m7", "full_walk_flip_m7"]),
  ("full_warmup_m7", ["full_assign"]),
  ("full_rephase", ["full_walk", "f64u_to_u64"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Walk

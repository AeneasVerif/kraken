module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Compact

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_compact_flush", ["full_flush_trail"]),
  ("full_compact_mark_live", ["full_arena_next"]),
  ("full_compact_arena", ["full_arena_next", "full_watch_push"]),
  ("full_compact_vmtf", ["full_compact_sift_q"]),
  ("full_compact_heap", ["full_compact_sift_h"]),
  ("full_compact", ["full_wstack_defrag", "full_rewatch_arena", "full_compact_assign_map"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Compact

module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Heap

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_heap_push", ["full_heap_up"]),
  ("full_heap_pop", ["full_heap_down"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Heap

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Heap
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Heap
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Heap
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Heap

/-!
# Plan-Inlined Subsystem `Heap`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Heap

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Heap.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Heap.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Heap

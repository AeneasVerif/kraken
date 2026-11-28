module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder
public import LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Reorder
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports

/-!
# Plan-Inlined Subsystem `Reorder`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Reorder

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Reorder.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Reorder.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Reorder

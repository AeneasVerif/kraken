module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Backtrack
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Backtrack
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports

/-!
# Plan-Inlined Subsystem `Backtrack`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Backtrack.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Backtrack.plan)
  (deps := LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Walk
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Walk
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Walk
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Walk
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports

/-!
# Plan-Inlined Subsystem `Walk`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Walk

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Walk.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Walk.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Walk

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate
public import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Eliminate
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports

/-!
# Plan-Inlined Subsystem `Eliminate`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Eliminate

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Eliminate.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Eliminate.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Eliminate

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Reduce
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports

/-!
# Plan-Inlined Subsystem `Reduce`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Reduce

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Reduce.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Reduce.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Reduce

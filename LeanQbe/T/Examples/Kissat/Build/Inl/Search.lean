module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Search
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Search
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Search
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Search
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports

/-!
# Plan-Inlined Subsystem `Search`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Search

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Search.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Search.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Search

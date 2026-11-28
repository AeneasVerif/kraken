module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Compact
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Compact
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Compact
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports

/-!
# Plan-Inlined Subsystem `Compact`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Compact

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Compact.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Compact.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Compact

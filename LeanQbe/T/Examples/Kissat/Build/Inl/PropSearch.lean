module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
public import LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.PropSearch
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports

/-!
# Plan-Inlined Subsystem `PropSearch`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.PropSearch.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.PropSearch.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch

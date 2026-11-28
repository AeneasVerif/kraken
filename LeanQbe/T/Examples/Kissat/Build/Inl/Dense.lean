module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Dense
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Dense
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Dense
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Dense
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports

/-!
# Plan-Inlined Subsystem `Dense`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Dense

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Dense.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Dense.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Dense

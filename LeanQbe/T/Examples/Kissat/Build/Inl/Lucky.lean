module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Lucky
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports

/-!
# Plan-Inlined Subsystem `Lucky`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Lucky

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Lucky.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Lucky.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Lucky

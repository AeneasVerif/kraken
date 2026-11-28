module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Clause
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Clause
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Clause
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Clause
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports

/-!
# Plan-Inlined Subsystem `Clause`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Clause

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Clause.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Clause.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Clause

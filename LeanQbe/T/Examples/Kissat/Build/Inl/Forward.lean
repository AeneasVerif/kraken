module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Forward
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Forward
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Forward
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports

/-!
# Plan-Inlined Subsystem `Forward`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Forward

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Forward.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Forward.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Forward

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Factor
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Factor
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Factor
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports

/-!
# Plan-Inlined Subsystem `Factor`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Factor

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Factor.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Factor.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Factor

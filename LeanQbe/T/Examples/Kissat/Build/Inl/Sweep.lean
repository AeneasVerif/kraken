module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Sweep
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep
public import LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Sweep
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports

/-!
# Plan-Inlined Subsystem `Sweep`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Sweep

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Sweep.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Sweep.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Sweep

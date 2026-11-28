module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Congruence
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Congruence
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports

/-!
# Plan-Inlined Subsystem `Congruence`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Congruence

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Congruence.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Congruence

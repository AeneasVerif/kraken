module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Transitive
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Transitive
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports

/-!
# Plan-Inlined Subsystem `Transitive`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Transitive

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Transitive.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Transitive.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Transitive

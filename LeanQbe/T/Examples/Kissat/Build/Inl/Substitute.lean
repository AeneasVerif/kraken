module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Substitute
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Substitute
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports

/-!
# Plan-Inlined Subsystem `Substitute`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Substitute

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Substitute.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Substitute.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Substitute

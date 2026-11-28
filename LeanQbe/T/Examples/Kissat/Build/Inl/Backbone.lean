module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Backbone
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Backbone
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports

/-!
# Plan-Inlined Subsystem `Backbone`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Backbone

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Backbone.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Backbone.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Backbone

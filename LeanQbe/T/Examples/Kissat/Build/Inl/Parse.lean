module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Parse
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Parse
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Parse
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Parse
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports

/-!
# Plan-Inlined Subsystem `Parse`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Parse

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Parse.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Parse.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Parse

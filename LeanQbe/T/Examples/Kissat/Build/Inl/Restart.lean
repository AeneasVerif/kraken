module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Restart
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Restart
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Restart
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports

/-!
# Plan-Inlined Subsystem `Restart`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Restart

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Restart.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Restart.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Restart

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Bump
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Bump
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Bump
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports

/-!
# Plan-Inlined Subsystem `Bump`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Bump

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Bump.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Bump.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Bump

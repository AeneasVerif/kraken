module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Internal
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Internal
public import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Internal
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Internal
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports

/-!
# Plan-Inlined Subsystem `Internal`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Internal

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Internal.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Internal.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Internal

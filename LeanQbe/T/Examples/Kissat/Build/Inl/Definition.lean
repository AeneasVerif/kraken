module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Definition
public import LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Definition
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Definition
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports

/-!
# Plan-Inlined Subsystem `Definition`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Definition

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Definition.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Definition.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Definition

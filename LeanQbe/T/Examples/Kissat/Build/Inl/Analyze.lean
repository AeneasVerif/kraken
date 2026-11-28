module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Analyze
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze
public import LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Analyze
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports

/-!
# Plan-Inlined Subsystem `Analyze`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Analyze

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Analyze.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Analyze.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Analyze

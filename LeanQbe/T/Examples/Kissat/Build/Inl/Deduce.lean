module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Deduce
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports

/-!
# Plan-Inlined Subsystem `Deduce`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Deduce

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Deduce.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Deduce.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Deduce

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Tiers
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports

/-!
# Plan-Inlined Subsystem `Tiers`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Tiers

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Tiers.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Tiers.plan)
  (deps := LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Tiers

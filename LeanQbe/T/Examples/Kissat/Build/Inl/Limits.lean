module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Limits
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Limits
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Limits
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Limits
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports

/-!
# Plan-Inlined Subsystem `Limits`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Limits

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Limits.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Limits.plan)
  (deps := LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Limits

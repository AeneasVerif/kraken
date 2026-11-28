module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Float64
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Float64
public import LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Float64
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Float64

/-!
# Plan-Inlined Subsystem `Float64`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Float64

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Float64.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Float64.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Float64

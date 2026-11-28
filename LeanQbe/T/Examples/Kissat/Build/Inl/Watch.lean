module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Watch
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Watch
public import LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Watch
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Watch

/-!
# Plan-Inlined Subsystem `Watch`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Watch

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Watch.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Watch.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Watch

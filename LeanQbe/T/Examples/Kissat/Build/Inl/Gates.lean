module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Gates
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Gates
public import LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Gates
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Gates

/-!
# Plan-Inlined Subsystem `Gates`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Gates

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Gates.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Gates.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Gates

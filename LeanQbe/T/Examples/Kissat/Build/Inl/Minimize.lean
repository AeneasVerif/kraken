module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Minimize
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize

/-!
# Plan-Inlined Subsystem `Minimize`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Minimize

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Minimize.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Minimize.plan)

end LeanQbe.T.Examples.Kissat.Build.Inl.Minimize

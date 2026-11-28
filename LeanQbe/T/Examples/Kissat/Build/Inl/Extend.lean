module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Extend
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Extend
public import LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Extend
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Extend

/-!
# Plan-Inlined Subsystem `Extend`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Extend

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Extend.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Extend.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Extend

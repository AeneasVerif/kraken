module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Dimacs
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs

/-!
# Plan-Inlined Subsystem `Dimacs`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Dimacs.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Dimacs.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs

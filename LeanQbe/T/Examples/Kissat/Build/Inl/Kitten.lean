module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Kitten
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten
public import LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Kitten
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten

/-!
# Plan-Inlined Subsystem `Kitten`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Kitten

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Kitten.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Kitten.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Kitten

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Arena
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Arena
public import LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Arena
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Arena

/-!
# Plan-Inlined Subsystem `Arena`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Arena

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Arena.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Arena.plan)
  (exports := LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Arena

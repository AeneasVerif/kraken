module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.Examples.Kissat.Src.Probe
public import LeanQbe.T.Examples.Kissat.Build.Oracle.Probe
public import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
public import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Examples.Kissat.Src.Probe
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Probe
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
meta import LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports

/-!
# Plan-Inlined Subsystem `Probe`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Probe

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbe.T.Examples.Kissat.Src.Probe.fns
  (plan := LeanQbe.T.Examples.Kissat.Build.Oracle.Probe.plan)
  (deps :=
    LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports.fns
    ++ LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports.fns)

end LeanQbe.T.Examples.Kissat.Build.Inl.Probe

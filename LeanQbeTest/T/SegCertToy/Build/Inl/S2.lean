module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbeTest.T.SegCertToy.Src2
public import LeanQbeTest.T.SegCertToy.Build.Oracle.S2
public import LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports
public import LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbeTest.T.SegCertToy.Src2
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.S2
meta import LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports

/-!
# Plan-Inlined Subsystem `S2`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Inl.S2

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbeTest.T.SegCertToy.Src2.fns
  (plan := LeanQbeTest.T.SegCertToy.Build.Oracle.S2.plan)
  (deps := LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports.fns)
  (exports := LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports.fns)

end LeanQbeTest.T.SegCertToy.Build.Inl.S2

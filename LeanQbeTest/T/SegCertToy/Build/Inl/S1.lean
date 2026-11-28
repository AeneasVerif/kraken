module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbeTest.T.SegCertToy.Src1
public import LeanQbeTest.T.SegCertToy.Build.Oracle.S1
public import LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbeTest.T.SegCertToy.Src1
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.S1

/-!
# Plan-Inlined Subsystem `S1`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Inl.S1

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbeTest.T.SegCertToy.Src1.fns
  (plan := LeanQbeTest.T.SegCertToy.Build.Oracle.S1.plan)
  (exports := LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports.fns)

end LeanQbeTest.T.SegCertToy.Build.Inl.S1

module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbeTest.T.SegCertToy.Src3
public import LeanQbeTest.T.SegCertToy.Build.Oracle.S3
public import LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports
public import LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbeTest.T.SegCertToy.Src3
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.S3
meta import LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports
meta import LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports

/-!
# Plan-Inlined Subsystem `S3`

Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`
+ dependency `Exports` leaves.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Inl.S3

open LeanQbe.T
open scoped LeanQbe.T

inline_seg! inl LeanQbeTest.T.SegCertToy.Src3.fns
  (plan := LeanQbeTest.T.SegCertToy.Build.Oracle.S3.plan)
  (deps :=
    LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports.fns
    ++ LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports.fns)

end LeanQbeTest.T.SegCertToy.Build.Inl.S3

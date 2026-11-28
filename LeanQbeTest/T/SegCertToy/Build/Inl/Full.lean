module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbeTest.T.SegCertToy.SrcFull
public import LeanQbeTest.T.SegCertToy.Build.Oracle.S1
public import LeanQbeTest.T.SegCertToy.Build.Inl.S1
public import LeanQbeTest.T.SegCertToy.Build.Oracle.S2
public import LeanQbeTest.T.SegCertToy.Build.Inl.S2
public import LeanQbeTest.T.SegCertToy.Build.Oracle.S3
public import LeanQbeTest.T.SegCertToy.Build.Inl.S3

/-!
# Whole-Module Plan-Inlined Assembly (`3` Subsystems)

Assembles `(srcMod.inlinePlan fullPlan).fns = InlSeg.allFns allSegs` in `O(#segs)`
without unfolding any function bodies.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Inl.Full

open LeanQbe.T

/-- Concatenated whole-module inline plan across all subsystems. -/
@[expose] def fullPlan : InlPlan :=
  LeanQbeTest.T.SegCertToy.Build.Oracle.S1.plan
  ++ LeanQbeTest.T.SegCertToy.Build.Oracle.S2.plan
  ++ LeanQbeTest.T.SegCertToy.Build.Oracle.S3.plan

/-- Ordered list of per-subsystem materialized `InlSeg` certificates. -/
@[expose] noncomputable def allSegs : List InlSeg := [
  LeanQbeTest.T.SegCertToy.Build.Inl.S1.inl.seg,
  LeanQbeTest.T.SegCertToy.Build.Inl.S2.inl.seg,
  LeanQbeTest.T.SegCertToy.Build.Inl.S3.inl.seg
]

/-- Concatenated post-inline function list across all subsystems. -/
@[expose] noncomputable def inlFns : List Fn := InlSeg.allFns allSegs

private theorem allSrc_eq :
    LeanQbeTest.T.SegCertToy.SrcFull.toyModule.fns =
      InlSeg.allSrcFns allSegs := rfl

private theorem allNames_nodup :
    listNodup ((InlSeg.allSrcFns allSegs).map Fn.name) = true := by
  decide

private theorem deps_ok : InlSeg.DepsOkFrom fullPlan [] [] allSegs := by
  refine
    ⟨by decide,
     InlSeg.forall_mem_nil,
     by decide,
    ⟨by decide,
     InlSeg.forall_mem_mono_append_right LeanQbeTest.T.SegCertToy.Build.Inl.S1.inl.exports_sub,
     by decide,
    ⟨by decide,
     InlSeg.forall_mem_append_elim
       (InlSeg.forall_mem_mono_append_right LeanQbeTest.T.SegCertToy.Build.Inl.S2.inl.exports_sub)
       (InlSeg.forall_mem_mono_append_left <|
       InlSeg.forall_mem_mono_append_right LeanQbeTest.T.SegCertToy.Build.Inl.S1.inl.exports_sub),
     by decide,
    trivial⟩⟩⟩

/-- Whole-module plan-inlining equality proved in `O(#segs)` via `InlinePlanSeg`. -/
theorem inlFns_eq :
    (LeanQbeTest.T.SegCertToy.SrcFull.toyModule.inlinePlan fullPlan).fns =
      inlFns :=
  InlSeg.module_inlinePlan_fns_of_segs
    LeanQbeTest.T.SegCertToy.SrcFull.toyModule fullPlan allSegs
    allSrc_eq allNames_nodup deps_ok

end LeanQbeTest.T.SegCertToy.Build.Inl.Full

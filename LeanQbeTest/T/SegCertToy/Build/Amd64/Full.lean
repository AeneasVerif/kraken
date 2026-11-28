module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.SegCertToy.SrcFull
public import LeanQbeTest.T.SegCertToy.Build.Inl.Full
public import LeanQbeTest.T.SegCertToy.Build.Amd64.S1
public import LeanQbeTest.T.SegCertToy.Build.Amd64.S2
public import LeanQbeTest.T.SegCertToy.Build.Amd64.S2.ToyMix2
public import LeanQbeTest.T.SegCertToy.Build.Amd64.S3

/-!
# Whole-Module Subsystem-Aligned Certificate on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Amd64.Full

open LeanQbe.T LeanQbe.T.Amd64

/-- Plan-inlined whole module certified by `fullCert`. -/
@[expose] def inlMod : Module :=
  LeanQbeTest.T.SegCertToy.SrcFull.toyModule.inlinePlan
    LeanQbeTest.T.SegCertToy.Build.Inl.Full.fullPlan

/-- Ordered list of subsystem and isolated heavy-function `SegChunks`. -/
@[expose] noncomputable def allSegChunks :
    List (SegChunks x64Target x64LegalTarget [] 0 2048) := [
  LeanQbeTest.T.SegCertToy.Build.Amd64.S1.cert,
  LeanQbeTest.T.SegCertToy.Build.Amd64.S2.cert.part0,
  LeanQbeTest.T.SegCertToy.Build.Amd64.S2.ToyMix2.cert,
  LeanQbeTest.T.SegCertToy.Build.Amd64.S3.cert
]

/-- Function-list alignment between `inlMod` and `allSegChunks`. -/
theorem allSegs_fns_eq :
    inlMod.fns = SegChunks.allFns allSegChunks := by
  unfold inlMod
  rw [LeanQbeTest.T.SegCertToy.Build.Inl.Full.inlFns_eq]
  rfl

/-- Whole-module cross-segment link check across `allSegChunks`. -/
theorem allSegs_link :
    checkLinkList x64Layout [] (SegChunks.allChunks allSegChunks) = true := by
  rfl

/-- Whole-module verified `LinkedCert` assembled via `LinkedCert.ofSegs`. -/
@[expose] noncomputable def fullCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      inlMod [] [] 0 2048 :=
  LinkedCert.ofSegs allSegChunks allSegs_fns_eq allSegs_link

end LeanQbeTest.T.SegCertToy.Build.Amd64.Full

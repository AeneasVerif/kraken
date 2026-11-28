module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbeTest.T.SegCertToy.Build.Inl.S1
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S1

/-!
# Declarative Subsystem Cert `S1` on AAPCS64 Arm64

Zero `Spill` meta import; reads precomputed oracle `hints` and `ext`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Arm64.S1

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

seg_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbeTest.T.SegCertToy.Build.Inl.S1.inl.fns
  (hints := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S1.hints)
  (ext := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S1.ext) (chunkSize := 1) (maxDirs := 600)
  (maxBound := 2048) (pruneExt := true)

end LeanQbeTest.T.SegCertToy.Build.Arm64.S1

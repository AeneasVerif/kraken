module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.SegCertToy.Build.Inl.S3
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S3

/-!
# Declarative Subsystem Cert `S3` on SysV x64

Zero `Spill` meta import; reads precomputed oracle `hints` and `ext`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Amd64.S3

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

seg_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbeTest.T.SegCertToy.Build.Inl.S3.inl.fns
  (hints := LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S3.hints)
  (ext := LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S3.ext) (chunkSize := 1) (maxDirs := 600)
  (maxBound := 2048) (pruneExt := true)

end LeanQbeTest.T.SegCertToy.Build.Amd64.S3

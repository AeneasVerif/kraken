module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Reorder
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder

/-!
# Declarative Subsystem Cert `Reorder` on AAPCS64 Arm64

Zero `Spill` meta import; reads precomputed oracle `hints` and `ext`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Arm64.Reorder

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

seg_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.inl.fns
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder.hints)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder.ext) (chunkSize := 1)
  (maxDirs := 600) (maxBound := 2048) (pruneExt := true)
  (exclude := ["full_reorder_queue_m7"])

end LeanQbe.T.Examples.Kissat.Build.Arm64.Reorder

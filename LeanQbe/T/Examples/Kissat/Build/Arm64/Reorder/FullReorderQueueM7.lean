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
# Isolated Heavy Function Cert `Reorder.full_reorder_queue_m7` on AAPCS64 Arm64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Arm64.Reorder.FullReorderQueueM7

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

fn_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.inl.flat.f1
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder.hint_full_reorder_queue_m7)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder.ext_full_reorder_queue_m7)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Arm64.Reorder.FullReorderQueueM7

module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Reorder
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reorder

/-!
# Isolated Heavy Function Cert `Reorder.full_reorder_queue_m7` on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder.FullReorderQueueM7

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

fn_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.inl.flat.f1
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reorder.hint_full_reorder_queue_m7)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reorder.ext_full_reorder_queue_m7)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder.FullReorderQueueM7

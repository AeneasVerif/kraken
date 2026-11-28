module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Sweep
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Sweep

/-!
# Isolated Heavy Function Cert `Sweep.full_m6_sweep_units` on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.FullM6SweepUnits

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

fn_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Sweep.inl.flat.f10
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Sweep.hint_full_m6_sweep_units)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Sweep.ext_full_m6_sweep_units)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.FullM6SweepUnits

module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Congruence
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Congruence

/-!
# Isolated Heavy Function Cert `Congruence.full_cong_fwd_subsume` on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.FullCongFwdSubsume

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

fn_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.inl.flat.f23
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Congruence.hint_full_cong_fwd_subsume)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Congruence.ext_full_cong_fwd_subsume)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.FullCongFwdSubsume

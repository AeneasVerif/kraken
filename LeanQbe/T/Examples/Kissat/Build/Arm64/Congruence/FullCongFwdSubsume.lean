module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Congruence
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Congruence

/-!
# Isolated Heavy Function Cert `Congruence.full_cong_fwd_subsume` on AAPCS64 Arm64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Arm64.Congruence.FullCongFwdSubsume

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

fn_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.inl.flat.f23
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Congruence.hint_full_cong_fwd_subsume)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Congruence.ext_full_cong_fwd_subsume)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Arm64.Congruence.FullCongFwdSubsume

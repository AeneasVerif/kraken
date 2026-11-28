module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Factor
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Factor

/-!
# Isolated Heavy Function Cert `Factor.full_bva_connect_clauses_fid` on AAPCS64 Arm64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Arm64.Factor.FullBvaConnectClausesFid

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

fn_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Factor.inl.flat.f5
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Factor.hint_full_bva_connect_clauses_fid)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Factor.ext_full_bva_connect_clauses_fid)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Arm64.Factor.FullBvaConnectClausesFid

module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Factor
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Factor

/-!
# Isolated Heavy Function Cert `Factor.full_bva_commit` on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.FullBvaCommit

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

fn_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Factor.inl.flat.f10
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Factor.hint_full_bva_commit)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Factor.ext_full_bva_commit)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.FullBvaCommit

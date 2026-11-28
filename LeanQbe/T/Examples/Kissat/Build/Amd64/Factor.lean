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
# Declarative Subsystem Cert `Factor` on SysV x64

Zero `Spill` meta import; reads precomputed oracle `hints` and `ext`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Factor

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

seg_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Factor.inl.fns
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Factor.hints)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Factor.ext) (chunkSize := 1) (maxDirs := 600)
  (maxBound := 2048) (pruneExt := true)
  (exclude := ["full_bva_connect_clauses_fid", "full_bva_commit"])

end LeanQbe.T.Examples.Kissat.Build.Amd64.Factor

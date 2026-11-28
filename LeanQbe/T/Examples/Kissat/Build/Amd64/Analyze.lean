module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Analyze
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Analyze

/-!
# Declarative Subsystem Cert `Analyze` on SysV x64

Zero `Spill` meta import; reads precomputed oracle `hints` and `ext`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Analyze

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

seg_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.inl.fns
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Analyze.hints)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Analyze.ext) (chunkSize := 1)
  (maxDirs := 600) (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Amd64.Analyze

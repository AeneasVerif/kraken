module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Deduce
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Deduce

/-!
# Isolated Heavy Function Cert `Deduce.full_deduce_1uip_m6_hdr` on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Deduce.FullDeduce1uipM6Hdr

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

fn_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.inl.flat.f6
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Deduce.hint_full_deduce_1uip_m6_hdr)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Deduce.ext_full_deduce_1uip_m6_hdr)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Amd64.Deduce.FullDeduce1uipM6Hdr

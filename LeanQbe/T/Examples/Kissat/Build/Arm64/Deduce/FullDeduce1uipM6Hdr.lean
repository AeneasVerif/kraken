module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Build.Inl.Deduce
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Deduce

/-!
# Isolated Heavy Function Cert `Deduce.full_deduce_1uip_m6_hdr` on AAPCS64 Arm64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Arm64.Deduce.FullDeduce1uipM6Hdr

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

fn_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.inl.flat.f6
  (hints := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Deduce.hint_full_deduce_1uip_m6_hdr)
  (ext := LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Deduce.ext_full_deduce_1uip_m6_hdr)
  (maxBound := 2048) (pruneExt := true)

end LeanQbe.T.Examples.Kissat.Build.Arm64.Deduce.FullDeduce1uipM6Hdr

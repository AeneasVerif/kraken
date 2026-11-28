module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbeTest.T.SegCertToy.Build.Inl.S2
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2

/-!
# Isolated Heavy Function Cert `S2.toy_mix2` on AAPCS64 Arm64
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Arm64.S2.ToyMix2

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

fn_cert! cert armTarget armLayout armLegalTarget armLabelClean
  LeanQbeTest.T.SegCertToy.Build.Inl.S2.inl.flat.f1
  (hints := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.hint_toy_mix2)
  (ext := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2) (maxBound := 2048)
  (pruneExt := true)

end LeanQbeTest.T.SegCertToy.Build.Arm64.S2.ToyMix2

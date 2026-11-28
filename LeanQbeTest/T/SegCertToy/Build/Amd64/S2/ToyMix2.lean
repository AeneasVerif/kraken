module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.SegCertToy.Build.Inl.S2
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S2

/-!
# Isolated Heavy Function Cert `S2.toy_mix2` on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Amd64.S2.ToyMix2

open LeanQbe.T LeanQbe.T.Amd64
open scoped LeanQbe.T

fn_cert! cert x64Target x64Layout x64LegalTarget x64LabelClean
  LeanQbeTest.T.SegCertToy.Build.Inl.S2.inl.flat.f1
  (hints := LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S2.hint_toy_mix2)
  (ext := LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S2.ext_toy_mix2) (maxBound := 2048)
  (pruneExt := true)

end LeanQbeTest.T.SegCertToy.Build.Amd64.S2.ToyMix2

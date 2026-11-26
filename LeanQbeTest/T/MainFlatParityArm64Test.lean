module

public import LeanQbeTest.T.MainFlatParityFixtures
public import LeanQbe.T.Arm64.Targ
public import Kraken.AArch64.Print
import LeanQbe.T.FlatDirectLemmas
meta import Lean
meta import LeanQbeTest.T.MainFlatParityFixtures
meta import LeanQbe.T.Arm64.Targ
meta import Kraken.AArch64.Print

/-!
# AAPCS64 Arm64 Differential Parity & Axiom Audit (`MainFlatParityArm64Test`)

Arm64 companion to `MainFlatParityTest` (zero `Kraken.X64`/`Amd64` imports): verifies
`compileModuleFlat = compileModule`, `compileFlatFn = compileFn`, byte-exact
`Kraken.AArch64.print` assembly on `Arm64.armTarget` (`armLegalTarget`) over native
`divConst`/`assumeElim`/`mergeRets`/loop `TFlatFn`s, Litmus programs, and Kissat C0 schedule
functions, plus `#print axioms` (`std3` only).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainFlatParityArm64Test

open LeanQbe.T
open LeanQbeTest.T.MainFlatParityFixtures

theorem compileModuleFlat_ok_implies_compileModule_arm
    (hints : List Arm64.armTarget.toIsa.Hints)
    {code : List Arm64.armTarget.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Arm64.armTarget.toIsa Arm64.armLegalTarget
      Arm64.armTarget.frame.raBytes [] [] 0 litmusTFlatMod hints = .ok (code, bounds)) :
    compileModule Arm64.armTarget.toIsa Arm64.armLegalTarget
        Arm64.armTarget.frame.raBytes [] [] 0 (litmusTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] [] 0 litmusTFlatMod hints code bounds hok

theorem divModFlat_compileFlatFn_eq_arm (h : Arm64.armTarget.toIsa.Hints) :
    compileFlatFn Arm64.armTarget.toIsa Arm64.armLegalTarget h divModFlat =
      compileFn Arm64.armTarget.toIsa Arm64.armLegalTarget h divModFlat.toFn :=
  compileFlatFn_eq_compileFn _ _ _ _ divModFlat_wf

theorem assumeLoopFlat_compileFlatFn_eq_arm (h : Arm64.armTarget.toIsa.Hints) :
    compileFlatFn Arm64.armTarget.toIsa Arm64.armLegalTarget h assumeLoopFlat =
      compileFn Arm64.armTarget.toIsa Arm64.armLegalTarget h assumeLoopFlat.toFn :=
  compileFlatFn_eq_compileFn _ _ _ _ assumeLoopFlat_wf

theorem compileModuleFlat_ok_implies_compileModule_litmusAll_arm
    (hints : List Arm64.armTarget.toIsa.Hints)
    {code : List Arm64.armTarget.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Arm64.armTarget.toIsa Arm64.armLegalTarget
      Arm64.armTarget.frame.raBytes [] ["fail"] 0 litmusAllTFlatMod hints = .ok (code, bounds)) :
    compileModule Arm64.armTarget.toIsa Arm64.armLegalTarget
        Arm64.armTarget.frame.raBytes [] ["fail"] 0 (litmusAllTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] ["fail"] 0 litmusAllTFlatMod hints code bounds hok

theorem compileModuleFlat_ok_implies_compileModule_lrat_arm
    (hints : List Arm64.armTarget.toIsa.Hints)
    {code : List Arm64.armTarget.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Arm64.armTarget.toIsa Arm64.armLegalTarget
      Arm64.armTarget.frame.raBytes [] [] 0 lratBytesTFlatMod hints = .ok (code, bounds)) :
    compileModule Arm64.armTarget.toIsa Arm64.armLegalTarget
        Arm64.armTarget.frame.raBytes [] [] 0 (lratBytesTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] [] 0 lratBytesTFlatMod hints code bounds hok

theorem compileModuleFlat_ok_implies_compileModule_fidSched_arm
    (hints : List Arm64.armTarget.toIsa.Hints)
    {code : List Arm64.armTarget.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Arm64.armTarget.toIsa Arm64.armLegalTarget
      Arm64.armTarget.frame.raBytes (fidSchedExtCallees Arm64.armLegalTarget) [] 0
      fidSchedTFlatMod hints = .ok (code, bounds)) :
    compileModule Arm64.armTarget.toIsa Arm64.armLegalTarget
        Arm64.armTarget.frame.raBytes (fidSchedExtCallees Arm64.armLegalTarget) [] 0
        (fidSchedTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ (fidSchedExtCallees Arm64.armLegalTarget) [] 0
    fidSchedTFlatMod hints code bounds hok

theorem fidPreprocessFlat_compileFlatFn_eq_arm (h : Arm64.armTarget.toIsa.Hints) :
    compileFlatFn Arm64.armTarget.toIsa Arm64.armLegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidPreprocessFn) =
      compileFn Arm64.armTarget.toIsa Arm64.armLegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidPreprocessFn).toFn :=
  compileFlatFn_eq_compileFn _ _ _ _
    (PassFlatKit.reifyFunc_wfCheck Examples.Kissat.FullM7FidelitySched.full_preprocess_fid_wf)

theorem fidReduceFlat_compileFlatFn_eq_arm (h : Arm64.armTarget.toIsa.Hints) :
    compileFlatFn Arm64.armTarget.toIsa Arm64.armLegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidReduceFn) =
      compileFn Arm64.armTarget.toIsa Arm64.armLegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidReduceFn).toFn :=
  compileFlatFn_eq_compileFn _ _ _ _
    (PassFlatKit.reifyFunc_wfCheck Examples.Kissat.FullM7FidelitySched.full_reduce_fid_wf)

#eval show IO Unit from
  checkTargetParity "arm64" Arm64.armTarget.toIsa Arm64.armLegalTarget
    Arm64.armTarget.frame.raBytes Kraken.AArch64.print

#print axioms compileModuleFlat_ok_implies_compileModule_arm
#print axioms divModFlat_compileFlatFn_eq_arm
#print axioms assumeLoopFlat_compileFlatFn_eq_arm
#print axioms compileModuleFlat_ok_implies_compileModule_litmusAll_arm
#print axioms compileModuleFlat_ok_implies_compileModule_lrat_arm
#print axioms compileModuleFlat_ok_implies_compileModule_fidSched_arm
#print axioms fidPreprocessFlat_compileFlatFn_eq_arm
#print axioms fidReduceFlat_compileFlatFn_eq_arm

end LeanQbeTest.T.MainFlatParityArm64Test

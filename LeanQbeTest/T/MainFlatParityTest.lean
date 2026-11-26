module

public import LeanQbeTest.T.MainFlatParityFixtures
public import LeanQbe.T.OptFlatValue
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.PrintAsm0
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.OptFlatValueLemmas
import LeanQbe.T.RegaFlatLemmas
meta import Lean
meta import LeanQbeTest.T.MainFlatParityFixtures
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.OptFlatValue
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintAsm0

/-!
# SysV x64 Differential Parity & Axiom Audit (`MainFlatParityTest`)

Verifies `compileModuleFlat = compileModule`, `compileFlatFn = compileFn`, byte-exact `printAsm0`
assembly on `Amd64.x64Target` (`x64LegalTarget`) over native `divConst`/`assumeElim`/`mergeRets`/
loop `TFlatFn`s, Litmus programs, and Kissat C0 schedule functions, and audits axioms (`std3` only).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainFlatParityTest

open LeanQbe.T
open LeanQbeTest.T.MainFlatParityFixtures

theorem compileModuleFlat_ok_implies_compileModule_x64
    (hints : List Amd64.x64Target.toIsa.Hints)
    {code : List Amd64.x64Target.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Amd64.x64Target.toIsa Amd64.x64LegalTarget
      Amd64.x64Target.frame.raBytes [] [] 0 litmusTFlatMod hints = .ok (code, bounds)) :
    compileModule Amd64.x64Target.toIsa Amd64.x64LegalTarget
        Amd64.x64Target.frame.raBytes [] [] 0 (litmusTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] [] 0 litmusTFlatMod hints code bounds hok

theorem divModFlat_compileFlatFn_eq_x64 (h : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h divModFlat =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h divModFlat.toFn :=
  compileFlatFn_eq_compileFn _ _ _ _ divModFlat_wf

theorem assumeLoopFlat_compileFlatFn_eq_x64 (h : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h assumeLoopFlat =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h assumeLoopFlat.toFn :=
  compileFlatFn_eq_compileFn _ _ _ _ assumeLoopFlat_wf

theorem compileModuleFlat_ok_implies_compileModule_litmusAll_x64
    (hints : List Amd64.x64Target.toIsa.Hints)
    {code : List Amd64.x64Target.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Amd64.x64Target.toIsa Amd64.x64LegalTarget
      Amd64.x64Target.frame.raBytes [] ["fail"] 0 litmusAllTFlatMod hints = .ok (code, bounds)) :
    compileModule Amd64.x64Target.toIsa Amd64.x64LegalTarget
        Amd64.x64Target.frame.raBytes [] ["fail"] 0 (litmusAllTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] ["fail"] 0 litmusAllTFlatMod hints code bounds hok

theorem compileModuleFlat_ok_implies_compileModule_lrat_x64
    (hints : List Amd64.x64Target.toIsa.Hints)
    {code : List Amd64.x64Target.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Amd64.x64Target.toIsa Amd64.x64LegalTarget
      Amd64.x64Target.frame.raBytes [] [] 0 lratBytesTFlatMod hints = .ok (code, bounds)) :
    compileModule Amd64.x64Target.toIsa Amd64.x64LegalTarget
        Amd64.x64Target.frame.raBytes [] [] 0 (lratBytesTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] [] 0 lratBytesTFlatMod hints code bounds hok

theorem compileModuleFlat_ok_implies_compileModule_fidSched_x64
    (hints : List Amd64.x64Target.toIsa.Hints)
    {code : List Amd64.x64Target.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Amd64.x64Target.toIsa Amd64.x64LegalTarget
      Amd64.x64Target.frame.raBytes (fidSchedExtCallees Amd64.x64LegalTarget) [] 0
      fidSchedTFlatMod hints = .ok (code, bounds)) :
    compileModule Amd64.x64Target.toIsa Amd64.x64LegalTarget
        Amd64.x64Target.frame.raBytes (fidSchedExtCallees Amd64.x64LegalTarget) [] 0
        (fidSchedTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ (fidSchedExtCallees Amd64.x64LegalTarget) [] 0
    fidSchedTFlatMod hints code bounds hok

theorem fidPreprocessFlat_compileFlatFn_eq_x64 (h : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidPreprocessFn) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidPreprocessFn).toFn :=
  compileFlatFn_eq_compileFn _ _ _ _
    (PassFlatKit.reifyFunc_wfCheck Examples.Kissat.FullM7FidelitySched.full_preprocess_fid_wf)

theorem fidReduceFlat_compileFlatFn_eq_x64 (h : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidReduceFn) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h
        (fnToTFlat Examples.Kissat.FullM7FidelitySched.fidReduceFn).toFn :=
  compileFlatFn_eq_compileFn _ _ _ _
    (PassFlatKit.reifyFunc_wfCheck Examples.Kissat.FullM7FidelitySched.full_reduce_fid_wf)

@[expose] def foldCasesFlat : TFlatFn :=
  { name := "fold_cases_flat"
    as := [i64, i32]
    rs := [i64]
    body :=
      .let_ ⟨.add i64, (.var 1, .imm 0#64, ())⟩ <|
      .let_ ⟨.sext 32 64, (.var 1, ())⟩ <|
      .let_ ⟨.trunc 64 32, (.var 0, ())⟩ <|
      .let_ ⟨.zext 32 64, (.var 0, ())⟩ <|
      .let_ ⟨.not i64, (.var 0, ())⟩ <|
      .let_ ⟨.not i64, (.var 0, ())⟩ <|
      .let_ ⟨.cmp .eq i64, (.imm 7#64, .imm 7#64, ())⟩ <|
      .jnz (.var 0)
        (.let_ ⟨.add i64, (.var 6, .var 1, ())⟩ <|
         .ret (.var 0, ()))
        (.ret (.imm 99#64, ())) }

@[expose] def copyCasesFlat : TFlatFn :=
  { name := "copy_cases_flat"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.copy i64, (.var 1, ())⟩ <|
      .let_ ⟨.mkpair i64 i64, (.var 0, .var 1, ())⟩ <|
      .let_ ⟨.unpair i64 i64, (.var 0, ())⟩ <|
      .let_ ⟨.add i64, (.var 1, .var 0, ())⟩ <|
      .ret (.var 0, ()) }

@[expose] def canonCasesFlat : TFlatFn :=
  { name := "canon_cases_flat"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.add i64, (.imm 3#64, .var 1, ())⟩ <|
      .let_ ⟨.add i64, (.var 0, .imm 5#64, ())⟩ <|
      .let_ ⟨.cmp .eq i64, (.imm 4#64, .var 0, ())⟩ <|
      .jnz (.var 0)
        (.group (sig := [[i64]])
          (.cons
            (.let_ ⟨.add i64, (.imm 1#64, .var 0, ())⟩ <|
             .ret (.var 0, ()))
            .nil)
          (.jump (ts := [i64]) 0 (.var 1, ())))
        (.ret (.var 1, ())) }

@[expose] def gvnCasesFlat : TFlatFn :=
  { name := "gvn_cases_flat"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.add i64, (.var 1, .var 0, ())⟩ <|
      .let_ ⟨.add i64, (.var 2, .var 1, ())⟩ <|
      .let_ ⟨.cmp .ult i64, (.var 0, .imm 10#64, ())⟩ <|
      .jnz (.var 0)
        (.let_ ⟨.add i64, (.var 4, .var 3, ())⟩ <|
         .let_ ⟨.add i64, (.var 0, .var 2, ())⟩ <|
         .ret (.var 0, ()))
        (.group (sig := [[i64]])
          (.cons
            (.let_ ⟨.add i64, (.var 0, .var 3, ())⟩ <|
             .ret (.var 0, ()))
            .nil)
          (.jump (ts := [i64]) 0 (.var 2, ()))) }

theorem foldCasesFlat_wf : foldCasesFlat.wfCheck = true := by decide
theorem copyCasesFlat_wf : copyCasesFlat.wfCheck = true := by decide
theorem canonCasesFlat_wf : canonCasesFlat.wfCheck = true := by decide
theorem gvnCasesFlat_wf : gvnCasesFlat.wfCheck = true := by decide

theorem foldCasesFlat_opt_eq :
    OptFlatValue.foldFlat foldCasesFlat.as foldCasesFlat.body =
      reifyFunc (Func.fold foldCasesFlat.toFn.body) :=
  OptFlatValue.foldFlat_eq foldCasesFlat.body foldCasesFlat_wf

theorem copyCasesFlat_opt_eq :
    OptFlatValue.copyFlat copyCasesFlat.as copyCasesFlat.body =
      reifyFunc (Func.copy copyCasesFlat.toFn.body) :=
  OptFlatValue.copyFlat_eq copyCasesFlat.body copyCasesFlat_wf

theorem canonCasesFlat_opt_eq :
    OptFlatValue.canonFlat canonCasesFlat.as canonCasesFlat.body =
      reifyFunc (Func.canon canonCasesFlat.toFn.body) :=
  OptFlatValue.canonFlat_eq canonCasesFlat.body canonCasesFlat_wf

theorem gvnCasesFlat_opt_eq :
    OptFlatValue.gvnFlat gvnCasesFlat.as gvnCasesFlat.body =
      reifyFunc (Func.gvn gvnCasesFlat.toFn.body) :=
  OptFlatValue.gvnFlat_eq gvnCasesFlat.body gvnCasesFlat_wf

theorem foldCasesFlat_toFn_eq :
    (OptFlatValue.foldFlatFn foldCasesFlat).toFn =
      ⟨foldCasesFlat.name, foldCasesFlat.as, foldCasesFlat.rs,
        Func.fold foldCasesFlat.toFn.body⟩ :=
  OptFlatValue.foldFlatFn_toFn foldCasesFlat foldCasesFlat_wf

theorem copyCasesFlat_toFn_eq :
    (OptFlatValue.copyFlatFn copyCasesFlat).toFn =
      ⟨copyCasesFlat.name, copyCasesFlat.as, copyCasesFlat.rs,
        Func.copy copyCasesFlat.toFn.body⟩ :=
  OptFlatValue.copyFlatFn_toFn copyCasesFlat copyCasesFlat_wf

theorem canonCasesFlat_toFn_eq :
    (OptFlatValue.canonFlatFn canonCasesFlat).toFn =
      ⟨canonCasesFlat.name, canonCasesFlat.as, canonCasesFlat.rs,
        Func.canon canonCasesFlat.toFn.body⟩ :=
  OptFlatValue.canonFlatFn_toFn canonCasesFlat canonCasesFlat_wf

theorem gvnCasesFlat_toFn_eq :
    (OptFlatValue.gvnFlatFn gvnCasesFlat).toFn =
      ⟨gvnCasesFlat.name, gvnCasesFlat.as, gvnCasesFlat.rs,
        Func.gvn gvnCasesFlat.toFn.body⟩ :=
  OptFlatValue.gvnFlatFn_toFn gvnCasesFlat gvnCasesFlat_wf

theorem optFlatValue_valueCases_compile_eq_x64
    (h1 : Amd64.x64Target.toIsa.Hints) (h2 : Amd64.x64Target.toIsa.Hints)
    (h3 : Amd64.x64Target.toIsa.Hints) (h4 : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h1
        (OptFlatValue.foldFlatFn foldCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h1
        ⟨foldCasesFlat.name, foldCasesFlat.as, foldCasesFlat.rs,
          Func.fold foldCasesFlat.toFn.body⟩ ∧
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h2
        (OptFlatValue.copyFlatFn copyCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h2
        ⟨copyCasesFlat.name, copyCasesFlat.as, copyCasesFlat.rs,
          Func.copy copyCasesFlat.toFn.body⟩ ∧
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h3
        (OptFlatValue.canonFlatFn canonCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h3
        ⟨canonCasesFlat.name, canonCasesFlat.as, canonCasesFlat.rs,
          Func.canon canonCasesFlat.toFn.body⟩ ∧
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h4
        (OptFlatValue.gvnFlatFn gvnCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h4
        ⟨gvnCasesFlat.name, gvnCasesFlat.as, gvnCasesFlat.rs,
          Func.gvn gvnCasesFlat.toFn.body⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatValue.foldFlatFn_wfCheck _ foldCasesFlat_wf), foldCasesFlat_toFn_eq]
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatValue.copyFlatFn_wfCheck _ copyCasesFlat_wf), copyCasesFlat_toFn_eq]
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatValue.canonFlatFn_wfCheck _ canonCasesFlat_wf), canonCasesFlat_toFn_eq]
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatValue.gvnFlatFn_wfCheck _ gvnCasesFlat_wf), gvnCasesFlat_toFn_eq]

#eval show IO Unit from do
  checkTargetParity "x64" Amd64.x64Target.toIsa Amd64.x64LegalTarget
    Amd64.x64Target.frame.raBytes Amd64.printAsm0
  let kissatFns : List TFlatFn :=
    (Examples.Kissat.FullM7FidelitySched.fidSchedFns.take 2).map fnToTFlat
  let testFns : List TFlatFn :=
    [foldCasesFlat, canonCasesFlat, gvnCasesFlat] ++ litmusTFlatMod ++ kissatFns
  let I := Amd64.x64Target.toIsa
  let lt := Amd64.x64LegalTarget
  for ff in testFns do
    if !ff.wfCheck then
      throw <| IO.userError s!"optFlatValue: wfCheck failed on {ff.name}"
    let fnsAndRefs : List (String × TFlatFn × TFlatFn) :=
      [ ("fold", OptFlatValue.foldFlatFn ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.fold ff.toFn.body)⟩)
      , ("copy", OptFlatValue.copyFlatFn ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.copy ff.toFn.body)⟩)
      , ("canon", OptFlatValue.canonFlatFn ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.canon ff.toFn.body)⟩)
      , ("gvn", OptFlatValue.gvnFlatFn ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.gvn ff.toFn.body)⟩) ]
    for (pTag, gotFf, refFf) in fnsAndRefs do
      if !gotFf.wfCheck then
        throw <| IO.userError s!"optFlatValue({pTag}): wfCheck failed on {ff.name}"
      let h := Fn.computeHints I lt refFf.toFn
      let gotDirs ← IO.ofExcept (compileFlatFn I lt h gotFf)
      let refDirs ← IO.ofExcept (compileFlatFn I lt h refFf)
      let gotBytes := (Amd64.printAsm0 gotDirs).toUTF8
      let refBytes := (Amd64.printAsm0 refDirs).toUTF8
      if let some (pos, bg, br) := firstByteDiff gotBytes refBytes then
        throw <| IO.userError
          s!"optFlatValue({pTag}) '{ff.name}' diff at byte {pos}: {bg} vs {br}"
  let copyGot := OptFlatValue.copyFlatFn copyCasesFlat
  if !copyGot.wfCheck then
    throw <| IO.userError "optFlatValue(copy) wfCheck failed on copyCasesFlat"
  IO.println s!"OK (optFlatValue): {testFns.length + 1} fns x 4 passes, 0 asm diff"

#print axioms LeanQbe.T.OptFlatValue.foldFlat_eq
#print axioms LeanQbe.T.OptFlatValue.denoteFunc_foldFlat
#print axioms LeanQbe.T.OptFlatValue.foldFlat_wfCheck
#print axioms LeanQbe.T.OptFlatValue.foldFlatFn_toFn
#print axioms LeanQbe.T.OptFlatValue.foldFlatFn_wfCheck
#print axioms LeanQbe.T.OptFlatValue.copyFlat_eq
#print axioms LeanQbe.T.OptFlatValue.denoteFunc_copyFlat
#print axioms LeanQbe.T.OptFlatValue.copyFlat_wfCheck
#print axioms LeanQbe.T.OptFlatValue.copyFlatFn_toFn
#print axioms LeanQbe.T.OptFlatValue.copyFlatFn_wfCheck
#print axioms LeanQbe.T.OptFlatValue.canonFlat_eq
#print axioms LeanQbe.T.OptFlatValue.denoteFunc_canonFlat
#print axioms LeanQbe.T.OptFlatValue.canonFlat_wfCheck
#print axioms LeanQbe.T.OptFlatValue.canonFlatFn_toFn
#print axioms LeanQbe.T.OptFlatValue.canonFlatFn_wfCheck
#print axioms LeanQbe.T.OptFlatValue.gvnFlat_eq
#print axioms LeanQbe.T.OptFlatValue.denoteFunc_gvnFlat
#print axioms LeanQbe.T.OptFlatValue.gvnFlat_wfCheck
#print axioms LeanQbe.T.OptFlatValue.gvnFlatFn_toFn
#print axioms LeanQbe.T.OptFlatValue.gvnFlatFn_wfCheck
#print axioms optFlatValue_valueCases_compile_eq_x64
#print axioms LeanQbe.T.denote_toTFlat_eq
#print axioms LeanQbe.T.Func.renorm_eq_self
#print axioms LeanQbe.T.reifyFunc_denoteFunc_eq
#print axioms LeanQbe.T.Func.renorm_denoteFunc
#print axioms LeanQbe.T.TFlat.ext_eq_fn_ext
#print axioms LeanQbe.T.TFlatFn.supportsSource_eq
#print axioms LeanQbe.T.legalFlat_eq
#print axioms LeanQbe.T.Rega.lowerFlatFn_eq_lowerFn
#print axioms LeanQbe.T.earlyOptFlat_toFn
#print axioms LeanQbe.T.midStageFlat_toFn
#print axioms LeanQbe.T.compileFlatFn_eq_compileFn
#print axioms LeanQbe.T.compileModule_of_compileModuleFlat
#print axioms compileModuleFlat_ok_implies_compileModule_x64
#print axioms divModFlat_compileFlatFn_eq_x64
#print axioms assumeLoopFlat_compileFlatFn_eq_x64
#print axioms compileModuleFlat_ok_implies_compileModule_litmusAll_x64
#print axioms compileModuleFlat_ok_implies_compileModule_lrat_x64
#print axioms compileModuleFlat_ok_implies_compileModule_fidSched_x64
#print axioms fidPreprocessFlat_compileFlatFn_eq_x64
#print axioms fidReduceFlat_compileFlatFn_eq_x64

end LeanQbeTest.T.MainFlatParityTest

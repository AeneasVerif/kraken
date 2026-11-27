module

public import LeanQbeTest.T.MainFlatParityFixtures
public import LeanQbe.T.OptFlatCfg
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.PrintAsm0
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.OptFlatCfgLemmas
import LeanQbe.T.RegaFlatLemmas
meta import Lean
meta import LeanQbeTest.T.MainFlatParityFixtures
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.OptFlatCfg
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintAsm0

/-!
# SysV x64 Differential Parity & Axiom Audit for `OptFlatCfg` (`MainFlatCfgParityTest`)

Verifies `OptFlatCfg.{dceFlat, deadLoadElimFlat, dcePFlat, ifOptFlat}` exact correspondence with
`Func.{dce, deadLoadElim, dceP, ifOpt, ifOptBits}` (`reifyFunc` + `compileFlatFn_eq_compileFn`),
byte-exact `Amd64.printAsm0` assembly parity against `reifyFunc (Func.* ff.toFn.body)`, and
`std3`-only axioms.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainFlatCfgParityTest

open LeanQbe.T
open LeanQbeTest.T.MainFlatParityFixtures

def dcePCasesFlat : TFlatFn :=
  { name := "dce_p_cases_flat"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.add i64, (.var 1, .var 0, ())⟩ <|
      .load i64 (.var 2) <|
      .group (sig := [[i64, i64]])
        (.cons
          (.let_ ⟨.add i64, (.var 1, .var 2, ())⟩ <|
           .ret (.var 0, ()))
          .nil)
        (.let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩ <|
         .jnz (.var 0)
           (.jump (ts := [i64, i64]) 0 (.var 3, .var 2, ()))
           (.jump (ts := [i64, i64]) 0 (.var 4, .var 2, ()))) }

def deadLoadCasesFlat : TFlatFn :=
  { name := "dead_load_cases_flat"
    as := [i64, i64]
    rs := [i64]
    body :=
      .load i64 (.var 1) <|
      .let_ ⟨.add i64, (.var 1, .imm 5#64, ())⟩ <|
      .load i64 (.var 2) <|
      .store (t := i64) (.var 0) (.var 4) <|
      .ret (.var 0, ()) }

def ifOptJoinCasesFlat : TFlatFn :=
  { name := "if_opt_join_cases_flat"
    as := [i64, i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩ <|
      .group (sig := [[i64]])
        (.cons
          (.let_ ⟨.add i64, (.var 0, .imm 1#64, ())⟩ <|
           .ret (.var 0, ()))
          .nil)
        (.jnz (.var 0)
          (.let_ ⟨.add i64, (.var 2, .imm 10#64, ())⟩ <|
           .jump (ts := [i64]) 0 (.var 0, ()))
          (.jump (ts := [i64]) 0 (.var 3, ()))) }

def ifOptBitsRetCasesFlat : TFlatFn :=
  { name := "if_opt_bits_ret_cases_flat"
    as := [i64, i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩ <|
      .jnz (.var 0)
        (.let_ ⟨.add i64, (.var 1, .imm 3#64, ())⟩ <|
         .ret (.var 0, ()))
        (.let_ ⟨.mul i64, (.var 2, .imm 7#64, ())⟩ <|
         .ret (.var 0, ())) }

theorem dcePCasesFlat_wf : dcePCasesFlat.wfCheck = true := by decide
theorem deadLoadCasesFlat_wf : deadLoadCasesFlat.wfCheck = true := by decide
theorem ifOptJoinCasesFlat_wf : ifOptJoinCasesFlat.wfCheck = true := by decide
theorem ifOptBitsRetCasesFlat_wf : ifOptBitsRetCasesFlat.wfCheck = true := by decide

theorem dcePCasesFlat_opt_eq :
    OptFlatCfg.dcePFlat dcePCasesFlat.as dcePCasesFlat.body =
      reifyFunc (Func.dceP dcePCasesFlat.toFn.body) :=
  OptFlatCfg.dcePFlat_eq dcePCasesFlat.body dcePCasesFlat_wf

theorem deadLoadCasesFlat_dce_eq :
    OptFlatCfg.dceFlat deadLoadCasesFlat.as deadLoadCasesFlat.body =
      reifyFunc (Func.dce deadLoadCasesFlat.toFn.body) :=
  OptFlatCfg.dceFlat_eq deadLoadCasesFlat.body deadLoadCasesFlat_wf

theorem deadLoadCasesFlat_dle_eq :
    OptFlatCfg.deadLoadElimFlat deadLoadCasesFlat.as deadLoadCasesFlat.body =
      reifyFunc (Func.deadLoadElim deadLoadCasesFlat.toFn.body) :=
  OptFlatCfg.deadLoadElimFlat_eq deadLoadCasesFlat.body deadLoadCasesFlat_wf

theorem ifOptJoinCasesFlat_false_eq :
    OptFlatCfg.ifOptFlat false ifOptJoinCasesFlat.as ifOptJoinCasesFlat.body =
      reifyFunc (Func.ifOpt ifOptJoinCasesFlat.toFn.body) :=
  OptFlatCfg.ifOptFlat_false_eq ifOptJoinCasesFlat.body ifOptJoinCasesFlat_wf

theorem ifOptJoinCasesFlat_true_eq :
    OptFlatCfg.ifOptFlat true ifOptJoinCasesFlat.as ifOptJoinCasesFlat.body =
      reifyFunc (Func.ifOptBits ifOptJoinCasesFlat.toFn.body) :=
  OptFlatCfg.ifOptFlat_true_eq ifOptJoinCasesFlat.body ifOptJoinCasesFlat_wf

theorem ifOptBitsRetCasesFlat_true_eq :
    OptFlatCfg.ifOptFlat true ifOptBitsRetCasesFlat.as ifOptBitsRetCasesFlat.body =
      reifyFunc (Func.ifOptBits ifOptBitsRetCasesFlat.toFn.body) :=
  OptFlatCfg.ifOptFlat_true_eq ifOptBitsRetCasesFlat.body ifOptBitsRetCasesFlat_wf

theorem dcePCasesFlat_toFn_eq :
    (OptFlatCfg.dcePFlatFn dcePCasesFlat).toFn =
      ⟨dcePCasesFlat.name, dcePCasesFlat.as, dcePCasesFlat.rs,
        Func.dceP dcePCasesFlat.toFn.body⟩ :=
  OptFlatCfg.dcePFlatFn_toFn dcePCasesFlat dcePCasesFlat_wf

theorem deadLoadCasesFlat_dle_toFn_eq :
    (OptFlatCfg.deadLoadElimFlatFn deadLoadCasesFlat).toFn =
      ⟨deadLoadCasesFlat.name, deadLoadCasesFlat.as, deadLoadCasesFlat.rs,
        Func.deadLoadElim deadLoadCasesFlat.toFn.body⟩ :=
  OptFlatCfg.deadLoadElimFlatFn_toFn deadLoadCasesFlat deadLoadCasesFlat_wf

theorem ifOptJoinCasesFlat_false_toFn_eq :
    (OptFlatCfg.ifOptFlatFn false ifOptJoinCasesFlat).toFn =
      ⟨ifOptJoinCasesFlat.name, ifOptJoinCasesFlat.as, ifOptJoinCasesFlat.rs,
        Func.ifOpt ifOptJoinCasesFlat.toFn.body⟩ :=
  OptFlatCfg.ifOptFlatFn_toFn false ifOptJoinCasesFlat ifOptJoinCasesFlat_wf

theorem optFlatCfg_cfgCases_compile_eq_x64
    (h1 : Amd64.x64Target.toIsa.Hints) (h2 : Amd64.x64Target.toIsa.Hints)
    (h3 : Amd64.x64Target.toIsa.Hints) (h4 : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h1
        (OptFlatCfg.dcePFlatFn dcePCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h1
        ⟨dcePCasesFlat.name, dcePCasesFlat.as, dcePCasesFlat.rs,
          Func.dceP dcePCasesFlat.toFn.body⟩ ∧
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h2
        (OptFlatCfg.deadLoadElimFlatFn deadLoadCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h2
        ⟨deadLoadCasesFlat.name, deadLoadCasesFlat.as, deadLoadCasesFlat.rs,
          Func.deadLoadElim deadLoadCasesFlat.toFn.body⟩ ∧
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h3
        (OptFlatCfg.ifOptFlatFn false ifOptJoinCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h3
        ⟨ifOptJoinCasesFlat.name, ifOptJoinCasesFlat.as, ifOptJoinCasesFlat.rs,
          Func.ifOpt ifOptJoinCasesFlat.toFn.body⟩ ∧
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h4
        (OptFlatCfg.ifOptFlatFn true ifOptBitsRetCasesFlat) =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h4
        ⟨ifOptBitsRetCasesFlat.name, ifOptBitsRetCasesFlat.as, ifOptBitsRetCasesFlat.rs,
          Func.ifOptBits ifOptBitsRetCasesFlat.toFn.body⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatCfg.dcePFlatFn_wfCheck _ dcePCasesFlat_wf), dcePCasesFlat_toFn_eq]
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatCfg.deadLoadElimFlatFn_wfCheck _ deadLoadCasesFlat_wf),
      deadLoadCasesFlat_dle_toFn_eq]
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatCfg.ifOptFlatFn_wfCheck _ _ ifOptJoinCasesFlat_wf),
      OptFlatCfg.ifOptFlatFn_toFn _ _ ifOptJoinCasesFlat_wf]
  · rw [compileFlatFn_eq_compileFn _ _ _ _
      (OptFlatCfg.ifOptFlatFn_wfCheck _ _ ifOptBitsRetCasesFlat_wf),
      OptFlatCfg.ifOptFlatFn_toFn _ _ ifOptBitsRetCasesFlat_wf]
    rfl

#eval show IO Unit from do
  let kissatFns : List TFlatFn :=
    (Examples.Kissat.Plain.plain1Module.fns.take 2).map fnToTFlat
  let testFns : List TFlatFn :=
    [dcePCasesFlat, deadLoadCasesFlat, ifOptJoinCasesFlat, ifOptBitsRetCasesFlat] ++
      litmusTFlatMod ++ kissatFns
  let I := Amd64.x64Target.toIsa
  let lt := Amd64.x64LegalTarget
  for ff in testFns do
    if !ff.wfCheck then
      throw <| IO.userError s!"optFlatCfg: wfCheck failed on {ff.name}"
    if !(OptFlatCfg.dceFlatFn ff).wfCheck then
      throw <| IO.userError s!"optFlatCfg(dce): wfCheck failed on {ff.name}"
    let fnsAndRefs : List (String × TFlatFn × TFlatFn) :=
      [ ("dceP", OptFlatCfg.dcePFlatFn ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.dceP ff.toFn.body)⟩)
      , ("deadLoadElim", OptFlatCfg.deadLoadElimFlatFn ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.deadLoadElim ff.toFn.body)⟩)
      , ("ifOpt", OptFlatCfg.ifOptFlatFn false ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.ifOpt ff.toFn.body)⟩)
      , ("ifOptBits", OptFlatCfg.ifOptFlatFn true ff,
          ⟨ff.name, ff.as, ff.rs, reifyFunc (Func.ifOptBits ff.toFn.body)⟩) ]
    for (pTag, gotFf, refFf) in fnsAndRefs do
      if !gotFf.wfCheck then
        throw <| IO.userError s!"optFlatCfg({pTag}): wfCheck failed on {ff.name}"
      let h := Fn.computeHints I lt refFf.toFn
      let gotDirs ← IO.ofExcept (compileFlatFn I lt h gotFf)
      let refDirs ← IO.ofExcept (compileFlatFn I lt h refFf)
      let gotBytes := (Amd64.printAsm0 gotDirs).toUTF8
      let refBytes := (Amd64.printAsm0 refDirs).toUTF8
      if let some (pos, bg, br) := firstByteDiff gotBytes refBytes then
        throw <| IO.userError
          s!"optFlatCfg({pTag}) '{ff.name}' diff at byte {pos}: {bg} vs {br}"
  IO.println s!"OK (optFlatCfg): {testFns.length} fns x 4 passes, 0 asm diff"

#print axioms LeanQbe.T.OptFlatCfg.dceWithFlat_eq
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_dceWithFlat
#print axioms LeanQbe.T.OptFlatCfg.dceWithFlat_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.dceFlat_eq
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_dceFlat
#print axioms LeanQbe.T.OptFlatCfg.dceFlat_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.dceFlatFn_toFn
#print axioms LeanQbe.T.OptFlatCfg.dceFlatFn_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.deadLoadElimFlat_eq
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_deadLoadElimFlat
#print axioms LeanQbe.T.OptFlatCfg.deadLoadElimFlat_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.deadLoadElimFlatFn_toFn
#print axioms LeanQbe.T.OptFlatCfg.deadLoadElimFlatFn_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.dcePWithFlat_eq
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_dcePWithFlat
#print axioms LeanQbe.T.OptFlatCfg.dcePWithFlat_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.dcePFlat_eq
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_dcePFlat
#print axioms LeanQbe.T.OptFlatCfg.dcePFlat_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.dcePFlatFn_toFn
#print axioms LeanQbe.T.OptFlatCfg.dcePFlatFn_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlat_eq
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlat_false_eq
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlat_true_eq
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_ifOptFlat
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_ifOptFlat_false
#print axioms LeanQbe.T.OptFlatCfg.denoteFunc_ifOptFlat_true
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlat_wfCheck
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlatFn_toFn
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlatFn_wfCheck
#print axioms optFlatCfg_cfgCases_compile_eq_x64

end LeanQbeTest.T.MainFlatCfgParityTest

module

public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
meta import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat `M5` (`FullM5KittenDefFix`)

1. Executable `#guard` checks on `m5KittenDefFixModule` (`6` owned `_m5` functions + `7` canonical
   `FullKitten` externs, `0` exits), `checkAcyclic = true`, `m5KittenDefFixSpecTable` (`13` rows),
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated headline theorems for all `6` parametric `Func.wp` contracts,
   `m5KittenDefFix_moduleOk : ModuleOk m5KittenDefFixEnv m5KittenDefFixModule`, and all `7`
   concrete `Mem 64` UNSAT non-vacuity witnesses (`XPost := False`, `0` SAT model proofs).
3. Single-line `#print axioms` audit (strictly `⊆ [propext, Classical.choice,
   Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatM5KittenDefFixTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM5KittenDefFix

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m5KittenDefFixModule.checkAcyclic == true
#guard m5KittenDefFixModule.exits.isEmpty
#guard m5KittenDefFix_fns.length == 6
#guard m5KittenDefFixExterns.length == 7
#guard m5KittenDefFixSpecTable.length == 13
#guard (m5KittenDefFixSpecTable.all fun e => e.noExit) == true
#guard m5KittenDefFix_fns.map Fn.name ==
  [ "full_kitten_add_clause_m5", "full_kitten_ana_clause_m5",
    "full_kitten_build_failing_m5", "full_kitten_solve_m5",
    "full_kitten_core_m5", "full_find_definition_m5" ]
#guard (ppTModule m5KittenDefFixModule).isOk
#guard (PrintQbe.module m5KittenDefFixModule).isOk
#guard (ppModule (m5KittenDefFix_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5KittenDefFix_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5KittenDefFix_fns.map (Fn.legal .x64AVX2))).isOk

end LeanQbeTest.T.KissatM5KittenDefFixTest

/-! ## 2. Short Root-Namespace Audit Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullDefSweep
open LeanQbe.T.Examples.Kissat.FullM5KittenDefFix

theorem m5kd_wf : ∀ f ∈ m5KittenDefFix_fns, f.Wf :=
  m5KittenDefFix_fns_wf

theorem m5kd_acyc : m5KittenDefFixModule.checkAcyclic = true :=
  m5KittenDefFixModule_acyclic

theorem m5kd_noExit : ∀ e ∈ m5KittenDefFixSpecTable, e.noExit = true :=
  m5KittenDefFixSpecTable_noExit

theorem m5kd_sigs :
    (m5KittenDefFixSpecTable.take 6).map (fun e => (e.name, e.as, e.rs)) =
      m5KittenDefFix_fns.map (fun f => (f.name, f.as, f.rs)) :=
  m5KittenDefFixSpecTable_sigs

theorem m5kd_ext_sigs :
    (m5KittenDefFixSpecTable.drop 6).map (fun e => ⟨e.name, e.as, e.rs⟩) =
      m5KittenDefFixExterns :=
  m5KittenDefFixSpecTable_ext_sigs

theorem m5kd_env_noExit :
    ∀ f as bs xs m Q X X',
      m5KittenDefFixEnv f as bs xs m Q X → m5KittenDefFixEnv f as bs xs m Q X' :=
  m5KittenDefFixEnv_noExit

theorem m5kd_add_wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullKittenWatchSpec a m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullKittenAddClauseSpec a m Q X →
      Func.wp Γ full_kitten_add_clause_m5_body a m Q X :=
  full_kitten_add_clause_m5_wp Γ hWatch

theorem m5kd_ana_wp (Γ : Env) :
    ∀ a m Q X, fullKittenAnaClauseM5Spec a m Q X →
      Func.wp Γ full_kitten_ana_clause_m5_body a m Q X :=
  full_kitten_ana_clause_m5_wp Γ

theorem m5kd_bf_wp (Γ : Env) :
    ∀ a m Q X, fullKittenBuildFailingSpec a m Q X →
      Func.wp Γ full_kitten_build_failing_m5_body a m Q X :=
  full_kitten_build_failing_m5_wp Γ

theorem m5kd_slv_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullKittenAssignSpec a m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullKittenBacktrackSpec a m Q X →
      Γ "full_kitten_backtrack" [i64, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullKittenPropagateSpec a m Q X →
      Γ "full_kitten_propagate" [i64] [i32] a m Q X)
    (hAnalyze : ∀ a m Q X, fullKittenAnalyzeSpec a m Q X →
      Γ "full_kitten_analyze" [i64, i32] [.bool] a m Q X)
    (hBuildFailing : ∀ a m Q X, fullKittenBuildFailingSpec a m Q X →
      Γ "full_kitten_build_failing_m5" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullKittenSolveSpec a m Q X →
      Func.wp Γ full_kitten_solve_m5_body a m Q X :=
  full_kitten_solve_m5_wp Γ hBacktrack hAssign hProp hAnalyze hBuildFailing

theorem m5kd_cor_wp (Γ : Env) :
    ∀ a m Q X, fullKittenCoreSpec a m Q X →
      Func.wp Γ full_kitten_core_m5_body a m Q X :=
  full_kitten_core_m5_wp Γ

theorem m5kd_def_wp (Γ : Env)
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLawsM5 KInv)
    (hInit : ∀ a m Q X, FullDefSweep.fullKittenInitSpec KInv a m Q X →
      Γ "full_kitten_init" [i64, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, FullDefSweep.fullKittenAddClauseSpec KInv a m Q X →
      Γ "full_kitten_add_clause_m5" [i64, i32, i64, i32] [.bool] a m Q X)
    (hSolve : ∀ a m Q X, FullDefSweep.fullKittenSolveSpec KInv a m Q X →
      Γ "full_kitten_solve_m5" [i64, i64] [i64] a m Q X)
    (hCore : ∀ a m Q X, FullDefSweep.fullKittenCoreSpec KInv a m Q X →
      Γ "full_kitten_core_m5" [i64] [i32] a m Q X)
    (hShrink : ∀ a m Q X, FullDefSweep.fullKittenShrinkSpec KInv a m Q X →
      Γ "full_kitten_shrink" [i64] [] a m Q X) :
    ∀ a m Q X, fullFindDefinitionSpec a m Q X →
      Func.wp Γ full_find_definition_m5_body a m Q X :=
  full_find_definition_m5_wp Γ hLaws hInit hAddCl hSolve hCore hShrink

theorem m5kd_mod_ok : ModuleOk m5KittenDefFixEnv m5KittenDefFixModule :=
  m5KittenDefFix_moduleOk

theorem m5kd_nv_add :
    Func.wp m5KittenDefFixEnv full_kitten_add_clause_m5_body
      (nvKittenCfg.hdr, 0#32, nvKittenCfg.pTmp, 0#32, ()) nvKittenMem
      (fun (ok, ()) m' => ∃ scr',
        let s' : FullState :=
          { nvKittenState with scratch := { nvKittenState.scratch with scratch_buf := scr' } }
        KittenScratchInv scr' ∧ (cnfOfClauses (kittenOrigClausesS scr')).Unsat ∧
        (ok = true ∨ ok = false) ∧ FullMem nvKittenCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_add_clause_m5

theorem m5kd_nv_ana :
    Func.wp m5KittenDefFixEnv full_kitten_ana_clause_m5_body
      (0x2000#64, 1#32, 0xFFFFFFFF#32, ()) nvM5AnaMem
      (fun () m' => ∃ ks',
        KittenAnaInvM5 1376 ks' [[0], [1]] 1 ∧
        (cnfOfClauses [[0], [1]]).Unsat ∧ KittenMem 0x2000#64 ks' m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_ana_clause_m5

theorem m5kd_nv_bf :
    Func.wp m5KittenDefFixEnv full_kitten_build_failing_m5_body
      (0x2000#64, 1#32, ()) nvM5FailMem
      (fun () m' => ∃ ks',
        ks'.Inv 1376 ∧ ks'.failing = 1#32 ∧
        (cnfOfClauses (kittenOrigClauses ks') ++ unitsCnf (kittenAssumpLits ks')).Unsat ∧
        KittenMem 0x2000#64 ks' m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_build_failing_m5

theorem m5kd_nv_slv :
    Func.wp m5KittenDefFixEnv full_kitten_solve_m5_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ fuel' scr',
        let s' : FullState :=
          { nvKittenState with
            core := { nvKittenState.core with fuel := fuel' }
            scratch := { nvKittenState.scratch with scratch_buf := scr' } }
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_solve_m5

theorem m5kd_nv_slv20 :
    Func.wp m5KittenDefFixEnv full_kitten_solve_m5_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ scr',
        r = 20#64 ∧ (kittenStateOfScratch scr').incons ≠ 0xFFFFFFFF#32 ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_solve_m5_unsat20

theorem m5kd_nv_cor :
    Func.wp m5KittenDefFixEnv full_kitten_core_m5_body (nvKittenCfg.hdr, ()) nvM5CoreMem
      (fun (_csz, ()) m' => ∃ scr',
        KittenScratchInv scr' ∧
        (cnfOfClauses (kittenCoreClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_core_m5

theorem m5kd_nv_def :
    Func.wp m5KittenDefFixEnv full_find_definition_m5_body
      (nvDefSweepCfg.hdr, 0#32, 1#32, 1#32, ()) nvDefSweepMem
      (fun () m' => ∃ s',
        Full.FullDenseInvW nvDefSweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_find_definition_m5

#print axioms m5kd_wf
#print axioms m5kd_acyc
#print axioms m5kd_noExit
#print axioms m5kd_sigs
#print axioms m5kd_ext_sigs
#print axioms m5kd_env_noExit
#print axioms m5kd_add_wp
#print axioms m5kd_ana_wp
#print axioms m5kd_bf_wp
#print axioms m5kd_slv_wp
#print axioms m5kd_cor_wp
#print axioms m5kd_def_wp
#print axioms m5kd_mod_ok
#print axioms m5kd_nv_add
#print axioms m5kd_nv_ana
#print axioms m5kd_nv_bf
#print axioms m5kd_nv_slv
#print axioms m5kd_nv_slv20
#print axioms m5kd_nv_cor
#print axioms m5kd_nv_def

end AxiomAudit

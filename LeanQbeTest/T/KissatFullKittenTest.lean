module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas
meta import LeanQbe.T.Examples.Kissat.FullKittenLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullKitten` (`15/15`)

1. Executable `#guard` checks on `fullKitten_fns` (`15` functions), names & signatures,
   `fullKittenModule.checkAcyclic`, `fullKittenSpecTable` (`15` rows, all `noExit = true`),
   and `nvKittenBytes.length == nvKittenCfg.avail` (`42716`).
2. Short root-namespace audit theorems + single-line `#print axioms` (`<= 100` cols, every
   `depends on axioms: [...]` output `< 115` chars on one line) on `fullKitten_fns_wf`,
   `fullKitten_acyclic`, all `15/15` `Func.wp` proofs, `fullKittenEnv_noExit`,
   `mkFullKittenEnv_moduleOk_of_parts`, unconditional `fullKittenEnv_moduleOk`, and concrete
   `Mem 64` UNSAT non-vacuity (`nv_full_kitten_solve`, `nv_full_kitten_solve_unsat20`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFullKittenTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Full

/-! ## 1. Executable `#guard` sanity checks -/

#guard fullKitten_fns.length == 15
#guard fullKittenModule.externs.length == 0
#guard fullKittenModule.checkAcyclic == true
#guard fullKittenSpecTable.length == 15
#guard (fullKittenSpecTable.all fun e => e.noExit) == true
#guard fullKitten_fns.map Fn.name ==
  [ "full_kitten_init", "full_kitten_watch", "full_kitten_add_clause",
    "full_kitten_assign", "full_kitten_mtf", "full_kitten_backtrack",
    "full_kitten_learn_unit0", "full_kitten_propagate", "full_kitten_ana_clause",
    "full_kitten_analyze", "full_kitten_build_failing", "full_kitten_solve",
    "full_kitten_core", "full_kitten_shrink", "full_kitten_flip" ]
#guard (fullKitten_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_kitten_init", 3, 0), ("full_kitten_watch", 4, 0),
    ("full_kitten_add_clause", 4, 1), ("full_kitten_assign", 3, 0),
    ("full_kitten_mtf", 2, 0), ("full_kitten_backtrack", 2, 0),
    ("full_kitten_learn_unit0", 4, 1), ("full_kitten_propagate", 1, 1),
    ("full_kitten_ana_clause", 3, 0), ("full_kitten_analyze", 2, 1),
    ("full_kitten_build_failing", 2, 0), ("full_kitten_solve", 2, 1),
    ("full_kitten_core", 1, 1), ("full_kitten_shrink", 1, 0),
    ("full_kitten_flip", 2, 1) ]
#guard nvKittenBytes.length == nvKittenCfg.avail

end LeanQbeTest.T.KissatFullKittenTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full

theorem fk_fns_wf : ∀ f ∈ fullKitten_fns, f.Wf := fullKitten_fns_wf

theorem fk_acyclic : fullKittenModule.checkAcyclic = true := fullKitten_acyclic

theorem fk_specs_noExit : ∀ e ∈ fullKittenSpecTable, e.noExit = true :=
  fullKittenSpecTable_noExit

theorem fk_specs_sigs :
    fullKittenSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fullKitten_fns.map (fun f => (f.name, f.as, f.rs)) :=
  fullKittenSpecTable_sigs

theorem fk_init_wp (Γ : Env) :
    ∀ a m Q X, fullKittenInitSpec a m Q X → Func.wp Γ full_kitten_init_body a m Q X :=
  full_kitten_init_wp Γ

theorem fk_watch_wp (Γ : Env) :
    ∀ a m Q X, fullKittenWatchSpec a m Q X → Func.wp Γ full_kitten_watch_body a m Q X :=
  full_kitten_watch_wp Γ

theorem fk_add_clause_wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullKittenWatchSpec a m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullKittenAddClauseSpec a m Q X →
      Func.wp Γ full_kitten_add_clause_body a m Q X :=
  full_kitten_add_clause_wp Γ hWatch

theorem fk_assign_wp (Γ : Env) :
    ∀ a m Q X, fullKittenAssignSpec a m Q X → Func.wp Γ full_kitten_assign_body a m Q X :=
  full_kitten_assign_wp Γ

theorem fk_mtf_wp (Γ : Env) :
    ∀ a m Q X, fullKittenMtfSpec a m Q X → Func.wp Γ full_kitten_mtf_body a m Q X :=
  full_kitten_mtf_wp Γ

theorem fk_backtrack_wp (Γ : Env) :
    ∀ a m Q X, fullKittenBacktrackSpec a m Q X →
      Func.wp Γ full_kitten_backtrack_body a m Q X :=
  full_kitten_backtrack_wp Γ

theorem fk_learn_unit0_wp (Γ : Env) :
    ∀ a m Q X, fullKittenLearnUnit0Spec a m Q X →
      Func.wp Γ full_kitten_learn_unit0_body a m Q X :=
  full_kitten_learn_unit0_wp Γ

theorem fk_propagate_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullKittenAssignSpec a m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] a m Q X)
    (hLearn : ∀ a m Q X, fullKittenLearnUnit0Spec a m Q X →
      Γ "full_kitten_learn_unit0" [i64, i32, i32, .bool] [i32] a m Q X) :
    ∀ a m Q X, fullKittenPropagateSpec a m Q X →
      Func.wp Γ full_kitten_propagate_body a m Q X :=
  full_kitten_propagate_wp Γ hAssign hLearn

theorem fk_ana_clause_wp (Γ : Env) :
    ∀ a m Q X, fullKittenAnaClauseSpec a m Q X →
      Func.wp Γ full_kitten_ana_clause_body a m Q X :=
  full_kitten_ana_clause_wp Γ

theorem fk_analyze_wp (Γ : Env)
    (hAnaCl : ∀ a m Q X, fullKittenAnaClauseSpec a m Q X →
      Γ "full_kitten_ana_clause" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ a m Q X, fullKittenBacktrackSpec a m Q X →
      Γ "full_kitten_backtrack" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullKittenMtfSpec a m Q X →
      Γ "full_kitten_mtf" [i64, i32] [] a m Q X)
    (hUnit0 : ∀ a m Q X, fullKittenLearnUnit0Spec a m Q X →
      Γ "full_kitten_learn_unit0" [i64, i32, i32, .bool] [i32] a m Q X)
    (hAssign : ∀ a m Q X, fullKittenAssignSpec a m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] a m Q X)
    (hWatch : ∀ a m Q X, fullKittenWatchSpec a m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullKittenAnalyzeSpec a m Q X →
      Func.wp Γ full_kitten_analyze_body a m Q X :=
  full_kitten_analyze_wp Γ hAnaCl hBt hMtf hUnit0 hAssign hWatch

theorem fk_build_failing_wp (Γ : Env) :
    ∀ a m Q X, fullKittenBuildFailingSpec a m Q X →
      Func.wp Γ full_kitten_build_failing_body a m Q X :=
  full_kitten_build_failing_wp Γ

theorem fk_core_wp (Γ : Env) :
    ∀ a m Q X, fullKittenCoreSpec a m Q X → Func.wp Γ full_kitten_core_body a m Q X :=
  full_kitten_core_wp Γ

theorem fk_shrink_wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullKittenWatchSpec a m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullKittenShrinkSpec a m Q X →
      Func.wp Γ full_kitten_shrink_body a m Q X :=
  full_kitten_shrink_wp Γ hWatch

theorem fk_flip_wp (Γ : Env) :
    ∀ a m Q X, fullKittenFlipSpec a m Q X → Func.wp Γ full_kitten_flip_body a m Q X :=
  full_kitten_flip_wp Γ

theorem fk_solve_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullKittenBacktrackSpec a m Q X →
      Γ "full_kitten_backtrack" [i64, i32] [] a m Q X)
    (hAsg : ∀ a m Q X, fullKittenAssignSpec a m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullKittenPropagateSpec a m Q X →
      Γ "full_kitten_propagate" [i64] [i32] a m Q X)
    (hAna : ∀ a m Q X, fullKittenAnalyzeSpec a m Q X →
      Γ "full_kitten_analyze" [i64, i32] [.bool] a m Q X)
    (hBf : ∀ a m Q X, fullKittenBuildFailingSpec a m Q X →
      Γ "full_kitten_build_failing" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullKittenSolveSpec a m Q X → Func.wp Γ full_kitten_solve_body a m Q X :=
  full_kitten_solve_wp Γ hBt hAsg hProp hAna hBf

theorem fk_env_noExit :
    ∀ f as bs xs m Q X X',
      fullKittenEnv f as bs xs m Q X → fullKittenEnv f as bs xs m Q X' :=
  fullKittenEnv_noExit

theorem fk_moduleOk_of_parts
    (h8 : ∀ a m Q X, fullKittenBuildFailingSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_build_failing_body a m Q X)
    (h9 : ∀ a m Q X, fullKittenFlipSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_flip_body a m Q X)
    (h10 : ∀ a m Q X, fullKittenPropagateSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_propagate_body a m Q X)
    (h11 : ∀ a m Q X, fullKittenAnaClauseSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_ana_clause_body a m Q X)
    (h12 : ∀ a m Q X, fullKittenAnalyzeSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_analyze_body a m Q X)
    (h13 : ∀ a m Q X, fullKittenCoreSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_core_body a m Q X)
    (h14 : ∀ a m Q X, fullKittenShrinkSpec a m Q X →
      Func.wp fullKittenEnv full_kitten_shrink_body a m Q X) :
    ModuleOk fullKittenEnv fullKittenModule :=
  mkFullKittenEnv_moduleOk_of_parts h8 h9 h10 h11 h12 h13 h14

theorem fk_moduleOk : ModuleOk fullKittenEnv fullKittenModule := fullKittenEnv_moduleOk

theorem fk_nv_mem_ok : FullMem nvKittenCfg nvKittenState nvKittenMem := nvKittenMem_ok

theorem fk_nv_solve :
    Func.wp fullKittenEnv full_kitten_solve_body
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
  nv_full_kitten_solve

theorem fk_nv_solve20 :
    Func.wp fullKittenEnv full_kitten_solve_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ scr',
        r = 20#64 ∧
        (kittenStateOfScratch scr').incons ≠ 0xFFFFFFFF#32 ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with
            scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_solve_unsat20

#print axioms fk_fns_wf
#print axioms fk_acyclic
#print axioms fk_specs_noExit
#print axioms fk_specs_sigs
#print axioms fk_init_wp
#print axioms fk_watch_wp
#print axioms fk_add_clause_wp
#print axioms fk_assign_wp
#print axioms fk_mtf_wp
#print axioms fk_backtrack_wp
#print axioms fk_learn_unit0_wp
#print axioms fk_propagate_wp
#print axioms fk_ana_clause_wp
#print axioms fk_analyze_wp
#print axioms fk_build_failing_wp
#print axioms fk_core_wp
#print axioms fk_shrink_wp
#print axioms fk_flip_wp
#print axioms fk_solve_wp
#print axioms fk_env_noExit
#print axioms fk_moduleOk_of_parts
#print axioms fk_moduleOk
#print axioms fk_nv_mem_ok
#print axioms fk_nv_solve
#print axioms fk_nv_solve20

end AxiomAudit

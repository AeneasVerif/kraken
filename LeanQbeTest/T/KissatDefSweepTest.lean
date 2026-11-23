module

public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas
meta import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullDefSweep` (`9/9`)

1. Executable `#guard` checks on `full_def_sweep_fns` (`9` functions), `fullDefSweepExterns`
   (`12` externs), `fullDefSweepModule.checkAcyclic`, `defSweepSpecTable` (`21` rows, all
   `noExit = true`), and `nvDefSweepBytes.length == nvDefSweepCfg.avail` (`42716`).
2. Short root-namespace `fds_*` audit theorems + single-line `#print axioms` audit.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatDefSweepTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullDefSweep

/-! ## 1. Executable `#guard` sanity checks -/

#guard full_def_sweep_fns.length == 9
#guard fullDefSweepModule.externs.length == 12
#guard fullDefSweepModule.checkAcyclic == true
#guard defSweepSpecTable.length == 21
#guard (defSweepSpecTable.all fun e => e.noExit) == true
#guard full_def_sweep_fns.map Fn.name ==
  [ "full_bve_mark_and", "full_find_definition", "full_bve_gates",
    "full_cong_extract", "full_congruence_dense", "full_sweep_cone",
    "full_sweep_refine_kitten", "full_sweep_var", "full_sweep_dense" ]
#guard (full_def_sweep_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_bve_mark_and", 5, 1), ("full_find_definition", 4, 0),
    ("full_bve_gates", 4, 0), ("full_cong_extract", 3, 1),
    ("full_congruence_dense", 2, 1), ("full_sweep_cone", 2, 1),
    ("full_sweep_refine_kitten", 3, 0), ("full_sweep_var", 3, 1),
    ("full_sweep_dense", 3, 1) ]
#guard nvDefSweepBytes.length == nvDefSweepCfg.avail

end LeanQbeTest.T.KissatDefSweepTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullDefSweep

theorem fds_fns_wf : ∀ f ∈ full_def_sweep_fns, f.Wf := full_def_sweep_fns_wf

theorem fds_acyclic : fullDefSweepModule.checkAcyclic = true := fullDefSweep_acyclic

theorem fds_noExit : ∀ e ∈ defSweepSpecTable, e.noExit = true :=
  defSweepSpecTable_noExit

theorem fds_sigs :
    (defSweepSpecTable.take 9).map (fun e => (e.name, e.as, e.rs)) =
      full_def_sweep_fns.map (fun f => (f.name, f.as, f.rs)) :=
  defSweepSpecTable_sigs

theorem fds_ext_sigs :
    (defSweepSpecTable.drop 9).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullDefSweepExterns :=
  defSweepSpecTable_ext_sigs

theorem fds_kinv_laws : KittenInvLaws defSweepKInv := defSweepKInv_laws

theorem fds_mark_and_wp (Γ : Env) :
    ∀ a m Q X, fullBveMarkAndDefSpec a m Q X →
      Func.wp Γ full_bve_mark_and_body a m Q X :=
  full_bve_mark_and_wp Γ

theorem fds_find_def_wp (Γ : Env) {KInv} (hL : KittenInvLaws KInv)
    (hI : EnvSpec Γ "full_kitten_init" (fullKittenInitSpec KInv))
    (hA : EnvSpec Γ "full_kitten_add_clause" (fullKittenAddClauseSpec KInv))
    (hS : EnvSpec Γ "full_kitten_solve" (fullKittenSolveSpec KInv))
    (hC : EnvSpec Γ "full_kitten_core" (fullKittenCoreSpec KInv))
    (hK : EnvSpec Γ "full_kitten_shrink" (fullKittenShrinkSpec KInv)) :
    ∀ a m Q X, fullFindDefinitionSpec a m Q X →
      Func.wp Γ full_find_definition_body a m Q X :=
  full_find_definition_wp Γ hL hI hA hS hC hK

theorem fds_bve_gates_wp (Γ : Env)
    (hM : ∀ a m Q X, fullBveMarkAndDefSpec a m Q X →
      Γ "full_bve_mark_and" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hF : ∀ a m Q X, fullFindDefinitionSpec a m Q X →
      Γ "full_find_definition" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBveGatesDefSpec a m Q X → Func.wp Γ full_bve_gates_body a m Q X :=
  full_bve_gates_wp Γ hM hF

theorem fds_cong_ext_wp (Γ : Env)
    (hN : EnvSpec Γ "full_arena_next" Full.FullCongSpecs.fullArenaNextSpec)
    (hB : EnvSpec Γ "full_has_bin" Full.FullCongSpecs.fullHasBinSpec)
    (hX : EnvSpec Γ "full_cong_try_xor_ite" Full.FullCongSpecs.fullCongTryXorIteSpec) :
    ∀ a m Q X, fullCongExtractTickSpec a m Q X →
      Func.wp Γ full_cong_extract_body a m Q X :=
  full_cong_extract_wp Γ hN hB hX

theorem fds_cong_dense_wp (Γ : Env)
    (hE : ∀ a m Q X, fullCongExtractTickSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hH : ∀ a m Q X, Full.FullCongSpecs.fullCongHashStepSpec a m Q X →
      Γ "full_cong_hash_step" [i64, i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullCongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X :=
  full_congruence_dense_wp Γ hE hH

theorem fds_cone_wp (Γ : Env) {KInv} (hL : KittenInvLaws KInv)
    (hI : EnvSpec Γ "full_kitten_init" (fullKittenInitSpec KInv))
    (hA : EnvSpec Γ "full_kitten_add_clause" (fullKittenAddClauseSpec KInv)) :
    ∀ a m Q X, fullSweepConeKittenSpec KInv a m Q X →
      Func.wp Γ full_sweep_cone_body a m Q X :=
  full_sweep_cone_wp Γ hL hI hA

theorem fds_refine_wp (Γ : Env) :
    ∀ a m Q X, fullSweepRefineKittenSpec a m Q X →
      Func.wp Γ full_sweep_refine_kitten_body a m Q X :=
  full_sweep_refine_kitten_wp Γ

theorem fds_sweep_var_wp (Γ : Env) {KInv} (hL : KittenInvLaws KInv)
    (hC : EnvSpec Γ "full_sweep_cone" (fullSweepConeKittenSpec KInv))
    (hS : EnvSpec Γ "full_kitten_solve" (fullKittenSolveSpec KInv))
    (hR : EnvSpec Γ "full_sweep_refine_kitten" fullSweepRefineKittenSpec)
    (hF : EnvSpec Γ "full_kitten_flip" (fullKittenFlipSpec KInv))
    (hU : EnvSpec Γ "full_add_unit" Full.FullSweepVarSpecs.fullAddUnitSpec)
    (hB : EnvSpec Γ "full_add_bin" Full.FullSweepVarSpecs.fullAddBinSpec) :
    ∀ a m Q X, fullSweepVarKittenSpec a m Q X → Func.wp Γ full_sweep_var_body a m Q X :=
  full_sweep_var_wp Γ hL hC hS hR hF hU hB

theorem fds_sweep_dense_wp (Γ : Env)
    (hV : EnvSpec Γ "full_sweep_var" fullSweepVarKittenSpec) :
    ∀ a m Q X, fullSweepDenseSpec a m Q X → Func.wp Γ full_sweep_dense_body a m Q X :=
  full_sweep_dense_wp Γ hV

theorem fds_env_noExit :
    ∀ f as bs xs m Q X X',
      defSweepEnv f as bs xs m Q X → defSweepEnv f as bs xs m Q X' :=
  defSweepEnv_noExit

theorem fds_modOk_parts
    (hVar : ∀ a m Q X, fullSweepVarKittenSpec a m Q X →
      Func.wp defSweepEnv full_sweep_var_body a m Q X)
    (hDense : ∀ a m Q X, fullSweepDenseSpec a m Q X →
      Func.wp defSweepEnv full_sweep_dense_body a m Q X) :
    ModuleOk defSweepEnv fullDefSweepModule :=
  mkDefSweepEnv_moduleOk_of_parts hVar hDense

theorem fds_moduleOk : ModuleOk defSweepEnv fullDefSweepModule := defSweepEnv_moduleOk

theorem fds_nv_mem_ok : Full.FullMem nvDefSweepCfg nvDefSweepState nvDefSweepMem :=
  nvDefSweepMem_ok

theorem fds_nv_gates :
    Func.wp defSweepEnv full_bve_gates_body (nvDefSweepCfg.hdr, 0#32, 1#32, 1#32, ()) nvDefSweepMem
      (fun () m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        FullDefGateUnsat nvDefSweepState 0
          ((s'.scratch.scratch_buf[128]?.getD 0#32).setWidth 64 |||
            ((s'.scratch.scratch_buf[129]?.getD 0#32).setWidth 64 <<< 32))
          ((s'.scratch.scratch_buf[130]?.getD 0#32).setWidth 64 |||
            ((s'.scratch.scratch_buf[131]?.getD 0#32).setWidth 64 <<< 32)) 1 1 ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_bve_gates

theorem fds_nv_find_def :
    Func.wp defSweepEnv full_find_definition_body
      (nvDefSweepCfg.hdr, 0#32, 1#32, 1#32, ()) nvDefSweepMem
      (fun () m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_find_definition

theorem fds_nv_cong :
    Func.wp defSweepEnv full_congruence_dense_body
      (nvDefSweepCfg.hdr, 100#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_congruence_dense

theorem fds_nv_cone :
    Func.wp defSweepEnv full_sweep_cone_body
      (nvDefSweepCfg.hdr, 0#32, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s' cls',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        fullSweepKittenConeOk [[0], [1]] s' cls' (r &&& 0xFFFF#64).toNat (r >>> 16).toNat ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_cone

theorem fds_nv_dense_parts
    (hDense : ∀ a m Q X, fullSweepDenseSpec a m Q X →
      Func.wp defSweepEnv full_sweep_dense_body a m Q X) :
    Func.wp defSweepEnv full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_dense_of_wp hDense

theorem fds_nv_var :
    Func.wp defSweepEnv full_sweep_var_body
      (nvDefSweepCfg.hdr, 0#32, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW nvDefSweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_var

theorem fds_nv_dense :
    Func.wp defSweepEnv full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_dense

theorem fds_nv_def_sweep :
    Func.wp defSweepEnv full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_def_sweep

#print axioms fds_fns_wf
#print axioms fds_acyclic
#print axioms fds_noExit
#print axioms fds_sigs
#print axioms fds_ext_sigs
#print axioms fds_kinv_laws
#print axioms fds_mark_and_wp
#print axioms fds_find_def_wp
#print axioms fds_bve_gates_wp
#print axioms fds_cong_ext_wp
#print axioms fds_cong_dense_wp
#print axioms fds_cone_wp
#print axioms fds_refine_wp
#print axioms fds_sweep_var_wp
#print axioms fds_sweep_dense_wp
#print axioms fds_env_noExit
#print axioms fds_modOk_parts
#print axioms fds_moduleOk
#print axioms fds_nv_mem_ok
#print axioms fds_nv_gates
#print axioms fds_nv_find_def
#print axioms fds_nv_cong
#print axioms fds_nv_cone
#print axioms fds_nv_dense_parts
#print axioms fds_nv_var
#print axioms fds_nv_dense
#print axioms fds_nv_def_sweep

end AxiomAudit

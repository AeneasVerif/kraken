/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BRows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofBackFwd
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofBve1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofBve2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofCong1a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofCong1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofCong2b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofCong3a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofCong3b
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM3Backbone
public import LeanQbe.T.Examples.Kissat.FullM3CongBva
public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
public import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
public import LeanQbe.T.Examples.Kissat.FullCongLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 12B Proof Rows & Parametric `Impl` Barrel (`FullFidelityStep12BRowsProof`)

Exports the `12` replacement specification rows (`fidStep12BReplRows`), `3` inserted helper rows
(`fidStep12BBeforeRows` / `fidStep12BBeforeRowGroups`), `1` rewired row (`fidStep12BRewireRows`
for `full_cong_work_step`), name/signature alignment theorems, `15/15` kernel-checked
`checkCallsOk` theorems, and `15/15` parametric `SpecEntry.Impl` lemmas (`0` `import all`,
`0` `@[expose]` on theorems/lemmas, `0` new `FullWitnessInv` conjuncts, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- The `12` sig-preserving replacement specification rows aligned 1-to-1 with `fidStep12BRepls`. -/
def fidStep12BReplRows : List SpecEntry :=
  [ ⟨"full_cong_extract", [i64, i64, i64], [i64], step12BCongExtractSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], step12BCongAndMatchSpec, true⟩
  , ⟨"full_cong_enq_var", [i64, i64, i32], [], step12BCongEnqVarSpec, true⟩
  , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
      step12BCongEvalGateSpec, true⟩
  , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], step12BCongWorklistSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_backbone_sched_m6", [i64], [i64], fullBackboneSchedM6Spec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], fullBackboneSpec, true⟩
  , ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩ ]

/-- The `3` inserted helper specification rows aligned 1-to-1 with
`fidStep12BBefores.flatMap Prod.snd`. -/
def fidStep12BBeforeRows : List SpecEntry :=
  [ ⟨"full_cong_extract_and_clause_fid", [i64, i32, i64, i64, i64], [i64],
      step12BCongExtractAndClauseSpec, true⟩
  , ⟨"full_cong_extract_from_fid", [i64, i64, i64, i64], [i64],
      step12BCongExtractFromSpec, true⟩
  , ⟨"full_bve_weaken_unit_fid", [i64, i32, i32, i32], [.bool],
      fullBveWeakenTmkSpec, true⟩ ]

/-- Grouped before-host specification rows aligned with `fidStep12BBefores`. -/
def fidStep12BBeforeRowGroups : List (Sym × List SpecEntry) :=
  [ ("full_cong_extract",
      [fidStep12BBeforeRows[0]'(by decide), fidStep12BBeforeRows[1]'(by decide)])
  , ("full_bve_var_m7",
      [fidStep12BBeforeRows[2]'(by decide)]) ]

/-- Rewired row allowing unchanged `full_cong_work_step` to consume `step12BCongEvalGateSpec`. -/
def fidStep12BRewireRows : List SpecEntry :=
  [⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m6CongWorkStepSpec, true⟩]

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep12BReplRows_names :
    fidStep12BReplRows.map SpecEntry.name = fidStep12BReplNames :=
  rfl

theorem fidStep12BReplRows_sigs :
    fidStep12BReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep12BRepls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep12BReplRows_noExit :
    fidStep12BReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep12BBeforeRows_names :
    fidStep12BBeforeRows.map SpecEntry.name = fidStep12BBeforeNames :=
  rfl

theorem fidStep12BBeforeRows_sigs :
    fidStep12BBeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep12BBefores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep12BBeforeRows_noExit :
    fidStep12BBeforeRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`15/15`) -/

theorem full_cong_extract_and_clause_fid_s12b_callsOk :
    fidStep12BCongExtractAndClauseFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_cong_extract_from_fid_s12b_callsOk :
    fidStep12BCongExtractFromFn.checkCallsOk
      [ ("full_arena_next", [i64, i32], [i32])
      , ("full_cong_count_bins", [i64], [])
      , ("full_cong_extract_and_clause_fid", [i64, i32, i64, i64, i64], [i64])
      , ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64])
      , ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_cong_extract_s12b_callsOk :
    fidStep12BCongExtractFn.checkCallsOk
      [ ("full_cong_extract_from_fid", [i64, i64, i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_cong_and_match_s12b_callsOk :
    fidStep12BCongAndMatchFn.checkCallsOk
      [ ("full_cong_find", [i64, i32], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_cong_enq_var_s12b_callsOk :
    fidStep12BCongEnqVarFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_cong_eval_gate_s12b_callsOk :
    fidStep12BCongEvalGateFn.checkCallsOk
      [ ("full_cong_find", [i64, i32], [i32])
      , ("full_sort_u32", [i64, i32], [])
      , ("full_cong_unit_fold", [i64, i32, i32], [i64])
      , ("full_cong_equiv_fold", [i64, i32, i32, i32], [i64])
      , ("full_cong_and_match", [i64, i32, i32], [.bool])
      , ("full_cong_xor_match", [i64, i32, i32], [i32])
      , ("full_cong_enq_var", [i64, i64, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_cong_worklist_s12b_callsOk :
    fidStep12BCongWorklistFn.checkCallsOk
      [ ("full_cong_find", [i64, i32], [i32])
      , ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_congruence_dense_s12b_callsOk :
    fidStep12BCongruenceDenseFn.checkCallsOk
      [ ("full_cong_extract_binaries", [i64, i64], [i64])
      , ("full_cong_find_units_equivs", [i64], [i64])
      , ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32])
      , ("full_cong_extract_from_fid", [i64, i64, i64, i64], [i64])
      , ("full_cong_worklist", [i64, i64, i64, i64], [i64])
      , ("full_cong_fwd_subsume", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_backbone_sched_m6_s12b_callsOk :
    fidStep12BBackboneSchedM6Fn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_backbone_m6_s12b_callsOk :
    fidStep12BBackboneM6Fn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_add_unit", [i64, i32], [.bool])
      , ("full_prioritize_binaries_m6", [i64], [.bool])
      , ("full_backbone_sched_m6", [i64], [i64])
      , ("full_backbone_round_m6", [i64, i64, .bool], [i64])
      , ("full_backbone_keep_m6", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_dense_prop_unit_m7_s12b_callsOk :
    fidStep12BDensePropUnitM7Fn.checkCallsOk
      [ ("full_add_unit", [i64, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_forward_sub_m7_s12b_callsOk :
    fidStep12BForwardSubM7Fn.checkCallsOk
      [ ("full_fwd_dedup_bins", [i64], [.bool])
      , ("full_dense_flush_units_m7", [i64], [.bool])
      , ("full_fwd_collect_sort_m7", [i64], [i64])
      , ("full_fwd_flush_large_m7", [i64], [])
      , ("full_fwd_check_cl_m7", [i64, i32], [.bool])
      , ("full_fwd_connect_subsumer_m7", [i64, i32], [])
      , ("full_arena_next", [i64, i32], [i32])
      , ("full_fwd_reconnect_irred_m7", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_bve_commit_res_s12b_callsOk :
    fidStep12BBveCommitResFn.checkCallsOk
      [ ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_add_bin", [i64, i32, i32], [i64])
      , ("full_add_unit", [i64, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_bve_weaken_unit_fid_s12b_callsOk :
    fidStep12BBveWeakenUnitFn.checkCallsOk
      [ ("full_delete_binary", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_bve_var_m7_s12b_callsOk :
    fidStep12BBveVarM7Fn.checkCallsOk
      [ ("full_bve_collect_m7", [i64, i32, i64, i32], [i32])
      , ("full_bve_ext_need", [i64, i32, i32], [i64])
      , ("full_bve_weaken", [i64, i32, i32, i32], [.bool])
      , ("full_bve_weaken_unit_fid", [i64, i32, i32, i32], [.bool])
      , ("full_set_inactive", [i64, i32, i32], [])
      , ("full_bve_gates_fid", [i64, i32, i32, i32], [])
      , ("full_bve_gates_m7", [i64, i32, i32, i32], [])
      , ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_wstack_defrag", [i64], [])
      , ("full_bve_commit_res", [i64, i64, i64], [i64])
      , ("full_dense_flush_units_m7", [i64], [.bool]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`15/15` + Rewired `full_cong_work_step`) -/

theorem full_cong_extract_and_clause_fid_s12b_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep12BCongExtractAndClauseFn
      (fidStep12BBeforeRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_cong_extract_and_clause_fid_s12b_wp Γ)

theorem full_cong_extract_from_fid_s12b_impl (Γ : Env)
    (hNext : ∀ a m Q X, FullCongSpecs.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hCountBins : ∀ a m Q X, m6CongCountBinsSpec a m Q X →
      Γ "full_cong_count_bins" [i64] [] a m Q X)
    (hExtAnd : ∀ a m Q X, step12BCongExtractAndClauseSpec a m Q X →
      Γ "full_cong_extract_and_clause_fid" [i64, i32, i64, i64, i64] [i64] a m Q X)
    (hTryXorIte : ∀ a m Q X, fidCongTryXorIteSpec a m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] a m Q X)
    (hExtractXorK : ∀ a m Q X, fidCongExtractXorKSpec a m Q X →
      Γ "full_cong_extract_xor_k" [i64, i32, i32, i64, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12BCongExtractFromFn
      (fidStep12BBeforeRows[1]'(by decide)) :=
  SpecEntry.Impl.of
    (full_cong_extract_from_fid_s12b_wp Γ hNext hCountBins hExtAnd hTryXorIte hExtractXorK)

theorem full_cong_extract_s12b_impl (Γ : Env)
    (hExtractFrom : ∀ a m Q X, step12BCongExtractFromSpec a m Q X →
      Γ "full_cong_extract_from_fid" [i64, i64, i64, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12BCongExtractFn
      (fidStep12BReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_cong_extract_s12b_wp Γ hExtractFrom)

theorem full_cong_and_match_s12b_impl (Γ : Env)
    (hFind : ∀ a m Q X, FullCongSpecs.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    SpecEntry.Impl Γ fidStep12BCongAndMatchFn
      (fidStep12BReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_cong_and_match_s12b_wp Γ hFind)

theorem full_cong_enq_var_s12b_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep12BCongEnqVarFn
      (fidStep12BReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_cong_enq_var_s12b_wp Γ)

theorem full_cong_eval_gate_s12b_impl (Γ : Env)
    (hFind : ∀ a m Q X, FullCongSpecs.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X →
      Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hUnitFold : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquivFold : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hAndMatch : ∀ a m Q X, step12BCongAndMatchSpec a m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] a m Q X)
    (hXorMatch : ∀ a m Q X, m6CongXorMatchSpec a m Q X →
      Γ "full_cong_xor_match" [i64, i32, i32] [i32] a m Q X)
    (hEnqVar : ∀ a m Q X, step12BCongEnqVarSpec a m Q X →
      Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12BCongEvalGateFn
      (fidStep12BReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of
    (full_cong_eval_gate_s12b_wp Γ hFind hSort hUnitFold hEquivFold hAndMatch hXorMatch hEnqVar)

theorem full_cong_worklist_s12b_impl (Γ : Env)
    (hFind : ∀ a m Q X, FullCongSpecs.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hEvalGate : ∀ a m Q X, step12BCongEvalGateSpec a m Q X →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12BCongWorklistFn
      (fidStep12BReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_cong_worklist_s12b_wp Γ hFind hEvalGate)

theorem full_congruence_dense_s12b_impl (Γ : Env)
    (hExtBins : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtIteAll : ∀ a m Q X, fidCongExtractIteAllSpec a m Q X →
      Γ "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X)
    (hExtFrom : ∀ a m Q X, step12BCongExtractFromSpec a m Q X →
      Γ "full_cong_extract_from_fid" [i64, i64, i64, i64] [i64] a m Q X)
    (hWorklist : ∀ a m Q X, step12BCongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12BCongruenceDenseFn
      (fidStep12BReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of
    (full_congruence_dense_s12b_wp Γ hExtBins hFindUE hExtIteAll hExtFrom hWorklist hFwdSub)

theorem full_backbone_sched_m6_s12b_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep12BBackboneSchedM6Fn
      (fidStep12BReplRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_backbone_sched_m6_s12b_wp Γ)

theorem full_backbone_m6_s12b_del_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12BBackboneM6Fn
      (fidStep12BReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of
    (full_backbone_m6_s12b_del_wp Γ hBacktrack hProp hAddUnit hPrio hSched hRound hKeep)

theorem full_backbone_m6_s12b_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12BBackboneM6Fn
      (fidStep12BReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of
    (full_backbone_m6_s12b_wp Γ hBacktrack hProp hAddUnit hPrio hSched hRound hKeep)

theorem full_dense_prop_unit_m7_s12b_impl (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep12BDensePropUnitM7Fn
      (fidStep12BReplRows[8]'(by decide)) :=
  SpecEntry.Impl.of (full_dense_prop_unit_m7_s12b_wp Γ hAddUnit)

theorem full_forward_sub_m7_s12b_impl (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12BForwardSubM7Fn
      (fidStep12BReplRows[9]'(by decide)) :=
  SpecEntry.Impl.of (full_forward_sub_m7_s12b_wp Γ hDedup hFlushUnits hCollectSort
    hFlushLarge hCheckCl hConnectSub hArenaNext hReconnect)

theorem full_bve_commit_res_s12b_impl (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep12BBveCommitResFn
      (fidStep12BReplRows[10]'(by decide)) :=
  SpecEntry.Impl.of (full_bve_commit_res_s12b_wp Γ hAlloc hWPush hAddBin hAddUnit)

theorem full_bve_weaken_unit_fid_s12b_impl (Γ : Env)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12BBveWeakenUnitFn
      (fidStep12BBeforeRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_bve_weaken_unit_fid_s12b_wp Γ hDelBin)

theorem full_bve_var_m7_s12b_impl (Γ : Env)
    (hCollect : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hWeakenUnit : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep12BBveVarM7Fn
      (fidStep12BReplRows[11]'(by decide)) :=
  SpecEntry.Impl.of (full_bve_var_m7_s12b_wp Γ hCollect hExtNeed hWeaken hWeakenUnit
    hSetInact hGatesFid hGatesM7 hResPair hAssign hDefrag hCommit hFlushUnits)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B

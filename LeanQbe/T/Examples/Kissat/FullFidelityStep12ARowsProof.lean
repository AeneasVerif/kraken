/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12ARows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12AProofTransLucky
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12AProofProbe
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12AProofFactor
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12AProofSweep
public import LeanQbe.T.Examples.Kissat.FullSpec

/-!
# Kissat Fidelity Step 12A Proof Rows & Parametric `Impl` Barrel (`FullFidelityStep12ARowsProof`)

Exports the `6` replacement specification rows (`fidStep12AReplRows`), the empty inserted-row list
(`fidStep12ABeforeRows := []`), name/signature/`noExit` alignment theorems, `6/6` kernel-checked
`checkCallsOk` certificates, and `6/6` parametric `SpecEntry.Impl` lemmas (`0` `import all`, `0`
`@[expose]` on theorems/lemmas, `0` new `FullWitnessInv` conjuncts, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullDefSweep
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep9
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- The `6` sig-preserving replacement specification rows aligned 1-to-1 with
`fidStep12ARepls`. -/
def fidStep12AReplRows : List SpecEntry :=
  [ ⟨"full_trans_sort_m6", [i64, i64], [], fullTransSortM6Spec, true⟩
  , ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], m6SweepSimSpec, true⟩
  , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], m6SweepVarsSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩ ]

/-- Empty list of inserted helper specification rows (`0` inserted functions in Step 12A). -/
def fidStep12ABeforeRows : List SpecEntry := []

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep12AReplRows_names :
    fidStep12AReplRows.map SpecEntry.name = fidStep12AReplNames :=
  rfl

theorem fidStep12AReplRows_sigs :
    fidStep12AReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep12ARepls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep12AReplRows_noExit :
    fidStep12AReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep12ABeforeRows_names :
    fidStep12ABeforeRows.map SpecEntry.name = fidStep12ABeforeNames :=
  rfl

theorem fidStep12ABeforeRows_sigs :
    fidStep12ABeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep12ABefores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep12ABeforeRows_noExit :
    fidStep12ABeforeRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`6/6`) -/

theorem full_trans_sort_m6_s12a_callsOk :
    fidStep12ATransSortFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_m6_sweep_sim_s12a_callsOk :
    fidStep12ASweepSimFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_m6_sweep_solve", [i64, i32, i64], [i64])
      , ("full_m6_sweep_refine_sig", [i64, i32, i32], [])
      , ("full_m6_sweep_flip_round", [i64, i32], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_m6_sweep_vars_s12a_callsOk :
    fidStep12ASweepVarsFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_m6_dense_prop", [i64], [.bool])
      , ("full_m6_collect_cands", [i64], [i32])
      , ("full_m6_sweep_var", [i64, i32, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_factor_s12a_callsOk :
    fidStep12AFactorFn.checkCallsOk
      [ ("full_bva_steps_cap_fid", [i64], [i32])
      , ("full_bva_connect_clauses_fid", [i64], [])
      , ("full_fheap_up_fid", [i64, i64, i64, i32], [])
      , ("full_fheap_down_fid", [i64, i64, i64, i32, i32], [])
      , ("full_bva_try_lit", [i64, i32, i64], [.bool])
      , ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_probe_m6_s12a_callsOk :
    fidStep12AProbeFn.checkCallsOk
      [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
      , ("full_log10_q16_m7", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64])
      , ("full_vivify_m6_hdr", [i64], [i64])
      , ("full_enter_dense", [i64], [.bool])
      , ("m6_hdr_delaying", [i64, i64], [.bool])
      , ("full_congruence_dense", [i64, i64], [i64])
      , ("full_rebuild_watches_nosort_fid", [i64], [i64])
      , ("m6_hdr_get_watermark", [i64, i64], [i64])
      , ("m6_hdr_set_watermark", [i64, i64, i64], [])
      , ("m6_hdr_reduce_delay", [i64, i64], [])
      , ("m6_hdr_bump_delay", [i64, i64], [])
      , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
      , ("full_substitute", [i64], [i64])
      , ("full_backbone_m6", [i64, i64], [i64])
      , ("full_transitive_m6", [i64, i64], [i64])
      , ("full_factor", [i64, i64], [i64])
      , ("full_sort_bin_watches_fid", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_preprocess_m6_s12a_callsOk :
    fidStep12APreprocessFn.checkCallsOk
      [ ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_lucky_late_m7", [i64], [i64])
      , ("full_compact_needed", [i64], [.bool])
      , ("full_compact", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64])
      , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`6/6`) -/

theorem full_trans_sort_m6_s12a_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep12ATransSortFn (fidStep12AReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_trans_sort_m6_step12a_wp Γ)

theorem full_m6_sweep_sim_s12a_impl (Γ : Env)
    (hMaxV : ∀ a m Q X, m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hSolve : ∀ a m Q X, m6SweepSolveSpec a m Q X →
      Γ "full_m6_sweep_solve" [i64, i32, i64] [i64] a m Q X)
    (hRef : ∀ a m Q X, m6SweepRefineSigSpec a m Q X →
      Γ "full_m6_sweep_refine_sig" [i64, i32, i32] [] a m Q X)
    (hFlipR : ∀ a m Q X, m6SweepFlipRoundSpec a m Q X →
      Γ "full_m6_sweep_flip_round" [i64, i32] [i32] a m Q X) :
    SpecEntry.Impl Γ fidStep12ASweepSimFn (fidStep12AReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_sweep_sim_step12a_wp Γ hMaxV hSolve hRef hFlipR)

theorem full_m6_sweep_vars_s12a_impl (Γ : Env)
    (hMaxV : ∀ a m Q X, m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hDP : ∀ a m Q X, m6DensePropSpec a m Q X →
      Γ "full_m6_dense_prop" [i64] [.bool] a m Q X)
    (hCol : ∀ a m Q X, m6CollectCandsSpec a m Q X →
      Γ "full_m6_collect_cands" [i64] [i32] a m Q X)
    (hSV : ∀ a m Q X, m6SweepVarSpec a m Q X →
      Γ "full_m6_sweep_var" [i64, i32, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12ASweepVarsFn (fidStep12AReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_sweep_vars_step12a_wp Γ hMaxV hDP hCol hSV)

theorem full_factor_s12a_impl (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hConnect : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hTryLit : ∀ a m Q X, step7BvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X)
    (hUpd : ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
      Γ "full_bva_upd_lit_fid" [i64, i64, i64, i64, i64, i64] [i32] a m Q X) :
    SpecEntry.Impl Γ fidStep12AFactorFn (fidStep12AReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_factor_step12a_wp Γ hSteps hConnect hUp hDown hTryLit hUpd)

theorem full_probe_m6_s12a_impl (Γ : Env)
    (hProbeDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScaleM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebNosort : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hSortBin : ∀ a m Q X, step7SortBinWatchesSpec a m Q X →
      Γ "full_sort_bin_watches_fid" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12AProbeFn (fidStep12AReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_probe_m6_step12a_wp Γ hProbeDt hLog10 hScaleM5 hViv hEnter hDelay
    hCong hRebNosort hGetWm hSetWm hRedD hBumpD hSweepD hSubst hBone hTrans hFactor hSortBin)

theorem full_preprocess_m6_s12a_impl (Γ : Env)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLuckyLate : ∀ a m Q X, m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12APreprocessFn (fidStep12AReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of
    (full_preprocess_m6_step12a_wp Γ hProp hSweep hLuckyLate hCompNeed hCompact hScale hProbe)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12A

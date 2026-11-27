/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1CoreProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1CoreProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1CoreProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof0b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2d
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof3a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof3b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSubProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSubProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSubProof2c
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullSpec

/-!
# Kissat Fidelity Step 13 Shard S1 Proof Rows & Parametric `Impl` Barrel

Exports the `18` replacement specification rows (`fidStep13S1ReplRows`), `7` added helper rows
(`fidStep13S1AddRows`), name/signature/`noExit` alignment theorems, `25/25` kernel-checked
`checkCallsOk` certificates, and `25/25` parametric `SpecEntry.Impl` lemmas (`0` `import all`,
`0` `@[expose]` on theorems/lemmas, `<= 100` cols, `< 1,400` LOC, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- The `18` sig-preserving replacement specification rows aligned 1-to-1 with
`fidStep13S1Repls`. -/
def fidStep13S1ReplRows : List SpecEntry :=
  [ ⟨"full_k6_init", [i64, i32], [], step13K6InitSpec, true⟩
  , ⟨"full_k6_add_clause", [i64, i64, i32], [.bool], step13K6AddClauseSpec, true⟩
  , ⟨"full_k6_core_m7", [i64], [], fullK6CoreM7Spec, true⟩
  , ⟨"full_k6_core_fid", [i64], [], fidK6CoreSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], step13EnterDenseM6Spec, true⟩
  , ⟨"full_sort_bin_watches_fid", [i64], [], step13SortBinWatchesSpec, true⟩
  , ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], step13ElsArSpec, true⟩
  , ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], step13ElsLitSpec, true⟩
  , ⟨"full_m6_dense_els", [i64, i32], [.bool], step13DenseElsSpec, true⟩
  , ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], step13SweepVarSpec, true⟩
  , ⟨"full_m6_collect_cands", [i64], [i32], step13CollectCandsSpec, true⟩
  , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], m6SweepVarsSpec, true⟩
  , ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], step13FwdScanLitSpec, true⟩
  , ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], step13FwdConnectSubsumerSpec, true⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool],
      fidBveCertifyUnitSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], step13BveVarKeySpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], step13EliminateM6Spec, true⟩ ]

/-- The `7` added helper specification rows aligned 1-to-1 with `fidStep13S1Adds`. -/
def fidStep13S1AddRows : List SpecEntry :=
  [ ⟨"full_dense_occ_cnt_fid", [i64, i32, i64], [i64], step13DenseOccCntSpec, true⟩
  , ⟨"full_enter_dense_ex_fid", [i64, .bool], [.bool], step13EnterDenseExM6Spec, true⟩
  , ⟨"full_dense_bin_roundtrip_fid", [i64], [], step13DenseBinRoundtripSpec, true⟩
  , ⟨"full_dense_bin_sort_roundtrip_fid", [i64], [], step13DenseBinSortRoundtripSpec, true⟩
  , ⟨"full_watch_large_clauses_fid", [i64], [], step13WatchLargeClausesSpec, true⟩
  , ⟨"full_has_factor_cands_fid", [i64], [.bool], step13HasFactorCandsSpec, true⟩
  , ⟨"full_has_elim_cands_fid", [i64], [.bool], step13HasElimCandsSpec, true⟩ ]

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep13S1ReplRows_names :
    fidStep13S1ReplRows.map SpecEntry.name = fidStep13S1ReplNames :=
  rfl

theorem fidStep13S1ReplRows_sigs :
    fidStep13S1ReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S1Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S1ReplRows_noExit :
    fidStep13S1ReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S1AddRows_names :
    fidStep13S1AddRows.map SpecEntry.name = fidStep13S1AddNames :=
  rfl

theorem fidStep13S1AddRows_sigs :
    fidStep13S1AddRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S1Adds.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S1AddRows_noExit :
    fidStep13S1AddRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`25/25`) -/

theorem full_k6_init_s13_callsOk :
    fidStep13S1K6InitFn.checkCallsOk [("full_m6_max_v", [i64], [i64])] [] = true := by
  t_kernel_rfl

theorem full_k6_add_clause_s13_callsOk :
    fidStep13S1K6AddClauseFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_k6_assign", [i64, i32, i32], [])
      , ("full_k6_add_ticks", [i64, i64], [])
      , ("full_k6_watch", [i64, i32, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_k6_core_m7_s13_callsOk :
    fidStep13S1K6CoreM7Fn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_k6_core_fid_s13_callsOk :
    fidStep13S1K6CoreFidFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_enter_dense_s13_callsOk :
    fidStep13S1EnterDenseFn.checkCallsOk
      [("full_enter_dense_ex_fid", [i64, .bool], [.bool])] [] = true := by
  t_kernel_rfl

theorem full_sort_bin_watches_fid_s13_callsOk :
    fidStep13S1SortBinWatchesFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_m6_els_ar_s13_callsOk :
    fidStep13S1ElsArFn.checkCallsOk
      [ ("full_cong_find", [i64, i32], [i32])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_add_unit", [i64, i32], [.bool])
      , ("full_add_bin", [i64, i32, i32], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_m6_els_lit_s13_callsOk :
    fidStep13S1ElsLitFn.checkCallsOk
      [ ("full_add_unit", [i64, i32], [.bool])
      , ("full_add_bin", [i64, i32, i32], [i64])
      , ("full_m6_els_ar", [i64, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_m6_dense_els_s13_callsOk :
    fidStep13S1DenseElsFn.checkCallsOk
      [ ("full_cong_find", [i64, i32], [i32])
      , ("full_add_unit", [i64, i32], [.bool])
      , ("full_m6_els_lit", [i64, i32, i32], [.bool])
      , ("full_add_bin", [i64, i32, i32], [i64])
      , ("full_m6_dense_prop", [i64], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_m6_sweep_var_s13_callsOk :
    fidStep13S1SweepVarFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_cong_find", [i64, i32], [i32])
      , ("full_m6_sweep_cone", [i64, i32], [i64])
      , ("full_m6_sweep_sim", [i64, i32, i64], [i32])
      , ("full_m6_sweep_units", [i64, i32, i32, i64], [i64])
      , ("full_m6_sweep_classes", [i64, i32, i32, i64], [i64])
      , ("full_m6_dense_els", [i64, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_m6_collect_cands_s13_callsOk :
    fidStep13S1CollectCandsFn.checkCallsOk
      [ ("full_dense_occ_cnt_fid", [i64, i32, i64], [i64])
      , ("full_m6_cand_sift", [i64, i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_m6_sweep_vars_s13_callsOk :
    fidStep13S1SweepVarsFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_m6_dense_prop", [i64], [.bool])
      , ("full_dense_occ_cnt_fid", [i64, i32, i64], [i64])
      , ("full_m6_collect_cands", [i64], [i32])
      , ("full_m6_sweep_var", [i64, i32, i64], [i64])
      , ("full_cong_find", [i64, i32], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_fwd_scan_lit_m7_s13_callsOk :
    fidStep13S1FwdScanLitFn.checkCallsOk
      [("full_dense_occ_cnt_fid", [i64, i32, i64], [i64])] [] = true := by
  t_kernel_rfl

theorem full_fwd_connect_subsumer_m7_s13_callsOk :
    fidStep13S1FwdConnectSubsumerFn.checkCallsOk
      [ ("full_dense_occ_cnt_fid", [i64, i32, i64], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_forward_sub_m7_s13_callsOk :
    fidStep13S1ForwardSubFn.checkCallsOk
      [ ("full_fwd_dedup_bins", [i64], [.bool])
      , ("full_dense_flush_units_m7", [i64], [.bool])
      , ("full_fwd_collect_sort_m7", [i64], [i64])
      , ("full_fwd_flush_large_m7", [i64], [])
      , ("full_fwd_check_cl_m7", [i64, i32], [.bool])
      , ("full_fwd_connect_subsumer_m7", [i64, i32], [])
      , ("full_arena_next", [i64, i32], [i32])
      , ("full_fwd_reconnect_irred_m7", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_bve_certify_unit_fid_s13_callsOk :
    fidStep13S1BveCertifyUnitFn.checkCallsOk
      [ ("full_m6_max_v", [i64], [i64])
      , ("full_k6_init", [i64, i32], [])
      , ("full_k6_add_clause", [i64, i64, i32], [.bool])
      , ("full_k6_solve", [i64, i64], [i64])
      , ("full_assign_lvl", [i64, i32, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_bve_var_key_m7_s13_callsOk :
    fidStep13S1BveVarKeyFn.checkCallsOk
      [ ("full_dense_occ_cnt_fid", [i64, i32, i64], [i64])
      , ("f64u_to_u64", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_eliminate_m6_s13_callsOk :
    fidStep13S1EliminateFn.checkCallsOk
      [ ("full_elim_dticks", [i64, .bool], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_nlogpown", [i64, i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("full_scale_delta", [i64, i64], [i64])
      , ("full_has_elim_cands_fid", [i64], [.bool])
      , ("full_enter_dense_ex_fid", [i64, .bool], [.bool])
      , ("full_forward_sub_m7", [i64, i64], [i64])
      , ("full_elim_bve_m7", [i64, i64], [i64])
      , ("full_rebuild_watches", [i64], [i64])
      , ("full_update_classify_fid", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_dense_occ_cnt_fid_s13_callsOk :
    fidStep13S1DenseOccCntFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_enter_dense_ex_fid_s13_callsOk :
    fidStep13S1EnterDenseExFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_flush_trail", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_sweep_bins", [i64], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_arena_next", [i64, i32], [i32]) ] [] = true := by
  t_kernel_rfl

theorem full_dense_bin_roundtrip_fid_s13_callsOk :
    fidStep13S1DenseBinRoundtripFn.checkCallsOk
      [ ("full_fwd_flush_large_m7", [i64], [])
      , ("full_sweep_bins", [i64], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_dense_bin_sort_roundtrip_fid_s13_callsOk :
    fidStep13S1DenseBinSortRoundtripFn.checkCallsOk
      [ ("full_fwd_flush_large_m7", [i64], [])
      , ("full_sweep_bins", [i64], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_watch_large_clauses_fid_s13_callsOk :
    fidStep13S1WatchLargeClausesFn.checkCallsOk
      [ ("full_arena_next", [i64, i32], [i32])
      , ("full_lit_rank_m6", [i64, i64, i32], [i64])
      , ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_has_factor_cands_fid_s13_callsOk :
    fidStep13S1HasFactorCandsFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_has_elim_cands_fid_s13_callsOk :
    fidStep13S1HasElimCandsFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`18` Replacements) -/

theorem full_k6_init_s13_impl (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    SpecEntry.Impl Γ fidStep13S1K6InitFn (fidStep13S1ReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_k6_init_s13_wp Γ hMaxV)

theorem full_k6_add_clause_s13_impl (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec)
    (hWatch : M6EnvSpec Γ "full_k6_watch" k6WatchSpec) :
    SpecEntry.Impl Γ fidStep13S1K6AddClauseFn (fidStep13S1ReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_k6_add_clause_s13_wp Γ hMaxV hAssign hAddTicks hWatch)

theorem full_k6_core_m7_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S1K6CoreM7Fn (fidStep13S1ReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_k6_core_m7_s13_wp Γ)

theorem full_k6_core_fid_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S1K6CoreFidFn (fidStep13S1ReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_k6_core_fid_s13_wp Γ)

theorem full_enter_dense_s13_impl (Γ : Env)
    (hEx : ∀ a m Q X, step13EnterDenseExM6Spec a m Q X →
      Γ "full_enter_dense_ex_fid" [i64, .bool] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1EnterDenseFn (fidStep13S1ReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_enter_dense_s13_wp Γ hEx)

theorem full_sort_bin_watches_fid_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S1SortBinWatchesFn (fidStep13S1ReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of (full_sort_bin_watches_fid_s13_wp Γ)

theorem full_m6_els_ar_s13_impl (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec) :
    SpecEntry.Impl Γ fidStep13S1ElsArFn (fidStep13S1ReplRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_els_ar_s13_wp Γ hFind hWatch hAddUnit hAddBin)

theorem full_m6_els_lit_s13_impl (Γ : Env)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    (hElsAr : ∀ a m Q X, step13ElsArSpec a m Q X →
      Γ "full_m6_els_ar" [i64, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1ElsLitFn (fidStep13S1ReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_els_lit_s13_wp Γ hAddUnit hAddBin hElsAr)

theorem full_m6_dense_els_s13_impl (Γ : Env)
    (hFind : ∀ a m Q X, Full.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hElsLit : ∀ a m Q X, step13ElsLitSpec a m Q X →
      Γ "full_m6_els_lit" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    (hProp : ∀ a m Q X, step13DensePropSpec a m Q X →
      Γ "full_m6_dense_prop" [i64] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1DenseElsFn (fidStep13S1ReplRows[8]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_dense_els_s13_wp Γ hFind hAddUnit hElsLit hAddBin hProp)

theorem full_m6_sweep_var_s13_impl (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hCone : ∀ a m Q X, step13SweepConeSpec a m Q X →
      Γ "full_m6_sweep_cone" [i64, i32] [i64] a m Q X)
    (hSim : ∀ a m Q X, step13SweepSimSpec a m Q X →
      Γ "full_m6_sweep_sim" [i64, i32, i64] [i32] a m Q X)
    (hUnits : ∀ a m Q X, step13SweepUnitsSpec a m Q X →
      Γ "full_m6_sweep_units" [i64, i32, i32, i64] [i64] a m Q X)
    (hClasses : ∀ a m Q X, step13SweepClassesSpec a m Q X →
      Γ "full_m6_sweep_classes" [i64, i32, i32, i64] [i64] a m Q X)
    (hEls : ∀ a m Q X, step13DenseElsSpec a m Q X →
      Γ "full_m6_dense_els" [i64, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1SweepVarFn (fidStep13S1ReplRows[9]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_sweep_var_s13_wp Γ hMaxV hFind hCone hSim hUnits hClasses hEls)

theorem full_m6_collect_cands_s13_impl (Γ : Env)
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    SpecEntry.Impl Γ fidStep13S1CollectCandsFn (fidStep13S1ReplRows[10]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_collect_cands_s13_wp Γ hOcc hSift)

theorem full_m6_sweep_vars_s13_impl (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : ∀ a m Q X, step13DensePropSpec a m Q X →
      Γ "full_m6_dense_prop" [i64] [.bool] a m Q X)
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    (hCol : ∀ a m Q X, step13CollectCandsSpec a m Q X →
      Γ "full_m6_collect_cands" [i64] [i32] a m Q X)
    (hSV : ∀ a m Q X, step13SweepVarSpec a m Q X →
      Γ "full_m6_sweep_var" [i64, i32, i64] [i64] a m Q X)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1SweepVarsFn (fidStep13S1ReplRows[11]'(by decide)) :=
  SpecEntry.Impl.of (full_m6_sweep_vars_s13_wp Γ hMaxV hDP hOcc hCol hSV hFind)

theorem full_fwd_scan_lit_m7_s13_impl (Γ : Env)
    (hOcc : M6EnvSpec Γ "full_dense_occ_cnt_fid" step13DenseOccCntSpec) :
    SpecEntry.Impl Γ fidStep13S1FwdScanLitFn (fidStep13S1ReplRows[12]'(by decide)) :=
  SpecEntry.Impl.of (full_fwd_scan_lit_m7_s13_wp Γ hOcc)

theorem full_fwd_connect_subsumer_m7_s13_impl (Γ : Env)
    (hOcc : M6EnvSpec Γ "full_dense_occ_cnt_fid" step13DenseOccCntSpec)
    (hWatchPush : M6EnvSpec Γ "full_watch_push" fullWatchPushSpec) :
    SpecEntry.Impl Γ fidStep13S1FwdConnectSubsumerFn (fidStep13S1ReplRows[13]'(by decide)) :=
  SpecEntry.Impl.of (full_fwd_connect_subsumer_m7_s13_wp Γ hOcc hWatchPush)

theorem full_forward_sub_m7_s13_impl (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, step13FwdFlushLargeCoreSpec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, step13FwdConnectSubsumerSpec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1ForwardSubFn (fidStep13S1ReplRows[14]'(by decide)) :=
  SpecEntry.Impl.of (full_forward_sub_m7_s13_wp Γ hDedup hFlushUnits hCollectSort hFlushLarge
    hCheckCl hConnectSub hArenaNext hReconnect)

theorem full_bve_certify_unit_fid_s13_impl (Γ : Env)
    (hMaxV : ∀ a m Q X, FullM6Sweep.m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hInit : M6EnvSpec Γ "full_k6_init" step13K6InitSpec)
    (hAdd : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (hSolve : ∀ a m Q X, FullM6Sweep.k6SolveSpec a m Q X →
      Γ "full_k6_solve" [i64, i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1BveCertifyUnitFn (fidStep13S1ReplRows[15]'(by decide)) :=
  SpecEntry.Impl.of (full_bve_certify_unit_fid_s13_wp Γ hMaxV hInit hAdd hSolve hAssign)

theorem full_bve_var_key_m7_s13_impl (Γ : Env)
    (hOcc : M6EnvSpec Γ "full_dense_occ_cnt_fid" step13DenseOccCntSpec)
    (hFtoU : M6EnvSpec Γ "f64u_to_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ fidStep13S1BveVarKeyFn (fidStep13S1ReplRows[16]'(by decide)) :=
  SpecEntry.Impl.of (full_bve_var_key_m7_s13_wp Γ hOcc hFtoU)

theorem full_eliminate_m6_s13_impl (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hF64Mul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hF64Nlog : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X)
    (hF64ToU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hHasCands : ∀ a m Q X, step13HasElimCandsSpec a m Q X →
      Γ "full_has_elim_cands_fid" [i64] [.bool] a m Q X)
    (hEnter : ∀ a m Q X, step13EnterDenseExM6Spec a m Q X →
      Γ "full_enter_dense_ex_fid" [i64, .bool] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hClassify : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1EliminateFn (fidStep13S1ReplRows[17]'(by decide)) :=
  SpecEntry.Impl.of (full_eliminate_m6_s13_wp Γ hDticks hF64Mul hF64Nlog hF64ToU64 hScale
    hHasCands hEnter hFwd hBve hReb hClassify)

/-! ## 4. Parametric `SpecEntry.Impl` Lemmas (`7` Additions) -/

theorem full_dense_occ_cnt_fid_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S1DenseOccCntFn (fidStep13S1AddRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_dense_occ_cnt_fid_s13_wp Γ)

theorem full_enter_dense_ex_fid_s13_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFlush : ∀ a m Q X, FullM6CompactFlush.fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, step13PropagateM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1EnterDenseExFn (fidStep13S1AddRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_enter_dense_ex_fid_s13_wp Γ hBacktrack hFlush hSweep hProp hSweepBins
    hWatchPush hArenaNext)

theorem full_dense_bin_roundtrip_fid_s13_impl (Γ : Env)
    (hFlushLarge : ∀ a m Q X, step13FwdFlushLargeCoreSpec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, Full.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1DenseBinRoundtripFn (fidStep13S1AddRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_dense_bin_roundtrip_fid_s13_wp Γ hFlushLarge hSweepBins hPush)

theorem full_dense_bin_sort_roundtrip_fid_s13_impl (Γ : Env)
    (hFlushLarge : ∀ a m Q X, step13FwdFlushLargeCoreSpec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, Full.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1DenseBinSortRoundtripFn (fidStep13S1AddRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_dense_bin_sort_roundtrip_fid_s13_wp Γ hFlushLarge hSweepBins hPush)

theorem full_watch_large_clauses_fid_s13_impl (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRank : ∀ a m Q X, Full.fullLitRankSpec a m Q X →
      Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S1WatchLargeClausesFn (fidStep13S1AddRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_watch_large_clauses_fid_s13_wp Γ hNext hRank hPush)

theorem full_has_factor_cands_fid_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S1HasFactorCandsFn (fidStep13S1AddRows[5]'(by decide)) :=
  SpecEntry.Impl.of (full_has_factor_cands_fid_s13_wp Γ)

theorem full_has_elim_cands_fid_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S1HasElimCandsFn (fidStep13S1AddRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_has_elim_cands_fid_s13_wp Γ)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

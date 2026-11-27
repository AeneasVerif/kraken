/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4SortAnaProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4RestoreProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4LuckyProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4ReorderMemProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4ReorderProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof0b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof2a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof2c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof3b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof4

/-!
# Kissat Fidelity Step 13 Shard S4 Proof Rows & Parametric `Impl` Barrel
(`FullFidelityStep13S4RowsProof`)

Exports the `15` replacement specification rows (`fidStep13S4ReplRows`), the `3` inserted helper
specification rows (`fidStep13S4BeforeRows`), name/signature/`noExit` alignment theorems,
`18/18` kernel-checked `checkCallsOk` certificates, and `18/18` parametric `SpecEntry.Impl`
lemmas (`0` `import all`, `0` `@[expose]` on theorems/lemmas, `0` Step-7..12 imports,
`XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- The `15` sig-preserving Step-13 S4 replacement spec rows aligned 1-to-1 with
`fidStep13S4Repls`. -/
def fidStep13S4ReplRows : List SpecEntry :=
  [ ⟨"full_rescale_m6", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], s13SortAnaQsSpec, true⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], step13LuckyScanM6Spec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], fullReorderQueueSpec, true⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], s13AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_bump_analyzed_m6_hdr", [i64], [], s13BumpAnalyzedM6HdrSpecP M6ExtW2bPres, true⟩
  , ⟨"full_restore_bump_ana_m6_hdr", [i64], [],
      s13RestoreBumpAnaM6HdrSpecP M6ExtW2bPres, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m6aAnaFailedLitSpecP M6ExtW2bPres, true⟩
  , ⟨"full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool], m8MinLitDfsSpec, true⟩
  , ⟨"full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool],
      m8ShrinkBlkBoolSpec, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], step13MinShrinkSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], FullM6Hdr.m6HdrAnalyzeSpec, true⟩
  , ⟨"full_analyze_m6_hdr", [i64], [i64], FullM6Hdr.m6HdrAnalyzeSpec, true⟩ ]

/-- The `3` inserted Step-13 S4 helper spec rows aligned 1-to-1 with
`fidStep13S4Befores.flatMap Prod.snd`. -/
def fidStep13S4BeforeRows : List SpecEntry :=
  [ ⟨"full_analyze_reasons_fid", [i64], [], s13AnalyzeReasonsSpecP M6ExtW2bPres, true⟩
  , ⟨"full_bump_analyzed_mode_fid", [i64, .bool], [],
      s13BumpAnalyzedModeSpecP M6ExtW2bPres, true⟩
  , ⟨"full_restore_bump_ana_mode_fid", [i64, .bool], [],
      s13RestoreBumpAnaModeSpecP M6ExtW2bPres, true⟩ ]

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep13S4ReplRows_names :
    fidStep13S4ReplRows.map SpecEntry.name = fidStep13S4ReplNames :=
  rfl

theorem fidStep13S4ReplRows_sigs :
    fidStep13S4ReplRows.map (fun e => (e.name, e.as, e.rs)) =
      fidStep13S4Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S4ReplRows_noExit :
    fidStep13S4ReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S4BeforeRows_names :
    fidStep13S4BeforeRows.map SpecEntry.name = fidStep13S4BeforeNames :=
  rfl

theorem fidStep13S4BeforeRows_sigs :
    fidStep13S4BeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep13S4Befores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S4BeforeRows_noExit :
    fidStep13S4BeforeRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`18/18`) -/

theorem full_rescale_m6_s13_callsOk :
    fidStep13S4RescaleM6Fn.checkCallsOk
      [ ("f64u_div", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_bump_var_s13_callsOk :
    fidStep13S4BumpVarFn.checkCallsOk
      [ ("f64u_add", [i64, i64], [i64])
      , ("full_heap_up", [i64, i32], [])
      , ("full_rescale", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_bump_decay_s13_callsOk :
    fidStep13S4BumpDecayFn.checkCallsOk
      [ ("f64u_mul", [i64, i64], [i64])
      , ("full_rescale", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_sort_ana_qs_m6_s13_callsOk :
    fidStep13S4SortAnaQsM6Fn.checkCallsOk
      [ ("full_ana_sift_m6", [i64, i64, i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_lucky_scan_s13_callsOk :
    fidStep13S4LuckyScanFn.checkCallsOk
      [ ("full_lucky_ord_fid", [i64], [i64])
      , ("full_assign", [i64, i32, i32], [])
      , ("full_backtrack", [i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_analyze_m6_hdr", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_reorder_queue_m7_s13_callsOk :
    fidStep13S4ReorderQueueM7Fn.checkCallsOk
      [ ("f64u_add", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("full_arena_next", [i64, i32], [i32])
      , ("full_rescale", [i64], [])
      , ("full_heap_up", [i64, i32], [])
      , ("full_reorder_sift_fid", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_analyze_rsn_m6_hdr_s13_callsOk :
    fidStep13S4AnalyzeRsnM6HdrFn.checkCallsOk
      [ ("full_analyze_lit", [i64, i32, i32], [.bool])
      , ("m6_hdr_record_used", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_bump_analyzed_m6_hdr_s13_callsOk :
    fidStep13S4BumpAnalyzedM6HdrFn.checkCallsOk
      [ ("full_bump_analyzed_mode_fid", [i64, .bool], []) ] [] = true := by
  t_kernel_rfl

theorem full_restore_bump_ana_m6_hdr_s13_callsOk :
    fidStep13S4RestoreBumpAnaM6HdrFn.checkCallsOk
      [ ("full_restore_bump_ana_mode_fid", [i64, .bool], []) ] [] = true := by
  t_kernel_rfl

theorem full_ana_failed_lit_m6_hdr_s13_callsOk :
    fidStep13S4AnaFailedLitM6HdrFn.checkCallsOk
      [ ("full_clear_ana", [i64], [])
      , ("full_bump_analyzed_mode_fid", [i64, .bool], [])
      , ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_min_lit_dfs_m8_s13_callsOk :
    fidStep13S4MinLitDfsM8Fn.checkCallsOk
      [ ("full_min_mark", [i64, i32, i8], []) ] [] = true := by
  t_kernel_rfl

theorem full_shrink_blk_bool_m8_s13_callsOk :
    fidStep13S4ShrinkBlkBoolM8Fn.checkCallsOk
      [ ("full_shrink_lower_m8", [i64, i32, i32], [.bool])
      , ("full_min_mark", [i64, i32, i8], []) ] [] = true := by
  t_kernel_rfl

theorem full_min_shrink_m6_s13_callsOk :
    fidStep13S4MinShrinkM6Fn.checkCallsOk
      [ ("full_sort_tmp", [i64], [])
      , ("full_min_mark", [i64, i32, i8], [])
      , ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool])
      , ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_analyze_core_m6_s13_callsOk :
    fidStep13S4AnalyzeCoreM6Fn.checkCallsOk
      [ ("full_one_lit_confl", [i64], [i64])
      , ("full_ana_failed_lit_m6_hdr", [i64], [i64])
      , ("full_deduce_1uip_m6_hdr", [i64], [i64])
      , ("m6_hdr_update_tier_limits", [i64], [])
      , ("full_restore_bump_ana_mode_fid", [i64, .bool], [])
      , ("full_min_shrink_m6", [i64], [])
      , ("full_analyze_reasons_fid", [i64], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], [])
      , ("full_learn_clause_m6", [i64, i64], [i64])
      , ("full_bump_analyzed_mode_fid", [i64, .bool], [])
      , ("full_clear_ana", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_analyze_m6_hdr_s13_callsOk :
    fidStep13S4AnalyzeM6HdrFn.checkCallsOk
      [ ("m6_hdr_dr_update", [i64], [])
      , ("full_analyze_core_m6", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_analyze_reasons_fid_s13_callsOk :
    fidStep13S4AnalyzeReasonsFidFn.checkCallsOk
      [ ("m6_hdr_delaying", [i64, i64], [.bool])
      , ("m6_hdr_dr_allow", [i64], [.bool])
      , ("m6_hdr_bump_delay", [i64, i64], [])
      , ("m6_hdr_reduce_delay", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_bump_analyzed_mode_fid_s13_callsOk :
    fidStep13S4BumpAnalyzedModeFidFn.checkCallsOk
      [ ("m6_hdr_delaying", [i64, i64], [.bool])
      , ("m6_hdr_dr_allow", [i64], [.bool])
      , ("m6_hdr_bump_delay", [i64, i64], [])
      , ("m6_hdr_reduce_delay", [i64, i64], [])
      , ("full_sort_ana_qs_m6", [i64, i64], [])
      , ("full_bump_var", [i64, i32], [])
      , ("full_queue_mtf", [i64, i32], [])
      , ("full_bump_decay", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_restore_bump_ana_mode_fid_s13_callsOk :
    fidStep13S4RestoreBumpAnaModeFidFn.checkCallsOk
      [ ("full_bump_analyzed_mode_fid", [i64, .bool], [])
      , ("full_clear_ana", [i64], []) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`18/18`) -/

theorem full_rescale_m6_s13_impl (Γ : Env)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4RescaleM6Fn (fidStep13S4ReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_rescale_m6_step13_wp Γ hDiv hMul)

theorem full_bump_var_s13_impl (Γ : Env)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, Full.fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4BumpVarFn (fidStep13S4ReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_bump_var_step13_wp Γ hAdd hUp hRes)

theorem full_bump_decay_s13_impl (Γ : Env)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hRes : ∀ a m Q X, Full.fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4BumpDecayFn (fidStep13S4ReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_bump_decay_step13_wp Γ hMul hRes)

theorem full_sort_ana_qs_m6_s13_impl (Γ : Env)
    (hSift : ∀ a m Q X, s13AnaSiftSpec a m Q X →
      Γ "full_ana_sift_m6" [i64, i64, i64, i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4SortAnaQsM6Fn (fidStep13S4ReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_sort_ana_qs_m6_step13_wp Γ hSift)

theorem full_lucky_scan_s13_impl (Γ : Env)
    (hOrd : ∀ a m Q X, fullLuckyOrdFidSpec a m Q X →
      Γ "full_lucky_ord_fid" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13PropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4LuckyScanFn (fidStep13S4ReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_lucky_scan_step13_wp Γ hOrd hAssign hBt hProp hAna)

theorem full_reorder_queue_m7_s13_impl (Γ : Env)
    (hFadd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hFmul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRescale : ∀ a m Q X, Full.fullRescaleSpec a m Q X →
      Γ "full_rescale" [i64] [] a m Q X)
    (hHeapUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hSift : ∀ a m Q X, s13ReorderSiftSpec a m Q X →
      Γ "full_reorder_sift_fid" [i64, i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4ReorderQueueM7Fn (fidStep13S4ReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of
    (full_reorder_queue_m7_step13_wp Γ hFadd hFmul hArenaNext hRescale hHeapUp hSift)

theorem full_analyze_rsn_m6_hdr_s13_impl (Γ : Env)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hRec : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_record_used" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4AnalyzeRsnM6HdrFn (fidStep13S4ReplRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_step13_wp Γ hLit hRec)

theorem full_bump_analyzed_m6_hdr_s13_impl (Γ : Env)
    (hBumpMode : ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4BumpAnalyzedM6HdrFn (fidStep13S4ReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of (full_bump_analyzed_m6_hdr_step13_wp Γ hBumpMode)

theorem full_restore_bump_ana_m6_hdr_s13_impl (Γ : Env)
    (hRestoreMode : ∀ a m Q X, s13RestoreBumpAnaModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_restore_bump_ana_mode_fid" [i64, .bool] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4RestoreBumpAnaM6HdrFn (fidStep13S4ReplRows[8]'(by decide)) :=
  SpecEntry.Impl.of (full_restore_bump_ana_m6_hdr_step13_wp Γ hRestoreMode)

theorem full_ana_failed_lit_m6_hdr_s13_impl (Γ : Env)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpMode : ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X)
    (hBacktrackAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hTickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4AnaFailedLitM6HdrFn (fidStep13S4ReplRows[9]'(by decide)) :=
  SpecEntry.Impl.of
    (full_ana_failed_lit_m6_hdr_step13_wp Γ hClear hBumpMode hBacktrackAc hAssignLvl hTickRel hEma)

theorem full_min_lit_dfs_m8_s13_impl (Γ : Env)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4MinLitDfsM8Fn (fidStep13S4ReplRows[10]'(by decide)) :=
  SpecEntry.Impl.of (full_min_lit_dfs_m8_step13_wp Γ hMm)

theorem full_shrink_blk_bool_m8_s13_impl (Γ : Env)
    (hSl : ∀ a m Q X, m8ShrinkLowerSpec a m Q X →
      Γ "full_shrink_lower_m8" [i64, i32, i32] [.bool] a m Q X)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4ShrinkBlkBoolM8Fn (fidStep13S4ReplRows[11]'(by decide)) :=
  SpecEntry.Impl.of (full_shrink_blk_bool_m8_step13_wp Γ hSl hMm)

theorem full_min_shrink_m6_s13_impl (Γ : Env)
    (hSt : ∀ a m Q X, step7SortTmpSpec a m Q X → Γ "full_sort_tmp" [i64] [] a m Q X)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X)
    (hDfs : ∀ a m Q X, m8MinLitDfsSpec a m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] a m Q X)
    (hSb : ∀ a m Q X, m8ShrinkBlkBoolSpec a m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4MinShrinkM6Fn (fidStep13S4ReplRows[12]'(by decide)) :=
  SpecEntry.Impl.of (full_min_shrink_m6_step13_wp Γ hSt hMm hDfs hSb)

theorem full_analyze_core_m6_s13_impl (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, s13Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hUpdTier : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_update_tier_limits" [i64] [] a m Q X)
    (hRestore : ∀ a m Q X, s13RestoreBumpAnaModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_restore_bump_ana_mode_fid" [i64, .bool] [] a m Q X)
    (hMinShrink : ∀ a m Q X, step13MinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hReasons : ∀ a m Q X, s13AnalyzeReasonsSpecP M6ExtW2bPres a m Q X →
      Γ "full_analyze_reasons_fid" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnM6 : ∀ a m Q X, step13LearnClauseM6Spec a m Q X →
      Γ "full_learn_clause_m6" [i64, i64] [i64] a m Q X)
    (hBumpMode : ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4AnalyzeCoreM6Fn (fidStep13S4ReplRows[13]'(by decide)) :=
  SpecEntry.Impl.of (full_analyze_core_m6_step13_wp Γ hOneLit hFailed hDeduce hUpdTier
    hRestore hMinShrink hReasons hTick hEma hLearnM6 hBumpMode hClear)

theorem full_analyze_m6_hdr_s13_impl (Γ : Env)
    (hDrUpd : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_update" [i64] [] a m Q X)
    (hAnaCore : ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_core_m6" [i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4AnalyzeM6HdrFn (fidStep13S4ReplRows[14]'(by decide)) :=
  SpecEntry.Impl.of (full_analyze_m6_hdr_step13_wp Γ hDrUpd hAnaCore)

theorem full_analyze_reasons_fid_s13_impl (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4AnalyzeReasonsFidFn (fidStep13S4BeforeRows[0]'(by decide)) :=
  SpecEntry.Impl.of
    (full_analyze_reasons_fid_step13_wp Γ hDelaying hDrAllow hBumpDelay hReduceDelay)

theorem full_bump_analyzed_mode_fid_s13_impl (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hSortAna : ∀ a m Q X, s13SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4BumpAnalyzedModeFidFn (fidStep13S4BeforeRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_bump_analyzed_mode_fid_step13_wp Γ hDelaying hDrAllow hBumpDelay
    hReduceDelay hSortAna hBumpVar hQueueMtf hBumpDecay)

theorem full_restore_bump_ana_mode_fid_s13_impl (Γ : Env)
    (hBumpAna : ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X)
    (hClearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S4RestoreBumpAnaModeFidFn
      (fidStep13S4BeforeRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_restore_bump_ana_mode_fid_step13_wp Γ hBumpAna hClearAna)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

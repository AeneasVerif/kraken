/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof1a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof4
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof1c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof3a1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactorProof0c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactorProof1c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactorProof2b
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 13 Shard S5 Proof Rows & Parametric `Impl` Barrel
(`FullFidelityStep13S5RowsProof`)

Exports the `27` replacement specification rows (`fidStep13S5ReplRows`), `1` inserted helper row
(`fidStep13S5BeforeRows` / `fidStep13S5BeforeRowGroups` for `full_viv_recompute_promote_fid`),
name/signature/`noExit` alignment theorems, `28/28` kernel-checked `checkCallsOk` theorems, and
`28/28` parametric `SpecEntry.Impl` lemmas (`0` `import all`, `0` `@[expose]` on
theorems/lemmas, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackbone
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor
open LeanQbe.T.Examples.Kissat.PatchModule
open FullM6Hdr FullM6Orch FullM6 FullM6CompactFlush FullM6VivBackbone FullFidelityTumble
open FullFidelityVivK6 FullBvaHeap FullFidelityBva FullFidelityStep7 FullFidelityStep9
open FullM7MemShrink

@[expose] public section

/-- The `27` sig-preserving replacement specification rows aligned 1-to-1 with
`fidStep13S5Repls`. -/
def fidStep13S5ReplRows : List SpecEntry :=
  [ ⟨"full_activate_lit_fid", [i64, i32], [], fullActivateLitFidSpec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], step13ParseBodyM6Spec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], step13SortRedsSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], step13ReduceM6Spec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], step13SetInactiveSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64], fullVivCommitM6Spec, true⟩
  , ⟨"full_viv_mark_garb_m6", [i64, i32], [], fullVivMarkGarbM6Spec, true⟩
  , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32], step13VivDeduceM6Spec, true⟩
  , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
      fullVivFinishM6Spec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], step13VivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], step13VivifySpec, true⟩
  , ⟨"full_backbone_keep_m6", [i64, i64], [], fullBackboneKeepM6Spec, true⟩
  , ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool], step13BackbonePropM6Spec, true⟩
  , ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32],
      step13BackboneAnalyzeM6Spec, true⟩
  , ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64], step13BackboneRoundM6Spec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], step13BackboneSpec, true⟩
  , ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], fullTransLitM6Spec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], step13TransitiveSpec, true⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], step13AddClauseSpec, true⟩
  , ⟨"full_add_bin_m6", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], step13DeleteBinarySpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], step13BvaScanCandsSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], step7BvaCommitSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩ ]

/-- The `1` inserted helper specification row aligned 1-to-1 with
`fidStep13S5Befores.flatMap Prod.snd`. -/
def fidStep13S5BeforeRows : List SpecEntry :=
  [ ⟨"full_viv_recompute_promote_fid", [i64, i32], [], step13VivRecomputePromoteSpec, true⟩ ]

/-- Grouped before-host specification rows aligned with `fidStep13S5Befores`. -/
def fidStep13S5BeforeRowGroups : List (Sym × List SpecEntry) :=
  [ ("full_viv_deduce_m6", [fidStep13S5BeforeRows[0]'(by decide)]) ]

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep13S5ReplRows_names :
    fidStep13S5ReplRows.map SpecEntry.name = fidStep13S5ReplNames :=
  rfl

theorem fidStep13S5ReplRows_sigs :
    fidStep13S5ReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S5Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S5ReplRows_noExit :
    fidStep13S5ReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S5BeforeRows_names :
    fidStep13S5BeforeRows.map SpecEntry.name = fidStep13S5BeforeNames :=
  rfl

theorem fidStep13S5BeforeRows_sigs :
    fidStep13S5BeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep13S5Befores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S5BeforeRows_noExit :
    fidStep13S5BeforeRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`28/28`) -/

theorem full_viv_recompute_promote_fid_s5_callsOk :
    fidStep13S5VivRecomputePromoteFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_activate_lit_fid_s5_callsOk :
    fidStep13S5ActivateLitFn.checkCallsOk
      [ ("f64u_inv_u64", [i64], [i64])
      , ("f64u_sub", [i64, i64], [i64])
      , ("full_heap_push", [i64, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_parse_body_m6_s5_callsOk :
    fidStep13S5ParseBodyFn.checkCallsOk
      [ ("full_skip_cl", [i64, i64], [.bool])
      , ("full_ingest_cl", [i64, i64], [i64])
      , ("full_propagate", [i64], [i64])
      , ("kissat_skip_ws_comments", [i64, i64], [i64])
      , ("full_tumble_finish_fid", [i64], [])
      , ("full_wstack_defrag", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_sort_reds_s5_callsOk :
    fidStep13S5SortRedsFn.checkCallsOk
      [ ("full_red_sift", [i64, i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_reduce_m6_s5_callsOk :
    fidStep13S5ReduceFn.checkCallsOk
      [ ("full_isqrt", [i64], [i64])
      , ("f64u_log10_u64", [i64], [i64])
      , ("f64u_sub", [i64, i64], [i64])
      , ("f64u_div", [i64, i64], [i64])
      , ("f64u_from_u64", [i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("full_arena_next", [i64, i32], [i32])
      , ("m6_hdr_recompute_tiers", [i64], [])
      , ("m6_hdr_set_watermark", [i64, i64, i64], [])
      , ("full_update_classify_fid", [i64], [])
      , ("full_mark_reasons", [i64, .bool], [])
      , ("full_sort_reds", [i64, i64], [])
      , ("full_backtrack", [i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_compact_needed", [i64], [.bool])
      , ("full_compact", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_set_inactive_s5_callsOk :
    fidStep13S5SetInactiveFn.checkCallsOk
      [ ("full_heap_up", [i64, i32], [])
      , ("full_heap_down", [i64, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_probe_tail_m6_s5_callsOk :
    fidStep13S5ProbeTailFn.checkCallsOk
      [ ("full_backbone_m6", [i64, i64], [i64])
      , ("full_transitive_m6", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_probe_m6_s5_callsOk :
    fidStep13S5ProbeFn.checkCallsOk
      [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
      , ("m6_hdr_delaying", [i64, i64], [.bool])
      , ("m6_hdr_reduce_delay", [i64, i64], [])
      , ("m6_hdr_bump_delay", [i64, i64], [])
      , ("m6_hdr_get_watermark", [i64, i64], [i64])
      , ("m6_hdr_set_watermark", [i64, i64, i64], [])
      , ("full_update_classify_fid", [i64], [])
      , ("full_enter_dense", [i64], [.bool])
      , ("full_enter_dense_ex_fid", [i64, .bool], [.bool])
      , ("full_congruence_dense", [i64, i64], [i64])
      , ("full_dense_bin_roundtrip_fid", [i64], [])
      , ("full_rebuild_watches_nosort_fid", [i64], [i64])
      , ("full_substitute", [i64], [i64])
      , ("full_backbone_m6", [i64, i64], [i64])
      , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
      , ("full_has_factor_cands_fid", [i64], [.bool])
      , ("full_factor", [i64, i64], [i64])
      , ("full_vivify_m6_hdr", [i64], [i64])
      , ("full_transitive_m6", [i64, i64], [i64])
      , ("f64u_nlogpown", [i64, i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_preprocess_m6_s5_callsOk :
    fidStep13S5PreprocessFn.checkCallsOk
      [ ("full_lucky_late_m7", [i64], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_compact_needed", [i64], [.bool])
      , ("full_compact", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64])
      , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_viv_commit_m6_s5_callsOk :
    fidStep13S5VivCommitFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_unwatch_large", [i64, i32, i32], [])
      , ("full_add_unit", [i64, i32], [.bool])
      , ("full_add_bin_m6", [i64, i32, i32], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_viv_unreason_m6", [i64, i32], [])
      , ("full_viv_best_watch_m6", [i64, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_viv_mark_garb_m6_s5_callsOk :
    fidStep13S5VivMarkGarbFn.checkCallsOk
      [ ("full_viv_unreason_m6", [i64, i32], [])
      , ("full_unwatch_large", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_viv_deduce_m6_s5_callsOk :
    fidStep13S5VivDeduceFn.checkCallsOk
      [ ("full_viv_recompute_promote_fid", [i64, i32], [])
      , ("full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool])
      , ("full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_viv_finish_m6_s5_callsOk :
    fidStep13S5VivFinishFn.checkCallsOk
      [ ("full_viv_deduce_m6", [i64, i32, i32, i32], [i32])
      , ("full_viv_mark_garb_m6", [i64, i32], [])
      , ("full_backtrack", [i64, i64], [])
      , ("full_viv_commit_m6", [i64, i32, i32, i32], [i64])
      , ("full_viv_reestablish_m6", [i64, i32], [])
      , ("full_viv_inst_m6", [i64, i32, i32], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_vivify_tier_m6_hdr_s5_callsOk :
    fidStep13S5VivifyTierFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_viv_collect_fid", [i64, i64], [i64])
      , ("full_arena_next", [i64, i32], [i32])
      , ("full_viv_sort_fid", [i64, i64], [])
      , ("m6_hdr_get_watermark", [i64, i64], [i64])
      , ("full_viv_clause_m6", [i64, i32], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_viv_clear_tier_m6", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_vivify_m6_hdr_s5_callsOk :
    fidStep13S5VivifyFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("m6_hdr_get_tier1", [i64, .bool], [i64])
      , ("m6_hdr_get_tier2", [i64, .bool], [i64])
      , ("m6_hdr_delaying", [i64, i64], [.bool])
      , ("m6_hdr_get_watermark", [i64, i64], [i64])
      , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])
      , ("m6_hdr_bump_delay", [i64, i64], [])
      , ("m6_hdr_reduce_delay", [i64, i64], [])
      , ("m6_hdr_sync_legacy_tiers", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_backbone_keep_m6_s5_callsOk :
    fidStep13S5BackboneKeepFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_backbone_prop_m6_s5_callsOk :
    fidStep13S5BackbonePropFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_backbone_analyze_m6_s5_callsOk :
    fidStep13S5BackboneAnalyzeFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_backbone_round_m6_s5_callsOk :
    fidStep13S5BackboneRoundFn.checkCallsOk
      [ ("full_backbone_prop_m6", [i64, i64, .bool], [.bool])
      , ("full_backbone_analyze_m6", [i64, i32, i32, i64], [i32])
      , ("full_backbone_unwind_m6", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_backbone_m6_s5_callsOk :
    fidStep13S5BackboneFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_add_unit", [i64, i32], [.bool])
      , ("full_prioritize_binaries_m6", [i64], [.bool])
      , ("full_backbone_sched_m6", [i64], [i64])
      , ("full_backbone_round_m6", [i64, i64, .bool], [i64])
      , ("full_backbone_keep_m6", [i64, i64], [])
      , ("m6_wm4_get", [i64], [i64])
      , ("m6_wm4_set", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_trans_lit_m6_s5_callsOk :
    fidStep13S5TransLitFn.checkCallsOk
      [ ("full_delete_bin_side", [i64, i32, i32], [])
      , ("full_add_unit", [i64, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_transitive_m6_s5_callsOk :
    fidStep13S5TransitiveFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_prioritize_binaries_m6", [i64], [.bool])
      , ("full_trans_sort_m6", [i64, i64], [])
      , ("full_trans_lit_m6", [i64, i32, .bool], [.bool])
      , ("full_propagate", [i64], [i64])
      , ("full_wstack_defrag", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_add_clause_s5_callsOk :
    fidStep13S5AddClauseFn.checkCallsOk
      [ ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_watch_pop_c0", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_add_bin_m6_s5_callsOk :
    fidStep13S5AddBinM6Fn.checkCallsOk
      [ ("full_has_bin", [i64, i32, i32], [.bool])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_delete_binary_s5_callsOk :
    fidStep13S5DeleteBinaryFn.checkCallsOk
      [ ("full_delete_bin_side", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_bva_scan_cands_s5_callsOk :
    fidStep13S5BvaScanCandsFn.checkCallsOk
      [ ("full_bva_clines_fid", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

theorem full_bva_commit_s5_callsOk :
    fidStep13S5BvaCommitFn.checkCallsOk
      [ ("full_bva_steps_cap_fid", [i64], [i32])
      , ("full_fill_u64_m7", [i64, i64, i64], [])
      , ("full_wstack_defrag", [i64], [])
      , ("full_init_fresh_var", [i64, i32], [])
      , ("full_add_bin", [i64, i32, i32], [i64])
      , ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_delete_binary", [i64, i32, i32], [])
      , ("full_unwatch_large", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_factor_s5_callsOk :
    fidStep13S5FactorFn.checkCallsOk
      [ ("full_bva_steps_cap_fid", [i64], [i32])
      , ("full_bva_connect_clauses_fid", [i64], [])
      , ("full_fheap_up_fid", [i64, i64, i64, i32], [])
      , ("full_fheap_down_fid", [i64, i64, i64, i32, i32], [])
      , ("full_bva_try_lit", [i64, i32, i64], [.bool])
      , ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`28/28`) -/

theorem full_viv_recompute_promote_fid_s5_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S5VivRecomputePromoteFn
      (fidStep13S5BeforeRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_viv_recompute_promote_fid_s5_wp Γ)

theorem full_activate_lit_fid_s5_impl (Γ : Env)
    (hInvU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_inv_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5ActivateLitFn (fidStep13S5ReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_activate_lit_fid_s5_wp Γ hInvU64 hSub hHeapPush)

theorem full_parse_body_m6_s5_impl (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClTumSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hFinish : ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Γ "full_tumble_finish_fid" [i64] [] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5ParseBodyFn (fidStep13S5ReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_parse_body_m6_s5_wp Γ hSkip hIngest hProp hSwc hFinish hDefrag)

theorem full_sort_reds_s5_impl (Γ : Env)
    (hSift : ∀ a m Q X, fullRedSiftSpec a m Q X →
      Γ "full_red_sift" [i64, i64, i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5SortRedsFn (fidStep13S5ReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_sort_reds_s5_wp Γ hSift)

theorem full_reduce_m6_s5_impl (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hFromU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hToU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, step13SortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, step13ArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5ReduceFn (fidStep13S5ReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_reduce_m6_s5_wp Γ hIsqrt hLog10 hSub hDiv hFromU64 hMul hToU64
    hArenaNext hRecomp hSetWm hUpdCls hMarkRsn hSortReds hBacktrack hProp hSweep hCompNeed
    hCompact)

theorem full_set_inactive_s5_impl (Γ : Env)
    (hHeapUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hHeapDown : ∀ a m Q X, step13HeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5SetInactiveFn (fidStep13S5ReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_set_inactive_s5_wp Γ hHeapUp hHeapDown)

theorem full_probe_tail_m6_s5_impl (Γ : Env)
    (hBackbone : ∀ a m Q X, s5aBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, s5aTransitiveSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5ProbeTailFn (fidStep13S5ReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of (full_probe_tail_m6_s5_wp Γ hBackbone hTrans)

theorem full_probe_m6_s5_impl (Γ : Env)
    (hProbeDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hEnter : ∀ a m Q X, step13EnterDenseM6Spec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hEnterEx : ∀ a m Q X, step13EnterDenseExM6Spec a m Q X →
      Γ "full_enter_dense_ex_fid" [i64, .bool] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hBinRt : ∀ a m Q X, step13DenseBinRoundtripSpec a m Q X →
      Γ "full_dense_bin_roundtrip_fid" [i64] [] a m Q X)
    (hRebNosort : ∀ a m Q X, step13RebuildWatchesM6Spec a m Q X →
      Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, step13SubstituteM6Spec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, s5aBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hHasFact : ∀ a m Q X, step13HasFactorCandsSpec a m Q X →
      Γ "full_has_factor_cands_fid" [i64] [.bool] a m Q X)
    (hFactor : ∀ a m Q X, fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, s5aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, s5aTransitiveSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hNlogpown : ∀ a m Q X, f64uPure2Spec a m Q X →
      Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hToU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hScaleM5 : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5ProbeFn (fidStep13S5ReplRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_probe_m6_s5_wp Γ hProbeDt hDelay hRedD hBumpD hGetWm hSetWm
    hUpdCls hEnter hEnterEx hCong hBinRt hRebNosort hSubst hBone hSweepD hHasFact hFactor
    hViv hTrans hNlogpown hMul hToU64 hScaleM5)

theorem full_preprocess_m6_s5_impl (Γ : Env)
    (hLuckyLate : ∀ a m Q X, step13LuckyLateM6Spec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5PreprocessFn (fidStep13S5ReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of (full_preprocess_m6_s5_wp Γ hLuckyLate hProp hSweep hCompNeed hCompact
    hScale hProbe)

theorem full_viv_commit_m6_s5_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinM6 : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnreason : ∀ a m Q X, fullVivUnreasonM6Spec a m Q X →
      Γ "full_viv_unreason_m6" [i64, i32] [] a m Q X)
    (hBestWatch : ∀ a m Q X, fullVivBestWatchM6Spec a m Q X →
      Γ "full_viv_best_watch_m6" [i64, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5VivCommitFn (fidStep13S5ReplRows[8]'(by decide)) :=
  SpecEntry.Impl.of (full_viv_commit_m6_s5_wp Γ hBacktrack hUnwatch hAddUnit hAddBinM6
    hWatchPush hUnreason hBestWatch)

theorem full_viv_mark_garb_m6_s5_impl (Γ : Env)
    (hUnreason : ∀ a m Q X, fullVivUnreasonM6Spec a m Q X →
      Γ "full_viv_unreason_m6" [i64, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5VivMarkGarbFn (fidStep13S5ReplRows[9]'(by decide)) :=
  SpecEntry.Impl.of (full_viv_mark_garb_m6_s5_wp Γ hUnreason hUnwatch)

theorem full_viv_deduce_m6_s5_impl (Γ : Env)
    (hPromote : ∀ a m Q X, step13VivRecomputePromoteSpec a m Q X →
      Γ "full_viv_recompute_promote_fid" [i64, i32] [] a m Q X)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5VivDeduceFn (fidStep13S5ReplRows[10]'(by decide)) :=
  SpecEntry.Impl.of (full_viv_deduce_m6_s5_wp Γ hPromote hSubBin hSubCl)

theorem full_viv_finish_m6_s5_impl (Γ : Env)
    (hDeduce : ∀ a m Q X, step13VivDeduceM6Spec a m Q X →
      Γ "full_viv_deduce_m6" [i64, i32, i32, i32] [i32] a m Q X)
    (hMarkGarb : ∀ a m Q X, fullVivMarkGarbM6Spec a m Q X →
      Γ "full_viv_mark_garb_m6" [i64, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Γ "full_viv_commit_m6" [i64, i32, i32, i32] [i64] a m Q X)
    (hReest : ∀ a m Q X, fullVivReestablishM6Spec a m Q X →
      Γ "full_viv_reestablish_m6" [i64, i32] [] a m Q X)
    (hInst : ∀ a m Q X, fullVivInstM6Spec a m Q X →
      Γ "full_viv_inst_m6" [i64, i32, i32] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5VivFinishFn (fidStep13S5ReplRows[11]'(by decide)) :=
  SpecEntry.Impl.of (full_viv_finish_m6_s5_wp Γ hDeduce hMarkGarb hBacktrack hCommit hReest hInst)

theorem full_vivify_tier_m6_hdr_s5_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      Γ "full_viv_collect_fid" [i64, i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Γ "full_viv_sort_fid" [i64, i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, step13HdrGetWatermarkSpec a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, s5bBcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5VivifyTierFn (fidStep13S5ReplRows[12]'(by decide)) :=
  SpecEntry.Impl.of (full_vivify_tier_m6_hdr_s5_wp Γ hBacktrack hCollect hArenaNext hSort
    hGetWm hVivClause hProp hClearTier)

theorem full_vivify_m6_hdr_s5_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hGetT1 : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "m6_hdr_get_tier1" [i64, .bool] [i64] a m Q X)
    (hGetT2 : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "m6_hdr_get_tier2" [i64, .bool] [i64] a m Q X)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivTier : ∀ a m Q X, step13VivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X)
    (hBump : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduce : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5VivifyFn (fidStep13S5ReplRows[13]'(by decide)) :=
  SpecEntry.Impl.of (full_vivify_m6_hdr_s5_wp Γ hBacktrack hGetT1 hGetT2 hDelaying hGetWm
    hVivTier hBump hReduce hSync)

theorem full_backbone_keep_m6_s5_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S5BackboneKeepFn (fidStep13S5ReplRows[14]'(by decide)) :=
  SpecEntry.Impl.of (full_backbone_keep_m6_s5_wp Γ)

theorem full_backbone_prop_m6_s5_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S5BackbonePropFn (fidStep13S5ReplRows[15]'(by decide)) :=
  SpecEntry.Impl.of (full_backbone_prop_m6_s5_wp Γ)

theorem full_backbone_analyze_m6_s5_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S5BackboneAnalyzeFn (fidStep13S5ReplRows[16]'(by decide)) :=
  SpecEntry.Impl.of (full_backbone_analyze_m6_s5_wp Γ)

theorem full_backbone_round_m6_s5_impl (Γ : Env)
    (hProp : ∀ a m Q X, step13BackbonePropM6Spec a m Q X →
      Γ "full_backbone_prop_m6" [i64, i64, .bool] [.bool] a m Q X)
    (hAnalyze : ∀ a m Q X, step13BackboneAnalyzeM6Spec a m Q X →
      Γ "full_backbone_analyze_m6" [i64, i32, i32, i64] [i32] a m Q X)
    (hUnwind : ∀ a m Q X, fullBackboneUnwindM6Spec a m Q X →
      Γ "full_backbone_unwind_m6" [i64, i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5BackboneRoundFn (fidStep13S5ReplRows[17]'(by decide)) :=
  SpecEntry.Impl.of (full_backbone_round_m6_s5_wp Γ hProp hAnalyze hUnwind)

theorem full_backbone_m6_s5_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, s5bBcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, step13BackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X)
    (hWm4Get : ∀ a m Q X, m6HdrW2aSpec [] [i64] a m Q X →
      Γ "m6_wm4_get" [i64] [i64] a m Q X)
    (hWm4Set : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_wm4_set" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5BackboneFn (fidStep13S5ReplRows[18]'(by decide)) :=
  SpecEntry.Impl.of (full_backbone_m6_s5_wp Γ hBacktrack hProp hAddUnit hPrio hSched hRound hKeep
    hWm4Get hWm4Set)

theorem full_trans_lit_m6_s5_impl (Γ : Env)
    (hDelBin : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5TransLitFn (fidStep13S5ReplRows[19]'(by decide)) :=
  SpecEntry.Impl.of (full_trans_lit_m6_s5_wp Γ hDelBin hAddUnit)

theorem full_transitive_m6_s5_impl (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSort : ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Γ "full_trans_sort_m6" [i64, i64] [] a m Q X)
    (hTransLit : ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Γ "full_trans_lit_m6" [i64, i32, .bool] [.bool] a m Q X)
    (hProp : ∀ a m Q X, s5bBcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5TransitiveFn (fidStep13S5ReplRows[20]'(by decide)) :=
  SpecEntry.Impl.of (full_transitive_m6_s5_wp Γ hBacktrack hPrio hSort hTransLit hProp hDefrag)

theorem full_add_clause_s5_impl (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hPop : ∀ a m Q X, step13WatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5AddClauseFn (fidStep13S5ReplRows[21]'(by decide)) :=
  SpecEntry.Impl.of (full_add_clause_s5_wp Γ hAlloc hPush hPop)

theorem full_add_bin_m6_s5_impl (Γ : Env)
    (hHas : ∀ a m Q X, fullHasBinSpec a m Q X → Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5AddBinM6Fn (fidStep13S5ReplRows[22]'(by decide)) :=
  SpecEntry.Impl.of (full_add_bin_m6_s5_wp Γ hHas hAssign hPush)

theorem full_delete_binary_s5_impl (Γ : Env)
    (hdbs : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5DeleteBinaryFn (fidStep13S5ReplRows[23]'(by decide)) :=
  SpecEntry.Impl.of (full_delete_binary_s5_wp Γ hdbs)

theorem full_bva_scan_cands_s5_impl (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5BvaScanCandsFn (fidStep13S5ReplRows[24]'(by decide)) :=
  SpecEntry.Impl.of (full_bva_scan_cands_s5_wp Γ hClines)

theorem full_bva_commit_s5_impl (Γ : Env)
    (hStepsCap : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hFillU64 : ∀ a m Q X, m7FillU64Spec a m Q X →
      Γ "full_fill_u64_m7" [i64, i64, i64] [] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hInitFresh : ∀ a m Q X, step7InitFreshVarSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAllocCl : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, step13DeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S5BvaCommitFn (fidStep13S5ReplRows[25]'(by decide)) :=
  SpecEntry.Impl.of (full_bva_commit_s5_wp Γ hStepsCap hFillU64 hDefrag hInitFresh hAddBin
    hAllocCl hWPush hDelBin hUnwatch)

theorem full_factor_s5_impl (Γ : Env)
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
    SpecEntry.Impl Γ fidStep13S5FactorFn (fidStep13S5ReplRows[26]'(by decide)) :=
  SpecEntry.Impl.of (full_factor_s5_wp Γ hSteps hConnect hUp hDown hTryLit hUpd)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

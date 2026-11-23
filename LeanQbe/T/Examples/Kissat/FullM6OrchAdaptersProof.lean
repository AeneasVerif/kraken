module

public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof2
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof3

/-!
# Kissat `M6.0` Orchestrator Adapter Proofs (`FullM6OrchAdaptersProof`)

Certifies all `16` clean `M6.0` adapter functions in `FullM6OrchAdapters.lean` (`Proof0`..`Proof3`)
and packages them into:
1. Closed `46`-row `m6OrchAdaptersSpecTable` (`16` defined adapter functions + `30` externs,
   all `noExit = true`),
2. `m6OrchAdaptersEnv` and `m6OrchAdaptersEnv_noExit`,
3. Parametric `m6OrchAdapters_tableImpl_of` (over any `Γ : Env` providing the extern/callee specs)
   and closed `m6OrchAdapters_tableImpl`,
4. Top-level closed `m6OrchAdapters_moduleOk : ModuleOk m6OrchAdaptersEnv m6OrchAdaptersModule`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5Sched
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

private def m6aRows : List SpecEntry :=
  [ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitS15Spec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩
  , ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
  , ⟨"full_restore_bump_ana_m6_hdr", [i64], [], m6aRestoreBumpAnaSpec, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m6aAnaFailedLitSpec, true⟩
  , ⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_rephase_m6_hdr", [i64], [], m6aRephaseSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarSpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_prop_lit_raw_s15", [i64, i32, i64], [.bool], fullPropLitS15Spec, true⟩
  , ⟨"full_propagate_ignore_s15", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_bcp_s15", [i64], [i64], fullBcpS15Spec, true⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  , ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  , ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  , ⟨"full_log10_q16", [i64], [i64], m5Log10Q16Spec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"full_add_bin_m6", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64], fullVivCollectM6Spec, true⟩
  , ⟨"full_viv_count_m6", [i64, i64], [], fullVivCountM6Spec, true⟩
  , ⟨"full_viv_keys_m6", [i64, i64], [], fullVivKeysM6Spec, true⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], [], fullVivSortSchedM6Spec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"full_bve_var_m6", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_forward_sub_m6", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_init_fresh_var_m6", [i64, i32], [], fullInitFreshVarSpec, true⟩ ]

/-- Closed `46`-row specification table for `m6OrchAdaptersModule` (`16` defined adapter
functions + `30` external callees, all `noExit = true`). -/
def m6OrchAdaptersSpecTable : List SpecEntry := m6aRows

theorem m6OrchAdaptersSpecTable_length : m6OrchAdaptersSpecTable.length = 46 := by rfl

theorem m6OrchAdaptersSpecTable_sigs :
    m6OrchAdaptersSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m6OrchAdaptersModule.fns.map Fn.sig ++ m6OrchAdaptersModule.externs.map Extern.sig := by
  rfl

theorem m6OrchAdaptersSpecTable_nodup : (m6OrchAdaptersSpecTable.map SpecEntry.name).Nodup := by
  show ([ "full_scale_delta", "full_prop_lit_raw", "full_propagate_ignore", "full_propagate"
    , "full_bump_analyzed_m6_hdr", "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr"
    , "full_analyze_m6_hdr", "full_rephase_m6_hdr", "full_add_bin", "full_vivify_tier_m6_hdr"
    , "full_vivify_m6_hdr", "full_bve_var", "full_forward_sub", "full_init_fresh_var"
    , "full_probe_dticks_m6_hdr"
    , "full_scale_delta_m5", "full_prop_lit_raw_s15", "full_propagate_ignore_s15"
    , "full_bcp_s15", "m6_hdr_dr_allow", "full_sort_ana_qs_m6", "full_bump_var"
    , "full_queue_mtf", "full_bump_decay", "full_clear_ana", "full_backtrack"
    , "full_assign_lvl", "m6_hdr_update_tier_limits", "m6_hdr_dr_update"
    , "full_analyze_core_m6", "full_walk", "full_log10_q16", "m6_hdr_set_watermark"
    , "full_add_bin_m6", "full_viv_collect_m6", "full_viv_count_m6", "full_viv_keys_m6"
    , "full_viv_sort_sched_m6", "full_viv_clause_m6", "full_viv_clear_tier_m6"
    , "m6_hdr_sync_legacy_tiers", "m6_hdr_get_watermark", "full_bve_var_m6"
    , "full_forward_sub_m6", "full_init_fresh_var_m6" ] : List String).Nodup
  decide

theorem m6OrchAdaptersSpecTable_noExit : ∀ e ∈ m6OrchAdaptersSpecTable, e.noExit = true := by
  intro e he
  simp only [m6OrchAdaptersSpecTable, m6aRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m6OrchAdaptersSpecTable_allNoExit : m6OrchAdaptersSpecTable.all (·.noExit) = true := by
  rfl

/-- Closed environment for `m6OrchAdaptersModule`. -/
def m6OrchAdaptersEnv : Env := Env.ofTable m6OrchAdaptersSpecTable

theorem m6OrchAdaptersEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6OrchAdaptersEnv f as bs xs m Q X → m6OrchAdaptersEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6OrchAdaptersSpecTable_noExit

theorem m6OrchAdaptersEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m6OrchAdaptersSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m6OrchAdaptersEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m6OrchAdaptersSpecTable_nodup (hno xs m Q X h)

theorem m6OrchAdapters_allFns_wf : AllFns Fn.Wf m6OrchAdaptersModule.fns :=
  allFns_of_mem m6OrchAdapters_fns_wf

/-- Parametric `TableImpl` theorem for `m6OrchAdaptersModule.fns` against
`m6OrchAdaptersSpecTable` over any environment `Γ` supplying all `30` external callees plus
the `3` intra-module callees (`"full_propagate"`, `"full_bump_analyzed_m6_hdr"`,
`"full_vivify_tier_m6_hdr"`). -/
theorem m6OrchAdapters_tableImpl_of (Γ : Env)
    (hScaleM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hRawS15 : ∀ a m Q X, fullPropLitS15Spec a m Q X →
      Γ "full_prop_lit_raw_s15" [i64, i32, i64] [.bool] a m Q X)
    (hPropIgnS15 : ∀ a m Q X, fullPropagateIgnoreS15Spec a m Q X →
      Γ "full_propagate_ignore_s15" [i64, i64] [i64] a m Q X)
    (hBcpS15 : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_bcp_s15" [i64] [i64] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hSortAna : ∀ a m Q X, m6SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hUpdTier : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_update_tier_limits" [i64] [] a m Q X)
    (hDrUpd : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_update" [i64] [] a m Q X)
    (hAnaCore : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_core_m6" [i64] [i64] a m Q X)
    (hWalk : ∀ a m Q X, fullWalkSpec a m Q X → Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, m5Log10Q16Spec a m Q X → Γ "full_log10_q16" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hVivCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hVivCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hVivKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hVivSort : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hVivClear : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m6" [i64, i32] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m6" [i64, i64] [i64] a m Q X)
    (hInitFv : ∀ a m Q X, fullInitFreshVarSpec a m Q X →
      Γ "full_init_fresh_var_m6" [i64, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hBumpAna : ∀ a m Q X, m6aBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6_hdr" [i64] [] a m Q X)
    (hVivTier : ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X) :
    TableImpl Γ m6OrchAdaptersModule.fns m6OrchAdaptersSpecTable :=
  ⟨ SpecEntry.Impl.of (full_scale_delta_wp Γ hScaleM5)
  , SpecEntry.Impl.of (full_prop_lit_raw_wp Γ hRawS15)
  , SpecEntry.Impl.of (full_propagate_ignore_wp Γ hPropIgnS15)
  , SpecEntry.Impl.of (full_propagate_wp Γ hBcpS15)
  , SpecEntry.Impl.of (full_bump_analyzed_m6_hdr_wp Γ hDrAllow hSortAna hBumpVar hQueueMtf
      hBumpDecay)
  , SpecEntry.Impl.of (full_restore_bump_ana_m6_hdr_wp Γ hBumpAna hClearAna)
  , SpecEntry.Impl.of (full_ana_failed_lit_m6_hdr_wp Γ hClearAna hBumpAna hBacktrack hAssignLvl)
  , SpecEntry.Impl.of (full_analyze_m6_hdr_wp Γ hUpdTier hDrUpd hAnaCore)
  , SpecEntry.Impl.of (full_rephase_m6_hdr_wp Γ hBacktrack hWalk hLog hSetWm)
  , SpecEntry.Impl.of (full_add_bin_wp Γ hAddBin)
  , SpecEntry.Impl.of (full_vivify_tier_m6_hdr_wp Γ hBacktrack hVivCollect hVivCount hVivKeys
      hVivSort hVivClause hProp hVivClear)
  , SpecEntry.Impl.of (full_vivify_m6_hdr_wp Γ hBacktrack hSync hGetWm hVivTier)
  , SpecEntry.Impl.of (full_bve_var_wp Γ hBveVar)
  , SpecEntry.Impl.of (full_forward_sub_wp Γ hFwdSub)
  , SpecEntry.Impl.of (full_init_fresh_var_wp Γ hInitFv)
  , SpecEntry.Impl.of (full_probe_dticks_m6_hdr_wp Γ hGetWm)
  , trivial ⟩

theorem m6OrchAdapters_tableImpl :
    TableImpl m6OrchAdaptersEnv m6OrchAdaptersModule.fns m6OrchAdaptersSpecTable :=
  m6OrchAdapters_tableImpl_of m6OrchAdaptersEnv
    (m6OrchAdaptersEnv_row_at 16
      ⟨"full_scale_delta_m5", [i64, i64], [i64], schedScaleDeltaSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 17
      ⟨"full_prop_lit_raw_s15", [i64, i32, i64], [.bool], fullPropLitS15Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 18
      ⟨"full_propagate_ignore_s15", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 19
      ⟨"full_bcp_s15", [i64], [i64], fullBcpS15Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 20
      ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrDrAllowSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 21
      ⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩
      (hno := fun _ _ _ _ h => m6SortAnaQsSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 22
      ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 23
      ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 24
      ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩)
    (m6OrchAdaptersEnv_row_at 25
      ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 26
      ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 27
      ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 28
      ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 29
      ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrDrMutSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 30
      ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 31
      ⟨"full_walk", [i64], [], fullWalkSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 32
      ⟨"full_log10_q16", [i64], [i64], m5Log10Q16Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 33
      ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 34
      ⟨"full_add_bin_m6", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 35
      ⟨"full_viv_collect_m6", [i64, i64], [i64], fullVivCollectM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 36
      ⟨"full_viv_count_m6", [i64, i64], [], fullVivCountM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 37
      ⟨"full_viv_keys_m6", [i64, i64], [], fullVivKeysM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 38
      ⟨"full_viv_sort_sched_m6", [i64, i64], [], fullVivSortSchedM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 39
      ⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 40
      ⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 41
      ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 42
      ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 43
      ⟨"full_bve_var_m6", [i64, i32], [i64], fullBveVarDefSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 44
      ⟨"full_forward_sub_m6", [i64, i64], [i64], fullForwardSubFastSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 45
      ⟨"full_init_fresh_var_m6", [i64, i32], [], fullInitFreshVarSpec, true⟩)
    (m6OrchAdaptersEnv_row_at 3
      ⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩)
    (m6OrchAdaptersEnv_row_at 4
      ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
      (hno := fun _ _ _ _ h => m6aBumpAnalyzedSpec_monoX h))
    (m6OrchAdaptersEnv_row_at 10
      ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
      (hno := fun _ _ _ _ h => m6aVivifyTierSpec_monoX h))

theorem m6OrchAdapters_moduleOk :
    ModuleOk m6OrchAdaptersEnv m6OrchAdaptersModule :=
  Env.ofTable_moduleOk m6OrchAdapters_acyclic m6OrchAdapters_allFns_wf
    m6OrchAdapters_tableImpl

end LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

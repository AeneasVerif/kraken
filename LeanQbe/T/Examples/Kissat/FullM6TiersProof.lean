module

public import LeanQbe.T.Examples.Kissat.FullM6TiersProof0
public import LeanQbe.T.Examples.Kissat.FullM6TiersProof1a
public import LeanQbe.T.Examples.Kissat.FullM6TiersProof1b

/-!
# Kissat Wave 2 `PR-W2A` (`RC-19`) Closed `ModuleOk` & `m6TiersSpecTable` (`FullM6TiersProof`)

Combines all `35` C0 `Func.wp` theorems from `FullM6TiersProof{0,1a,1b}` and the `18` canonical
`FullSpec` externs into a closed `53`-row specification table:
- `m6TiersSpecTable` (`53` rows, all `noExit = true`) and
  `m6TiersEnv := Env.ofTable m6TiersSpecTable`.
- `m6TiersSpecTable_noExit`, `m6Tiers_noExit`, `m6Tiers_tableImpl`, and
  `m6Tiers_moduleOk : ModuleOk m6TiersEnv m6TiersModule`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Tiers

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full

/-- Closed `53`-row specification table covering `m6Tiers_fns` (`35` fns) and `m6TiersExterns`
(`18` canonical `FullSpec` externs), all with `noExit = true`. -/
def m6TiersSpecTable : List SpecEntry :=
  [ ⟨"full_m6_hdr_sizeof", [], [i64], m6HdrSizeofSpec, true⟩
  , ⟨"full_m6_ext_sizeof", [], [i64], m6ExtSizeofSpec, true⟩
  , ⟨"full_m6_get64", [i64, i64], [i64], m6Get64Spec, true⟩
  , ⟨"full_m6_set64", [i64, i64, i64], [], m6Set64Spec, true⟩
  , ⟨"full_m6_ext_ready", [i64], [.bool], m6ExtReadySpec, true⟩
  , ⟨"full_m6_sync_legacy_tiers", [i64], [], m6SafetyVoidSpec, true⟩
  , ⟨"full_m6_recompute_tiers_legacy", [i64], [], m6SafetyVoidSpec, true⟩
  , ⟨"full_m6_recompute_tiers_ext", [i64, i64], [], m6RecomputeExtSpec, true⟩
  , ⟨"full_m6_recompute_tiers_mode", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  , ⟨"full_recompute_tiers_m6", [i64], [], m6SafetyVoidSpec, true⟩
  , ⟨"full_m6_update_tier_limits", [i64], [], m6SafetyVoidSpec, true⟩
  , ⟨"full_m6_record_used", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  , ⟨"full_m6_get_tier1", [i64, .bool], [i64], m6SafetyBoolU64Spec, true⟩
  , ⟨"full_m6_get_tier2", [i64, .bool], [i64], m6SafetyBoolU64Spec, true⟩
  , ⟨"full_m6_delaying", [i64, i64], [.bool], m6DelayingSpec, true⟩
  , ⟨"full_m6_bump_delay", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  , ⟨"full_m6_reduce_delay", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  , ⟨"full_m6_reset_delay", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  , ⟨"full_m6_get_watermark", [i64, i64], [i64], m6GetWmSpec, true⟩
  , ⟨"full_m6_set_watermark", [i64, i64, i64], [], m6SetWmSpec, true⟩
  , ⟨"full_m6_add_ticks", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  , ⟨"full_log10_q16_m6", [i64], [i64], m6Log10Q16Spec, true⟩
  , ⟨"full_scale_delta_m6", [i64, i64], [i64], m6ScaleDeltaSpec, true⟩
  , ⟨"full_probe_dticks_m6", [i64, .bool], [i64], m6DticksSpec, true⟩
  , ⟨"full_elim_dticks_m6", [i64, .bool], [i64], m6DticksSpec, true⟩
  , ⟨"full_switch_mode_m6", [i64], [], Full.fullSwitchModeSpec, true⟩
  , ⟨"full_rephase_m6", [i64], [], m6RephaseSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  , ⟨"full_analyze_rsn_m6", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  , ⟨"full_analyze_m6", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeInitSpec, true⟩
  , ⟨"full_probe", [i64], [i64], Full.fullProbeSpec, true⟩
  , ⟨"full_elim_bve_m6", [i64, i64], [i64], m6ElimBveSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], m6ElimInitSpec, true⟩
  , ⟨"full_eliminate", [i64], [i64], Full.fullEliminateSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWalkSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  , ⟨"full_congruence", [i64], [i64], Full.fullCongruenceSpec, true⟩
  , ⟨"full_sweep_sat", [i64], [i64], Full.fullSweepSatSpec, true⟩
  , ⟨"full_transitive", [i64], [i64], Full.fullTransitiveSpec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], Full.fullProbeRunSpec, true⟩
  , ⟨"full_vivify", [i64, i64], [i64], Full.fullVivifySpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], Full.fullEnterDenseSpec, true⟩
  , ⟨"full_forward_sub", [i64], [i64], Full.fullForwardSubSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], Full.fullBveVarSpec, true⟩
  , ⟨"full_factor", [i64], [i64], Full.fullFactorSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  ]

/-- Specification environment induced by `m6TiersSpecTable`. -/
def m6TiersEnv : Env := Env.ofTable m6TiersSpecTable

theorem m6TiersSpecTable_noExit : ∀ e ∈ m6TiersSpecTable, e.noExit = true := by
  intro e he
  have hall : m6TiersSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m6Tiers_noExit :
    ∀ f as bs xs m Q X X',
      m6TiersEnv f as bs xs m Q X → m6TiersEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6TiersSpecTable_noExit

private theorem m6TiersSpecTable_nodup : (m6TiersSpecTable.map SpecEntry.name).Nodup := by
  show
    ( [ "full_m6_hdr_sizeof", "full_m6_ext_sizeof", "full_m6_get64", "full_m6_set64",
        "full_m6_ext_ready", "full_m6_sync_legacy_tiers", "full_m6_recompute_tiers_legacy",
        "full_m6_recompute_tiers_ext", "full_m6_recompute_tiers_mode", "full_recompute_tiers_m6",
        "full_m6_update_tier_limits", "full_m6_record_used", "full_m6_get_tier1",
        "full_m6_get_tier2", "full_m6_delaying", "full_m6_bump_delay", "full_m6_reduce_delay",
        "full_m6_reset_delay", "full_m6_get_watermark", "full_m6_set_watermark",
        "full_m6_add_ticks", "full_log10_q16_m6", "full_scale_delta_m6",
        "full_probe_dticks_m6", "full_elim_dticks_m6", "full_switch_mode_m6",
        "full_rephase_m6", "full_reduce_m6", "full_analyze_rsn_m6", "full_analyze_m6",
        "full_probe_m6", "full_probe", "full_elim_bve_m6", "full_eliminate_m6",
        "full_eliminate", "full_ilog10", "full_heap_down", "full_backtrack", "full_walk",
        "full_reduce", "full_analyze_rsn", "full_analyze", "full_substitute",
        "full_congruence", "full_sweep_sat", "full_transitive", "full_probe_run",
        "full_vivify", "full_enter_dense", "full_forward_sub", "full_bve_var", "full_factor",
        "full_rebuild_watches" ] : List String).Nodup
  decide

private theorem m6TiersEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m6TiersSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m6TiersEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m6TiersSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m6Tiers_fns` (`35` fns) against `m6TiersSpecTable`. -/
theorem m6Tiers_tableImpl :
    TableImpl m6TiersEnv m6Tiers_fns m6TiersSpecTable := by
  let h2 := m6TiersEnv_row_at 2 ⟨"full_m6_get64", [i64, i64], [i64], m6Get64Spec, true⟩
  let h3 := m6TiersEnv_row_at 3 ⟨"full_m6_set64", [i64, i64, i64], [], m6Set64Spec, true⟩
  let h4 := m6TiersEnv_row_at 4 ⟨"full_m6_ext_ready", [i64], [.bool], m6ExtReadySpec, true⟩
  let h5 := m6TiersEnv_row_at 5
    ⟨"full_m6_sync_legacy_tiers", [i64], [], m6SafetyVoidSpec, true⟩
  let h6 := m6TiersEnv_row_at 6
    ⟨"full_m6_recompute_tiers_legacy", [i64], [], m6SafetyVoidSpec, true⟩
  let h7 := m6TiersEnv_row_at 7
    ⟨"full_m6_recompute_tiers_ext", [i64, i64], [], m6RecomputeExtSpec, true⟩
  let h8 := m6TiersEnv_row_at 8
    ⟨"full_m6_recompute_tiers_mode", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  let h9 := m6TiersEnv_row_at 9 ⟨"full_recompute_tiers_m6", [i64], [], m6SafetyVoidSpec, true⟩
  let h10 := m6TiersEnv_row_at 10
    ⟨"full_m6_update_tier_limits", [i64], [], m6SafetyVoidSpec, true⟩
  let h11 := m6TiersEnv_row_at 11
    ⟨"full_m6_record_used", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  let h14 := m6TiersEnv_row_at 14 ⟨"full_m6_delaying", [i64, i64], [.bool], m6DelayingSpec, true⟩
  let h15 := m6TiersEnv_row_at 15
    ⟨"full_m6_bump_delay", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  let h16 := m6TiersEnv_row_at 16
    ⟨"full_m6_reduce_delay", [i64, i64], [], m6SafetyArgVoidSpec i64, true⟩
  let h18 := m6TiersEnv_row_at 18
    ⟨"full_m6_get_watermark", [i64, i64], [i64], m6GetWmSpec, true⟩
  let h19 := m6TiersEnv_row_at 19
    ⟨"full_m6_set_watermark", [i64, i64, i64], [], m6SetWmSpec, true⟩
  let h21 := m6TiersEnv_row_at 21 ⟨"full_log10_q16_m6", [i64], [i64], m6Log10Q16Spec, true⟩
  let h22 := m6TiersEnv_row_at 22
    ⟨"full_scale_delta_m6", [i64, i64], [i64], m6ScaleDeltaSpec, true⟩
  let h23 := m6TiersEnv_row_at 23
    ⟨"full_probe_dticks_m6", [i64, .bool], [i64], m6DticksSpec, true⟩
  let h24 := m6TiersEnv_row_at 24
    ⟨"full_elim_dticks_m6", [i64, .bool], [i64], m6DticksSpec, true⟩
  let h30 := m6TiersEnv_row_at 30 ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeInitSpec, true⟩
  let h32 := m6TiersEnv_row_at 32 ⟨"full_elim_bve_m6", [i64, i64], [i64], m6ElimBveSpec, true⟩
  let h33 := m6TiersEnv_row_at 33
    ⟨"full_eliminate_m6", [i64, .bool], [i64], m6ElimInitSpec, true⟩
  let h35 := m6TiersEnv_row_at 35 ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  let h36 := m6TiersEnv_row_at 36 ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  let h37 := m6TiersEnv_row_at 37 ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let h38 := m6TiersEnv_row_at 38 ⟨"full_walk", [i64], [], Full.fullWalkSpec, true⟩
  let h39 := m6TiersEnv_row_at 39 ⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  let h40 := m6TiersEnv_row_at 40
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  let h41 := m6TiersEnv_row_at 41 ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  let h42 := m6TiersEnv_row_at 42 ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  let h43 := m6TiersEnv_row_at 43 ⟨"full_congruence", [i64], [i64], Full.fullCongruenceSpec, true⟩
  let h44 := m6TiersEnv_row_at 44 ⟨"full_sweep_sat", [i64], [i64], Full.fullSweepSatSpec, true⟩
  let h45 := m6TiersEnv_row_at 45 ⟨"full_transitive", [i64], [i64], Full.fullTransitiveSpec, true⟩
  let h46 := m6TiersEnv_row_at 46
    ⟨"full_probe_run", [i64, i64], [i64], Full.fullProbeRunSpec, true⟩
  let h47 := m6TiersEnv_row_at 47 ⟨"full_vivify", [i64, i64], [i64], Full.fullVivifySpec, true⟩
  let h48 :=
    m6TiersEnv_row_at 48 ⟨"full_enter_dense", [i64], [.bool], Full.fullEnterDenseSpec, true⟩
  let h49 := m6TiersEnv_row_at 49 ⟨"full_forward_sub", [i64], [i64], Full.fullForwardSubSpec, true⟩
  let h50 := m6TiersEnv_row_at 50 ⟨"full_bve_var", [i64, i32], [i64], Full.fullBveVarSpec, true⟩
  let h51 := m6TiersEnv_row_at 51 ⟨"full_factor", [i64], [i64], Full.fullFactorSpec, true⟩
  let h52 := m6TiersEnv_row_at 52
    ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  exact ⟨.of (full_m6_hdr_sizeof_wp m6TiersEnv),
    ⟨.of (full_m6_ext_sizeof_wp m6TiersEnv),
    ⟨.of (full_m6_get64_wp m6TiersEnv),
    ⟨.of (full_m6_set64_wp m6TiersEnv),
    ⟨.of (full_m6_ext_ready_wp m6TiersEnv h2 h3),
    ⟨.of (full_m6_sync_legacy_tiers_wp m6TiersEnv h4),
    ⟨.of (full_m6_recompute_tiers_legacy_wp m6TiersEnv),
    ⟨.of (full_m6_recompute_tiers_ext_wp m6TiersEnv h2 h3 h5),
    ⟨.of (full_m6_recompute_tiers_mode_wp m6TiersEnv h4 h6 h7),
    ⟨.of (full_recompute_tiers_m6_wp m6TiersEnv h8),
    ⟨.of (full_m6_update_tier_limits_wp m6TiersEnv h4 h2 h3 h9),
    ⟨.of (full_m6_record_used_wp m6TiersEnv h4 h2 h3),
    ⟨.of (full_m6_get_tier1_wp m6TiersEnv h4),
    ⟨.of (full_m6_get_tier2_wp m6TiersEnv h4),
    ⟨.of (full_m6_delaying_wp m6TiersEnv h4),
    ⟨.of (full_m6_bump_delay_wp m6TiersEnv h4),
    ⟨.of (full_m6_reduce_delay_wp m6TiersEnv h4),
    ⟨.of (full_m6_reset_delay_wp m6TiersEnv h4),
    ⟨.of (full_m6_get_watermark_wp m6TiersEnv h4 h2),
    ⟨.of (full_m6_set_watermark_wp m6TiersEnv h4 h3),
    ⟨.of (full_m6_add_ticks_wp m6TiersEnv h4 h18 h19),
    ⟨.of (full_log10_q16_m6_wp m6TiersEnv),
    ⟨.of (full_scale_delta_m6_wp m6TiersEnv h21),
    ⟨.of (full_probe_dticks_m6_wp m6TiersEnv h18),
    ⟨.of (full_elim_dticks_m6_wp m6TiersEnv h18),
    ⟨.of (full_switch_mode_m6_wp m6TiersEnv h36 h4 h18 h19 h21 h35),
    ⟨.of (full_rephase_m6_wp m6TiersEnv h37 h38 h21 h19),
    ⟨.of (full_reduce_m6_wp m6TiersEnv h9 h39 h19),
    ⟨.of (full_analyze_rsn_m6_wp m6TiersEnv h11 h40),
    ⟨.of (full_analyze_m6_wp m6TiersEnv h10 h41),
    ⟨.of (full_probe_m6_wp m6TiersEnv h4 h18 h19 h14 h15 h16 h23 h22 h35 h42 h43 h44 h45 h46
      h47 h37),
    ⟨.of (full_probe_wp m6TiersEnv h30),
    ⟨.of (full_elim_bve_m6_wp m6TiersEnv h50),
    ⟨.of (full_eliminate_m6_wp m6TiersEnv h4 h18 h19 h24 h22 h35 h48 h49 h32 h51 h52),
    ⟨.of (full_eliminate_wp m6TiersEnv h33),
      trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m6TiersModule` under canonical `m6TiersEnv`. -/
theorem m6Tiers_moduleOk : ModuleOk m6TiersEnv m6TiersModule :=
  Env.ofTable_moduleOk m6Tiers_acyclic
    ⟨full_m6_hdr_sizeof_wf, full_m6_ext_sizeof_wf, full_m6_get64_wf, full_m6_set64_wf,
      full_m6_ext_ready_wf, full_m6_sync_legacy_tiers_wf, full_m6_recompute_tiers_legacy_wf,
      full_m6_recompute_tiers_ext_wf, full_m6_recompute_tiers_mode_wf, full_recompute_tiers_m6_wf,
      full_m6_update_tier_limits_wf, full_m6_record_used_wf, full_m6_get_tier1_wf,
      full_m6_get_tier2_wf, full_m6_delaying_wf, full_m6_bump_delay_wf, full_m6_reduce_delay_wf,
      full_m6_reset_delay_wf, full_m6_get_watermark_wf, full_m6_set_watermark_wf,
      full_m6_add_ticks_wf, full_log10_q16_m6_wf, full_scale_delta_m6_wf, full_probe_dticks_m6_wf,
      full_elim_dticks_m6_wf, full_switch_mode_m6_wf, full_rephase_m6_wf, full_reduce_m6_wf,
      full_analyze_rsn_m6_wf, full_analyze_m6_wf, full_probe_m6_wf, full_probe_wf,
      full_elim_bve_m6_wf, full_eliminate_m6_wf, full_eliminate_wf, trivial⟩
    m6Tiers_tableImpl

end LeanQbe.T.Examples.Kissat.FullM6Tiers

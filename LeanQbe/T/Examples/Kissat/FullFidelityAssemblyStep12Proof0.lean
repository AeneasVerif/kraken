/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofAnalyze
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3RowsProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12ARows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12ARowsProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BRows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BRowsProof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRowsProof
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleRows
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleRowsProof
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 12 Assembly Proof Foundation (`FullFidelityAssemblyStep12Proof0`)

Row tables, `fidStep12Bundle`, `fidStep12Env`, `length` (`517`), `namesNodup`,
`161`-slot Step-10 `(slot, sig)` lookup lifted from `Step7 -> Step8 -> Step9 -> Step10`,
replacement signature agreement, `noCallBad`, `full_cong_work_step` identity, and
`patchFns_split_12` structural helpers (`0` `@[expose]` on thms/lemmas, `0` `import all`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityStep11
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3
open LeanQbe.T.Examples.Kissat.FullFidelityStep12A
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open LeanQbe.T.Examples.Kissat.FullFidelityStep12C
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- PR 1 (`8` repls) spec rows matching `fid12Pr1Repls`. -/
def fid12Pr1Rows : List SpecEntry :=
  [ ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], m6AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m6aAnaFailedLitSpecP M6ExtW2bPres, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], FullM8CoreParity.m8MinShrinkSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], FullM7Search.m7SwitchModeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩ ]

/-- PR 3 (`11` kept repls) spec rows matching `fid12Pr3Repls`. -/
def fid12Pr3ReplRows : List SpecEntry :=
  fidStep11Pr3ReplRows.take 4 ++
  [ ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], FullFidelityStep11.s11Deduce1uipHdrSpec, true⟩ ] ++
  (fidStep11Pr3ReplRows.drop 5).take 2 ++ fidStep11Pr3ReplRows.drop 8

/-- Step-12A (`5` direct repls) spec rows matching `fidStep12ARepls`. -/
def fid12Step12AReplRows : List SpecEntry :=
  FullFidelityStep12A.fidStep12AReplRows.filter (·.name != "full_preprocess_m6")

/-- Combined `46` replacement rows matching `fidStep12Repls`. -/
def fidStep12ReplRows : List SpecEntry :=
  fid12Pr1Rows ++ fidStep11TumReplRows ++ fid12Pr3ReplRows ++
  fidStep12BReplRows ++ fidStep12CReplRows ++ fid12Step12AReplRows

/-- Combined `12` inserted helper rows matching `fidStep12Befores`. -/
def fidStep12BeforeRows : List SpecEntry :=
  fidStep11TumBeforeRows ++ fidStep11Pr3BeforeRows ++
  fidStep12BBeforeRows ++ fidStep12CBeforeRows

/-- Step-12 `PatchBundle` composing `fidStep10Module` + `fidStep12Repls` +
`fidStep12Befores` + `fidStep12BRewireRows` (`505 -> 517` fns). -/
def fidStep12Bundle : PatchBundle where
  baseMod := fidStep10Module
  baseTable := fidStep10BaseSpecTable
  baseOk := fidStep10Base_moduleOk
  repls := fidStep12Repls
  replRows := fidStep12ReplRows
  befores := fidStep12Befores
  beforeRows := fidStep12BeforeRows
  rewiredRows := fidStep12BRewireRows

/-- Closed `Env` for `fidStep12Module` (`517` fns). -/
def fidStep12Env : Env :=
  patchEnv fidStep12Bundle

/-- All `59` names overridden or inserted in `fidStep12Bundle.frontTable`. -/
def fidStep12FrontNames : List Sym :=
  [ "full_cong_work_step"
  , "full_analyze_rsn_m6_hdr", "full_ana_failed_lit_m6_hdr", "full_min_shrink_m6"
  , "full_analyze", "full_analyze_core_m6", "full_vivify_tier_m6_hdr"
  , "full_switch_mode_m7", "full_preprocess_m6"
  , "full_zero_tables2", "full_init_hdr", "full_ingest_cl"
  , "full_parse_body_m6", "full_extend", "full_lucky_scan"
  , "full_m6_sweep_cone", "full_save_target_best", "full_backtrack"
  , "full_deduce_1uip_m6", "full_deduce_1uip_m6_hdr", "full_one_lit_confl"
  , "full_learn_clause", "full_viv_collect_fid", "full_viv_sort2_fid"
  , "full_viv_sort_fid", "full_viv_clause_m6"
  , "full_cong_extract", "full_cong_and_match", "full_cong_enq_var"
  , "full_cong_eval_gate", "full_cong_worklist", "full_congruence_dense"
  , "full_backbone_sched_m6", "full_backbone_m6", "full_dense_prop_unit_m7"
  , "full_forward_sub_m7", "full_bve_commit_res", "full_bve_var_m7"
  , "full_add_clause", "full_sweep_copy", "full_learn_clause_m6", "full_viv_sort_counts_m6"
  , "full_trans_sort_m6", "full_m6_sweep_sim", "full_m6_sweep_vars"
  , "full_factor", "full_probe_m6"
  , "full_activate_lit_fid", "full_tumble_finish_fid", "full_extend_core_fid"
  , "full_unperm_fid", "full_lucky_ord_fid", "full_backtrack_ac_fid"
  , "full_cong_extract_and_clause_fid", "full_cong_extract_from_fid"
  , "full_bve_weaken_unit_fid", "full_watch_pop_c0", "full_reduce_purge_c0"
  , "full_viv_sift_counts_m6" ]

/-- Anchor-aware name expansion for `fidStep12Befores`. -/
def fidStep12PatchStr (nm : Sym) : List Sym :=
  if nm == "full_ingest_cl" then ["full_activate_lit_fid", nm]
  else if nm == "full_parse_body_m6" then ["full_tumble_finish_fid", nm]
  else if nm == "full_extend" then ["full_extend_core_fid", "full_unperm_fid", nm]
  else if nm == "full_lucky_scan" then ["full_lucky_ord_fid", nm]
  else if nm == "full_ana_failed_lit_m6_hdr" then ["full_backtrack_ac_fid", nm]
  else if nm == "full_cong_extract" then
    ["full_cong_extract_and_clause_fid", "full_cong_extract_from_fid", nm]
  else if nm == "full_bve_var_m7" then ["full_bve_weaken_unit_fid", nm]
  else if nm == "full_add_clause" then ["full_watch_pop_c0", nm]
  else if nm == "full_learn_clause_m6" then ["full_reduce_purge_c0", nm]
  else if nm == "full_viv_sort_counts_m6" then ["full_viv_sift_counts_m6", nm]
  else [nm]

/-- Ordered `517` function names of `fidStep12Module`. -/
def fidStep12FnNames : List Sym :=
  fidStep10FnNames.flatMap fidStep12PatchStr

/-- Sorted `(slot, sig)` table for all `161` target symbols in `fidStep10Module.fns`. -/
def fidStep10_step12_sigPairs : List (Nat × SigEntry) :=
  [ (2, ("kissat_skip_ws_comments", [i64, i64], [i64]))
  , (6, ("kissat_next_lit", [i64, i64], [i64]))
  , (9, ("full_ilog10", [i64], [i64]))
  , (11, ("full_arena_next", [i64, i32], [i32]))
  , (12, ("full_alloc_cl", [i64, i32, i32, .bool], [i64]))
  , (18, ("full_wstack_defrag", [i64], []))
  , (19, ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]))
  , (21, ("full_heap_down", [i64, i32], []))
  , (22, ("full_heap_push", [i64, i32], []))
  , (30, ("full_tick_rel", [i64], []))
  , (32, ("full_log10_q16_m7", [i64], [i64]))
  , (33, ("full_scale_delta_m5", [i64, i64], [i64]))
  , (34, ("full_ema_update", [i64, i64], []))
  , (36, ("full_assign_lvl", [i64, i32, i32, i32], []))
  , (37, ("full_assign", [i64, i32, i32], []))
  , (38, ("full_save_target_best", [i64], []))
  , (39, ("full_backtrack_raw_m5", [i64, i64], []))
  , (40, ("full_backtrack", [i64, i64], []))
  , (41, ("full_add_clause", [i64, i32, i32, .bool], [i64]))
  , (44, ("full_zero_tables2", [i64], []))
  , (47, ("full_init_hdr", [i64, i64, i64, i64], []))
  , (65, ("m6_hdr_record_used", [i64, i64], []))
  , (68, ("m6_hdr_delaying", [i64, i64], [.bool]))
  , (69, ("m6_hdr_bump_delay", [i64, i64], []))
  , (70, ("m6_hdr_reduce_delay", [i64, i64], []))
  , (72, ("m6_hdr_get_watermark", [i64, i64], [i64]))
  , (73, ("m6_hdr_set_watermark", [i64, i64, i64], []))
  , (78, ("full_skip_cl", [i64, i64], [.bool]))
  , (79, ("full_ingest_cl", [i64, i64], [i64]))
  , (82, ("full_unwatch_large", [i64, i32, i32], []))
  , (89, ("full_propagate_ignore", [i64, i64], [i64]))
  , (90, ("full_propagate", [i64], [i64]))
  , (91, ("full_parse_body_m6", [i64, i64], [i64]))
  , (101, ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]))
  , (108, ("full_arena_sweep", [i64], [i64]))
  , (109, ("full_mark_reasons", [i64, .bool], []))
  , (114, ("full_reduce", [i64, .bool], [i64]))
  , (115, ("full_reduce_m6", [i64, .bool], [i64]))
  , (116, ("full_analyze_lit", [i64, i32, i32], [.bool]))
  , (117, ("full_analyze_rsn", [i64, i32, i32], [.bool]))
  , (118, ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]))
  , (119, ("full_clear_ana", [i64], []))
  , (122, ("full_bump_analyzed_m6_hdr", [i64], []))
  , (123, ("full_restore_bump_ana_m6_hdr", [i64], []))
  , (124, ("full_ana_failed_lit_m6_hdr", [i64], [i64]))
  , (125, ("full_otfs_large", [i64, i32, i32], [.bool]))
  , (126, ("full_otfs_bin", [i64, i32, i32], [.bool]))
  , (127, ("full_otfs_subsume", [i64, i32, i64, i64, .bool], []))
  , (128, ("full_min_mark", [i64, i32, i8], []))
  , (133, ("full_sort_tmp", [i64], []))
  , (139, ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]))
  , (141, ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]))
  , (142, ("full_min_shrink_m6", [i64], []))
  , (143, ("full_deduce_1uip_m6", [i64], [i64]))
  , (144, ("full_min_shrink", [i64], []))
  , (145, ("full_deduce_1uip", [i64], [i64]))
  , (146, ("full_deduce_1uip_m6_hdr", [i64], [i64]))
  , (147, ("full_det_new_level", [i64, i64], [i64]))
  , (148, ("full_one_lit_confl", [i64], [i64]))
  , (149, ("full_eager_subsume", [i64, i64], []))
  , (150, ("full_learn_clause", [i64, i64], [i64]))
  , (155, ("full_restore_bump_ana_m5", [i64], []))
  , (156, ("full_analyze", [i64], [i64]))
  , (157, ("full_learn_clause_m6", [i64, i64], [i64]))
  , (158, ("full_analyze_core_m6", [i64], [i64]))
  , (182, ("full_extend", [i64], []))
  , (186, ("full_add_bin", [i64, i32, i32], [i64]))
  , (187, ("full_delete_binary", [i64, i32, i32], []))
  , (188, ("full_set_inactive", [i64, i32, i32], []))
  , (189, ("full_add_unit", [i64, i32], [.bool]))
  , (190, ("full_lucky_scan", [i64, .bool, .bool], [i64]))
  , (208, ("full_viv_best_implied_m6", [i64, i32], [i32]))
  , (212, ("full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64]))
  , (213, ("full_viv_sort_counts_m6", [i64, i32], []))
  , (215, ("full_viv_l0_simp_m6", [i64, i32, i32], [i64]))
  , (216, ("full_viv_reuse_prefix_m6", [i64, i32, i32], []))
  , (217, ("full_viv_clause_m6", [i64, i32], [i64]))
  , (218, ("full_viv_tier_match_m6", [i64, i32, i64], [.bool]))
  , (223, ("full_viv_clear_tier_m6", [i64, i64], []))
  , (225, ("full_viv_collect_fid", [i64, i64], [i64]))
  , (226, ("full_viv_count_fid", [i64, i64], []))
  , (227, ("full_viv_sort2_fid", [i64, i64, i64], []))
  , (228, ("full_viv_sort_fid", [i64, i64], []))
  , (229, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))
  , (230, ("full_vivify_m6_hdr", [i64], [i64]))
  , (231, ("full_prioritize_binaries_m6", [i64], [.bool]))
  , (232, ("full_backbone_sched_m6", [i64], [i64]))
  , (233, ("full_backbone_keep_m6", [i64, i64], []))
  , (237, ("full_backbone_round_m6", [i64, i64, .bool], [i64]))
  , (238, ("full_backbone_m6", [i64, i64], [i64]))
  , (240, ("full_trans_sort_m6", [i64, i64], []))
  , (241, ("full_transitive_m6", [i64, i64], [i64]))
  , (247, ("full_substitute", [i64], [i64]))
  , (248, ("full_enter_dense", [i64], [.bool]))
  , (249, ("full_sort_bin_watches_fid", [i64], []))
  , (250, ("full_rebuild_watches_nosort_fid", [i64], [i64]))
  , (252, ("full_cong_find", [i64, i32], [i32]))
  , (255, ("full_cong_unit_fold", [i64, i32, i32], [i64]))
  , (256, ("full_cong_equiv_fold", [i64, i32, i32, i32], [i64]))
  , (258, ("full_sort_u32", [i64, i32], []))
  , (263, ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64]))
  , (264, ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64]))
  , (265, ("full_cong_count_bins", [i64], []))
  , (267, ("full_cong_extract_binaries", [i64, i64], [i64]))
  , (268, ("full_cong_find_units_equivs", [i64], [i64]))
  , (269, ("full_cong_extract", [i64, i64, i64], [i64]))
  , (270, ("full_cong_and_match", [i64, i32, i32], [.bool]))
  , (271, ("full_cong_xor_match", [i64, i32, i32], [i32]))
  , (272, ("full_cong_enq_var", [i64, i64, i32], []))
  , (273, ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]))
  , (274, ("full_cong_work_step", [i64, i64, i64, i64, i32], [i64]))
  , (275, ("full_cong_worklist", [i64, i64, i64, i64], [i64]))
  , (278, ("full_cong_fwd_subsume", [i64, i64], [i64]))
  , (291, ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]))
  , (292, ("full_congruence_dense", [i64, i64], [i64]))
  , (316, ("full_m6_max_v", [i64], [i64]))
  , (318, ("full_k6_init", [i64, i32], []))
  , (321, ("full_k6_add_clause", [i64, i64, i32], [.bool]))
  , (331, ("full_m6_dense_prop", [i64], [.bool]))
  , (332, ("full_m6_sweep_cone", [i64, i32], [i64]))
  , (333, ("full_m6_sweep_refine_sig", [i64, i32, i32], []))
  , (335, ("full_m6_sweep_solve", [i64, i32, i64], [i64]))
  , (336, ("full_m6_sweep_flip_round", [i64, i32], [i32]))
  , (337, ("full_m6_sweep_sim", [i64, i32, i64], [i32]))
  , (348, ("full_m6_sweep_var", [i64, i32, i64], [i64]))
  , (350, ("full_m6_collect_cands", [i64], [i32]))
  , (351, ("full_m6_sweep_vars", [i64, i64, i64], [i64]))
  , (352, ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  , (353, ("full_fwd_dedup_bins", [i64], [.bool]))
  , (354, ("full_dense_prop_unit_m7", [i64, i32], [.bool]))
  , (355, ("full_dense_flush_units_m7", [i64], [.bool]))
  , (356, ("full_fwd_flush_large_m7", [i64], []))
  , (357, ("full_fwd_reconnect_irred_m7", [i64], []))
  , (359, ("full_fwd_check_cl_m7", [i64, i32], [.bool]))
  , (360, ("full_fwd_connect_subsumer_m7", [i64, i32], []))
  , (361, ("full_fwd_collect_sort_m7", [i64], [i64]))
  , (362, ("full_forward_sub_m7", [i64, i64], [i64]))
  , (363, ("full_bve_collect_m7", [i64, i32, i64, i32], [i32]))
  , (385, ("full_bve_gates_m7", [i64, i32, i32, i32], []))
  , (386, ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]))
  , (387, ("full_bve_weaken", [i64, i32, i32, i32], [.bool]))
  , (389, ("full_bve_commit_res", [i64, i64, i64], [i64]))
  , (390, ("full_bve_ext_need", [i64, i32, i32], [i64]))
  , (421, ("full_bve_gates_fid", [i64, i32, i32, i32], []))
  , (422, ("full_bve_var_m7", [i64, i32], [i64]))
  , (429, ("full_bva_steps_cap_fid", [i64], [i32]))
  , (431, ("full_fheap_up_fid", [i64, i64, i64, i32], []))
  , (432, ("full_fheap_down_fid", [i64, i64, i64, i32, i32], []))
  , (434, ("full_bva_connect_clauses_fid", [i64], []))
  , (441, ("full_bva_try_lit", [i64, i32, i64], [.bool]))
  , (444, ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32]))
  , (445, ("full_factor", [i64, i64], [i64]))
  , (446, ("full_compact_needed", [i64], [.bool]))
  , (458, ("full_compact", [i64], [i64]))
  , (481, ("full_m7_get64", [i64, i64], [i64]))
  , (482, ("full_m7_set64", [i64, i64, i64], []))
  , (488, ("full_lucky_late_m7", [i64], [i64]))
  , (492, ("full_ema_swap_m7", [i64, i64, i64], []))
  , (493, ("full_switch_mode_m7", [i64], []))
  , (494, ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
  , (496, ("full_probe_m6", [i64, .bool], [i64]))
  , (497, ("full_preprocess_m6", [i64], [i64])) ]

/-- The `7` base Step-10 specs modified in Step 12. -/
def fidStep12Bad : List Sym :=
  [ "full_ingest_cl"
  , "full_viv_collect_fid"
  , "full_cong_extract"
  , "full_cong_and_match"
  , "full_cong_enq_var"
  , "full_cong_eval_gate"
  , "full_cong_worklist" ]

/-- Ordered `12` `(new_name, anchor_name)` helper insertion pairs of `fidStep12Befores`. -/
def fidStep12BeforePairs : List (Sym × Sym) :=
  [ ("full_activate_lit_fid", "full_ingest_cl")
  , ("full_tumble_finish_fid", "full_parse_body_m6")
  , ("full_extend_core_fid", "full_extend")
  , ("full_unperm_fid", "full_extend")
  , ("full_lucky_ord_fid", "full_lucky_scan")
  , ("full_backtrack_ac_fid", "full_ana_failed_lit_m6_hdr")
  , ("full_cong_extract_and_clause_fid", "full_cong_extract")
  , ("full_cong_extract_from_fid", "full_cong_extract")
  , ("full_bve_weaken_unit_fid", "full_bve_var_m7")
  , ("full_watch_pop_c0", "full_add_clause")
  , ("full_reduce_purge_c0", "full_learn_clause_m6")
  , ("full_viv_sift_counts_m6", "full_viv_sort_counts_m6") ]

/-- Ordered `12` inserted helper names matching `fidStep12Befores`. -/
def fidStep12BeforeNames : List Sym :=
  fidStep12BeforePairs.map Prod.fst

/-- Exact pure `(name, as, rs)` signature list for all `46` replacements in `fidStep12Repls`. -/
def fidStep12ReplSigs : List SigEntry :=
  [ ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool])
  , ("full_ana_failed_lit_m6_hdr", [i64], [i64])
  , ("full_min_shrink_m6", [i64], [])
  , ("full_analyze", [i64], [i64])
  , ("full_analyze_core_m6", [i64], [i64])
  , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])
  , ("full_switch_mode_m7", [i64], [])
  , ("full_preprocess_m6", [i64], [i64])
  , ("full_zero_tables2", [i64], [])
  , ("full_init_hdr", [i64, i64, i64, i64], [])
  , ("full_ingest_cl", [i64, i64], [i64])
  , ("full_parse_body_m6", [i64, i64], [i64])
  , ("full_extend", [i64], [])
  , ("full_lucky_scan", [i64, .bool, .bool], [i64])
  , ("full_m6_sweep_cone", [i64, i32], [i64])
  , ("full_save_target_best", [i64], [])
  , ("full_backtrack", [i64, i64], [])
  , ("full_deduce_1uip_m6", [i64], [i64])
  , ("full_deduce_1uip_m6_hdr", [i64], [i64])
  , ("full_one_lit_confl", [i64], [i64])
  , ("full_learn_clause", [i64, i64], [i64])
  , ("full_viv_collect_fid", [i64, i64], [i64])
  , ("full_viv_sort2_fid", [i64, i64, i64], [])
  , ("full_viv_sort_fid", [i64, i64], [])
  , ("full_viv_clause_m6", [i64, i32], [i64])
  , ("full_cong_extract", [i64, i64, i64], [i64])
  , ("full_cong_and_match", [i64, i32, i32], [.bool])
  , ("full_cong_enq_var", [i64, i64, i32], [])
  , ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64])
  , ("full_cong_worklist", [i64, i64, i64, i64], [i64])
  , ("full_congruence_dense", [i64, i64], [i64])
  , ("full_backbone_sched_m6", [i64], [i64])
  , ("full_backbone_m6", [i64, i64], [i64])
  , ("full_dense_prop_unit_m7", [i64, i32], [.bool])
  , ("full_forward_sub_m7", [i64, i64], [i64])
  , ("full_bve_commit_res", [i64, i64, i64], [i64])
  , ("full_bve_var_m7", [i64, i32], [i64])
  , ("full_add_clause", [i64, i32, i32, .bool], [i64])
  , ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64])
  , ("full_learn_clause_m6", [i64, i64], [i64])
  , ("full_viv_sort_counts_m6", [i64, i32], [])
  , ("full_trans_sort_m6", [i64, i64], [])
  , ("full_m6_sweep_sim", [i64, i32, i64], [i32])
  , ("full_m6_sweep_vars", [i64, i64, i64], [i64])
  , ("full_factor", [i64, i64], [i64])
  , ("full_probe_m6", [i64, .bool], [i64]) ]

/-- Skip list for `checkNoCallBad` over Step-10 functions. -/
def fidStep12NoCallSkip : List Sym :=
  "full_cong_work_step" :: fidStep12Repls.map Fn.name

end

public section

theorem fidStep12_externs_empty : fidStep12Module.externs = [] :=
  fidStep10_externs_empty

theorem fidStep12_frontNames_eq :
    fidStep12Bundle.frontTable.map SpecEntry.name = fidStep12FrontNames :=
  rfl

private theorem fidStep12_befores_not_in10 :
    fidStep12BeforeNames.all (fun nm => !(fidStep10FnNames.contains nm)) = true := by
  t_kernel_rfl

private theorem fidStep12BeforePairs_anchor_eq :
    ∀ {x y1 y2 : Sym},
      (x, y1) ∈ fidStep12BeforePairs → (x, y2) ∈ fidStep12BeforePairs → y1 = y2 := by
  have hall : fidStep12BeforePairs.all (fun p =>
      fidStep12BeforePairs.all (fun q => !(p.1 == q.1) || (p.2 == q.2))) = true := by
    decide
  intro x y1 y2 hp1 hp2
  have hchk := List.all_eq_true.mp (List.all_eq_true.mp hall (x, y1) hp1) (x, y2) hp2
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at hchk
  exact hchk.elim (fun hne => absurd rfl hne) (fun h => h)

private theorem mem_fidStep12PatchStr {x y : Sym} (hx : x ∈ fidStep12PatchStr y) :
    x = y ∨ (x, y) ∈ fidStep12BeforePairs := by
  unfold fidStep12PatchStr at hx
  split at hx
  · rename_i h; have := beq_iff_eq.mp h; subst this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
  · split at hx
    · rename_i _ h; have := beq_iff_eq.mp h; subst this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
    · split at hx
      · rename_i _ _ h; have := beq_iff_eq.mp h; subst this
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
      · split at hx
        · rename_i _ _ _ h; have := beq_iff_eq.mp h; subst this
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
        · split at hx
          · rename_i _ _ _ _ h; have := beq_iff_eq.mp h; subst this
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
          · split at hx
            · rename_i _ _ _ _ _ h; have := beq_iff_eq.mp h; subst this
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl <;>
                (first | exact Or.inl rfl | exact Or.inr (by decide))
            · split at hx
              · rename_i _ _ _ _ _ _ h; have := beq_iff_eq.mp h; subst this
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
              · split at hx
                · rename_i _ _ _ _ _ _ _ h; have := beq_iff_eq.mp h; subst this
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                  rcases hx with rfl | rfl <;> (first | exact Or.inl rfl | exact Or.inr (by decide))
                · split at hx
                  · rename_i _ _ _ _ _ _ _ _ h; have := beq_iff_eq.mp h; subst this
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl <;>
                      (first | exact Or.inl rfl | exact Or.inr (by decide))
                  · split at hx
                    · rename_i _ _ _ _ _ _ _ _ _ h; have := beq_iff_eq.mp h; subst this
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                      rcases hx with rfl | rfl <;>
                        (first | exact Or.inl rfl | exact Or.inr (by decide))
                    · simp only [List.mem_singleton] at hx; exact Or.inl hx

private theorem mem_flatMap_fidStep12PatchStr {x : Sym} {nms : List Sym}
    (hx : x ∈ nms.flatMap fidStep12PatchStr) :
    x ∈ nms ∨ ∃ y ∈ nms, (x, y) ∈ fidStep12BeforePairs := by
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  rcases mem_fidStep12PatchStr hxy with rfl | hp
  · exact Or.inl hy
  · exact Or.inr ⟨y, hy, hp⟩

private theorem nodup_fidStep12PatchStr (nm : Sym) : (fidStep12PatchStr nm).Nodup := by
  unfold fidStep12PatchStr
  split
  · rename_i h; rw [beq_iff_eq.mp h]; decide
  · split
    · rename_i _ h; rw [beq_iff_eq.mp h]; decide
    · split
      · rename_i _ _ h; rw [beq_iff_eq.mp h]; decide
      · split
        · rename_i _ _ _ h; rw [beq_iff_eq.mp h]; decide
        · split
          · rename_i _ _ _ _ h; rw [beq_iff_eq.mp h]; decide
          · split
            · rename_i _ _ _ _ _ h; rw [beq_iff_eq.mp h]; decide
            · split
              · rename_i _ _ _ _ _ _ h; rw [beq_iff_eq.mp h]; decide
              · split
                · rename_i _ _ _ _ _ _ _ h; rw [beq_iff_eq.mp h]; decide
                · split
                  · rename_i _ _ _ _ _ _ _ _ h; rw [beq_iff_eq.mp h]; decide
                  · split
                    · rename_i _ _ _ _ _ _ _ _ _ h; rw [beq_iff_eq.mp h]; decide
                    · simp

private theorem nodup_flatMap_fidStep12PatchStr :
    ∀ {nms : List Sym}, nms.Nodup → (∀ p ∈ fidStep12BeforePairs, p.1 ∉ nms) →
      (nms.flatMap fidStep12PatchStr).Nodup
  | [], _, _ => List.nodup_nil
  | nm :: nms, hnd, hnot => by
    have ⟨hnm, hnd'⟩ := List.nodup_cons.mp hnd
    have hnot' : ∀ p ∈ fidStep12BeforePairs, p.1 ∉ nms := fun p hp hm =>
      hnot p hp (List.mem_cons_of_mem _ hm)
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_fidStep12PatchStr nm, nodup_flatMap_fidStep12PatchStr hnd' hnot',
      fun x hx y hy heq => ?_⟩
    subst heq
    rcases mem_fidStep12PatchStr hx with rfl | hpx
    · rcases mem_flatMap_fidStep12PatchStr hy with hyn | ⟨z, _, hpz⟩
      · exact hnm hyn
      · exact hnot (x, z) hpz List.mem_cons_self
    · rcases mem_flatMap_fidStep12PatchStr hy with hyn | ⟨z, hz, hpz⟩
      · exact hnot (x, nm) hpx (List.mem_cons_of_mem _ hyn)
      · have heq := fidStep12BeforePairs_anchor_eq hpx hpz
        subst heq; exact hnm hz

theorem fidStep12_front_nodup :
    (fidStep12Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep12_frontNames_eq]
  decide

private theorem patchFns_map_name_12 (repls : List Fn) :
    ∀ (fs : List Fn),
      (patchFns repls fidStep12Befores fs).map Fn.name =
        (fs.map Fn.name).flatMap fidStep12PatchStr
  | [] => rfl
  | f :: fs => by
    have hnm : ((repls.find? (·.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (·.name == f.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)
    have hl : patchFns repls fidStep12Befores (f :: fs) =
        patchInsAt fidStep12Befores f ++ [(repls.find? (·.name == f.name)).getD f] ++
          patchFns repls fidStep12Befores fs := rfl
    have hbef : (patchInsAt fidStep12Befores f).map Fn.name ++ [f.name] =
        fidStep12PatchStr f.name := by
      unfold patchInsAt fidStep12Befores fidStep11TumBefores fidStep12BBefores fidStep12CBefores
        fidStep12BCongBefores fidStep12BBveFwdBefores fidStep12PatchStr
      simp only [List.cons_append, List.nil_append, List.find?]
      by_cases h1 : f.name = "full_ingest_cl"
      · simp [h1, fidStep11ActivateLitFn]
      · by_cases h2 : f.name = "full_parse_body_m6"
        · simp [h2, fidStep11TumbleFinishFn]
        · by_cases h3 : f.name = "full_extend"
          · simp [h3, fidStep11ExtendCoreFn, fidStep11UnpermFn]
          · by_cases h4 : f.name = "full_lucky_scan"
            · simp [h4, fidStep11LuckyOrdFn]
            · by_cases h5 : f.name = "full_ana_failed_lit_m6_hdr"
              · simp [h5, FullFidelityBacktrackCs.fid11BacktrackAcFn]
              · by_cases h6 : f.name = "full_cong_extract"
                · simp [h6, fidStep12BCongExtractAndClauseFn, fidStep12BCongExtractFromFn]
                · by_cases h7 : f.name = "full_bve_var_m7"
                  · simp [h7, fidStep12BBveWeakenUnitFn]
                  · by_cases h8 : f.name = "full_add_clause"
                    · simp [h8, fidStep12CWatchPopFn, FullM7V2Robust.v2rWatchPopFn]
                    · by_cases h9 : f.name = "full_learn_clause_m6"
                      · simp [h9, fidStep12CReducePurgeFn, FullM7V2Robust.v2rReducePurgeFn]
                      · by_cases h10 : f.name = "full_viv_sort_counts_m6"
                        · simp [h10, fidStep12CVivSiftCountsM6Fn]
                        · simp [beq_false_of_ne (Ne.symm h1), beq_false_of_ne h1,
                            beq_false_of_ne (Ne.symm h2), beq_false_of_ne h2,
                            beq_false_of_ne (Ne.symm h3), beq_false_of_ne h3,
                            beq_false_of_ne (Ne.symm h4), beq_false_of_ne h4,
                            beq_false_of_ne (Ne.symm h5), beq_false_of_ne h5,
                            beq_false_of_ne (Ne.symm h6), beq_false_of_ne h6,
                            beq_false_of_ne (Ne.symm h7), beq_false_of_ne h7,
                            beq_false_of_ne (Ne.symm h8), beq_false_of_ne h8,
                            beq_false_of_ne (Ne.symm h9), beq_false_of_ne h9,
                            beq_false_of_ne (Ne.symm h10), beq_false_of_ne h10]
    rw [List.map_cons, List.flatMap_cons, hl, List.map_append, List.map_append,
      List.map_singleton, hnm, hbef, patchFns_map_name_12 repls fs]

theorem fidStep12Module_map_name :
    fidStep12Module.fns.map Fn.name = fidStep12FnNames := by
  rw [fidStep12Module_fns, fidStep12Fns, patchFns_map_name_12, ← fidStep10Fns_eq,
    fidStep10Module_map_name]
  rfl

theorem fidStep12Fns_length : fidStep12Fns.length = 517 := by
  rw [← List.length_map Fn.name, ← fidStep12Module_fns, fidStep12Module_map_name]
  t_kernel_rfl

private theorem fidStep12FnNames_nodup : fidStep12FnNames.Nodup := by
  have hnd10 : fidStep10FnNames.Nodup := by
    rw [← fidStep10Module_map_name]
    exact module_fns_namesNodup fidStep10Module_names_nodup
  refine nodup_flatMap_fidStep12PatchStr hnd10 fun p hp hm => ?_
  have hnb := List.all_eq_true.mp fidStep12_befores_not_in10 p.1
    (List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [List.contains_iff_mem.mpr hm] at hnb
  cases hnb

theorem fidStep12Module_names_nodup : fidStep12Module.namesNodup := by
  change (fidStep12Module.fns.map Fn.name ++ fidStep12Module.externs.map Extern.name).Nodup
  rw [fidStep12_externs_empty, List.map_nil, List.append_nil, fidStep12Module_map_name]
  exact fidStep12FnNames_nodup

private def step7To10Slot12 (k : Nat) : Nat :=
  let i9 := k + (if k ≤ 42 then 0 else if k ≤ 84 then 1 else if k ≤ 247 then 2 else 3)
  if i9 ≤ 157 then i9 else i9 + 1

private theorem fidStep10_from_step7_ok :
    fidStep10_step12_sigPairs.all (fun q =>
      (q == (157, ("full_learn_clause_m6", [i64, i64], [i64]))) ||
      (q == (158, ("full_analyze_core_m6", [i64], [i64]))) ||
      (q == (226, ("full_viv_count_fid", [i64, i64], []))) ||
      (q == (250, ("full_rebuild_watches_nosort_fid", [i64], [i64]))) ||
      (q == (444, ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32]))) ||
      fidStep7_step12_sigPairs.any (fun p =>
        (step7To10Slot12 p.1 == q.1) && (p.2 == q.2) &&
        (p.2.1 != "full_bva_upd_lit_fid") &&
        (p.2.1 != "full_zero_tables1") &&
        (p.2.1 != "full_prop_flush_del_fid") &&
        (p.2.1 != "full_rebuild_watches") &&
        (p.2.1 != "full_analyze_core_m6"))) = true := by
  t_kernel_rfl

theorem fidStep10_step12_sig_at {p : Nat × SigEntry}
    (hp : p ∈ fidStep10_step12_sigPairs) :
    fidStep10Module.fns[p.1]?.map Fn.sig = some p.2 := by
  have hall := List.all_eq_true.mp fidStep10_from_step7_ok p hp
  rcases Bool.or_eq_true _ _ |>.mp hall with h12345 | h7
  · rcases Bool.or_eq_true _ _ |>.mp h12345 with h1234 | h5
    · rcases Bool.or_eq_true _ _ |>.mp h1234 with h123 | h4
      · rcases Bool.or_eq_true _ _ |>.mp h123 with h12 | h3
        · rcases Bool.or_eq_true _ _ |>.mp h12 with h1 | h2
          · rw [beq_iff_eq.mp h1]; exact fidStep10_slot_learnAndCore.1
          · rw [beq_iff_eq.mp h2]; exact fidStep10_slot_learnAndCore.2
        · rw [beq_iff_eq.mp h3]
          exact fidStep10_step11_sig_at (p := (226, ("full_viv_count_fid", [i64, i64], [])))
            (by decide)
      · rw [beq_iff_eq.mp h4]; exact fidStep10_slot_rebuildWatchesNosort
    · rw [beq_iff_eq.mp h5]; exact fidStep10_slot_bvaUpdLit
  · obtain ⟨q, hq, hchk⟩ := List.any_eq_true.mp h7
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨⟨⟨hsl, hsig⟩, hbva⟩, hz1⟩, hpf⟩, hrb⟩, hac⟩
    have h8 := fidStep8_step12_sig_at hq
    have h9 := fidStep9_slot_of_step8 h8 hbva ⟨hz1, hpf, hrb⟩ rfl
    have h10 := fidStep10_slot_of_step9 h9 hac rfl
    rw [← hsl, ← hsig]
    exact h10

theorem fidStep10_sig_at_mem {j : Nat} {s : SigEntry}
    (hp : (j, s) ∈ fidStep10_step12_sigPairs) :
    ∃ g ∈ fidStep10Module.fns, fidStep10Module.fns[j]? = some g ∧ g.sig = s := by
  have hs := fidStep10_step12_sig_at hp
  cases hg : fidStep10Module.fns[j]? with
  | none => simp [hg] at hs
  | some g =>
    simp only [hg, Option.map_some, Option.some.injEq] at hs
    exact ⟨g, List.mem_of_getElem? hg, rfl, hs⟩

private theorem fidStep12Repls_map_sig :
    fidStep12Repls.map Fn.sig = fidStep12ReplSigs := by
  t_kernel_rfl

private theorem fidStep12Repls_checkSigs :
    fidStep12ReplSigs.all (fun s => fidStep10_step12_sigPairs.any (fun p => p.2 == s)) =
      true := by
  t_kernel_rfl

theorem fidStep12Module_replSigs_ok :
    ∀ r ∈ fidStep12Repls, ∀ g ∈ fidStep10Module.fns,
      r.name = g.name → r.sig = g.sig := by
  have hnd := module_fns_namesNodup fidStep10Module_names_nodup
  intro r hr g hg hnm
  have hrsig : r.sig ∈ fidStep12ReplSigs := fidStep12Repls_map_sig ▸ List.mem_map_of_mem hr
  have hany : fidStep10_step12_sigPairs.any (fun p => p.2 == r.sig) = true :=
    List.all_eq_true.mp fidStep12Repls_checkSigs r.sig hrsig
  obtain ⟨⟨j, s⟩, hmem, hbeq⟩ := List.any_eq_true.mp hany
  have hrs : s = r.sig := beq_iff_eq.mp hbeq
  obtain ⟨g0, hg0, _, hsg⟩ := fidStep10_sig_at_mem hmem
  have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.symm.trans hsg.symm)
  rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans hgnm), hsg, hrs]

theorem fidStep10_noCallBad {fn : Fn} (hmem : fn ∈ fidStep10Module.fns)
    (hnskip : !(fidStep12NoCallSkip.contains fn.name) = true) :
    noCallInFn fidStep12Bad fn = true := by
  have hit := List.all_eq_true.mp fidStep10_s12_noCallBad fn hmem
  have hsk : fidS12SkipNames = fidStep12NoCallSkip := rfl
  have hbd : fidS12BadNames = fidStep12Bad := rfl
  rw [hsk, hbd] at hit
  rcases (Bool.or_eq_true _ _).mp hit with hskip | hok
  · rw [hskip] at hnskip; cases hnskip
  · exact hok

theorem fidStep10_workStep_eq {f0 : Fn} (hf0 : f0 ∈ fidStep10Module.fns)
    (hnm : f0.name = "full_cong_work_step") : f0 = full_cong_work_step :=
  nodup_name_eq Fn.name (module_fns_namesNodup fidStep10Module_names_nodup)
    hf0 (List.mem_of_getElem? fidStep10_workStep_at) hnm

theorem nodup_getElem?_inj_12 {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : xs[j]? = some a) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    have ⟨hnmem, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj; subst hi
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨j, hj⟩))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj; subst hj
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      | succ j => simp at hi hj; exact congrArg Nat.succ (ih hnd' hi hj)

private theorem drop_eq_cons_12 {α : Type _} :
    ∀ {xs : List α} {i : Nat} {x : α}, xs[i]? = some x → xs.drop i = x :: xs.drop (i + 1)
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by simp at h; simp [h]
  | _ :: xs, i + 1, _, h => drop_eq_cons_12 (xs := xs) (i := i) h

private theorem split_append_cons_12 {α : Type _} {xs : List α} {x y : α} {zs pre post : List α}
    (h : xs ++ y :: zs = pre ++ x :: post) :
    (∃ iPre iPost, xs = iPre ++ x :: iPost ∧ pre = iPre) ∨
    (x = y ∧ pre = xs) ∨
    (∃ tPre, zs = tPre ++ x :: post ∧ pre = xs ++ y :: tPre) := by
  by_cases hlt : pre.length < xs.length
  · have hpre_eq : pre = xs.take pre.length := by
      have ht := congrArg (List.take pre.length) h
      simpa [List.take_left', List.take_append_of_le_length (Nat.le_of_lt hlt)] using ht.symm
    have hget : xs[pre.length]? = some x := by
      have hg := congrArg (·[pre.length]?) h
      simpa [List.getElem?_append_left hlt] using hg
    have hx_split : xs = xs.take pre.length ++ x :: xs.drop (pre.length + 1) := by
      have hd := List.take_append_drop pre.length xs
      have hdrop : xs.drop pre.length = x :: xs.drop (pre.length + 1) := drop_eq_cons_12 hget
      simpa [hdrop] using hd.symm
    exact Or.inl ⟨xs.take pre.length, xs.drop (pre.length + 1), hx_split, hpre_eq⟩
  · have hge : xs.length ≤ pre.length := Nat.not_lt.mp hlt
    by_cases heq : pre.length = xs.length
    · have hpre_eq : pre = xs := by
        have ht := congrArg (List.take pre.length) h
        simpa [List.take_left', heq] using ht.symm
      have hget : x = y := by
        have hg := congrArg (·[xs.length]?) h
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero] at hg
        have hg2 : (pre ++ x :: post)[pre.length]? = some x := by simp
        rw [← heq, hg2] at hg
        exact (Option.some.inj hg).symm
      exact Or.inr (Or.inl ⟨hget, hpre_eq⟩)
    · have hgt : xs.length < pre.length := by omega
      have htake_pre : pre.take (xs.length + 1) = xs ++ [y] := by
        have ht := congrArg (List.take (xs.length + 1)) h
        have hL : (xs ++ y :: zs).take (xs.length + 1) = xs ++ [y] := by
          have : xs ++ y :: zs = (xs ++ [y]) ++ zs := by simp [List.append_assoc]
          rw [this, List.take_left' (by simp)]
        have hR : (pre ++ x :: post).take (xs.length + 1) = pre.take (xs.length + 1) := by
          rw [List.take_append_of_le_length hgt]
        exact hR.symm.trans (ht.symm.trans hL)
      have hpre_eq : pre = xs ++ y :: pre.drop (xs.length + 1) := by
        have hd := List.take_append_drop (xs.length + 1) pre
        rw [htake_pre, List.append_assoc, List.singleton_append] at hd
        exact hd.symm
      rw [hpre_eq, List.append_assoc, List.cons_append] at h
      have h1 := List.append_cancel_left h
      have h2 := (List.cons.inj h1).2
      exact Or.inr (Or.inr ⟨pre.drop (xs.length + 1), h2, hpre_eq⟩)

theorem patchFns_split_12 {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs pre post : List Fn} {fn : Fn}
    (hsplit : patchFns repls befores fs = pre ++ fn :: post) :
    ∃ bPre f0 bPost, fs = bPre ++ f0 :: bPost ∧
      ((∃ iPre iPost, patchInsAt befores f0 = iPre ++ fn :: iPost ∧
          ∀ s, s ∈ (patchFns repls befores bPre ++ iPre).map Fn.sig → s ∈ pre.map Fn.sig) ∨
       (fn = (repls.find? (·.name == f0.name)).getD f0 ∧
          ∀ s, s ∈ (patchFns repls befores bPre ++ patchInsAt befores f0).map Fn.sig →
            s ∈ pre.map Fn.sig)) := by
  induction fs generalizing pre with
  | nil => simp [patchFns] at hsplit
  | cons f fs ih =>
    have hcons : patchFns repls befores (f :: fs) =
        patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f] ++
          patchFns repls befores fs := by
      simp [patchFns]
    rw [hcons, List.append_assoc, List.singleton_append] at hsplit
    rcases split_append_cons_12 hsplit with
      ⟨iPre, iPost, hi, hpreEq⟩ | ⟨hr, rfl⟩ | ⟨preRest, htail, rfl⟩
    · subst hpreEq
      refine ⟨[], f, fs, rfl, Or.inl ⟨pre, iPost, hi, fun s hs => ?_⟩⟩
      simpa [patchFns] using hs
    · refine ⟨[], f, fs, rfl, Or.inr ⟨hr, fun s hs => ?_⟩⟩
      simpa [patchFns] using hs
    · obtain ⟨bPre', f0, bPost, hfs_eq, hcase⟩ := ih htail
      refine ⟨f :: bPre', f0, bPost, by rw [hfs_eq, List.cons_append], ?_⟩
      have hcons' : patchFns repls befores (f :: bPre') =
          patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f] ++
            patchFns repls befores bPre' := by
        simp [patchFns]
      rcases hcase with ⟨iPre, iPost, hi, hpreM⟩ | ⟨hr', hpreM⟩
      · refine Or.inl ⟨iPre, iPost, hi, fun s hs => ?_⟩
        rw [List.map_append, List.mem_append, hcons'] at hs
        rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        rcases hs with hA | h3
        · simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton] at hA
          rcases hA with (h1 | hcur) | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inl hcur)
          · exact Or.inr (Or.inr (hpreM s (by
              rw [List.map_append, List.mem_append]; exact Or.inl h2)))
        · exact Or.inr (Or.inr (hpreM s (by
            rw [List.map_append, List.mem_append]; exact Or.inr h3)))
      · refine Or.inr ⟨hr', fun s hs => ?_⟩
        rw [List.map_append, List.mem_append, hcons'] at hs
        rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        rcases hs with hA | h3
        · simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton] at hA
          rcases hA with (h1 | hcur) | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inl hcur)
          · exact Or.inr (Or.inr (hpreM s (by
              rw [List.map_append, List.mem_append]; exact Or.inl h2)))
        · exact Or.inr (Or.inr (hpreM s (by
            rw [List.map_append, List.mem_append]; exact Or.inr h3)))

theorem patchFns_sig_preserved12 {bPre : List Fn}
    (hsub : ∀ f ∈ bPre, f ∈ fidStep10Module.fns) {f : Fn} (hf : f ∈ bPre) :
    f.sig ∈ (patchFns fidStep12Repls fidStep12Befores bPre).map Fn.sig := by
  have hmem : (fidStep12Repls.find? (·.name == f.name)).getD f ∈
      patchFns fidStep12Repls fidStep12Befores bPre := by
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨f, hf, Or.inr rfl⟩
  have hsig : ((fidStep12Repls.find? (·.name == f.name)).getD f).sig = f.sig := by
    cases hr : fidStep12Repls.find? (·.name == f.name) with
    | none => rfl
    | some r =>
      have hrnm : r.name = f.name :=
        beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hr)
      exact fidStep12Module_replSigs_ok r (List.mem_of_find?_eq_some hr) f (hsub f hf) hrnm
  exact hsig ▸ List.mem_map_of_mem hmem

theorem fidStep12_slot_eq_len {bPre bPost : List Fn} {f0 : Fn} {slot : Nat}
    {sf0 : SigEntry} (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hs : (slot, sf0) ∈ fidStep10_step12_sigPairs) (hf0 : f0.name = sf0.1) :
    bPre.length = slot := by
  obtain ⟨g0, _, hg0, hsg0⟩ := fidStep10_sig_at_mem hs
  have h1 : (fidStep10Module.fns.map Fn.name)[bPre.length]? = some sf0.1 := by
    rw [hfs]; simp [hf0]
  have h2 : (fidStep10Module.fns.map Fn.name)[slot]? = some sf0.1 := by
    simp [List.getElem?_map, hg0, ← hsg0, Fn.sig]
  exact nodup_getElem?_inj_12 (module_fns_namesNodup fidStep10Module_names_nodup) h1 h2

theorem fidStep12_base_sig_in_patch {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    {j : Nat} {s : SigEntry} (hs : (j, s) ∈ fidStep10_step12_sigPairs)
    (hlt : j < bPre.length) :
    s ∈ (patchFns fidStep12Repls fidStep12Befores bPre).map Fn.sig := by
  obtain ⟨g, _, hgi, hsg⟩ := fidStep10_sig_at_mem hs
  have hgb : bPre[j]? = some g := by rwa [hfs, List.getElem?_append_left hlt] at hgi
  have hsub : ∀ f ∈ bPre, f ∈ fidStep10Module.fns := fun f hf => hfs ▸ List.mem_append_left _ hf
  exact hsg ▸ patchFns_sig_preserved12 hsub (List.mem_of_getElem? hgb)

theorem fidStep12_before_sig_in_patch {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    {j : Nat} {s : SigEntry} (hs : (j, s) ∈ fidStep10_step12_sigPairs)
    (hlt : j < bPre.length) {ins : Fn}
    (hins : fidStep12Befores.find? (·.1 == s.1) = some (s.1, [ins]) ∨
      ∃ ps, fidStep12Befores.find? (·.1 == s.1) = some (s.1, ps) ∧ ins ∈ ps) :
    ins.sig ∈ (patchFns fidStep12Repls fidStep12Befores bPre).map Fn.sig := by
  obtain ⟨g, _, hgi, hsg⟩ := fidStep10_sig_at_mem hs
  have hgb : bPre[j]? = some g := by rwa [hfs, List.getElem?_append_left hlt] at hgi
  have hgnm : g.name = s.1 := congrArg Prod.fst hsg
  have hins_mem : ins ∈ patchInsAt fidStep12Befores g := by
    unfold patchInsAt
    rcases hins with h | ⟨ps, h, hp⟩
    · simp [hgnm, h]
    · simp [hgnm, h, hp]
  have hmem : ins ∈ patchFns fidStep12Repls fidStep12Befores bPre := by
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨g, List.mem_of_getElem? hgb, Or.inl hins_mem⟩
  exact List.mem_map_of_mem hmem

theorem fidStep12_slot_lt_of {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    {tgt : Sym} (hf0 : f0.name = tgt) (j : Nat) {d : SigEntry}
    (hchk : (fidStep10_step12_sigPairs.find? (·.2.1 == tgt)).elim false
      (fun s => (fidStep10_step12_sigPairs.find? (·.1 == j)).elim false
        (fun dj => decide (dj.1 < s.1) && (dj.2 == d))) = true) :
    (j, d) ∈ fidStep10_step12_sigPairs ∧ j < bPre.length := by
  cases h1 : fidStep10_step12_sigPairs.find? (·.2.1 == tgt) with
  | none => simp [h1] at hchk
  | some s =>
    cases h2 : fidStep10_step12_sigPairs.find? (·.1 == j) with
    | none => simp [h1, h2] at hchk
    | some dj =>
      simp only [h1, h2, Option.elim_some, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hchk
      have hs_mem := List.mem_of_find?_eq_some h1
      have hsnm : s.2.1 = tgt :=
        beq_iff_eq.mp (List.find?_some (p := fun q : Nat × SigEntry => q.2.1 == tgt) h1)
      have hj_eq : dj.1 = j :=
        beq_iff_eq.mp (List.find?_some (p := fun q : Nat × SigEntry => q.1 == j) h2)
      have hd_mem : (j, d) ∈ fidStep10_step12_sigPairs := by
        rcases dj with ⟨dj1, dj2⟩
        simp only at hj_eq hchk
        rw [← hj_eq, ← hchk.2]
        exact List.mem_of_find?_eq_some h2
      exact ⟨hd_mem,
        (fidStep12_slot_eq_len hfs hs_mem (hf0.trans hsnm.symm)).symm ▸ hj_eq ▸ hchk.1⟩

theorem fidStep12_callsOk_of {fn : Fn} {deps : List SigEntry} {pre : List Fn}
    (hchk : fn.checkCallsOk deps [] = true) (hsub : ∀ d ∈ deps, d ∈ pre.map Fn.sig) :
    fn.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig)
      fidStep12Module.exits := by
  rw [fidStep12_noExit, fidStep12_externs_empty, List.map_nil, List.append_nil]
  exact fn_callsOk_mono hsub (Fn.callsOk_of_checkCallsOk hchk)

theorem fidStep12_front_none_of_names {nm : Sym}
    (hf12 : !(fidStep12FrontNames.contains nm) = true) :
    fidStep12Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : fidStep12FrontNames.contains nm = true :=
    List.contains_iff_mem.mpr
      (fidStep12_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he))
  have hnot : fidStep12FrontNames.contains nm = false := by
    cases hc : fidStep12FrontNames.contains nm
    · rfl
    · rw [hc] at hf12; cases hf12
  exact Bool.false_ne_true (hnot.symm.trans hm)

theorem fidStep12_front_none_of_repl_none {f0 : Fn} (hf0 : f0 ∈ fidStep10Module.fns)
    (hnotWs : f0.name ≠ "full_cong_work_step")
    (h : fidStep12Repls.find? (·.name == f0.name) = none) :
    fidStep12Bundle.frontTable.find? (·.name == f0.name) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = f0.name := beq_iff_eq.mp hbeq
  have hmem : e.name ∈ fidStep12FrontNames :=
    fidStep12_frontNames_eq ▸ List.mem_map_of_mem he
  rw [hnm] at hmem
  have hf0_in10 : f0.name ∈ fidStep10FnNames := by
    rw [← fidStep10Module_map_name]; exact List.mem_map_of_mem hf0
  have hbef_nm : (fidStep12Befores.flatMap Prod.snd).map Fn.name = fidStep12BeforeNames := by
    t_kernel_rfl
  have hfront_eq : fidStep12FrontNames =
      "full_cong_work_step" ::
        (fidStep12Repls.map Fn.name ++ (fidStep12Befores.flatMap Prod.snd).map Fn.name) :=
    rfl
  rw [hfront_eq, List.mem_cons, List.mem_append, List.mem_map, List.mem_map] at hmem
  rcases hmem with hws | ⟨r, hr, hrn⟩ | ⟨b, hb, hbn⟩
  · exact hnotWs hws
  · have hnone := List.find?_eq_none.mp h r hr
    simp [hrn] at hnone
  · have hbm : b.name ∈ fidStep12BeforeNames := hbef_nm ▸ List.mem_map_of_mem hb
    have hnb := List.all_eq_true.mp fidStep12_befores_not_in10 b.name hbm
    rw [hbn, List.contains_iff_mem.mpr hf0_in10] at hnb
    cases hnb

end

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

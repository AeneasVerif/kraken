/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Inline
public import LeanQbe.T.Examples.Kissat.Src.Full
import LeanQbe.T.FlatLemmas
import LeanQbe.T.MainLemmas

/-!
# Legacy-Free `418`-Fn Profile-Guided Inline Policy (`Src.InlPolicy`)

Clean, `Full*`-free, `PatchModule`-free, `Solver`-free PGO inline policy for
`Src.Full.kissatModule` (`418` live functions), matching Step-13 `OPT-9` Arm B + Tier A/B PGO
budgets filtered strictly to the `418` live functions in `Src.Full.kissatFns`:
* **Tier A (`full_analyze_rsn_m6_hdr => 480`)** and **Tier B (`f64u_round_pack => 240`)**.
* **Gate-G4-winning `OPT-9` Arm B**: `full_fwd_scan_lit_m7 => 260`,
  `full_save_target_best => 95`, and `full_add_unit => 0` (+ `"full_add_unit"` in
  `keepOutOfLine`).
* **Parity guards**: every named override and `keepOutOfLine` symbol exists in
  `Src.Full.kissatFns`, `kissatPgoBudget` agrees with `kissatPgoOverrides`, every out-of-line
  entry has budget `0`, and `kissatInlChunkPolicy.singleSiteMax = 0`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Src.InlPolicy

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Full

/-- Exact `154`-entry per-callee PGO override table for `Src.Full.kissatFns` (`418` live fns),
combining Step-13 Tier A/B (`full_analyze_rsn_m6_hdr => 480`, `f64u_round_pack => 240`),
`OPT-9` Arm B (`full_fwd_scan_lit_m7 => 260`, `full_save_target_best => 95`,
`full_add_unit => 0`), and live M6/M7/Fidelity PGO budgets in topological order. -/
@[expose] def kissatPgoOverrides : List (Sym × Nat) :=
  [ ("f64u_round_pack", 240)
  , ("kissat_skip_ws_comments", 45)
  , ("kissat_read_nat", 69)
  , ("kissat_next_lit", 235)
  , ("full_isqrt", 38)
  , ("full_tick_rel", 96)
  , ("full_scale_delta_m5", 101)
  , ("full_ema_update", 97)
  , ("full_scale_delta", 103)
  , ("full_fill_u64_m7", 40)
  , ("full_sort_u32", 162)
  , ("full_elim_dticks", 42)
  , ("full_m7_get64", 24)
  , ("full_m7_set64", 24)
  , ("full_arena_next", 55)
  , ("full_alloc_cl", 39)
  , ("full_wsort_sift", 65)
  , ("full_watch_push_slow_m6", 0)
  , ("full_watch_push_m6", 200)
  , ("full_watch_push", 220)
  , ("full_unwatch_large", 0)
  , ("full_has_bin", 86)
  , ("full_delete_bin_side", 102)
  , ("full_sort_bin_watches_fid", 110)
  , ("full_heap_up", 83)
  , ("full_heap_down", 113)
  , ("full_heap_push", 125)
  , ("full_heap_pop", 181)
  , ("full_assign_lvl", 180)
  , ("full_assign", 150)
  , ("full_save_target_best", 95)
  , ("full_backtrack", 64)
  , ("full_add_unit", 0)
  , ("m6_hdr_init", 0)
  , ("m6_ext_ensure_init", 75)
  , ("m6_hdr_sync_legacy_tiers", 30)
  , ("m6_hdr_update_tier_limits", 58)
  , ("m6_hdr_record_used", 60)
  , ("m6_hdr_delaying", 40)
  , ("m6_hdr_bump_delay", 82)
  , ("m6_hdr_reduce_delay", 48)
  , ("m6_hdr_get_watermark", 21)
  , ("m6_hdr_set_watermark", 21)
  , ("m6_hdr_dr_init", 60)
  , ("m6_hdr_dr_update", 109)
  , ("m6_hdr_dr_allow", 50)
  , ("full_rescale_m6", 36)
  , ("full_rescale", 38)
  , ("full_bump_var", 175)
  , ("full_queue_renumber", 46)
  , ("full_queue_mtf", 240)
  , ("full_ana_sift_m6", 77)
  , ("full_set_inactive", 53)
  , ("full_prop_flush_slow_fid", 0)
  , ("full_prop_flush_del_fid", 0)
  , ("full_flush_trail", 52)
  , ("full_lit_rank_m6", 30)
  , ("full_sweep_copy", 315)
  , ("full_move_red_pass2_m6", 74)
  , ("full_mark_reasons_m6", 87)
  , ("full_mark_reasons", 89)
  , ("full_compact_needed", 26)
  , ("full_compact_sift_q", 56)
  , ("full_compact_sift_h", 66)
  , ("full_red_less", 26)
  , ("full_red_sift", 103)
  , ("full_analyze_lit", 103)
  , ("full_analyze_rsn_m6_hdr", 480)
  , ("full_clear_ana", 30)
  , ("full_otfs_subsume", 130)
  , ("full_min_mark", 90)
  , ("full_shrink_lower_m8", 165)
  , ("full_det_new_level", 18)
  , ("full_decide_m7", 265)
  , ("m6_hdr_decide_fid", 130)
  , ("full_restart_due", 130)
  , ("full_restart", 95)
  , ("full_extend_push2", 97)
  , ("full_viv_unreason_m6", 39)
  , ("full_viv_watch_rank_m6", 34)
  , ("full_viv_best_watch_m6", 123)
  , ("full_viv_subsumes_bin_m6", 69)
  , ("full_viv_subsumes_cl_m6", 58)
  , ("full_viv_best_implied_m6", 41)
  , ("full_viv_inst_check_m6", 63)
  , ("full_viv_sort_counts_m6", 55)
  , ("full_viv_has_l0_m6", 39)
  , ("full_viv_l0_simp_m6", 52)
  , ("full_viv_reuse_prefix_m6", 120)
  , ("full_viv_tier_match_m6", 47)
  , ("full_backbone_unwind_m6", 33)
  , ("full_backbone_analyze_m6", 109)
  , ("full_tarjan_pop_scc", 118)
  , ("full_rebuild_watches_nosort_fid", 0)
  , ("full_rebuild_watches", 29)
  , ("full_m6_dense_prop", 44)
  , ("full_dense_flush_units_m7", 40)
  , ("full_cong_find", 52)
  , ("full_cong_mark_trail", 76)
  , ("full_cong_unit_fold", 72)
  , ("full_cong_emit_xor", 41)
  , ("full_cong_eb_match", 200)
  , ("full_cong_and_match", 105)
  , ("full_cong_enq_var", 85)
  , ("full_cong_sift_pairs_fid", 95)
  , ("full_cong_u64_sift_m7", 60)
  , ("full_cong_u64_sort_m7", 146)
  , ("full_cong_bsearch_u64_m7", 24)
  , ("full_congruence_dense", 0)
  , ("full_m6_max_v", 32)
  , ("full_k6_add_ticks", 18)
  , ("full_k6_init", 0)
  , ("full_k6_watch", 70)
  , ("full_k6_assign", 97)
  , ("full_k6_mtf", 177)
  , ("full_k6_backtrack", 137)
  , ("full_k6_flip", 290)
  , ("full_m6_sweep_refine_sig", 90)
  , ("full_m6_sweep_rand_phases", 110)
  , ("full_m6_sweep_solve", 115)
  , ("full_m6_sweep_rearm", 155)
  , ("full_fwd_scan_lit_m7", 260)
  , ("full_bve_get_tern_m7", 68)
  , ("full_bve_xor_pat_m7", 86)
  , ("full_bve_match_tern_m8", 115)
  , ("full_k6_watch_m7", 59)
  , ("full_k6_assign_m7", 84)
  , ("full_k6_backtrack_m7", 132)
  , ("full_bve_k6_mv_fid", 25)
  , ("full_fid_k6_add_ticks", 30)
  , ("full_k6_watch_fid", 90)
  , ("full_k6_assign_fid", 115)
  , ("full_k6_mtf_fid", 135)
  , ("full_k6_backtrack_fid", 120)
  , ("full_k6_ana_cl_fid", 145)
  , ("full_bve_def_k6_fid", 90)
  , ("full_bve_collect_m7", 90)
  , ("full_bve_ext_need", 31)
  , ("full_bve_var_key_m7", 68)
  , ("full_bve_heap_up_m7", 71)
  , ("full_bve_heap_down_m7", 99)
  , ("full_bva_steps_cap_fid", 20)
  , ("full_bva_clines_fid", 15)
  , ("full_fheap_up_fid", 55)
  , ("full_fheap_down_fid", 80)
  , ("full_bva_count_lit_deg_fid", 55)
  , ("full_bva_match_large_bva_fid", 70)
  , ("full_bva_pick_cand", 74)
  , ("full_reorder_sift_fid", 105)
  , ("full_walk_cb_inv_m7", 85)
  , ("full_walk_effort_m7", 38)
  , ("full_walk_break_m7", 87)
  , ("full_walk_flip_m7", 280)
  , ("full_walk_save_min_m7", 108) ]

/-- Per-callee PGO inline budget for `Src.Full.kissatModule` (`15` base threshold for
unlisted symbols; Step-13 `OPT-9` Arm B + Tier A/B budgets for live symbols). -/
@[expose] def kissatPgoBudget (s : Sym) : Nat :=
  (kissatPgoOverrides.find? (fun p => p.1 == s)).elim 15 Prod.snd

/-- Canonical legacy-free `InlinePolicy` for `Src.Full.kissatModule` (`maxCallerSize := 2800`,
`leafMax := 165`, `maxCalleeLoops := some 1`, `maxTotalDup := 1500`, `maxCallerCalls := 24`,
and `OPT-9` Arm B `full_add_unit` kept out of line). -/
@[expose] def kissatInlPolicy : InlinePolicy :=
  { budget := kissatPgoBudget
    leafMax := 165
    singleSiteMax := 0
    maxCallerSize := 2800
    maxCalleeCalls := 2
    maxCalleeLoops := some 1
    maxTotalDup := 1500
    requireLoopSite := false
    maxCallerCalls := 24
    keepOutOfLine :=
      [ "full_add_unit"
      , "m6_hdr_init"
      , "full_watch_push_slow_m6"
      , "full_prop_flush_slow_fid"
      , "full_prop_flush_del_fid"
      , "full_k6_init" ] }

/-- Zero-scan chunkable `InlinePolicy` matching `kissatInlPolicy`: sets `singleSiteMax := 0`,
`maxTotalDup := 0`, and `requireLoopSite := false` so `inlSiteCounts` and `inlLoopCounts`
reduce to `[]` in `O(1)` inside `inline_chunk_base!`. -/
@[expose] def kissatInlChunkPolicy : InlinePolicy :=
  { kissatInlPolicy with
    singleSiteMax := 0
    maxTotalDup := 0
    requireLoopSite := false }

private def memSymTR (s : Sym) : List Sym → Bool
  | [] => false
  | x :: xs => if s == x then true else memSymTR s xs

private theorem mem_of_memSymTR {s : Sym} : ∀ {xs : List Sym}, memSymTR s xs = true → s ∈ xs
  | [], h => by cases h
  | x :: xs, h => by
    dsimp only [memSymTR] at h
    split at h
    · rename_i heq
      rw [beq_iff_eq] at heq
      subst heq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_memSymTR h)

private def allOverridesLiveTR (live : List Sym) : List (Sym × Nat) → Bool
  | [] => true
  | p :: ps => if memSymTR p.1 live then allOverridesLiveTR live ps else false

private theorem allOverridesLive_of_TR (live : List Sym) :
    ∀ {ps : List (Sym × Nat)}, allOverridesLiveTR live ps = true →
      ∀ p ∈ ps, p.1 ∈ live
  | [], _, _, hp => nomatch hp
  | p :: ps, h, q, hq => by
    dsimp only [allOverridesLiveTR] at h
    split at h
    · rename_i hm
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact mem_of_memSymTR hm
      · exact allOverridesLive_of_TR live h q hq'
    · cases h

private def allBudgetsMatchTR : List (Sym × Nat) → Bool
  | [] => true
  | p :: ps => if kissatPgoBudget p.1 == p.2 then allBudgetsMatchTR ps else false

private theorem allBudgetsMatch_of_TR :
    ∀ {ps : List (Sym × Nat)}, allBudgetsMatchTR ps = true →
      ∀ p ∈ ps, kissatPgoBudget p.1 = p.2
  | [], _, _, hp => nomatch hp
  | p :: ps, h, q, hq => by
    dsimp only [allBudgetsMatchTR] at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact beq_iff_eq.mp heq
      · exact allBudgetsMatch_of_TR h q hq'
    · cases h

private def allKoolLiveTR (live : List Sym) : List Sym → Bool
  | [] => true
  | s :: ss =>
    if memSymTR s live then
      if kissatPgoBudget s == 0 then allKoolLiveTR live ss else false
    else false

private theorem allKoolLive_of_TR (live : List Sym) :
    ∀ {ss : List Sym}, allKoolLiveTR live ss = true →
      ∀ s ∈ ss, s ∈ live ∧ kissatPgoBudget s = 0
  | [], _, _, hs => nomatch hs
  | s :: ss, h, t, ht => by
    dsimp only [allKoolLiveTR] at h
    split at h
    · rename_i hm
      split at h
      · rename_i hz
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact ⟨mem_of_memSymTR hm, beq_iff_eq.mp hz⟩
        · exact allKoolLive_of_TR live h t ht'
      · cases h
    · cases h

private theorem kissatPgoOverrides_check_live :
    allOverridesLiveTR (kissatFns.map Fn.name) kissatPgoOverrides = true := by
  t_kernel_rfl

private theorem kissatPgoOverrides_check_nodup :
    stringsNodup (kissatPgoOverrides.map Prod.fst) = true := by
  t_kernel_rfl

private theorem kissatPgoOverrides_check_budget :
    allBudgetsMatchTR kissatPgoOverrides = true := by
  t_kernel_rfl

private theorem kissatInlPolicy_check_kool_live :
    allKoolLiveTR (kissatFns.map Fn.name) kissatInlPolicy.keepOutOfLine = true := by
  t_kernel_rfl

/-- Every named PGO override symbol in `kissatPgoOverrides` exists in `Src.Full.kissatFns`. -/
theorem kissatPgoOverrides_live :
    ∀ s ∈ kissatPgoOverrides.map Prod.fst, s ∈ kissatFns.map Fn.name := by
  intro s hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  exact allOverridesLive_of_TR (kissatFns.map Fn.name) kissatPgoOverrides_check_live p hp

/-- No duplicate override symbol keys in `kissatPgoOverrides`. -/
theorem kissatPgoOverrides_nodup :
    (kissatPgoOverrides.map Prod.fst).Nodup :=
  stringsNodup_nodup kissatPgoOverrides_check_nodup

/-- `kissatPgoBudget` returns the exact table budget on every override entry. -/
theorem kissatPgoBudget_eq_of_mem :
    ∀ p ∈ kissatPgoOverrides, kissatPgoBudget p.1 = p.2 :=
  allBudgetsMatch_of_TR kissatPgoOverrides_check_budget

/-- Any symbol with non-default (`≠ 15`) budget in `kissatPgoBudget` is a live function in
`Src.Full.kissatFns`. -/
theorem kissatPgoBudget_ne_default_live :
    ∀ s : Sym, kissatPgoBudget s ≠ 15 → s ∈ kissatFns.map Fn.name := by
  intro s hne
  unfold kissatPgoBudget at hne
  cases hlk : kissatPgoOverrides.find? (fun p => p.1 == s) with
  | none =>
    rw [hlk] at hne
    exact absurd rfl hne
  | some p =>
    have hpMem : p ∈ kissatPgoOverrides := List.mem_of_find?_eq_some hlk
    have hbeq : (p.1 == s) = true := List.find?_some (p := fun q : Sym × Nat => q.1 == s) hlk
    rw [beq_iff_eq] at hbeq
    subst hbeq
    exact kissatPgoOverrides_live p.1 (List.mem_map_of_mem hpMem)

/-- Every `keepOutOfLine` symbol in `kissatInlPolicy` exists in `Src.Full.kissatFns`. -/
theorem kissatInlPolicy_keepOutOfLine_live :
    ∀ s ∈ kissatInlPolicy.keepOutOfLine, s ∈ kissatFns.map Fn.name := fun s hs =>
  (allKoolLive_of_TR (kissatFns.map Fn.name) kissatInlPolicy_check_kool_live s hs).1

/-- Every `keepOutOfLine` symbol in `kissatInlPolicy` also has base budget `0`. -/
theorem kissatInlPolicy_keepOutOfLine_zero :
    ∀ s ∈ kissatInlPolicy.keepOutOfLine, kissatPgoBudget s = 0 := fun s hs =>
  (allKoolLive_of_TR (kissatFns.map Fn.name) kissatInlPolicy_check_kool_live s hs).2

/-- `kissatInlChunkPolicy` has `singleSiteMax = 0` for `O(1)` site-count elimination. -/
theorem kissatInlChunkPolicy_singleSiteMax :
    kissatInlChunkPolicy.singleSiteMax = 0 :=
  rfl

/-- `kissatInlChunkPolicy` has `maxTotalDup = 0` for `O(1)` site-count elimination. -/
theorem kissatInlChunkPolicy_maxTotalDup :
    kissatInlChunkPolicy.maxTotalDup = 0 :=
  rfl

/-- `kissatInlChunkPolicy` has `requireLoopSite = false` for `O(1)` loop-site elimination. -/
theorem kissatInlChunkPolicy_requireLoopSite :
    kissatInlChunkPolicy.requireLoopSite = false :=
  rfl

/-- `kissatInlChunkPolicy` matches `kissatInlPolicy` on `budget`, `leafMax`, `maxCallerSize`,
`maxCalleeCalls`, `maxCalleeLoops`, `maxCallerCalls`, and `keepOutOfLine`. -/
theorem kissatInlChunkPolicy_parity :
    kissatInlChunkPolicy.budget = kissatInlPolicy.budget ∧
    kissatInlChunkPolicy.leafMax = kissatInlPolicy.leafMax ∧
    kissatInlChunkPolicy.maxCallerSize = kissatInlPolicy.maxCallerSize ∧
    kissatInlChunkPolicy.maxCalleeCalls = kissatInlPolicy.maxCalleeCalls ∧
    kissatInlChunkPolicy.maxCalleeLoops = kissatInlPolicy.maxCalleeLoops ∧
    kissatInlChunkPolicy.maxCallerCalls = kissatInlPolicy.maxCallerCalls ∧
    kissatInlChunkPolicy.keepOutOfLine = kissatInlPolicy.keepOutOfLine :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanQbe.T.Examples.Kissat.Src.InlPolicy

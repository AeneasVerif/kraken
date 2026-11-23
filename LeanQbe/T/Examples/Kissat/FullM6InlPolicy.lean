module

public import LeanQbe.T.Inline

/-!
# Profile-Guided `InlinePolicy` for Unified Kissat `M6.0` (`FullM6InlPolicy`)

Calibrated from live 140-CNF `perf -F 999` Stage-1 hotness profiling
(`80%` of cycles in `11` fns, `95%` in `37` fns, `99%` in `79` fns) plus M6.0 hotspot telemetry:

* **Hot Search / BCP / Watch / Analyze / Minimize / Reduce / Cong / BVA / Viv / Parser callees:**
  preserve exact `InlinePolicy.b5` size thresholds (`40..165`) and caller caps (`maxCallerSize :=
  660`, `maxCalleeCalls := 2`, `maxCalleeLoops := some 2`, `maxCallerCalls := 4`).
* **Forwarding wrappers (`size ≤ 15`):** universally inlined (`budget = 15`), eliminating all
  shim-call overhead (`full_prop_lit_raw`, `full_watch_push`, `full_wstack_defrag`, `full_assign`,
  `full_min_shrink`, `full_deduce_1uip`, `full_arena_sweep`, etc.).
* **Cold / Inprocessing helpers (`> 15` nodes outside hot profile):** kept out-of-line (`b1`/`b3`
  discipline), avoiding `O(N)` kernel loop/site-count scans (`singleSiteMax := 0`,
  `maxTotalDup := 0`, `requireLoopSite := false`) and cold code bloat.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6InlPolicy

open LeanQbe.T

/-- Profile-guided per-symbol IR node budget derived from live 140-CNF `perf` hotness and
`FullM6` call-graph topology (`15` base threshold inlines all forwarding shims; `40..165` preserves
full `InlinePolicy.b5` inlining on all hot paths). -/
def m6PgoBudget : Sym → Nat
  -- Parser
  | "kissat_skip_ws_comments" => 45
  | "kissat_read_nat" => 69
  -- Core / Watch / Reduce
  | "full_isqrt" => 38
  | "full_alloc_cl" => 39
  | "full_wsort_sift" => 65
  | "full_lit_rank_m6" => 30
  | "full_move_red_pass2_m6" => 74
  | "full_mark_reasons_m6" => 87
  | "full_mark_reasons" => 89
  | "full_red_less" => 26
  | "full_red_sift" => 103
  -- Heuristics / Trail / Backtrack / Restart / EMA
  | "full_heap_up" => 83
  | "full_heap_push" => 125
  | "full_heap_pop" => 68
  | "full_rescale_m6" => 36
  | "full_rescale" => 38
  | "full_queue_renumber" => 46
  | "full_tick_rel" => 96
  | "full_log10_q16" => 60
  | "full_ema_update" => 97
  | "full_save_target_best" => 79
  | "full_restart_due" => 130
  | "full_restart" => 95
  -- Analyze / Minimize / Shrink / M6Hdr hot watermarks & tier limits
  | "full_clear_ana" => 30
  | "full_ana_sift_m6" => 77
  | "full_tmp_less" => 24
  | "full_sort_tmp_sift" => 106
  | "full_shrink_lower_m6" => 36
  | "full_det_new_level" => 18
  | "m6_hdr_update_tier_limits" => 58
  | "m6_hdr_record_used" => 60
  | "m6_hdr_get_watermark" => 21
  | "m6_hdr_set_watermark" => 21
  | "m6_hdr_dr_update" => 109
  | "m6_hdr_dr_allow" => 50
  -- Congruence / Tarjan / K512 / Sweep
  | "full_has_bin" => 86
  | "full_delete_bin_side" => 102
  | "full_add_unit" => 39
  | "full_tarjan_pop_scc" => 118
  | "full_cong_find" => 31
  | "full_sort_u32" => 40
  | "full_cong_emit_xor" => 41
  | "full_k512_watch" => 43
  | "full_k512_mtf" => 163
  | "full_m4_sweep_refine_sig" => 53
  -- Vivification / Backbone / BVA / FHeap
  | "full_find_repl" => 89
  | "full_viv_unreason_m6" => 39
  | "full_viv_watch_rank_m6" => 34
  | "full_viv_best_watch_m6" => 123
  | "full_viv_subsumes_bin_m6" => 69
  | "full_viv_subsumes_cl_m6" => 58
  | "full_viv_best_implied_m6" => 41
  | "full_viv_sort_counts_m6" => 55
  | "full_viv_has_l0_m6" => 39
  | "full_viv_l0_simp_m6" => 52
  | "full_viv_reuse_prefix_m6" => 120
  | "full_viv_tier_match_m6" => 47
  | "full_backbone_unwind_m6" => 33
  | "full_backbone_analyze_m6" => 109
  | "full_bva_match_large" => 60
  | "full_bva_pick_cand" => 74
  | "full_fheap_up" => 51
  | "full_fheap_down" => 77
  -- Cold/inprocessing functions: forwarding shims (`≤ 15` nodes) only
  | _ => 15

/-- Profile-guided `InlinePolicy` for `FullM6.m6Module` (`382` fns). -/
def m6InlPolicy : InlinePolicy :=
  { budget := m6PgoBudget
    leafMax := 0
    singleSiteMax := 0
    maxCallerSize := 660
    maxCalleeCalls := 2
    maxCalleeLoops := some 2
    maxTotalDup := 0
    requireLoopSite := false
    maxCallerCalls := 4
    keepOutOfLine := [] }

end LeanQbe.T.Examples.Kissat.FullM6InlPolicy

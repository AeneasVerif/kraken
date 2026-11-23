module

public import LeanQbe.T.Inline
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-!
# Profile-Guided Inline Policy for Kissat M7 (`FullM7InlPolicy`)

Extends `FullM6InlPolicy.m6PgoBudget` with:
* M7-specific hot helper budgets (`full_log10_q16_m7`, `full_sort_tmp_*_m7`,
  `full_cong_*_m7`, `full_m7_{get,set}64`, `full_bve_var_key_m7`, `full_walk_*_m7`,
  `full_bump_sift_m7`, `full_reorder_sift_m7`);
* verified Phase-2 hot tiny and medium Kissat callees (`full_k512_*`, `full_heap_down`,
  `full_restore_bump_ana_*`, `kissat_next_lit`, `full_arena_next`, `full_bve_*`,
  `full_viv_*`, `full_kitten_*`, `full_unwatch_large`, `full_fheap_down`, etc.).

Unlisted cold helpers fall back to `m6PgoBudget` (`| _ => 15`) so cold code stays
out-of-line and module elaboration remains fast.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7InlPolicy

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-- Per-callee PGO inline budget for Kissat M7, delegating cold symbols to `m6PgoBudget`. -/
def m7PgoBudget : Sym → Nat
  -- M7 hot helpers
  | "full_log10_q16_m7" => 60
  | "full_sort_tmp_sift_m7" => 106
  | "full_sort_tmp_heap_m7" => 40
  | "full_cong_ht_hash_ent_m7" => 48
  | "full_cong_u64_sift_m7" => 60
  | "full_cong_u64_sort_m7" => 146
  | "full_cong_bsearch_u64_m7" => 24
  | "full_m7_get64" => 24
  | "full_m7_set64" => 24
  | "full_bve_var_key_m7" => 68
  | "full_walk_init_table_m7" => 33
  | "full_walk_effort_m7" => 38
  | "full_walk_cb_inv_m7" => 85
  | "full_walk_save_min_m7" => 108
  | "full_walk_break_m7" => 87
  | "full_bump_sift_m7" => 110
  | "full_reorder_sift_m7" => 103
  | "full_k6_watch_m7" => 59
  | "full_k6_assign_m7" => 84
  | "full_k6_backtrack_m7" => 132
  | "full_bve_get_tern_m7" => 68
  | "full_bve_xor_pat_m7" => 86
  | "full_bve_collect_m7" => 90
  | "full_bve_heap_up_m7" => 71
  | "full_bve_heap_down_m7" => 99
  | "full_dense_flush_units_m7" => 40
  | "full_tumble_clause_m7" => 90
  -- Phase-2 PGO helpers missed or capped by `m6PgoBudget` / `InlinePolicy.b5`
  | "full_k512_assign" => 78
  | "full_k512_backtrack" => 120
  | "full_k512_ana_clause" => 131
  | "full_k512_add_clause" => 225
  | "full_heap_down" => 113
  | "full_heap_pop" => 181
  | "full_restore_bump_ana_m5" => 90
  | "full_restore_bump_ana_m6_hdr" => 144
  | "kissat_next_lit" => 235
  | "full_arena_next" => 55
  | "full_bve_mark_and" => 120
  | "full_bve_mark_and_m6" => 172
  | "full_viv_keys_m4" => 92
  | "full_viv_keys_m6" => 89
  | "full_viv_l0_simp_m4" => 60
  | "full_viv_count_m6" => 70
  | "full_viv_inst_check_m6" => 63
  | "full_unwatch_large" => 89
  | "full_bve_try_bce" => 140
  | "full_bve_collect" => 90
  | "full_bve_collect_m6" => 90
  | "full_bve_ext_need" => 31
  | "full_bve_get_tern_m6" => 68
  | "full_bve_var_key_m6" => 66
  | "full_bve_heap_up_m6" => 71
  | "full_bve_heap_down_m6" => 99
  | "full_dense_flush_units_m6" => 40
  | "full_set_inactive" => 53
  | "full_rng_next" => 20
  | "full_kitten_watch" => 43
  | "full_kitten_assign" => 78
  | "full_kitten_backtrack" => 120
  | "full_kitten_mtf" => 163
  | "full_analyze_lit" => 103
  | "full_recompute_tiers" => 69
  | "full_probe_prop" => 47
  | "full_probe_flush_hbr" => 49
  | "full_cong_and_match" => 105
  | "full_walk_score_m6" => 31
  | "full_walk_break_m6" => 60
  | "full_walk_cb_inv_m6" => 66
  | "full_rebuild_watches" => 29
  | "full_flush_trail" => 52
  | "full_compact_sift_q" => 56
  | "full_compact_sift_h" => 66
  | "full_compact_needed" => 26
  | "full_m4_sweep_build_pht" => 82
  | "full_scale_delta_m5" => 101
  | "full_scale_delta" => 103
  | s => m6PgoBudget s

/-- Profile-guided `InlinePolicy` for Kissat M7 (`maxCallerSize := 1020`, `cold => 15`). -/
def m7InlPolicy : InlinePolicy :=
  { budget := m7PgoBudget
    leafMax := 0
    singleSiteMax := 0
    maxCallerSize := 1020
    maxCalleeCalls := 2
    maxCalleeLoops := some 2
    maxTotalDup := 0
    requireLoopSite := false
    maxCallerCalls := 4
    keepOutOfLine := [] }

end LeanQbe.T.Examples.Kissat.FullM7InlPolicy

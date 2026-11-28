module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("full_cong_merge", ["full_add_bin", "full_cong_find"]),
  ("full_cong_mark_trail", ["full_cong_find"]),
  ("full_cong_unit_fold", ["full_cong_mark_trail"]),
  ("full_cong_equiv_fold", ["full_cong_find", "full_cong_mark_trail"]),
  ("full_cong_extract_xor_k", ["full_cong_emit_xor4", "full_sort_u32"]),
  ("full_cong_try_xor_ite", ["full_cong_emit_xor"]),
  ("full_cong_eb_match", ["full_has_bin"]),
  ("full_cong_extract_binaries", ["full_add_bin", "full_arena_next", "full_has_bin",
      "full_cong_eb_match"]),
  ("full_cong_extract_from_fid", ["full_arena_next"]),
  ("full_cong_and_match", ["full_cong_find"]),
  ("full_cong_xor_match", ["full_cong_find", "full_sort_u32"]),
  ("full_cong_eval_gate", ["full_cong_find", "full_sort_u32"]),
  ("full_cong_worklist", ["full_cong_find"]),
  ("full_cong_sort_pairs_fid", ["full_cong_sift_pairs_fid"]),
  ("full_cong_fwd_subsume", ["full_cong_find", "full_arena_next"]),
  ("full_cong_u64_sort_m7", ["full_cong_u64_sift_m7"]),
  ("full_cong_copy_condbin_m7", ["full_cong_u64_sort_m7"]),
  ("full_cong_extract_condeq_m7", ["full_cong_bsearch_u64_m7", "full_cong_u64_sort_m7"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Congruence

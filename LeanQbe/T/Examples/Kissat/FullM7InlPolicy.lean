module

public import LeanQbe.T.Inline
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-!
# Profile-Guided `InlinePolicy` for Unified Kissat `M7` (`FullM7InlPolicy`)

Extends `FullM6InlPolicy.m6PgoBudget` with hot `M7` helpers (`full_log10_q16_m7`,
`full_sort_tmp_{sift,heap}_m7`, `full_cong_{ht_hash_ent,u64_sift,bsearch_u64}_m7`,
`full_m7_{get64,set64}`, `full_bve_var_key_m7`), keeping forwarding shims (`≤ 15` nodes)
inlined and cold/inprocessing functions out-of-line.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7InlPolicy

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-- Profile-guided per-symbol IR node budget for `FullM7.m7Module` (`410` fns). -/
def m7PgoBudget : Sym → Nat
  | "full_log10_q16_m7" => 60
  | "full_sort_tmp_sift_m7" => 106
  | "full_sort_tmp_heap_m7" => 40
  | "full_cong_ht_hash_ent_m7" => 48
  | "full_cong_u64_sift_m7" => 60
  | "full_cong_bsearch_u64_m7" => 24
  | "full_m7_get64" => 24
  | "full_m7_set64" => 24
  | "full_bve_var_key_m7" => 68
  | s => m6PgoBudget s

/-- Profile-guided `InlinePolicy` for `FullM7.m7Module` (`410` fns). -/
def m7InlPolicy : InlinePolicy :=
  { budget := m7PgoBudget
    leafMax := 0
    singleSiteMax := 0
    maxCallerSize := 660
    maxCalleeCalls := 2
    maxCalleeLoops := some 2
    maxTotalDup := 0
    requireLoopSite := false
    maxCallerCalls := 4
    keepOutOfLine := [] }

end LeanQbe.T.Examples.Kissat.FullM7InlPolicy

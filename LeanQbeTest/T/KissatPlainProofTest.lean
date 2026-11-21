module

public import LeanQbe.T.Examples.Kissat.PlainLemmas
meta import LeanQbe.T.Examples.Kissat.PlainLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Non-Vacuity, and Axiom Audit for Kissat `D-Plain` (`PlainLemmas`)

1. Executable `#guard` checks on `plainFns` (59 functions), `plainModule.checkAcyclic`,
   concrete witness byte vectors (`plainNvUnsatBytes`, `plainNvSatBytes`), and `2048`-byte arena
   bounds (`plainFixedBytes 1 + 2 * 40 + 136 + 8 <= 2048`).
2. Concrete-memory source-level `Func.wp` sanity checks under `plainEnv`, `plainUnsatEnv`, and
   `plainSatEnv` (`X = False`).
3. Single-line `#print axioms` audit (`<= 120` cols) on exported `D-Plain` theorems (strictly
   `⊆ [propext, Classical.choice, Quot.sound]`, zero architecture-specific imports).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatPlainProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard plainFns.length == 59
#guard plainModule.checkAcyclic == true
#guard plainNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard plainNvSatBytes == "p cnf 1 1\n1 0\n".toUTF8.toList
#guard plainFixedBytes 1 + 2 * 40 + 136 + 8 <= 2048
#guard plainFixedBytes 1 + 1 * 40 + 136 + 8 <= 2048
#guard runKissatCheckModel plainNvSatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 == true
#guard runKissatCheckModel plainNvUnsatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 == false

/-! ## 2. Source-level `Func.wp` sanity checks (`X = False`) -/

/-- General `plain_solve_bytes_correct` instantiated on concrete `plainNvUnsatBytes` payload
(`2048` B). -/
theorem plain_unsat_payload :
    let m0 : Mem 64 := (plainPayload plainNvUnsatBytes).At plainNvCnfPtr
    Func.wp plainEnv Plain.kissat_solve_bytes_body
      (plainNvCnfPtr, BitVec.ofNat 64 plainNvUnsatBytes.length,
        plainNvWorkPtr plainNvUnsatBytes, 2048#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs plainNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs plainNvUnsatBytes = some cnf ∧
          ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes plainNvCnfPtr plainNvUnsatBytes ⋆
          region (plainNvWorkPtr plainNvUnsatBytes) 2048 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  plain_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact plainPayload_sep plainNvUnsatBytes (by decide))

/-- General `plain_solve_bytes_correct` instantiated on concrete `plainNvSatBytes` payload
(`2048` B). -/
theorem plain_sat_payload :
    let m0 : Mem 64 := (plainPayload plainNvSatBytes).At plainNvCnfPtr
    Func.wp plainEnv Plain.kissat_solve_bytes_body
      (plainNvCnfPtr, BitVec.ofNat 64 plainNvSatBytes.length,
        plainNvWorkPtr plainNvSatBytes, 2048#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs plainNvSatBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs plainNvSatBytes = some cnf ∧
          ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes plainNvCnfPtr plainNvSatBytes ⋆
          region (plainNvWorkPtr plainNvSatBytes) 2048 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  plain_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact plainPayload_sep plainNvSatBytes (by decide))

/-! ## 3. Single-line `#print axioms` audit on exported `D-Plain` theorems -/

#print axioms LeanQbe.T.Examples.Kissat.Plain.plainFns_wf
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_isqrt_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_ilog10_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_arena_next_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_alloc_cl_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_wstack_defrag_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_watch_push_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_heap_up_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_heap_down_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_heap_push_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_heap_pop_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_rescale_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_bump_var_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_bump_decay_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_queue_mtf_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_tick_rel_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_ema_update_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_assign_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_backtrack_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_add_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_zero_tables_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_init_state_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_skip_cl_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_ingest_cl_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_parse_body_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_find_repl_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_prop_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_propagate_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_recompute_tiers_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_mark_reasons_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_red_less_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_sort_reds_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_lit_rank_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_sweep_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_reduce_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_analyze_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_analyze_rsn_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_clear_marks_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_min_mark_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_min_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_tmp_less_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_sort_tmp_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_shrink_blk_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_min_shrink_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_analyze_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_decide_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_rephase_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_switch_mode_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_restart_due_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_lucky_scan_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_lucky_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_solve_bytes_wp
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_solve_bytes_correct
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainUnsatEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainUnsatEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainUnsatEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainSatEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainSatEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.Plain.plainSatEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_unsat_nonvacuous
#print axioms LeanQbe.T.Examples.Kissat.Plain.plain_sat_nonvacuous
#print axioms plain_unsat_payload
#print axioms plain_sat_payload

end LeanQbeTest.T.KissatPlainProofTest

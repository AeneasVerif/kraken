module

public import LeanQbe.T.Examples.Kissat.CorePlusLemmas
meta import LeanQbe.T.Examples.Kissat.CorePlusLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Non-Vacuity, and Axiom Audit for Kissat `D-Core+` (`CorePlusLemmas`)

1. Executable `#guard` checks on `coreplusFns` (36 functions), `coreplusModule.checkAcyclic`,
   concrete witness byte vectors (`cpNvUnsatBytes`, `cpNvSatBytes`), and `1024`-byte arena bounds.
2. Concrete-memory source-level `Func.wp` sanity checks under `corePlusEnv`, `cpUnsatEnv`, and
   `cpSatEnv` (`X = False`).
3. Single-line `#print axioms` audit (`<= 120` cols) on all exported `D-Core+` theorems (strictly
   `⊆ [propext, Classical.choice, Quot.sound]`, zero architecture-specific imports).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatCorePlusProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.CorePlus
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard coreplusFns.length == 36
#guard coreplusModule.checkAcyclic == true
#guard cpNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard cpNvSatBytes == "p cnf 1 1\n1 0\n".toUTF8.toList
#guard cpFixedBytes 1 + 2 * 24 + 8 <= 1024
#guard cpFixedBytes 1 + 1 * 24 + 8 <= 1024
#guard runKissatCheckModel cpNvSatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 == true
#guard runKissatCheckModel cpNvUnsatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 == false

/-! ## 2. Source-level `Func.wp` sanity checks (`X = False`) -/

/-- General `solve_bytes_correct` instantiated on concrete `cpNvUnsatBytes` payload (`1024` B). -/
theorem cp_unsat_payload :
    let m0 : Mem 64 := (corePlusPayload cpNvUnsatBytes).At corePlusNvCnfPtr
    Func.wp corePlusEnv CorePlus.kissat_solve_bytes_body
      (corePlusNvCnfPtr, BitVec.ofNat 64 cpNvUnsatBytes.length,
        corePlusNvWorkPtr cpNvUnsatBytes, 1024#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cpNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cpNvUnsatBytes = some cnf ∧
          ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes corePlusNvCnfPtr cpNvUnsatBytes ⋆
          region (corePlusNvWorkPtr cpNvUnsatBytes) 1024 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact corePlusPayload_sep cpNvUnsatBytes (by decide))

/-- General `solve_bytes_correct` instantiated on concrete `cpNvSatBytes` payload (`1024` B). -/
theorem cp_sat_payload :
    let m0 : Mem 64 := (corePlusPayload cpNvSatBytes).At corePlusNvCnfPtr
    Func.wp corePlusEnv CorePlus.kissat_solve_bytes_body
      (corePlusNvCnfPtr, BitVec.ofNat 64 cpNvSatBytes.length,
        corePlusNvWorkPtr cpNvSatBytes, 1024#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cpNvSatBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cpNvSatBytes = some cnf ∧
          ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes corePlusNvCnfPtr cpNvSatBytes ⋆
          region (corePlusNvWorkPtr cpNvSatBytes) 1024 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact corePlusPayload_sep cpNvSatBytes (by decide))

/-! ## 3. Single-line `#print axioms` audit on exported `D-Core+` theorems -/

#print axioms LeanQbe.T.Examples.Kissat.CorePlus.coreplusFns_wf
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.coreplus_acyclic
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_heap_sift_up_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_heap_sift_down_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_heap_push_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_heap_pop_max_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_rescale_scores_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_bump_var_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_bump_decay_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_tick_reluctant_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_assign_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_add_watch_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_add_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_backtrack_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_zero_tables_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_init_state_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_ingest_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_parse_body_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_find_repl_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_propagate_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_propagate_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_analyze_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_clear_marks_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_min_mark_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_minimize_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_min_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_analyze_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_decide_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.kissat_solve_bytes_wp
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.corePlusEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.corePlusEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.corePlusEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.solve_bytes_correct
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.cpUnsatEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.cpUnsatEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.cpUnsatEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.cpSatEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.cpSatEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.cpSatEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.unsat_nonvacuous
#print axioms LeanQbe.T.Examples.Kissat.CorePlus.sat_nonvacuous
#print axioms cp_unsat_payload
#print axioms cp_sat_payload

end LeanQbeTest.T.KissatCorePlusProofTest

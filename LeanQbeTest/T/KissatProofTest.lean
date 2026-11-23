module

public import LeanQbe.T.Examples.Kissat.SolverLemmas
meta import LeanQbe.T.Examples.Kissat.SolverLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Non-Vacuity, and Axiom Audit for `Kissat.SolverLemmas`

1. Executable `#guard` checks on `kissatFns` (25 functions), `kissatModule.checkAcyclic`,
   concrete witness byte vectors (`nvUnsatBytes`, `nvSatBytes`), and arena size bounds.
2. Concrete-memory source-level `Func.wp` sanity checks under `kissatEnv`,
   `kissatUnsatWitnessEnv`, and `kissatSatWitnessEnv` (`X = False`).
3. Single-line `#print axioms` audit on all exported solver theorems (strictly
   `[propext, Classical.choice, Quot.sound]`). Note: architecture-specific Kraken `Eventually`
   theorems are audited separately in `Amd64.Kissat` and `Arm64.Kissat` (zero cross-arch imports).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard kissatFns.length == 25
#guard kissatModule.checkAcyclic == true
#guard nvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard nvSatBytes == "p cnf 1 1\n1 0\n".toUTF8.toList
#guard nvUnsatBytes == nvDimacsBytes
#guard fixedBytes 1 + 2 * 24 + 8 <= 512
#guard fixedBytes 1 + 1 * 24 + 8 <= 512
#guard runKissatCheckModel nvSatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 == true
#guard runKissatCheckModel nvUnsatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 == false

/-! ## 2. Source-level `Func.wp` sanity checks (`X = False`) -/

/-- General `kissat_solve_bytes_correct` instantiated on concrete `nvUnsatBytes` payload. -/
theorem nv_general_unsat_payload :
    let m0 : Mem 64 := (kissatPayload nvUnsatBytes).At kissatNvCnfPtr
    Func.wp kissatEnv kissat_solve_bytes_body
      (kissatNvCnfPtr, BitVec.ofNat 64 nvUnsatBytes.length,
        kissatNvWorkPtr nvUnsatBytes, 512#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs nvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs nvUnsatBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes kissatNvCnfPtr nvUnsatBytes ⋆ region (kissatNvWorkPtr nvUnsatBytes) 512 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  kissat_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact kissatPayload_sep nvUnsatBytes (by decide))

/-- General `kissat_solve_bytes_correct` instantiated on concrete `nvSatBytes` payload. -/
theorem nv_general_sat_payload :
    let m0 : Mem 64 := (kissatPayload nvSatBytes).At kissatNvCnfPtr
    Func.wp kissatEnv kissat_solve_bytes_body
      (kissatNvCnfPtr, BitVec.ofNat 64 nvSatBytes.length,
        kissatNvWorkPtr nvSatBytes, 512#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs nvSatBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs nvSatBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes kissatNvCnfPtr nvSatBytes ⋆ region (kissatNvWorkPtr nvSatBytes) 512 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  kissat_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact kissatPayload_sep nvSatBytes (by decide))

/-! ## 3. Single-line `#print axioms` audit on exported solver theorems -/

#print axioms LeanQbe.T.Examples.Kissat.kissatFns_wf
#print axioms LeanQbe.T.Examples.Kissat.kissatModule_checkAcyclic
#print axioms LeanQbe.T.Examples.Kissat.kissat_assign_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_add_watch_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_add_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_backtrack_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_zero_tables_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_init_state_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_skip_clause_syntax_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_ingest_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_parse_body_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_find_repl_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_propagate_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_propagate_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_analyze_clause_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_clear_marks_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_analyze_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_decide_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_solve_bytes_wp
#print axioms LeanQbe.T.Examples.Kissat.kissatEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.kissatEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.kissatEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.kissat_solve_bytes_correct
#print axioms LeanQbe.T.Examples.Kissat.kissatUnsatWitnessEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.kissatUnsatWitnessEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.kissatSatWitnessEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.kissatSatWitnessEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.kissat_unsat_nonvacuous
#print axioms LeanQbe.T.Examples.Kissat.kissat_sat_nonvacuous
#print axioms nv_general_unsat_payload
#print axioms nv_general_sat_payload

end LeanQbeTest.T.KissatProofTest

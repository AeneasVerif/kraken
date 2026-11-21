module

public import LeanQbe.T.Examples.Kissat.FullProof
meta import LeanQbe.T.Examples.Kissat.FullProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Kissat `D-Full` (`FullProof`)

1. Executable `#guard` checks on `fullFns` (166 functions), `fullModule.checkAcyclic`,
   `fullBridge9Indices`, `fullRemaining8aIndices`, `fullRemaining8bIndices`, concrete UNSAT
   witness byte vector (`fullNvUnsatBytes`), and `4096`-byte arena bounds.
2. Concrete-memory source-level `Func.wp` sanity check (`full_unsat_payload`, `X = False`,
   canonical `fullEnv`, strictly UNSAT-only — ZERO SAT / model-finding checks).
3. Single-line `#print axioms` audit (`<= 100` cols) on all exported Stage-4 top orchestrator,
   `FullBridgeLemmas9`, and `151/166` `ModuleOk` assembly theorems
   (strictly `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFullProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard fullFns.length == 166
#guard fullModule.checkAcyclic == true
#guard fullBridge9Indices == [160, 161, 162, 163, 164, 165]
#guard fullRemaining8aIndices.length == 6
#guard fullRemaining8bIndices.length == 9
#guard fullNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096

/-! ## 2. Source-level `Func.wp` sanity check (`X = False`, UNSAT-only, canonical `fullEnv`) -/

/-- General `full_solve_bytes_correct` instantiated on `fullNvUnsatBytes` payload (`4096` B). -/
theorem full_unsat_payload :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fullEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  full_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide))

/-! ## 3. Single-line `#print axioms` audit on exported `D-Full` top & bridge theorems -/

#print axioms LeanQbe.T.Examples.Kissat.Full.fullFns_wf
#print axioms LeanQbe.T.Examples.Kissat.Full.full_acyclic
#print axioms LeanQbe.T.Examples.Kissat.Full.full_probe_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.full_eliminate_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.full_preprocess_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.full_simplify_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.full_search_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.kissat_solve_bytes_core_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.kissat_solve_bytes_wp
#print axioms LeanQbe.T.Examples.Kissat.Full.full_bridge_9_mk_ok
#print axioms LeanQbe.T.Examples.Kissat.Full.full_bridge_9_ok
#print axioms LeanQbe.T.Examples.Kissat.Full.full_bridge_9_core_ok
#print axioms LeanQbe.T.Examples.Kissat.Full.full_solve_bytes_correct
#print axioms LeanQbe.T.Examples.Kissat.Full.full_unsat_nonvacuous
#print axioms LeanQbe.T.Examples.Kissat.Full.fullEnv_moduleOk_of_missing
#print axioms LeanQbe.T.Examples.Kissat.Full.fullUnsatEnv_modOk_rem
#print axioms full_unsat_payload

end LeanQbeTest.T.KissatFullProofTest

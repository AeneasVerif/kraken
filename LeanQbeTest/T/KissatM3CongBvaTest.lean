module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas
meta import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas
import LeanQbe.T.Logic.MemLemmas

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Kissat M3 (`FullM3CongBva`)

1. Executable `#guard` checks on `m3CongBva_fns` (`11` fns), `m3Module.checkAcyclic`,
   `m3Fns` (`201` fns), `m3FullModule.checkAcyclic`, `m3SpecTable` (`31` rows),
   `m3UnlandedIndices` (`43` fns), `schedNvUnsatBytes`, and `4096`-byte arena bounds.
2. Concrete-memory source-level `Func.wp` sanity check (`m3_unsat_payload`, `X = False`,
   canonical `m3FullEnv`, strictly UNSAT-only — no SAT / model-finding checks).
3. Single-line `#print axioms` audit across `Func.Wf`, acyclicity, all `11`
   `FullM3CongBva` `Func.wp` proofs, `m3_fast_probe_tail_wp`, unconditional standalone
   `m3_moduleOk`, `m3Full_moduleOk_of_m2b` (`158 / 201`), `m3_solve_bytes_correct`, and
   `m3_unsat_nonvacuous` (strictly `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatM3CongBvaTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard m3CongBva_fns.length == 11
#guard m3Module.checkAcyclic == true
#guard m3Fns.length == 201
#guard m3FullModule.checkAcyclic == true
#guard m3SpecTable.length == 31
#guard m3UnlandedIndices.length == 43
#guard schedNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096

/-! ## 2. Source-level `Func.wp` sanity check (`X = False`, UNSAT-only, `m3FullEnv`) -/

/-- General `m3_solve_bytes_correct` instantiated on `schedNvUnsatBytes` payload (`4096` B). -/
theorem m3_unsat_payload :
    let m0 : Mem 64 := (schedPayload schedNvUnsatBytes).At schedNvCnfPtr
    Func.wp m3FullEnv Full.kissat_solve_bytes_body
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs schedNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
          region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m3_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact schedPayload_sep schedNvUnsatBytes (by decide))

/-! ## 3. Single-line `#print axioms` audit on exported `FullM3CongBva` & unified theorems -/

#print axioms m3_fns_wf
#print axioms m3_acyclic
#print axioms m3Fns_wf
#print axioms m3FullAcyc
#print axioms m3MarkTrailWp
#print axioms m3UnitFoldWp
#print axioms m3EquivFoldWp
#print axioms m3AndMatchWp
#print axioms m3WorkStepWp
#print axioms m3CongDenseWp
#print axioms m3ElimNbrsWp
#print axioms m3ElimBveWp
#print axioms m3ProbeTailWp
#print axioms m3ProbeWp
#print axioms m3ElimWp
#print axioms m3PreWp
#print axioms m3ModOk
#print axioms m3FullOk
#print axioms m3SolveOk
#print axioms m3UnsatNv
#print axioms m3_unsat_payload

end LeanQbeTest.T.KissatM3CongBvaTest

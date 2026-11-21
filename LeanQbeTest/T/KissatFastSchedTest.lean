module

public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
meta import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Kissat M2 Fast Scheduler (`FullFastSched`)

1. Executable `#guard` checks on `sched_fns` (`15` upgraded/new fns), `schedSplicedFns` (`173` fns),
   `schedModule.checkAcyclic`, `schedProvedIndices` (`16` proved entries), spliced function names,
   concrete UNSAT witness bytes (`schedNvUnsatBytes`), and `4096`-byte workspace bounds.
2. Concrete-memory source-level `Func.wp` sanity check (`sched_unsat_payload`, `X = False`,
   `schedEnv`, strictly UNSAT-only — ZERO SAT / model-finding checks).
3. Single-line `#print axioms` audit (`<= 100` cols) on all exported `FullFastSched` and
   `FullFastSchedLemmas` theorems (strictly `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFastSchedTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard sched_fns.length == 15
#guard schedSplicedFns.length == 173
#guard schedModule.checkAcyclic == true
#guard schedProvedIndices.length == 16
#guard schedSplicedFns[57]?.map Fn.name == some "full_sweep_bins"
#guard schedSplicedFns[125]?.map Fn.name == some "full_substitute"
#guard schedSplicedFns[126]?.map Fn.name == some "full_enter_dense"
#guard schedSplicedFns[160]?.map Fn.name == some "full_scale_delta"
#guard schedSplicedFns[165]?.map Fn.name == some "full_probe"
#guard schedSplicedFns[168]?.map Fn.name == some "full_eliminate"
#guard schedSplicedFns[169]?.map Fn.name == some "full_preprocess"
#guard schedSplicedFns[170]?.map Fn.name == some "full_simplify"
#guard schedSplicedFns[171]?.map Fn.name == some "full_search"
#guard schedSplicedFns[172]?.map Fn.name == some "kissat_solve_bytes"
#guard schedNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096

/-! ## 2. Source-level `Func.wp` sanity check (`X = False`, UNSAT-only, `schedEnv`) -/

/-- General `sched_solve_bytes_correct` instantiated on `schedNvUnsatBytes` (`4096` B). -/
theorem sched_unsat_payload :
    let m0 : Mem 64 := (schedPayload schedNvUnsatBytes).At schedNvCnfPtr
    Func.wp schedEnv Full.kissat_solve_bytes_body
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs schedNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
          region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  sched_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact schedPayload_sep schedNvUnsatBytes (by decide))

/-! ## 3. Single-line `#print axioms` audit on exported `FullFastSched` theorems -/

theorem audit_noExit (ms : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ schedSpecTable ms, e.noExit = true := schedSpecTable_noExit ms

theorem audit_enter_dense (Γ : Env)
    (h1 : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (h2 : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, fullSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (h4 : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (h5 : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (h6 : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Func.wp Γ FullFastSched.full_enter_dense_body a m Q X :=
  sched_enter_dense_wp Γ h1 h2 h3 h4 h5 h6

theorem audit_scale_delta (Γ : Env)
    (h1 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_body a m Q X :=
  sched_scale_delta_wp Γ h1

theorem audit_probe_dticks (Γ : Env)
    (h1 : ∀ a m Q X, schedMaxU64Spec a m Q X → Γ "full_max_u64" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeDticksSpec a m Q X → Func.wp Γ full_probe_dticks_body a m Q X :=
  sched_probe_dticks_wp Γ h1

theorem audit_elim_dticks (Γ : Env) :
    ∀ a m Q X, schedElimDticksSpec a m Q X → Func.wp Γ full_elim_dticks_body a m Q X :=
  sched_elim_dticks_wp Γ

theorem audit_solve_core (Γ : Env)
    (h1 : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (h2 : ∀ a m Q X, fullParseBodySpec a m Q X → Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (h4 : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (h5 : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (h6 : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesCoreSpec a m Q X → Func.wp Γ Full.kissat_solve_bytes_body a m Q X :=
  sched_kissat_solve_bytes_core_wp Γ h1 h2 h3 h4 h5 h6

theorem audit_solve_bytes (Γ : Env)
    (h1 : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (h2 : ∀ a m Q X, fullParseBodySpec a m Q X → Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (h4 : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (h5 : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (h6 : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesSpec a m Q X → Func.wp Γ Full.kissat_solve_bytes_body a m Q X :=
  sched_kissat_solve_bytes_wp Γ h1 h2 h3 h4 h5 h6

theorem audit_proved_rows (ms : Spec [i64, i64, i64, i64, i64] [i64])
    (hw : ∀ a m Q X, ms a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ∀ n ∈ schedProvedIndices,
      ∃ fn row, schedSplicedFns[n]? = some fn ∧ (schedSpecTable ms)[n]? = some row ∧
        SpecEntry.Impl (mkSchedEnv ms) fn row :=
  sched_proved_rows_ok ms hw

theorem audit_correct {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp schedEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  sched_solve_bytes_correct hcfit hwfit hm

theorem audit_nonvacuous :
    let m0 : Mem 64 := (schedPayload schedNvUnsatBytes).At schedNvCnfPtr
    Func.wp schedUnsatEnv Full.kissat_solve_bytes_body
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ schedNvUnsatCnf.Unsat ∧
        (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
          region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  sched_unsat_nonvacuous

#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns_wf
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_acyclic
#print axioms audit_noExit
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.schedSpecTable_sigs
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_sweep_bins_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_substitute_wp
#print axioms audit_enter_dense
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_min_u64_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_max_u64_wp
#print axioms audit_scale_delta
#print axioms audit_probe_dticks
#print axioms audit_elim_dticks
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_probe_tail_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_probe_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_elim_bve_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_eliminate_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_preprocess_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_simplify_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastSched.sched_search_wp
#print axioms audit_solve_core
#print axioms audit_solve_bytes
#print axioms audit_proved_rows
#print axioms audit_correct
#print axioms audit_nonvacuous
#print axioms sched_unsat_payload

end LeanQbeTest.T.KissatFastSchedTest

module

public import LeanQbe.T.Examples.Kissat.FullFastProof
meta import LeanQbe.T.Examples.Kissat.FullFastProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Kissat M2 (`FullFastProof`, `196/196`)

1. Executable `#guard` checks on `fastFns` (`196` functions), `fastModule.checkAcyclic`,
   `fastSpecTable`, the M2b slice index lists (`3 + 13 + 15 + 9 = 40` rows; all `196/196` closed),
   concrete UNSAT witness bytes (`fullNvUnsatBytes`), and `4096`-byte workspace bounds.
2. Concrete `Mem 64` source-level `Func.wp` sanity check (`fast_unsat_payload`, `X = False`,
   canonical `196`-function `fastEnv`, strictly UNSAT-only — ZERO SAT / model proofs).
3. Root-namespace short aliases for single-line `#print axioms` audit (`<= 100` cols, `wrapped = 0`)
   covering all M2 orchestrators, `TmkZero` M1 helpers, headline UNSAT soundness/non-vacuity, and
   unconditional `196/196` `ModuleOk` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFastProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFast
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard fastFns.length == 196
#guard fastModule.checkAcyclic == true
#guard fastCoreIndices.length == 3
#guard fastBvaHeapIndices.length == 13
#guard fastKittenIndices.length == 15
#guard fastDefSweepIndices.length == 9
#guard fullNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096

/-! ## 2. Source-level `Func.wp` sanity check (`X = False`, UNSAT-only, `fastEnv`) -/

/-- General `fast_solve_bytes_correct` instantiated on `fullNvUnsatBytes` payload (`4096` B). -/
theorem fast_unsat_payload :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fastEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  fast_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide))

end LeanQbeTest.T.KissatFastProofTest

/-! ## 3. Root-namespace short aliases for single-line `#print axioms` audit -/

section AxiomAudit

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFast
open LeanQbeTest.T.KissatFastProofTest

theorem m2_fast_fns_wf : ∀ f ∈ fastFns, f.Wf := fastFns_wf

theorem m2_fast_acyclic : fastModule.checkAcyclic = true := fast_acyclic

theorem m2_ext_push2_tmk (Γ : Env) :
    ∀ a m Q X, FullFastBveBudgets.fullExtendPush2TmkSpec a m Q X →
      Func.wp Γ Full.full_extend_push2_body a m Q X :=
  fast_extend_push2_tmk_wp Γ

theorem m2_ext_push_cl_tmk (Γ : Env) :
    ∀ a m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec a m Q X →
      Func.wp Γ Full.full_extend_push_cl_body a m Q X :=
  fast_extend_push_cl_tmk_wp Γ

theorem m2_bve_weaken_tmk (Γ : Env)
    (h1 : ∀ xs m Q X, FullFastBveBudgets.fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (h2 : ∀ xs m Q X, Full.fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (h3 : ∀ xs m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec args m Q X →
      Func.wp Γ Full.full_bve_weaken_body args m Q X :=
  fast_bve_weaken_tmk_wp Γ h1 h2 h3

theorem m2_bve_commit_tmk (Γ : Env)
    (h1 : ∀ xs m Q X, Full.fullAllocClSpec xs m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X)
    (h2 : ∀ xs m Q X, Full.fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h3 : ∀ xs m Q X, Full.fullAddBinSpec xs m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (h4 : ∀ xs m Q X, Full.fullAddUnitSpec xs m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] xs m Q X) :
    ∀ args m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec args m Q X →
      Func.wp Γ Full.full_bve_commit_res_body args m Q X :=
  fast_bve_commit_res_tmk_wp Γ h1 h2 h3 h4

theorem m2_probe_tail_wp (Γ : Env)
    (h1 : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (h2 : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, FullFastBveBudgets.fullProbeRunFastSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (h4 : ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Func.wp Γ full_probe_tail_body a m Q X :=
  fast_probe_tail_wp Γ h1 h2 h3 h4

theorem m2_probe_wp (Γ : Env)
    (h1 : ∀ a m Q X, FullFastSched.schedProbeDticksSpec a m Q X →
      Γ "full_probe_dticks" [i64, .bool] [i64] a m Q X)
    (h2 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (h4 : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (h5 : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (h6 : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (h7 : ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (h8 : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (h9 : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (h10 : ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X → Func.wp Γ FullFast.full_probe_body a m Q X :=
  fast_probe_wp Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem m2_elim_bve_wp (Γ : Env)
    (h1 : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fastElimBveSpec a m Q X →
      Func.wp Γ FullFastSched.full_elim_bve_body a m Q X :=
  fast_elim_bve_tmk_wp Γ h1

theorem m2_eliminate_wp (Γ : Env)
    (h1 : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (h2 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (h4 : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (h5 : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (h6 : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (h7 : ∀ a m Q X, fastElimBveSpec a m Q X → Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (h8 : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (h9 : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ FullFast.full_eliminate_body a m Q X :=
  fast_eliminate_wp Γ h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem m2_solve_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fastEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  fast_solve_bytes_correct hcfit hwfit hm

theorem m2_unsat_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fastUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  fast_unsat_nonvacuous

theorem m2_unsat_payload :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fastEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  fast_unsat_payload

theorem m2_table_impl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkFastEnv mainSpec) fastFns (fastSpecTable mainSpec) :=
  mkFastEnv_tableImpl mainSpec hweaken

theorem m2_env_modok : ModuleOk fastEnv fastModule :=
  fastEnv_moduleOk

theorem m2_unsat_modok : ModuleOk fastUnsatEnv fastModule :=
  fastUnsatEnv_moduleOk

#print axioms m2_fast_fns_wf
#print axioms m2_fast_acyclic
#print axioms m2_ext_push2_tmk
#print axioms m2_ext_push_cl_tmk
#print axioms m2_bve_weaken_tmk
#print axioms m2_bve_commit_tmk
#print axioms m2_probe_tail_wp
#print axioms m2_probe_wp
#print axioms m2_elim_bve_wp
#print axioms m2_eliminate_wp
#print axioms m2_solve_correct
#print axioms m2_unsat_nv
#print axioms m2_unsat_payload
#print axioms m2_table_impl
#print axioms m2_env_modok
#print axioms m2_unsat_modok

end AxiomAudit

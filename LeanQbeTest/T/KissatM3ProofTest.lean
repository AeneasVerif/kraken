module

public import LeanQbe.T.Examples.Kissat.FullM3Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM3Proof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Unified Kissat M3 (`FullM3`, `204/204`)

1. Executable `#guard` checks on `m3Fns` (`204` functions), `m3Module.checkAcyclic`,
   `(m3SpecTable fullSolveBytesSpec).length == 204`, concrete `fullNvUnsatBytes` payload bounds,
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `.aarch64`, `.scalar64`, and `.x64AVX2`.
2. Concrete `Mem 64` source-level `Func.wp` sanity check (`m3_unsat_payload`, `XPost := False`,
   canonical `204`-function `m3Env`, strictly UNSAT-only — no SAT / model-finding proofs).
3. Root-namespace short aliases for single-line `#print axioms` audit covering
   `Func.Wf`, acyclicity, merged M3 orchestrators (`full_probe_tail`, `full_probe`), unconditional
   `204/204` `ModuleOk`, `m3_solve_bytes_correct`, and `m3_unsat_nonvacuous`
   (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM3ProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Sanity Checks & Backend Compilation Guards -/

#guard m3Fns.length == 204
#guard m3Module.checkAcyclic == true
#guard m3Module.exits.isEmpty && m3Module.externs.isEmpty
#guard (m3SpecTable Full.fullSolveBytesSpec).length == 204
#guard fullNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096
#guard (ppTModule m3Module).isOk
#guard (PrintQbe.module m3Module).isOk
#guard (ppModule (m3Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m3Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m3Fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Source-Level `Func.wp` Sanity Check (`XPost = False`, UNSAT-only, `m3Env`) -/

/-- General `m3_solve_bytes_correct` instantiated on `fullNvUnsatBytes` payload (`4096` B). -/
theorem m3_unsat_payload :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3Env Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m3_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide))

end LeanQbeTest.T.KissatM3ProofTest

/-! ## 3. Root-Namespace Short Aliases for Single-Line `#print axioms` Audit -/

section AxiomAudit

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3
open LeanQbeTest.T.KissatM3ProofTest

theorem m3_fns_wf_ok : ∀ f ∈ m3Fns, f.Wf := m3Fns_wf

theorem m3_mod_acyclic : m3Module.checkAcyclic = true := m3_acyclic

theorem m3_tail_wp (Γ : Env)
    (h1 : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (h2 : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (h3 : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (h4 : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (h5 : ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Func.wp Γ FullM3.full_probe_tail_body a m Q X :=
  m3_probe_tail_wp Γ h1 h2 h3 h4 h5

theorem m3_prb_wp (Γ : Env)
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
    (h7 : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (h8 : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (h9 : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (h10 : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (h11 : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (h12 : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (h13 : ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X → Func.wp Γ FullM3.full_probe_body a m Q X :=
  m3_probe_wp Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem m3_solve_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m3Env Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m3_solve_bytes_correct hcfit hwfit hm

theorem m3_unsat_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3UnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m3_unsat_nonvacuous

theorem m3_unsat_pay :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3Env Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m3_unsat_payload

theorem m3_tbl_impl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3Env mainSpec) m3Fns (m3SpecTable mainSpec) :=
  mkM3Env_tableImpl mainSpec hweaken

theorem m3_env_ok : ModuleOk m3Env m3Module := m3Env_moduleOk

theorem m3_uenv_ok : ModuleOk m3UnsatEnv m3Module := m3UnsatEnv_moduleOk

#print axioms m3_fns_wf_ok
#print axioms m3_mod_acyclic
#print axioms m3_tail_wp
#print axioms m3_prb_wp
#print axioms m3_solve_ok
#print axioms m3_unsat_nv
#print axioms m3_unsat_pay
#print axioms m3_tbl_impl
#print axioms m3_env_ok
#print axioms m3_uenv_ok

end AxiomAudit

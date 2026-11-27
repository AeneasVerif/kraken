module

public import LeanQbe.T.Examples.Kissat.FullM4BvaProof
meta import LeanQbe.T.Examples.Kissat.FullM4BvaProof
import LeanQbe.T.Logic.MemLemmas

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Kissat M4 (`FullM4Bva`)

1. Executable `#guard` checks on `m4Bva_fns` (`10` upgraded fns), `m4BvaModule.checkAcyclic`,
   `m4BvaSpecTable` (`33` rows), `m4BvaFullFns` (`204` fns), `m4BvaFullModule.checkAcyclic`,
   `m4BvaFullSpecTable` (`204` rows), `full_bva_m4`, and `fullNvUnsatBytes`.
2. Concrete-memory source-level `Func.wp` sanity check (`unsat_payload`, `X = False`,
   closed `204`-function `m4BvaFullEnv`, strictly UNSAT-only — no SAT / model-finding checks).
3. Explicit-type audit theorems and single-line `#print axioms` covering
   `Func.Wf`, acyclicity, all `11` upgraded/re-specced M4 BVA `Func.wp` proofs, standalone
   `m4Bva_moduleOk`, closed `204/204` `m4BvaFullEnv_moduleOk` & `m4BvaFullUnsatEnv_moduleOk`,
   `m4_bva_solve_bytes_correct`, and all concrete `Mem 64` UNSAT non-vacuity theorems
   (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace M4BvaAudit

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM4Bva
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Executable `#guard` sanity checks -/

#guard m4Bva_fns.length == 10
#guard m4BvaModule.checkAcyclic == true
#guard m4BvaSpecTable.length == 33
#guard m4BvaFullFns.length == 204
#guard m4BvaFullModule.checkAcyclic == true
#guard (m4BvaFullSpecTable fullSolveBytesSpec).length == 204
#guard full_bva_m4.name == "full_factor"
#guard fullNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096

/-! ## 2. Source-level `Func.wp` sanity check (`X = False`, UNSAT-only, `m4BvaFullEnv`) -/

/-- General `m4_bva_solve_bytes_correct` instantiated on `fullNvUnsatBytes` payload (`4096` B). -/
theorem unsat_payload :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m4BvaFullEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m4_bva_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide))

/-! ## 3. Explicit-type audit handles & single-line `#print axioms` -/

theorem fns_wf : ∀ f ∈ m4Bva_fns, f.Wf := m4Bva_fns_wf
theorem mod_acyc : m4BvaModule.checkAcyclic = true := m4Bva_acyclic
theorem full_wf : ∀ f ∈ m4BvaFullFns, f.Wf := m4BvaFullFns_wf
theorem full_acyc : m4BvaFullModule.checkAcyclic = true := m4BvaFull_acyclic

theorem hop1_wp (Γ : Env) :
    ∀ a m Q X, fullBvaHop1Spec a m Q X → Func.wp Γ FullM4Bva.full_bva_hop1_body a m Q X :=
  m4_bva_hop1_wp Γ

theorem hop2_wp (Γ : Env)
    (h1 : ∀ a m Q X, fullBvaHop1Spec a m Q X → Γ "full_bva_hop1" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullBvaHop2Spec a m Q X → Func.wp Γ FullM4Bva.full_bva_hop2_body a m Q X :=
  m4_bva_hop2_wp Γ h1

theorem hop3_wp (Γ : Env)
    (h2 : ∀ a m Q X, fullBvaHop2Spec a m Q X → Γ "full_bva_hop2" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, m4BvaHop3Spec a m Q X → Func.wp Γ FullM4Bva.full_bva_hop3_body a m Q X :=
  m4_bva_hop3_wp Γ h2

theorem pick_wp (Γ : Env)
    (h3 : ∀ a m Q X, m4BvaHop3Spec a m Q X → Γ "full_bva_hop3" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Func.wp Γ FullM4Bva.full_bva_pick_cand_body a m Q X :=
  m4_bva_pick_cand_wp Γ h3

theorem scan_wp (Γ : Env) :
    ∀ a m Q X, m4BvaScanCandsSpec a m Q X →
      Func.wp Γ FullBvaHeap.full_bva_scan_cands_body a m Q X :=
  m4_bva_scan_cands_wp Γ

theorem filter_wp (Γ : Env)
    (hm : ∀ a m Q X, fullBvaMatchLargeSpec a m Q X →
      Γ "full_bva_match_large" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m4BvaFilterRowSpec a m Q X →
      Func.wp Γ FullM4Bva.full_bva_filter_row_body a m Q X :=
  m4_bva_filter_row_wp Γ hm

theorem commit_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hInit : ∀ a m Q X, fullInitFreshVarHeapSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, m4BvaCommitSpec a m Q X → Func.wp Γ FullM4Bva.full_bva_commit_body a m Q X :=
  m4_bva_commit_wp Γ hDefrag hInit hAddBin hAlloc hWPush hDelBin hUnw

theorem try_lit_wp (Γ : Env)
    (hScan : ∀ a m Q X, m4BvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilt : ∀ a m Q X, m4BvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hComm : ∀ a m Q X, m4BvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBvaTryLitHeapSpec a m Q X →
      Func.wp Γ FullM4Bva.full_bva_try_lit_body a m Q X :=
  m4_bva_try_lit_wp Γ hScan hPick hFilt hComm

theorem factor_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullFheapUpSpec a m Q X →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fullFheapDownSpec a m Q X →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] a m Q X)
    (hTry : ∀ a m Q X, fullBvaTryLitHeapSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullFactorHeapSpec a m Q X → Func.wp Γ FullM4Bva.full_factor_body a m Q X :=
  m4_factor_wp Γ hUp hDown hTry

theorem elim_wp (Γ : Env)
    (hDt : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnt : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X → Func.wp Γ FullM4Bva.full_eliminate_body a m Q X :=
  m4_eliminate_wp Γ hDt hIlog hIsqrt hScale hEnt hFwd hMin hBve hFact hReb

theorem pre_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwp : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPrb : ∀ a m Q X, schedProbeSpec a m Q X → Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, schedEliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullPreprocessSpec a m Q X → Func.wp Γ FullM4Bva.full_preprocess_body a m Q X :=
  m4_preprocess_wp Γ hProp hSwp hScale hMin hPrb hElim

theorem mod_ok : ModuleOk m4BvaEnv m4BvaModule := m4Bva_moduleOk
theorem full_ok : ModuleOk m4BvaFullEnv m4BvaFullModule := m4BvaFullEnv_moduleOk
theorem full_unsat_ok : ModuleOk m4BvaFullUnsatEnv m4BvaFullModule := m4BvaFullUnsatEnv_moduleOk

theorem solve_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4BvaFullEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m4_bva_solve_bytes_correct hcfit hwfit hm

theorem unsat_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m4BvaFullUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m4_bva_unsat_nonvacuous

theorem nv_factor :
    Func.wp m4BvaEnv FullM4Bva.full_factor_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_factor

theorem nv_try_lit :
    Func.wp m4BvaEnv FullM4Bva.full_bva_try_lit_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bva_try_lit

theorem nv_hop3 :
    Func.wp m4BvaEnv FullM4Bva.full_bva_hop3_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bva_hop3

theorem nv_pick :
    Func.wp m4BvaEnv FullM4Bva.full_bva_pick_cand_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bva_pick_cand

#print axioms fns_wf
#print axioms mod_acyc
#print axioms full_wf
#print axioms full_acyc
#print axioms hop1_wp
#print axioms hop2_wp
#print axioms hop3_wp
#print axioms pick_wp
#print axioms scan_wp
#print axioms filter_wp
#print axioms commit_wp
#print axioms try_lit_wp
#print axioms factor_wp
#print axioms elim_wp
#print axioms pre_wp
#print axioms mod_ok
#print axioms full_ok
#print axioms full_unsat_ok
#print axioms solve_ok
#print axioms unsat_nv
#print axioms unsat_payload
#print axioms nv_factor
#print axioms nv_try_lit
#print axioms nv_hop3
#print axioms nv_pick

end M4BvaAudit

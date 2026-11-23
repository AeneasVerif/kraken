/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, `PH_BVA_Q` Guards, Codegen & Axiom Audit (`FullM7FidelityCore`)

1. Executable `#guard` checks on `fidCoreModule` (`9` fns, `23` externs, `32` spec rows, `0`
   exits), `checkAcyclic = true`, `FullM7Splice.patchFns` / `patchBefores` / `patchRows` handles,
   `PH_BVA_Q = 0x02000000` vs `PH_VIV = 0x00100000` bit isolation, `PrintCpp`, `PrintQbe`, and
   4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`.
2. Audit-ready restated headline theorems (`Wf`, `checkAcyclic`, all `9` parametric `Func.wp`
   contracts, standalone `fidCore_moduleOk`, concrete `Mem 64` UNSAT NV `XPost := False`,
   spliced `412`-fn `fidCorePatched_acyclic`, `fidCorePatched_moduleOk`,
   `fidCorePatched_solve_bytes_sound`, `fidCorePatched_unsat_nv`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7FidelityCoreTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7FidelityCore
open Kraken.Bedrock2.Test

/-! ## 1. Module Structure, `PH_BVA_Q`, Codegen, & 4-ISA Legalization Guards -/

#guard fidCoreModule.checkAcyclic == true
#guard fidCoreModule.exits.isEmpty == true
#guard fidCoreFns.length == 9
#guard fidCoreExterns.length == 23
#guard fidCoreSpecTable.length == 32
#guard fidCoreSpecTable.all (·.noExit) == true
#guard fidCoreSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  fidCoreModule.fns.map Fn.sig ++ fidCoreModule.externs.map Extern.sig
#guard fidCoreFns.map Fn.name ==
  [ "full_min_shrink_fid", "full_bva_match_large_fid", "full_bva_scan_cands_fid"
  , "full_bva_filter_row_fid", "full_reorder_sift_fid", "full_reorder_queue_fid"
  , "full_reorder_fid", "full_elim_bve_fid", "full_walk_fid" ]
#guard fidCorePatchFns.length == 7
#guard fidCorePatchRows.length == 7
#guard fidCorePatchFns.map Fn.sig ==
  fidCorePatchRows.map (fun e => (e.name, e.as, e.rs))
#guard fidMinShrinkM6Fn.name == "full_min_shrink_m6"
#guard fidBvaMatchLargeFidFn.name == "full_bva_match_large_fid"
#guard fidBvaScanCandsFn.name == "full_bva_scan_cands"
#guard fidBvaFilterRowFn.name == "full_bva_filter_row"
#guard fidReorderSiftFidFn.name == "full_reorder_sift_fid"
#guard fidReorderQueueM7Fn.name == "full_reorder_queue_m7"
#guard fidReorderM6Fn.name == "full_reorder_m6"
#guard fidElimBveM7Fn.name == "full_elim_bve_m7"
#guard fidWalkM7Fn.name == "full_walk_m7"
#guard fidCorePatchBefores.length == 2
#guard fidCorePatchRowBefores.length == 2
#guard fidCorePatchedFns.length == 412
#guard fidCorePatchedModule.checkAcyclic == true
#guard fidCorePatchedFns.map Fn.sig ==
  (FullM7Splice.patchFns fidCorePatchFns fidCorePatchBefores m7Fns).map Fn.sig
#guard match ppTModule fidCorePatchedModule,
    ppTModule { m7Module with
      fns := FullM7Splice.patchFns fidCorePatchFns fidCorePatchBefores m7Fns } with
  | .ok s1, .ok s2 => s1 == s2
  | _, _ => false
#guard ((0x02000000#32 &&& 0x00100000#32) == 0#32)
#guard ((0x02480000#32 &&& 0x00100000#32) == 0#32)
#guard ((0x02000000#32 ||| 0x00400000#32 ||| 0x00080000#32) == 0x02480000#32)
#guard (ppTModule fidCoreModule).isOk
#guard match ppTModule fidCoreModule with
  | .ok s =>
      (s.splitOn "full_min_shrink_fid").length > 1 &&
      (s.splitOn "full_bva_match_large_fid").length > 1 &&
      (s.splitOn "full_bva_scan_cands_fid").length > 1 &&
      (s.splitOn "full_bva_filter_row_fid").length > 1 &&
      (s.splitOn "full_reorder_sift_fid").length > 1 &&
      (s.splitOn "full_reorder_queue_fid").length > 1 &&
      (s.splitOn "full_reorder_fid").length > 1 &&
      (s.splitOn "full_elim_bve_fid").length > 1 &&
      (s.splitOn "full_walk_fid").length > 1
  | .error _ => false
#guard (PrintQbe.module fidCoreModule).isOk
#guard (ppModule (fidCoreFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidCoreFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidCoreFns.map (Fn.legal .x64AVX2))).isOk
#guard fidCoreFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem fc_fns_wf : ∀ f ∈ fidCoreFns, f.Wf := fidCore_fns_wf
theorem fc_acyc : fidCoreModule.checkAcyclic = true := fidCore_acyclic
theorem fc_nd : (fidCoreSpecTable.map SpecEntry.name).Nodup := fidCoreSpecTable_nodup

theorem fc_no_exit :
    ∀ f as bs xs m Q X X', fidCoreEnv f as bs xs m Q X → fidCoreEnv f as bs xs m Q X' :=
  fidCoreEnv_noExit

theorem fc_min_shrink_wp (Γ : Env)
    (hSt : ∀ args m Q X, FullM7AnalyzeSort.m7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, FullM6MinShrink.m6MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, FullM6MinShrink.m6ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m6" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, FullM7SpecBridges.m7MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_fid_body args m Q X :=
  full_min_shrink_fid_wp Γ hSt hMm hDfs hSb

theorem fc_bva_match_large_wp (Γ : Env) :
    ∀ args m Q X, fidBvaMatchLargeSpec args m Q X →
      Func.wp Γ full_bva_match_large_fid_body args m Q X :=
  full_bva_match_large_fid_wp Γ

theorem fc_bva_scan_cands_wp (Γ : Env) :
    ∀ args m Q X, FullM4Bva.m4BvaScanCandsSpec args m Q X →
      Func.wp Γ full_bva_scan_cands_fid_body args m Q X :=
  full_bva_scan_cands_fid_wp Γ

theorem fc_bva_filter_row_wp (Γ : Env)
    (hMatchLarge : ∀ args m Q X, fidBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large_fid" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, FullM4Bva.m4BvaFilterRowSpec args m Q X →
      Func.wp Γ full_bva_filter_row_fid_body args m Q X :=
  full_bva_filter_row_fid_wp Γ hMatchLarge

theorem fc_reorder_sift_wp (Γ : Env) :
    ∀ a m Q X, fidReorderSiftSpec a m Q X →
      Func.wp Γ full_reorder_sift_fid_body a m Q X :=
  full_reorder_sift_fid_wp Γ

theorem fc_reorder_queue_wp (Γ : Env)
    (hArenaNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec)
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_fid" fidReorderSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp Γ full_reorder_queue_fid_body a m Q X :=
  full_reorder_queue_fid_wp Γ hArenaNext hRescale hHeapUp hSift

theorem fc_reorder_wp (Γ : Env)
    (hQueue : ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Func.wp Γ full_reorder_fid_body a m Q X :=
  full_reorder_fid_wp Γ hQueue

theorem fc_elim_bve_wp (Γ : Env)
    (hFlush : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, FullM6BveFwd.fullBveHeapPushM6Spec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X)
    (hPop : ∀ a m Q X, FullM6BveFwd.fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m7" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, FullM3CongBva.m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m7" [i64, i32] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Func.wp Γ full_elim_bve_fid_body a m Q X :=
  full_elim_bve_fid_wp Γ hFlush hPush hPop hNbrs hBveVar

theorem fc_walk_wp (Γ : Env)
    (hInitVals : ∀ a m Q X, FullM7Walk.m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, FullM7Walk.m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, FullM7Walk.m7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hInitTable : ∀ a m Q X, FullM7Walk.m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    (hBuildOcc : ∀ a m Q X, FullM7Walk.m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, FullM7Walk.m7EffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, FullM7Walk.m7PickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, FullM7Walk.m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, FullM7Walk.m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, .bool] [] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullWalkSpec a m Q X → Func.wp Γ full_walk_fid_body a m Q X :=
  full_walk_fid_wp Γ hInitVals hCollect hCbInv hInitTable hBuildOcc hEffort hPick hFlip
    hSaveMin hRng

theorem fc_mod_ok : ModuleOk fidCoreEnv fidCoreModule := fidCore_moduleOk

theorem fc_nv_rq :
    Func.wp fidCoreEnv full_reorder_queue_fid_body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ s' : FullState,
        s'.core = nvM4TernaryState.core ∧ s'.LengthsOk nvM4TernaryCfg ∧
        FullExtScratchPres nvM4TernaryState s' ∧ nvM4TernaryF0.Unsat ∧
        FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nvFidCore_reorder_queue

theorem fc_nv_ro :
    Func.wp fidCoreEnv full_reorder_fid_body (nvM4TernaryCfg.hdr, 10#64, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ s' : FullState,
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        FullArenaPermEq nvM4TernaryState.core s'.core ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nvFidCore_reorder

theorem fc_nv_wk :
    Func.wp fidCoreEnv full_walk_fid_body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun _ m' => ∃ s' : FullState,
        s'.LengthsOk nvM4TernaryCfg ∧ nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nvFidCore_walk

theorem fc_pat_len : fidCorePatchedFns.length = 412 := fidCorePatchedFns_length
theorem fc_pat_acyc : fidCorePatchedModule.checkAcyclic = true := fidCorePatched_acyclic

theorem fc_pat_ok
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve)
    (hCoreBve : FidCoreBveCallees tBve)
    (hBridge : FidCoreM7BridgeRows (m7SpecTable tBve solveSpec)) :
    ModuleOk (mkFidCorePatchedEnv tBve solveSpec) fidCorePatchedModule :=
  fidCorePatched_moduleOk tBve solveSpec hWeaken hSolveMonoX hBveSigs hBveNoExit hBveSpecs
    hBveOk hCoreBve hBridge

theorem fc_pat_snd
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    (hCoreBve : FidCoreBveCallees tBve)
    (hBridge : FidCoreM7BridgeRows (m7SpecTable tBve fullM6SolveBytesSpec))
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkFidCorePatchedEnv tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidCorePatched_solve_bytes_sound tBve hBveSigs hBveNoExit hBveSpecs hBveOk hCoreBve hBridge
    hcfit hwfit hm

theorem fc_pat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve)
    (hCoreBve : FidCoreBveCallees tBve)
    (hBridge : FidCoreM7BridgeRows (m7SpecTable tBve fullM6SolveBytesCoreModelSpec)) :
    Func.wp (mkFidCorePatchedEnv tBve fullM6SolveBytesCoreModelSpec)
      FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidCorePatched_unsat_nv tBve hBveSigs hBveNoExit hBveSpecs hBveOk hCoreBve hBridge

end AuditSpec

end LeanQbeTest.T.KissatM7FidelityCoreTest

/-! ## 3. Single-Line `< 115c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7fc_wf := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_fns_wf
abbrev m7fc_ac := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_acyc
abbrev m7fc_nd := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_nd
abbrev m7fc_nx := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_no_exit
abbrev m7fc_ms := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_min_shrink_wp
abbrev m7fc_bml := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_bva_match_large_wp
abbrev m7fc_bsc := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_bva_scan_cands_wp
abbrev m7fc_bfr := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_bva_filter_row_wp
abbrev m7fc_rs := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_reorder_sift_wp
abbrev m7fc_rq := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_reorder_queue_wp
abbrev m7fc_ro := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_reorder_wp
abbrev m7fc_eb := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_elim_bve_wp
abbrev m7fc_wk := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_walk_wp
abbrev m7fc_ok := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_mod_ok
abbrev m7fc_nvrq := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_nv_rq
abbrev m7fc_nvro := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_nv_ro
abbrev m7fc_nvwk := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_nv_wk
abbrev m7fc_plen := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_pat_len
abbrev m7fc_pacyc := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_pat_acyc
abbrev m7fc_pok := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_pat_ok
abbrev m7fc_psnd := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_pat_snd
abbrev m7fc_pnv := @LeanQbeTest.T.KissatM7FidelityCoreTest.fc_pat_nv

#print axioms m7fc_wf
#print axioms m7fc_ac
#print axioms m7fc_nd
#print axioms m7fc_nx
#print axioms m7fc_ms
#print axioms m7fc_bml
#print axioms m7fc_bsc
#print axioms m7fc_bfr
#print axioms m7fc_rs
#print axioms m7fc_rq
#print axioms m7fc_ro
#print axioms m7fc_eb
#print axioms m7fc_wk
#print axioms m7fc_ok
#print axioms m7fc_nvrq
#print axioms m7fc_nvro
#print axioms m7fc_nvwk
#print axioms m7fc_plen
#print axioms m7fc_pacyc
#print axioms m7fc_pok
#print axioms m7fc_psnd
#print axioms m7fc_pnv

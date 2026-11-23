/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullBveVarLemmas1

/-!
# Kissat `D-Full` Unified `M6.0` Part 3 (`256..381`, `FullM6Proof0c`)

Assembles `m6RowsPart3Pfx tPfx` (`121` rows) and `m6OrchTailRows solveSpec` (`5` rows) aligned
1-to-1 with `FullM6.m6FnsPart3`, proves `sigs`/`noExit` metadata, certifies the `121`-fn prefix
(including `m6_bce_m4_s15_wp` delayed-watch bridge, `FullM6CompactFlush`, `FullM6BveFwd`, `BVA`,
`Compact`, `FullM7Reorder`, and `4` `FullM6OrchAdapters`), and certifies the `5`-fn tail directly
on `m6FnsPart3.drop 121` using `FullM6OrchProof2`. Plain `public section`, `0` expose tags.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6S15Bridge
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. Part 3 Prefix & Tail Segment Rows (`121` + `5` Entries) -/

private def p3Sweep22Rows : List SpecEntry := FullM4Sweep.fullM4SweepSpecTable.take 22
private def p3SweepDenseM5Rows : List SpecEntry :=
  [⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩]
private def p3FwdDedupBinsRows : List SpecEntry := (fullBaseTable.drop 145).take 1
private def p3BveFwd0Rows : List SpecEntry :=
  [ ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], FullM6BveFwd.fullDensePropUnitM6Spec, true⟩
  , ⟨"full_dense_flush_units_m6", [i64], [.bool], FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_fwd_flush_large_m6", [i64], [], FullM6BveFwd.fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_fwd_reconnect_irred_m6", [i64], [], FullM6BveFwd.fullFwdReconnectIrredM6Spec, true⟩
  , ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32],
      FullM6BveFwd.fullFwdScanLitM6Spec, true⟩
  , ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], FullM6BveFwd.fullFwdCheckClM6Spec, true⟩
  , ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [],
      FullM6BveFwd.fullFwdConnectSubsumerM6Spec, true⟩
  , ⟨"full_fwd_collect_sort_m6", [i64], [i64], FullM6BveFwd.fullFwdCollectSortM6Spec, true⟩
  , ⟨"full_forward_sub_m6", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ ]
private def p3KittenInitRows : List SpecEntry :=
  [⟨"full_kitten_init", [i64, i32, i32], [], Full.fullKittenInitSpec, true⟩]
private def p3Kitten14Rows : List SpecEntry := (Full.fullKittenSpecTable.drop 1).take 14
private def p3KittenDefFix5Rows : List SpecEntry :=
  FullM5KittenDefFix.m5KittenDefFixSpecTable.take 5
private def p3FindDefinitionRows : List SpecEntry :=
  [⟨"full_find_definition", [i64, i32, i32, i32], [], FullDefSweep.fullFindDefinitionSpec, true⟩]
private def p3BveFwd1T5Rows : List SpecEntry :=
  [ ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
      FullM6BveFwd.fullBveMarkAndM6Spec, true⟩
  , ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool],
      FullM6BveFwd.fullBveGetTernM6Spec, true⟩
  , ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
      FullM6BveFwd.fullBveMatchTernM6Spec, true⟩
  , ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool],
      FullM6BveFwd.fullBveFindIteM6Spec, true⟩
  , ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], FullM6BveFwd.fullBveGatesM6Spec, true⟩ ]
private def p3BveCollectRows : List SpecEntry := (fullBaseTable.drop 148).take 1
private def p3BveResPairRows : List SpecEntry := (fullBaseTable.drop 151).take 1
private def p3BveWeakenRows : List SpecEntry :=
  [⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
    FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩]
private def p3BveTryBceRows : List SpecEntry := (fullBaseTable.drop 153).take 1
private def p3BveCommitResRows : List SpecEntry :=
  [⟨"full_bve_commit_res", [i64, i64, i64], [i64],
    FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩]
private def p3BveExtNeedRows : List SpecEntry := (fullBaseTable.drop 155).take 1
private def p3BveFwd1D5Rows : List SpecEntry :=
  [⟨"full_bve_var_m6", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩]
private def p3Adp1213Rows : List SpecEntry :=
  [ ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩ ]
private def p3InitFreshVarM6Rows : List SpecEntry :=
  [⟨"full_init_fresh_var_m6", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩]
private def p3Adp14Rows : List SpecEntry :=
  [⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩]
private def p3BvaHopRows : List SpecEntry := FullM4Bva.m4BvaSpecTable.take 3
private def p3BvaMatchLargeRows : List SpecEntry :=
  [⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], FullBvaHeap.fullBvaMatchLargeSpec, true⟩]
private def p3BvaScanCandsRows : List SpecEntry :=
  [⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩]
private def p3BvaPickCandRows : List SpecEntry :=
  [⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩]
private def p3BvaFilterRowRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 4).take 1
private def p3BvaCommitRows : List SpecEntry :=
  [⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩]
private def p3BvaTryLitRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 6).take 1
private def p3FheapPairRows : List SpecEntry :=
  [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩ ]
private def p3FactorRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 7).take 1
private def p3CfCompact3Rows : List SpecEntry :=
  [ ⟨"full_compact_needed", [i64], [.bool], FullM6CompactFlush.fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩ ]
private def p3Compact10Rows : List SpecEntry := (FullM4Compact.compactSpecTable.drop 3).take 10
private def p3ReorderRows : List SpecEntry :=
  [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.m7ReorderWeightSpec, true⟩
  , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.m7ReorderSiftSpec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩ ]
private def p3VivBce4Rows : List SpecEntry :=
  [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4VivBce.fullBceSideM4Spec, true⟩
  , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.fullBcePairM4Spec, true⟩
  , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.fullBceVarM4Spec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩ ]
private def p3SchedMinMaxRows : List SpecEntry :=
  [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩ ]
private def p3ElimDticksRows : List SpecEntry :=
  [⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩]
private def p3BveFwd2Rows : List SpecEntry :=
  [ ⟨"full_bve_var_key_m6", [i64, i32], [i64], FullM6BveFwd.fullBveVarKeyM6Spec, true⟩
  , ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], FullM6BveFwd.fullBveHeapUpM6Spec, true⟩
  , ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], FullM6BveFwd.fullBveHeapDownM6Spec, true⟩
  , ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], FullM6BveFwd.fullBveHeapPushM6Spec, true⟩
  , ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], FullM6BveFwd.fullBveHeapPopM6Spec, true⟩
  , ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64], FullM3CongBva.m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve_m6", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩ ]
private def p3Adp15Rows : List SpecEntry :=
  [⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩]

/-- Part 3 prefix rows (`256..376`, `121` entries) aligned with `m6FnsPart3.take 121`. -/
def m6RowsPart3Pfx (tPfx : List SpecEntry) : List SpecEntry :=
  p3Sweep22Rows ++ (p3SweepDenseM5Rows ++ ((tPfx.drop 18).take 1 ++ (p3FwdDedupBinsRows ++
  (p3BveFwd0Rows ++ (p3KittenInitRows ++ (p3Kitten14Rows ++ (p3KittenDefFix5Rows ++
  (p3FindDefinitionRows ++ (p3BveFwd1T5Rows ++ (p3BveCollectRows ++ (p3BveResPairRows ++
  (p3BveWeakenRows ++ (p3BveTryBceRows ++ (p3BveCommitResRows ++ (p3BveExtNeedRows ++
  (p3BveFwd1D5Rows ++ (p3Adp1213Rows ++ (p3InitFreshVarM6Rows ++ (p3Adp14Rows ++
  (p3BvaHopRows ++ (p3BvaMatchLargeRows ++ (p3BvaScanCandsRows ++ (p3BvaPickCandRows ++
  (p3BvaFilterRowRows ++ (p3BvaCommitRows ++ (p3BvaTryLitRows ++ (p3FheapPairRows ++
  (p3FactorRows ++ (p3CfCompact3Rows ++ (p3Compact10Rows ++ (p3ReorderRows ++
  ((tPfx.drop 19).take 1 ++ (p3VivBce4Rows ++ (p3SchedMinMaxRows ++ (p3ElimDticksRows ++
  (p3BveFwd2Rows ++ (p3Adp15Rows ++ (tPfx.drop 20).take 4)))))))))))))))))))))))))))))))))))))

/-- Part 3 tail rows (`377..381`, `5` entries) aligned with `m6FnsPart3.drop 121`. -/
def m6OrchTailRows
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesCoreModelSpec) :
    List SpecEntry :=
  [ ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_search", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩ ]

/-! ## 2. Part 3 Function Decomposition & Metadata -/

private def p3Sweep22Fns : List Fn := FullM4Sweep.fullM4Sweep_fns.take 22
private def p3SweepDenseM5Fns : List Fn := (FullM5.m5Fns.drop 200).take 1
private def p3FwdDedupBinsFns : List Fn := (Full.fullFns.drop 145).take 1
private def p3BveFwd0Fns : List Fn := FullM6BveFwd.m6BveFwd_fns.take 10
private def p3KittenInitFns : List Fn := (FullM5.m5Fns.drop 147).take 1
private def p3Kitten14Fns : List Fn := (Full.fullKittenModule.fns.drop 1).take 14
private def p3KittenDefFix5Fns : List Fn := FullM5KittenDefFix.m5KittenDefFix_fns.take 5
private def p3FindDefinitionFns : List Fn := (FullM5.m5Fns.drop 211).take 1
private def p3BveFwd1T5Fns : List Fn := (FullM6BveFwd.m6BveFwd_fns.drop 10).take 5
private def p3BveCollectFns : List Fn := (Full.fullFns.drop 148).take 1
private def p3BveResPairFns : List Fn := (Full.fullFns.drop 151).take 1
private def p3BveWeakenFns : List Fn := (Full.fullFns.drop 152).take 1
private def p3BveTryBceFns : List Fn := (Full.fullFns.drop 153).take 1
private def p3BveCommitResFns : List Fn := (Full.fullFns.drop 154).take 1
private def p3BveExtNeedFns : List Fn := (Full.fullFns.drop 155).take 1
private def p3BveFwd1D5Fns : List Fn := (FullM6BveFwd.m6BveFwd_fns.drop 15).take 1
private def p3Adp1213Fns : List Fn := [m6aBveVarFn, m6aForwardSubFn]
private def p3InitFreshVarM6Fns : List Fn := (FullM6VivBackbone.m6VivBackbone_fns.drop 1).take 1
private def p3Adp14Fns : List Fn := [m6aInitFreshVarFn]
private def p3BvaHopFns : List Fn := FullM4Bva.m4Bva_fns.take 3
private def p3BvaMatchLargeFns : List Fn := (FullM5.m5Fns.drop 223).take 1
private def p3BvaScanCandsFns : List Fn := (FullM5.m5Fns.drop 224).take 1
private def p3BvaPickCandFns : List Fn := FullM6BvaNoHops.m6BvaNoHopsFns
private def p3BvaFilterRowFns : List Fn := (FullM4Bva.m4Bva_fns.drop 4).take 1
private def p3BvaCommitFns : List Fn := (FullM5.m5Fns.drop 227).take 1
private def p3BvaTryLitFns : List Fn := (FullM4Bva.m4Bva_fns.drop 6).take 1
private def p3FheapPairFns : List Fn := (FullM5.m5Fns.drop 229).take 2
private def p3FactorFns : List Fn := (FullM4Bva.m4Bva_fns.drop 7).take 1
private def p3CfCompact3Fns : List Fn :=
  [ FullM6CompactFlush.m6cfCompactNeededFn
  , FullM6CompactFlush.m6cfCompactFlushFn
  , FullM6CompactFlush.m6cfCompactMarkLiveFn ]
private def p3Compact10Fns : List Fn := (FullM4Compact.compact_fns.drop 3).take 10
private def p3ReorderFns : List Fn := FullM7Reorder.m7ReorderFns
private def p3VivBce4Fns : List Fn := (FullM4VivBce.m4VivBce_fns.drop 12).take 4
private def p3SchedMinMaxFns : List Fn := (FullM5.m5Fns.drop 252).take 2
private def p3ElimDticksFns : List Fn := [m6CanonicalElimDticksFn]
private def p3BveFwd2Fns : List Fn := FullM6BveFwd.m6BveFwd_fns.drop 16
private def p3Adp15Fns : List Fn := [m6aProbeDticksM6HdrFn]

private def p3PfxSeg : List Fn :=
  p3Sweep22Fns ++ (p3SweepDenseM5Fns ++ (((m6Orch_fns.take 24).drop 18).take 1 ++
  (p3FwdDedupBinsFns ++ (p3BveFwd0Fns ++ (p3KittenInitFns ++ (p3Kitten14Fns ++
  (p3KittenDefFix5Fns ++ (p3FindDefinitionFns ++ (p3BveFwd1T5Fns ++ (p3BveCollectFns ++
  (p3BveResPairFns ++ (p3BveWeakenFns ++ (p3BveTryBceFns ++ (p3BveCommitResFns ++
  (p3BveExtNeedFns ++ (p3BveFwd1D5Fns ++ (p3Adp1213Fns ++ (p3InitFreshVarM6Fns ++
  (p3Adp14Fns ++ (p3BvaHopFns ++ (p3BvaMatchLargeFns ++ (p3BvaScanCandsFns ++
  (p3BvaPickCandFns ++ (p3BvaFilterRowFns ++ (p3BvaCommitFns ++ (p3BvaTryLitFns ++
  (p3FheapPairFns ++ (p3FactorFns ++ (p3CfCompact3Fns ++ (p3Compact10Fns ++ (p3ReorderFns ++
  (((m6Orch_fns.take 24).drop 19).take 1 ++ (p3VivBce4Fns ++ (p3SchedMinMaxFns ++
  (p3ElimDticksFns ++ (p3BveFwd2Fns ++ (p3Adp15Fns ++
    ((m6Orch_fns.take 24).drop 20).take 4)))))))))))))))))))))))))))))))))))))

private def p3TailSeg : List Fn :=
  [ m6oSearchM6Fn, m6oSolveBytesM6Fn, m6oPreprocessFn, m6oSearchFn, m6oSolveBytesFn ]

private theorem p3Pfx_eq : m6FnsPart3.take 121 = p3PfxSeg := by t_kernel_rfl
private theorem p3Tail_eq : m6FnsPart3.drop 121 = p3TailSeg := by t_kernel_rfl

theorem m6RowsPart3Pfx_sigs {tPfx : List SpecEntry}
    (hsig : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    (m6RowsPart3Pfx tPfx).map (fun e => (e.name, e.as, e.rs)) =
      (m6FnsPart3.take 121).map Fn.sig := by
  have s01 : p3Sweep22Rows.map (fun e => (e.name, e.as, e.rs)) = p3Sweep22Fns.map Fn.sig := by
    t_kernel_rfl
  have s02 : p3SweepDenseM5Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3SweepDenseM5Fns.map Fn.sig := by t_kernel_rfl
  have s03 : p3FwdDedupBinsRows.map (fun e => (e.name, e.as, e.rs)) =
      p3FwdDedupBinsFns.map Fn.sig := by t_kernel_rfl
  have s04 : p3BveFwd0Rows.map (fun e => (e.name, e.as, e.rs)) = p3BveFwd0Fns.map Fn.sig := by
    t_kernel_rfl
  have s05 : p3KittenInitRows.map (fun e => (e.name, e.as, e.rs)) = p3KittenInitFns.map Fn.sig := by
    t_kernel_rfl
  have s06 : p3Kitten14Rows.map (fun e => (e.name, e.as, e.rs)) = p3Kitten14Fns.map Fn.sig := by
    t_kernel_rfl
  have s07 : p3KittenDefFix5Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3KittenDefFix5Fns.map Fn.sig := by t_kernel_rfl
  have s08 : p3FindDefinitionRows.map (fun e => (e.name, e.as, e.rs)) =
      p3FindDefinitionFns.map Fn.sig := by t_kernel_rfl
  have s09 : p3BveFwd1T5Rows.map (fun e => (e.name, e.as, e.rs)) = p3BveFwd1T5Fns.map Fn.sig := by
    t_kernel_rfl
  have s10 : p3BveCollectRows.map (fun e => (e.name, e.as, e.rs)) = p3BveCollectFns.map Fn.sig := by
    t_kernel_rfl
  have s11 : p3BveResPairRows.map (fun e => (e.name, e.as, e.rs)) = p3BveResPairFns.map Fn.sig := by
    t_kernel_rfl
  have s12 : p3BveWeakenRows.map (fun e => (e.name, e.as, e.rs)) = p3BveWeakenFns.map Fn.sig := by
    t_kernel_rfl
  have s13 : p3BveTryBceRows.map (fun e => (e.name, e.as, e.rs)) = p3BveTryBceFns.map Fn.sig := by
    t_kernel_rfl
  have s14 : p3BveCommitResRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BveCommitResFns.map Fn.sig := by t_kernel_rfl
  have s15 : p3BveExtNeedRows.map (fun e => (e.name, e.as, e.rs)) = p3BveExtNeedFns.map Fn.sig := by
    t_kernel_rfl
  have s16 : p3BveFwd1D5Rows.map (fun e => (e.name, e.as, e.rs)) = p3BveFwd1D5Fns.map Fn.sig := by
    t_kernel_rfl
  have s17 : p3Adp1213Rows.map (fun e => (e.name, e.as, e.rs)) = p3Adp1213Fns.map Fn.sig := by
    t_kernel_rfl
  have s18 : p3InitFreshVarM6Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3InitFreshVarM6Fns.map Fn.sig := by t_kernel_rfl
  have s19 : p3Adp14Rows.map (fun e => (e.name, e.as, e.rs)) = p3Adp14Fns.map Fn.sig := by
    t_kernel_rfl
  have s20 : p3BvaHopRows.map (fun e => (e.name, e.as, e.rs)) = p3BvaHopFns.map Fn.sig := by
    t_kernel_rfl
  have s21 : p3BvaMatchLargeRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaMatchLargeFns.map Fn.sig := by t_kernel_rfl
  have s22 : p3BvaScanCandsRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaScanCandsFns.map Fn.sig := by t_kernel_rfl
  have s23 : p3BvaPickCandRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaPickCandFns.map Fn.sig := by t_kernel_rfl
  have s24 : p3BvaFilterRowRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaFilterRowFns.map Fn.sig := by t_kernel_rfl
  have s25 : p3BvaCommitRows.map (fun e => (e.name, e.as, e.rs)) = p3BvaCommitFns.map Fn.sig := by
    t_kernel_rfl
  have s26 : p3BvaTryLitRows.map (fun e => (e.name, e.as, e.rs)) = p3BvaTryLitFns.map Fn.sig := by
    t_kernel_rfl
  have s27 : p3FheapPairRows.map (fun e => (e.name, e.as, e.rs)) = p3FheapPairFns.map Fn.sig := by
    t_kernel_rfl
  have s28 : p3FactorRows.map (fun e => (e.name, e.as, e.rs)) = p3FactorFns.map Fn.sig := by
    t_kernel_rfl
  have s29 : p3CfCompact3Rows.map (fun e => (e.name, e.as, e.rs)) = p3CfCompact3Fns.map Fn.sig := by
    t_kernel_rfl
  have s30 : p3Compact10Rows.map (fun e => (e.name, e.as, e.rs)) = p3Compact10Fns.map Fn.sig := by
    t_kernel_rfl
  have s31 : p3ReorderRows.map (fun e => (e.name, e.as, e.rs)) = p3ReorderFns.map Fn.sig := by
    t_kernel_rfl
  have s32 : p3VivBce4Rows.map (fun e => (e.name, e.as, e.rs)) = p3VivBce4Fns.map Fn.sig := by
    t_kernel_rfl
  have s33 : p3SchedMinMaxRows.map (fun e => (e.name, e.as, e.rs)) =
      p3SchedMinMaxFns.map Fn.sig := by t_kernel_rfl
  have s34 : p3ElimDticksRows.map (fun e => (e.name, e.as, e.rs)) = p3ElimDticksFns.map Fn.sig := by
    t_kernel_rfl
  have s35 : p3BveFwd2Rows.map (fun e => (e.name, e.as, e.rs)) = p3BveFwd2Fns.map Fn.sig := by
    t_kernel_rfl
  have s36 : p3Adp15Rows.map (fun e => (e.name, e.as, e.rs)) = p3Adp15Fns.map Fn.sig := by
    t_kernel_rfl
  rw [p3Pfx_eq]
  simp only [m6RowsPart3Pfx, p3PfxSeg, List.map_append, s01, s02, s03, s04, s05, s06, s07, s08,
    s09, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27,
    s28, s29, s30, s31, s32, s33, s34, s35, s36, pfxSlice_sigs hsig]

theorem m6RowsPart3Pfx_noExit {tPfx : List SpecEntry}
    (hno : tPfx.all SpecEntry.noExit = true) :
    (m6RowsPart3Pfx tPfx).all SpecEntry.noExit = true := by
  have n01 : p3Sweep22Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n02 : p3SweepDenseM5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n03 : p3FwdDedupBinsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n04 : p3BveFwd0Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n05 : p3KittenInitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n06 : p3Kitten14Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n07 : p3KittenDefFix5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n08 : p3FindDefinitionRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n09 : p3BveFwd1T5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n10 : p3BveCollectRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n11 : p3BveResPairRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n12 : p3BveWeakenRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n13 : p3BveTryBceRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n14 : p3BveCommitResRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n15 : p3BveExtNeedRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n16 : p3BveFwd1D5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n17 : p3Adp1213Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n18 : p3InitFreshVarM6Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n19 : p3Adp14Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n20 : p3BvaHopRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n21 : p3BvaMatchLargeRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n22 : p3BvaScanCandsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n23 : p3BvaPickCandRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n24 : p3BvaFilterRowRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n25 : p3BvaCommitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n26 : p3BvaTryLitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n27 : p3FheapPairRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n28 : p3FactorRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n29 : p3CfCompact3Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n30 : p3Compact10Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n31 : p3ReorderRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n32 : p3VivBce4Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n33 : p3SchedMinMaxRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n34 : p3ElimDticksRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n35 : p3BveFwd2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n36 : p3Adp15Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  simp only [m6RowsPart3Pfx, List.all_append, n01, n02, n03, n04, n05, n06, n07, n08, n09, n10, n11,
    n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30,
    n31, n32, n33, n34, n35, n36, pfxSlice_noExit hno, Bool.and_self]

theorem m6OrchTailRows_sigs
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchTailRows solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      (m6FnsPart3.drop 121).map Fn.sig := by
  rw [p3Tail_eq]; rfl

theorem m6OrchTailRows_noExit
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchTailRows solveSpec).all SpecEntry.noExit = true := by
  simp only [m6OrchTailRows, List.all_cons, List.all_nil, Bool.and_true]

/-! ## 3. Local Adapter & `S1.5` Helper Proofs (`full_init_fresh_var` Heap & `full_bce_m4`) -/

private theorem full_init_fresh_var_heap_wp (Γ : Env)
    (hInitFv : ∀ a m Q X, FullBvaHeap.fullInitFreshVarHeapSpec a m Q X →
      Γ "full_init_fresh_var_m6" [i64, i32] [] a m Q X) :
    ∀ a m Q X, FullBvaHeap.fullInitFreshVarHeapSpec a m Q X →
      Func.wp Γ FullM6OrchAdapters.full_init_fresh_var_body a m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv, hm, hQ⟩
  unfold Func.wp FullM6OrchAdapters.full_init_fresh_var_body
  c0_hsteps_nogrp
  c0_call hInitFv
  refine ⟨c, s, R, rfl, hslen, hfv, hm,
    fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m'
      hlen' hext' hsb hws htm htr hsig hv0 hv1 hvo hm0 hmo hl0 hlo hr0 hro hw0 hwo hm' => ?_⟩
  c0_steps
  exact hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m'
    hlen' hext' hsb hws htm htr hsig hv0 hv1 hvo hm0 hmo hl0 hlo hr0 hro hw0 hwo hm'

section BceS15Section

open LeanQbe.T.Examples.Kissat.FullM4VivBce
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics M4Tactics

private theorem bv64_toNat_setWidth32_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

private theorem m6_bce_m4_s15_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold LratBytes.dimacsBound at hmx
  unfold Func.wp full_bce_m4_body
  fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    c0_call hEnterDense
    refine ⟨c, F0, s, R, rfl, hsp0, hm0, fun ok s1 m1 hcl1 hfl1 hok_t hok_f hm1 => ?_⟩
    fvt_to_group
    · have hdn1 : FullDenseInv c F0 s1 := hok_t (by c0_bound)
      obtain ⟨F_cur1, hdw1⟩ := FullBveVarHelpers.fullDenseInv_exists_witness hdn1
      have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hdw1.1.core_ok.cur_vars_le
      fvt_steps
      refine wp_loop_inv (ts := [i64, i64])
        (fun (v, done, ()) ml => ∃ sl : FullState,
          FullDenseInvW c F0 F_cur1 sl ∧ sl.core.cur_vars = s1.core.cur_vars ∧
          sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧ v.toNat ≤ s1.core.cur_vars ∧
          (FullMem c sl ⋆ R) ml)
        (fun (v, _, _) _ => s1.core.cur_vars - v.toNat) ?_ ?_
      · intro J hJ; fvt_steps
        exact hJ (0#64, 0#64, ()) m1 ⟨s1, hdw1, rfl, hfl1, Nat.zero_le _, hm1⟩
      · intro J ⟨v, done, ⟨⟩⟩ ml ⟨sl, hinvl, hcvl, hfll, hv_le, hml⟩ ih
        have hv_lt_cv_of : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat →
            v.toNat < s1.core.cur_vars := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact id
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () m_ex => ∃ s_ex : FullState,
            FullDenseInvW c F0 F_cur1 s_ex ∧ s_ex.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c s_ex ⋆ R) m_ex) ?_ ?_
        · rintro _ ⟨⟩ m_ex ⟨s_ex, hinv_ex, hfl_ex, hm_ex⟩
          c0_call hRebuild
          refine ⟨c, F0, s_ex, R, rfl, hinv_ex.toDense, hm_ex,
            fun rr s3 m3 hsp3 hcl3 hfl3 _ h20_3 hm3 => ?_⟩
          fvt_steps
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => h20_3 (by c0_bound)) hm3
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => m4_unsat_of_inconsistent hsp3 (by c0_bound)) hm3
          · obtain ⟨F_cur3, hsw3⟩ := hsp3.exists_witness
            c0_call hProp
            refine ⟨c, F0, F_cur3, s3, R, rfl, hsw3.1, hsw3.2.1, hsw3.2.2.2.2.2, hm3,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s4_c : FullState :=
              { s3 with
                core := { s3.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s3.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p } }
            have hlen_c : s4_c.LengthsOk c :=
              ⟨hlen_p.core_ok, { hlen_p.scratch_ok with
                delayed_len_arr := hsw3.1.scratch_ok.delayed_len_arr }⟩
            have hsw4_c : FullSparseInvW c F0 F_cur3 s4_c :=
              m4_sparseInvW_of_prop_canon hsw3 hlen_c hw_p hperm_p
            let s4 : FullState :=
              { s4_c with scratch := { s4_c.scratch with delayed := delayed_p } }
            have hsp4 : FullSparseInv c F0 s4 :=
              ⟨⟨hlen_p, F_cur3, hsw4_c.2.1⟩, hsw4_c.2.2.1, hsw4_c.2.2.2.1, hsw4_c.2.2.2.2.1,
                hsw4_c.2.2.2.2.2⟩
            have hfl4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfl_p (Nat.le_trans hfl3 hfl_ex)
            fvt_steps
            all_goals first
              | exact hQ 1#64 s4 m_p hsp4 hcl3 hfl4 (Or.inl rfl)
                  (fun h => by cases h) hm_p
              | exact hQ 20#64 s4 m_p hsp4 hcl3 hfl4 (Or.inr rfl)
                  (fun _ => FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl3
                    (hpr1 (by c0_bound)).2.2) hm_p
        · intro Jex hJex
          fvt_to_group
          · have hv_lt : v.toNat < s1.core.cur_vars := hv_lt_cv_of (by c0_bound)
            have hv_fl : v.toNat < sl.core.flags.length := by
              rw [hinvl.1.core_ok.flags_len]; omega
            have hv2_lt : (v <<< (BitVec.toNat (1 : BitVec 64) % 64)).toNat <
                sl.core.vals.length := by
              rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
                Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hinvl.1.core_ok.vals_len]
              omega
            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
            refine wp_join_group (ts := [i64])
              (fun (done', ()) mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur1 sj ∧ sj.core.cur_vars = s1.core.cur_vars ∧
                sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj) ?_ ?_
            · rintro _ ⟨done', ⟨⟩⟩ mj ⟨sj, hinvj, hcvj, hflj, hmj⟩
              fvt_steps
              exact ih (v + 1#64, done', ()) mj (by dsimp only; omega)
                ⟨sj, hinvj, hcvj, hflj, by omega, hmj⟩
            · intro Jv hJv
              fvt_steps
              · c0_call hBceVar
                refine ⟨c, F0, F_cur1, sl, R, rfl, hinvl,
                  by rw [bv64_toNat_setWidth32_lt (by omega), hcvl]; exact hv_lt, hml,
                  fun sv mv hinvv hcvv hflv hmv =>
                    hJv (done + 1#64, ()) mv ⟨sv, hinvv, hcvv.trans hcvl,
                      by rw [hflv]; exact hfll, hmv⟩⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
          all_goals exact hJex () ml ⟨sl, hinvl, hfll, hml⟩
    · have hsp1 : FullSparseInv c F0 s1 := hok_f (by c0_bound)
      fvt_steps
      · exact hQ 20#64 s1 m1 hsp1 hcl1 hfl1 (Or.inr rfl)
          (fun _ => m4_unsat_of_inconsistent hsp1 (by c0_bound)) hm1
      · exact hQ 1#64 s1 m1 hsp1 hcl1 hfl1 (Or.inl rfl)
          (fun h => by cases h) hm1

end BceS15Section

/-! ## 4. Part 3 Segment `TableImpl` Helpers -/

private theorem p3BveFwd0_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3BveFwd0Rows, e ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hUnw : ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hDed : ⟨"full_fwd_dedup_bins", [i64], [.bool], Full.fullFwdDedupBinsSpec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3BveFwd0Fns p3BveFwd0Rows := by
  have hfn : p3BveFwd0Fns =
      [ ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], FullM6BveFwd.full_dense_prop_unit_m6_body⟩
      , ⟨"full_dense_flush_units_m6", [i64], [.bool], FullM6BveFwd.full_dense_flush_units_m6_body⟩
      , ⟨"full_fwd_flush_large_m6", [i64], [], FullM6BveFwd.full_fwd_flush_large_m6_body⟩
      , ⟨"full_fwd_reconnect_irred_m6", [i64], [],
          FullM6BveFwd.full_fwd_reconnect_irred_m6_body⟩
      , ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32],
          FullM6BveFwd.full_fwd_scan_lit_m6_body⟩
      , ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], FullM6BveFwd.full_fwd_check_cl_m6_body⟩
      , ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [],
          FullM6BveFwd.full_fwd_connect_subsumer_m6_body⟩
      , ⟨"full_fwd_collect_sort_m6", [i64], [i64], FullM6BveFwd.full_fwd_collect_sort_m6_body⟩
      , ⟨"full_forward_sub_m6", [i64, i64], [i64], FullM6BveFwd.full_forward_sub_m6_body⟩
      , ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32],
          FullM6BveFwd.full_bve_collect_m6_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have rWp := envRow_mem hnd _ _ _ _ hWp; have rNext := envRow_mem hnd _ _ _ _ hNext
  have r1 := er 1 rfl FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit
  have r2 := er 2 rfl FullM6BveFwd.fullFwdFlushLargeM6Spec_noExit
  rw [hfn]; unfold p3BveFwd0Rows
  exact ⟨ SpecEntry.Impl.of (FullM6BveFwd.full_dense_prop_unit_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hAu))
    , SpecEntry.Impl.of (FullM6BveFwd.full_dense_flush_units_m6_wp (Env.ofTable tbl)
        (er 0 rfl FullM6BveFwd.fullDensePropUnitM6Spec_noExit))
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_flush_large_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDef))
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_reconnect_irred_m6_wp (Env.ofTable tbl)
        r2 rNext rWp)
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_scan_lit_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_check_cl_m6_wp (Env.ofTable tbl)
        (er 4 rfl FullM6BveFwd.fullFwdScanLitM6Spec_noExit) (envRow_mem hnd _ _ _ _ hUnw)
        (envRow_mem hnd _ _ _ _ hAu) (envRow_mem hnd _ _ _ _ hAb) r1)
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_connect_subsumer_m6_wp (Env.ofTable tbl) rWp)
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_collect_sort_m6_wp (Env.ofTable tbl) rNext)
    , SpecEntry.Impl.of (FullM6BveFwd.full_forward_sub_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDed) r1 (er 7 rfl FullM6BveFwd.fullFwdCollectSortM6Spec_noExit)
        r2 (er 5 rfl FullM6BveFwd.fullFwdCheckClM6Spec_noExit)
        (er 6 rfl FullM6BveFwd.fullFwdConnectSubsumerM6Spec_noExit) rNext
        (er 3 rfl FullM6BveFwd.fullFwdReconnectIrredM6Spec_noExit))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_collect_m6_wp (Env.ofTable tbl)), trivial ⟩

private theorem p3BveFwd1T5_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3BveFwd1T5Rows, e ∈ tbl)
    (hFindDef : ⟨"full_find_definition", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3BveFwd1T5Fns p3BveFwd1T5Rows := by
  have hfn : p3BveFwd1T5Fns =
      [ ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
          FullM6BveFwd.full_bve_mark_and_m6_body⟩
      , ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool],
          FullM6BveFwd.full_bve_get_tern_m6_body⟩
      , ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
          FullM6BveFwd.full_bve_match_tern_m6_body⟩
      , ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool],
          FullM6BveFwd.full_bve_find_ite_m6_body⟩
      , ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], FullM6BveFwd.full_bve_gates_m6_body⟩ ] :=
    rfl
  have er := envRowAt hnd hown
  have rGt := er 1 rfl FullM6BveFwd.fullBveGetTernM6Spec_noExit
  rw [hfn]; unfold p3BveFwd1T5Rows
  exact ⟨ SpecEntry.Impl.of (FullM6BveFwd.full_bve_mark_and_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_get_tern_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_match_tern_m6_wp (Env.ofTable tbl) rGt)
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_find_ite_m6_wp (Env.ofTable tbl) rGt
        (er 2 rfl FullM6BveFwd.fullBveMatchTernM6Spec_noExit))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_gates_m6_wp (Env.ofTable tbl)
        (er 0 rfl FullM6BveFwd.fullBveMarkAndM6Spec_noExit)
        (er 3 rfl FullM6BveFwd.fullBveFindIteM6Spec_noExit)
        (envRow_mem hnd _ _ _ _ hFindDef)), trivial ⟩

private theorem p3Adp1213_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hBveVarM6 : ⟨"full_bve_var_m6", [i64, i32], [i64],
      FullFastBveBudgets.fullBveVarDefSpec, true⟩ ∈ tbl)
    (hFwdSubM6 : ⟨"full_forward_sub_m6", [i64, i64], [i64],
      FullFastBveBudgets.fullForwardSubFastSpec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3Adp1213Fns p3Adp1213Rows := by
  unfold p3Adp1213Fns p3Adp1213Rows
  exact ⟨ SpecEntry.Impl.of (full_bve_var_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hBveVarM6))
    , SpecEntry.Impl.of (full_forward_sub_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFwdSubM6)), trivial ⟩

private theorem p3CfCompact3_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hFlush : ⟨"full_flush_trail", [i64], [i64],
      FullM6CompactFlush.fullFlushTrailSpec, true⟩ ∈ tbl)
    (hSweep : ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3CfCompact3Fns p3CfCompact3Rows := by
  unfold p3CfCompact3Fns p3CfCompact3Rows
  exact ⟨ SpecEntry.Impl.of (FullM6CompactFlush.full_compact_needed_m6cf_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CompactFlush.full_compact_flush_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFlush) (envRow_mem hnd _ _ _ _ hSweep))
    , SpecEntry.Impl.of (FullM6CompactFlush.full_compact_mark_live_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext)), trivial ⟩

private theorem p3Reorder_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3ReorderRows, e ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3ReorderFns p3ReorderRows := by
  have hfn : p3ReorderFns =
      [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.full_reorder_weight_m7_body⟩
      , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.full_reorder_sift_m7_body⟩
      , ⟨"full_reorder_queue_m7", [i64], [i64], FullM7Reorder.full_reorder_queue_m7_body⟩ ] := rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p3ReorderRows
  exact ⟨ SpecEntry.Impl.of (FullM7Reorder.full_reorder_weight_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_queue_m7_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderWeightSpec_noExit h))
        (envRow_mem hnd _ _ _ _ hNext)
        (er 1 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderSiftSpec_noExit h))), trivial ⟩

private theorem p3VivBce4_s15_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3VivBce4Rows, e ∈ tbl)
    (hBce : ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool],
      Full.fullBveTryBceSpec, true⟩ ∈ tbl)
    (hEp2 : ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ ∈ tbl)
    (hEpCl : ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ ∈ tbl)
    (hDelBin : ⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ ∈ tbl)
    (hCol : ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ ∈ tbl)
    (hEd : ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩ ∈ tbl)
    (hReb : ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3VivBce4Fns p3VivBce4Rows := by
  have hfn : p3VivBce4Fns =
      [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
          FullM4VivBce.full_bce_side_m4_body⟩
      , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.full_bce_pair_m4_body⟩
      , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.full_bce_var_m4_body⟩
      , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.full_bce_m4_body⟩ ] := rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p3VivBce4Rows
  exact ⟨ SpecEntry.Impl.of (FullM4VivBce.full_bce_side_m4_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBce)
        (m6_extend_push2_tmk_to_canon (envRow_mem hnd _ _ _ _ hEp2))
        (m6_extend_push_cl_tmk_to_canon (envRow_mem hnd _ _ _ _ hEpCl))
        (envRow_mem hnd _ _ _ _ hDelBin))
    , SpecEntry.Impl.of (FullM4VivBce.full_bce_pair_m4_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM4VivBce.full_bce_var_m4_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hCol) (er 1 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (m6_bce_m4_s15_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hEd)
        (er 2 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hReb)
        (envRow_mem hnd _ _ _ _ hProp)), trivial ⟩

private theorem p3BveFwd2_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3BveFwd2Rows, e ∈ tbl)
    (hFlushU : ⟨"full_dense_flush_units_m6", [i64], [.bool],
      FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩ ∈ tbl)
    (hBveVar : ⟨"full_bve_var_m6", [i64, i32], [i64],
      FullFastBveBudgets.fullBveVarDefSpec, true⟩ ∈ tbl)
    (hElimDt : ⟨"full_elim_dticks", [i64, .bool], [i64],
      FullFastSched.schedElimDticksSpec, true⟩ ∈ tbl)
    (hIlog : ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ ∈ tbl)
    (hScale : ⟨"full_scale_delta", [i64, i64], [i64],
      FullFastSched.schedScaleDeltaSpec, true⟩ ∈ tbl)
    (hEd : ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩ ∈ tbl)
    (hMinU : ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩ ∈ tbl)
    (hFwdSub : ⟨"full_forward_sub_m6", [i64, i64], [i64],
      FullFastBveBudgets.fullForwardSubFastSpec, true⟩ ∈ tbl)
    (hFactor : ⟨"full_factor", [i64, i64], [i64], FullM3CongBva.fullFactorHeapSpec, true⟩ ∈ tbl)
    (hReb : ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3BveFwd2Fns p3BveFwd2Rows := by
  have hfn : p3BveFwd2Fns =
      [ ⟨"full_bve_var_key_m6", [i64, i32], [i64], FullM6BveFwd.full_bve_var_key_m6_body⟩
      , ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], FullM6BveFwd.full_bve_heap_up_m6_body⟩
      , ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], FullM6BveFwd.full_bve_heap_down_m6_body⟩
      , ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], FullM6BveFwd.full_bve_heap_push_m6_body⟩
      , ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], FullM6BveFwd.full_bve_heap_pop_m6_body⟩
      , ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64],
          FullM6BveFwd.full_bve_collect_nbrs_m6_body⟩
      , ⟨"full_elim_bve_m6", [i64, i64], [i64], FullM6BveFwd.full_elim_bve_m6_body⟩
      , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullM6BveFwd.full_eliminate_m6_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have rDown := er 2 rfl FullM6BveFwd.fullBveHeapDownM6Spec_noExit
  rw [hfn]; unfold p3BveFwd2Rows
  exact ⟨ SpecEntry.Impl.of (FullM6BveFwd.full_bve_var_key_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_up_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_down_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_push_m6_wp (Env.ofTable tbl)
        (er 0 rfl FullM6BveFwd.fullBveVarKeyM6Spec_noExit)
        (er 1 rfl FullM6BveFwd.fullBveHeapUpM6Spec_noExit) rDown)
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_pop_m6_wp (Env.ofTable tbl) rDown)
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_collect_nbrs_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_elim_bve_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFlushU FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit)
        (er 3 rfl FullM6BveFwd.fullBveHeapPushM6Spec_noExit)
        (er 4 rfl FullM6BveFwd.fullBveHeapPopM6Spec_noExit)
        (er 5 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hBveVar))
    , SpecEntry.Impl.of (FullM6BveFwd.full_eliminate_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hElimDt) (envRow_mem hnd _ _ _ _ hIlog)
        (envRow_mem hnd _ _ _ _ hScale) (envRow_mem hnd _ _ _ _ hEd)
        (envRow_mem hnd _ _ _ _ hMinU) (envRow_mem hnd _ _ _ _ hFwdSub)
        (er 6 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hFactor)
        (envRow_mem hnd _ _ _ _ hReb)), trivial ⟩

/-! ## 5. Part 3 Prefix `TableImpl` (`121` Functions) & `5`-Fn Tail `TableImpl` -/

/-- Certifies the `121`-fn prefix of `FullM6.m6FnsPart3` against `m6RowsPart3Pfx tPfx`. -/
theorem m6RowsPart3Pfx_tableImpl {tPfx tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxLen : (m6Orch_fns.take 24).length = tPfx.length)
    (hPfxOk : TableImpl (Env.ofTable tbl) (m6Orch_fns.take 24) tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hc1 : M6Part1Callees tbl) (hc2 : M6Part2Callees tbl)
    (hOwn : ∀ e ∈ m6RowsPart3Pfx tPfx, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) (m6FnsPart3.take 121) (m6RowsPart3Pfx tPfx) := by
  have sub_sw22 : ∀ e ∈ p3Sweep22Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; exact List.mem_append_left _ h)
  have sub_fwd : ∀ e ∈ p3FwdDedupBinsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 3 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bf0 : ∀ e ∈ p3BveFwd0Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 4 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ki : ∀ e ∈ p3KittenInitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 5 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_k14 : ∀ e ∈ p3Kitten14Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 6 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_kdf : ∀ e ∈ p3KittenDefFix5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 7 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_fdef : ∀ e ∈ p3FindDefinitionRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 8 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bf1t : ∀ e ∈ p3BveFwd1T5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 9 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bc : ∀ e ∈ p3BveCollectRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 10 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_brp : ∀ e ∈ p3BveResPairRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 11 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wk : ∀ e ∈ p3BveWeakenRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 12 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_btb : ∀ e ∈ p3BveTryBceRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 13 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bcr : ∀ e ∈ p3BveCommitResRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 14 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ben : ∀ e ∈ p3BveExtNeedRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 15 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bf1d : ∀ e ∈ p3BveFwd1D5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 16 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ifv6 : ∀ e ∈ p3InitFreshVarM6Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 18 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_adp14 : ∀ e ∈ p3Adp14Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 19 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bhop : ∀ e ∈ p3BvaHopRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 20 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bml : ∀ e ∈ p3BvaMatchLargeRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 21 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bsc : ∀ e ∈ p3BvaScanCandsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 22 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bpc : ∀ e ∈ p3BvaPickCandRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 23 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bfr : ∀ e ∈ p3BvaFilterRowRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 24 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bcom : ∀ e ∈ p3BvaCommitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 25 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_btl : ∀ e ∈ p3BvaTryLitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 26 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_fh : ∀ e ∈ p3FheapPairRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 27 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_fac : ∀ e ∈ p3FactorRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 28 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cfc : ∀ e ∈ p3CfCompact3Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 29 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cmp10 : ∀ e ∈ p3Compact10Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 30 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_reord : ∀ e ∈ p3ReorderRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 31 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bce4 : ∀ e ∈ p3VivBce4Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 33 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_minmax : ∀ e ∈ p3SchedMinMaxRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 34 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_edticks : ∀ e ∈ p3ElimDticksRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 35 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bf2 : ∀ e ∈ p3BveFwd2Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m6RowsPart3Pfx; (iterate 36 apply List.mem_append_right); exact List.mem_append_left _ h)
  have rDef := htPfx _ hPfxSpecs.wstackDefrag
  have rWp := htPfx _ hPfxSpecs.watchPush
  have rRew := htPfx _ hPfxSpecs.rewatchArena
  have rSwp := htPfx _ hPfxSpecs.arenaSweep
  have rSwpVar := sub_sw22 _ (List.mem_of_getElem? (i := 21) rfl)
  have rFwdDed := sub_fwd _ (List.mem_of_getElem? (i := 0) rfl)
  have rFlushU := sub_bf0 _ (List.mem_of_getElem? (i := 1) rfl)
  have rFwdSub := sub_bf0 _ (List.mem_of_getElem? (i := 8) rfl)
  have rBveColM6 := sub_bf0 _ (List.mem_of_getElem? (i := 9) rfl)
  have rKInit := sub_ki _ (List.mem_of_getElem? (i := 0) rfl)
  have rKWatch := sub_k14 _ (List.mem_of_getElem? (i := 0) rfl)
  have rKAssign := sub_k14 _ (List.mem_of_getElem? (i := 2) rfl)
  have rKBt := sub_k14 _ (List.mem_of_getElem? (i := 4) rfl)
  have rKProp := sub_k14 _ (List.mem_of_getElem? (i := 6) rfl)
  have rKAna := sub_k14 _ (List.mem_of_getElem? (i := 8) rfl)
  have rKShrink := sub_k14 _ (List.mem_of_getElem? (i := 12) rfl)
  have rKAddCl := sub_kdf _ (List.mem_of_getElem? (i := 0) rfl)
  have rKSolve := sub_kdf _ (List.mem_of_getElem? (i := 3) rfl)
  have rKCore := sub_kdf _ (List.mem_of_getElem? (i := 4) rfl)
  have rFdef := sub_fdef _ (List.mem_of_getElem? (i := 0) rfl)
  have rBveVarM6 := sub_bf1d _ (List.mem_of_getElem? (i := 0) rfl)
  have rBveCol := sub_bc _ (List.mem_of_getElem? (i := 0) rfl)
  have rResPair := sub_brp _ (List.mem_of_getElem? (i := 0) rfl)
  have rWeaken := sub_wk _ (List.mem_of_getElem? (i := 0) rfl)
  have rTryBce := sub_btb _ (List.mem_of_getElem? (i := 0) rfl)
  have rCommit := sub_bcr _ (List.mem_of_getElem? (i := 0) rfl)
  have rExtNeed := sub_ben _ (List.mem_of_getElem? (i := 0) rfl)
  have rIfvM6 := sub_ifv6 _ (List.mem_of_getElem? (i := 0) rfl)
  have rIfv := sub_adp14 _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaML := sub_bml _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaSC := sub_bsc _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaPC := sub_bpc _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaFR := sub_bfr _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaCom := sub_bcom _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaTL := sub_btl _ (List.mem_of_getElem? (i := 0) rfl)
  have rFhUp := sub_fh _ (List.mem_of_getElem? (i := 0) rfl)
  have rFhDn := sub_fh _ (List.mem_of_getElem? (i := 1) rfl)
  have rFactor := sub_fac _ (List.mem_of_getElem? (i := 0) rfl)
  have rCmpFl := sub_cfc _ (List.mem_of_getElem? (i := 1) rfl)
  have rCmpMl := sub_cfc _ (List.mem_of_getElem? (i := 2) rfl)
  have rMinU := sub_minmax _ (List.mem_of_getElem? (i := 0) rfl)
  have rMaxU := sub_minmax _ (List.mem_of_getElem? (i := 1) rfl)
  have rElimDt := sub_edticks _ (List.mem_of_getElem? (i := 0) rfl)
  have rGates := sub_bf1t _ (List.mem_of_getElem? (i := 4) rfl)
  have ps : ∀ off n,
      TableImpl (Env.ofTable tbl) (((m6Orch_fns.take 24).drop off).take n)
        ((tPfx.drop off).take n) :=
    tableImpl_drop_take hPfxLen hPfxOk
  have hlen_p : ∀ (off n : Nat),
      (((m6Orch_fns.take 24).drop off).take n).length = ((tPfx.drop off).take n).length := by
    intro off n; simp [hPfxLen]
  have i_sw22 : TableImpl (Env.ofTable tbl) p3Sweep22Fns p3Sweep22Rows :=
    (modTakeSliceTransport FullM4Sweep.fullM4SweepEnv_moduleOk
      FullM4Sweep.fullM4SweepSpecTable_nodup (by t_kernel_rfl) 0 22 (by decide)
      [ FullM4Sweep.fullM4SweepSpecTable[24]'(by decide)
      , FullM4Sweep.fullM4SweepSpecTable[27]'(by decide)
      , FullM4Sweep.fullM4SweepSpecTable[28]'(by decide) ]
      (by t_kernel_rfl)
      (m6_memC (List.getElem_mem _) (m6_memC (List.getElem_mem _) (m6_mem1 (List.getElem_mem _))))
      hnd sub_sw22 (m6_memC hc1.rngNext (m6_memC hc2.addUnit (m6_mem1 hc2.addBin)))).2
  have i_swdm5 : TableImpl (Env.ofTable tbl) p3SweepDenseM5Fns p3SweepDenseM5Rows :=
    m6_oneImpl rfl rfl (FullM5Orch.full_sweep_dense_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rSwpVar))
  have i_fwd : TableImpl (Env.ofTable tbl) p3FwdDedupBinsFns p3FwdDedupBinsRows :=
    (fullSliceTransport 145 1
      [⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩]
      (by t_kernel_rfl) (m6_mem1 (fullRow_at 102 _)) hnd sub_fwd (m6_mem1 hc2.addUnit)).2
  have i_bf0 := p3BveFwd0_impl hnd sub_bf0 hc2.addUnit rDef hc1.arenaNext rWp hc1.unwatchLarge
    hc2.addBin rFwdDed
  have i_ki : TableImpl (Env.ofTable tbl) p3KittenInitFns p3KittenInitRows :=
    m6_oneImpl rfl rfl (FullM4InprocHot.full_kitten_init_m4_wp (Env.ofTable tbl))
  have i_k14 : TableImpl (Env.ofTable tbl) p3Kitten14Fns p3Kitten14Rows :=
    (modTakeSliceTransport Full.fullKittenEnv_moduleOk Full.fullKittenSpecTable_nodup
      (by t_kernel_rfl) 1 14 (by decide) [] (by t_kernel_rfl) (fun _ h => nomatch h)
      hnd sub_k14 (fun _ h => nomatch h)).2
  have i_kdf : TableImpl (Env.ofTable tbl) p3KittenDefFix5Fns p3KittenDefFix5Rows :=
    (modTakeSliceTransport FullM5KittenDefFix.m5KittenDefFix_moduleOk
      FullM5KittenDefFix.m5KittenDefFixSpecTable_nodup (by t_kernel_rfl) 0 5 (by decide)
      [ FullM5KittenDefFix.m5KittenDefFixSpecTable[7]'(by decide)
      , FullM5KittenDefFix.m5KittenDefFixSpecTable[8]'(by decide)
      , FullM5KittenDefFix.m5KittenDefFixSpecTable[9]'(by decide)
      , FullM5KittenDefFix.m5KittenDefFixSpecTable[10]'(by decide)
      , FullM5KittenDefFix.m5KittenDefFixSpecTable[11]'(by decide) ]
      (by t_kernel_rfl)
      (m6_memC (List.getElem_mem _) <| m6_memC (List.getElem_mem _) <|
        m6_memC (List.getElem_mem _) <| m6_memC (List.getElem_mem _) <|
        m6_mem1 (List.getElem_mem _))
      hnd sub_kdf (m6_memC rKWatch <| m6_memC rKAssign <| m6_memC rKBt <|
        m6_memC rKProp <| m6_mem1 rKAna)).2
  have i_fdef : TableImpl (Env.ofTable tbl) p3FindDefinitionFns p3FindDefinitionRows := by
    let Γ := Env.ofTable tbl
    let Γ' : Env := fun f as rs =>
      if f = "full_kitten_add_clause" then Γ "full_kitten_add_clause_m5" as rs
      else if f = "full_kitten_solve" then Γ "full_kitten_solve_m5" as rs
      else if f = "full_kitten_core" then Γ "full_kitten_core_m5" as rs
      else Γ f as rs
    exact m6_oneImpl rfl rfl
      (FullM5KittenDefFix.full_find_definition_m5_wp Γ FullM5KittenDefFix.fastKInv_laws_m5
        (FullFast.fast_kitten_init_adapter (envRow_mem hnd _ _ _ _ rKInit))
        (FullFast.fast_kitten_add_clause_adapter (Γ := Γ') (envRow_mem hnd _ _ _ _ rKAddCl))
        (FullFast.fast_kitten_solve_adapter (Γ := Γ') (envRow_mem hnd _ _ _ _ rKSolve))
        (FullFast.fast_kitten_core_adapter (Γ := Γ') (envRow_mem hnd _ _ _ _ rKCore))
        (FullFast.fast_kitten_shrink_adapter (envRow_mem hnd _ _ _ _ rKShrink)))
  have i_bf1t := p3BveFwd1T5_impl hnd sub_bf1t rFdef
  have i_bc : TableImpl (Env.ofTable tbl) p3BveCollectFns p3BveCollectRows :=
    (fullSliceTransport 148 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_bc
      (fun _ h => nomatch h)).2
  have i_brp : TableImpl (Env.ofTable tbl) p3BveResPairFns p3BveResPairRows :=
    (fullSliceTransport 151 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_brp
      (fun _ h => nomatch h)).2
  have i_bwk : TableImpl (Env.ofTable tbl) p3BveWeakenFns p3BveWeakenRows :=
    m6_oneImpl rfl rfl (FullFast.fast_bve_weaken_tmk_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc2.extendPush2) (envRow_mem hnd _ _ _ _ hc2.deleteBinary)
      (envRow_mem hnd _ _ _ _ hc2.extendPushCl))
  have i_btb : TableImpl (Env.ofTable tbl) p3BveTryBceFns p3BveTryBceRows :=
    (fullSliceTransport 153 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_btb
      (fun _ h => nomatch h)).2
  have i_bcr : TableImpl (Env.ofTable tbl) p3BveCommitResFns p3BveCommitResRows :=
    m6_oneImpl rfl rfl (FullFast.fast_bve_commit_res_tmk_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.allocCl) (envRow_mem hnd _ _ _ _ rWp)
      (envRow_mem hnd _ _ _ _ hc2.addBin) (envRow_mem hnd _ _ _ _ hc2.addUnit))
  have i_ben : TableImpl (Env.ofTable tbl) p3BveExtNeedFns p3BveExtNeedRows :=
    (fullSliceTransport 155 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_ben
      (fun _ h => nomatch h)).2
  have i_bf1d : TableImpl (Env.ofTable tbl) p3BveFwd1D5Fns p3BveFwd1D5Rows :=
    m6_oneImpl rfl rfl (FullM6BveFwd.full_bve_var_m6_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rBveColM6) (envRow_mem hnd _ _ _ _ rExtNeed)
      (envRow_mem hnd _ _ _ _ rWeaken) (envRow_mem hnd _ _ _ _ hc2.setInactive)
      (envRow_mem hnd _ _ _ _ rGates FullM6BveFwd.fullBveGatesM6Spec_noExit)
      (envRow_mem hnd _ _ _ _ rResPair) (envRow_mem hnd _ _ _ _ rDef)
      (envRow_mem hnd _ _ _ _ rCommit)
      (envRow_mem hnd _ _ _ _ rFlushU FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit)
      (envRow_mem hnd _ _ _ _ rTryBce) (envRow_mem hnd _ _ _ _ hc2.extendPush2)
      (envRow_mem hnd _ _ _ _ hc2.deleteBinary) (envRow_mem hnd _ _ _ _ hc2.extendPushCl))
  have i_adp1213 := p3Adp1213_impl hnd rBveVarM6 rFwdSub
  have i_ifv6 : TableImpl (Env.ofTable tbl) p3InitFreshVarM6Fns p3InitFreshVarM6Rows :=
    m6_oneImpl rfl rfl (FullM6VivBackbone.full_init_fresh_var_m6_heap_wp (Env.ofTable tbl))
  have i_adp14 : TableImpl (Env.ofTable tbl) p3Adp14Fns p3Adp14Rows :=
    m6_oneImpl rfl rfl (full_init_fresh_var_heap_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rIfvM6))
  have i_bhop : TableImpl (Env.ofTable tbl) p3BvaHopFns p3BvaHopRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      0 3 (by decide) [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_bhop
      (fun _ h => nomatch h)).2
  have i_bml : TableImpl (Env.ofTable tbl) p3BvaMatchLargeFns p3BvaMatchLargeRows :=
    m6_oneImpl rfl rfl (FullBvaHeap.full_bva_match_large_wp (Env.ofTable tbl))
  have i_bsc : TableImpl (Env.ofTable tbl) p3BvaScanCandsFns p3BvaScanCandsRows :=
    m6_oneImpl rfl rfl (FullM4Bva.m4_bva_scan_cands_wp (Env.ofTable tbl))
  have i_bpc : TableImpl (Env.ofTable tbl) p3BvaPickCandFns p3BvaPickCandRows :=
    m6_oneImpl rfl rfl (FullM6BvaNoHops.m6_bva_pick_cand_no_hops_wp (Env.ofTable tbl))
  have i_bfr : TableImpl (Env.ofTable tbl) p3BvaFilterRowFns p3BvaFilterRowRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      4 1 (by decide) [FullM4Bva.m4BvaSpecTable[19]'(by decide)] (by t_kernel_rfl)
      (m6_mem1 (List.getElem_mem _)) hnd sub_bfr (m6_mem1 rBvaML)).2
  have i_bcom : TableImpl (Env.ofTable tbl) p3BvaCommitFns p3BvaCommitRows :=
    m6_oneImpl rfl rfl (FullM5DenseSafe.full_bva_commit_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rDef) (envRow_mem hnd _ _ _ _ rIfv)
      (envRow_mem hnd _ _ _ _ hc2.addBin) (envRow_mem hnd _ _ _ _ hc1.allocCl)
      (envRow_mem hnd _ _ _ _ rWp) (envRow_mem hnd _ _ _ _ hc2.deleteBinary)
      (envRow_mem hnd _ _ _ _ hc1.unwatchLarge))
  have i_btl : TableImpl (Env.ofTable tbl) p3BvaTryLitFns p3BvaTryLitRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      6 1 (by decide)
      [ FullM4Bva.m4BvaSpecTable[3]'(by decide), FullM4Bva.m4BvaSpecTable[4]'(by decide)
      , FullM4Bva.m4BvaSpecTable[5]'(by decide), FullM4Bva.m4BvaSpecTable[20]'(by decide) ]
      (by t_kernel_rfl)
      (m6_memC (List.getElem_mem _) <| m6_memC (List.getElem_mem _) <|
        m6_memC (List.getElem_mem _) <| m6_mem1 (List.getElem_mem _))
      hnd sub_btl (m6_memC rBvaPC <| m6_memC rBvaFR <| m6_memC rBvaCom <| m6_mem1 rBvaSC)).2
  have i_fh : TableImpl (Env.ofTable tbl) p3FheapPairFns p3FheapPairRows := by
    have hfn : p3FheapPairFns =
        [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.full_fheap_up_body⟩
        , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
            FullBvaHeap.full_fheap_down_body⟩ ] := rfl
    rw [hfn]; unfold p3FheapPairRows
    exact ⟨ SpecEntry.Impl.of (FullBvaHeap.full_fheap_up_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullBvaHeap.full_fheap_down_wp (Env.ofTable tbl)), trivial ⟩
  have i_fac : TableImpl (Env.ofTable tbl) p3FactorFns p3FactorRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      7 1 (by decide)
      [ FullM4Bva.m4BvaSpecTable[6]'(by decide)
      , FullM4Bva.m4BvaSpecTable[21]'(by decide)
      , FullM4Bva.m4BvaSpecTable[22]'(by decide) ]
      (by t_kernel_rfl)
      (m6_memC (List.getElem_mem _) <| m6_memC (List.getElem_mem _) <|
        m6_mem1 (List.getElem_mem _))
      hnd sub_fac (m6_memC rBvaTL <| m6_memC rFhUp <| m6_mem1 rFhDn)).2
  have i_cfc := p3CfCompact3_impl hnd hc1.flushTrail rSwp hc1.arenaNext
  have i_cmp10 : TableImpl (Env.ofTable tbl) p3Compact10Fns p3Compact10Rows :=
    (modTakeSliceTransport FullM4Compact.compact_moduleOk FullM4Compact.compactSpecTable_nodup
      (by t_kernel_rfl) 3 10 (by decide)
      [ FullM4Compact.compactSpecTable[1]'(by decide)
      , FullM4Compact.compactSpecTable[2]'(by decide)
      , FullM4Compact.compactSpecTable[13]'(by decide)
      , FullM4Compact.compactSpecTable[14]'(by decide)
      , FullM4Compact.compactSpecTable[15]'(by decide)
      , FullM4Compact.compactSpecTable[18]'(by decide) ]
      (by t_kernel_rfl)
      (m6_memC (List.getElem_mem _) <| m6_memC (List.getElem_mem _) <|
        m6_memC (List.getElem_mem _) <| m6_memC (List.getElem_mem _) <|
        m6_memC (List.getElem_mem _) <| m6_mem1 (List.getElem_mem _))
      hnd sub_cmp10
      (m6_memC rCmpFl <| m6_memC rCmpMl <| m6_memC hc1.arenaNext <|
        m6_memC rDef <| m6_memC rWp <| m6_mem1 rRew)).2
  have i_reord := p3Reorder_impl hnd sub_reord hc1.arenaNext
  have i_bce4 := p3VivBce4_s15_impl hnd sub_bce4 rTryBce hc2.extendPush2 hc2.extendPushCl
    hc2.deleteBinary rBveCol hc2.enterDense hc2.rebuildWatches hc1.propagate
  have i_minmax : TableImpl (Env.ofTable tbl) p3SchedMinMaxFns p3SchedMinMaxRows := by
    have hfn : p3SchedMinMaxFns =
        [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.full_min_u64_body⟩
        , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.full_max_u64_body⟩ ] := rfl
    rw [hfn]; unfold p3SchedMinMaxRows
    exact ⟨ SpecEntry.Impl.of (FullFastSched.sched_min_u64_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullFastSched.sched_max_u64_wp (Env.ofTable tbl)), trivial ⟩
  have i_edticks : TableImpl (Env.ofTable tbl) p3ElimDticksFns p3ElimDticksRows :=
    m6_oneImpl rfl rfl (FullM5Orch.full_elim_dticks_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rMaxU))
  have i_bf2 := p3BveFwd2_impl hnd sub_bf2 rFlushU rBveVarM6 rElimDt hc1.ilog10 hc1.scaleDelta
    hc2.enterDense rMinU rFwdSub rFactor hc2.rebuildWatches
  have i_adp15 : TableImpl (Env.ofTable tbl) p3Adp15Fns p3Adp15Rows :=
    m6_oneImpl rfl rfl (full_probe_dticks_m6_hdr_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.hdrGetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))
  rw [p3Pfx_eq]; unfold p3PfxSeg m6RowsPart3Pfx
  refine tableImpl_append rfl i_sw22 (tableImpl_append rfl i_swdm5 ?_)
  refine tableImpl_append (hlen_p 18 1) (ps 18 1) (tableImpl_append rfl i_fwd ?_)
  refine tableImpl_append rfl i_bf0 (tableImpl_append rfl i_ki (tableImpl_append rfl i_k14 ?_))
  refine tableImpl_append rfl i_kdf (tableImpl_append rfl i_fdef (tableImpl_append rfl i_bf1t ?_))
  refine tableImpl_append rfl i_bc (tableImpl_append rfl i_brp (tableImpl_append rfl i_bwk ?_))
  refine tableImpl_append rfl i_btb (tableImpl_append rfl i_bcr (tableImpl_append rfl i_ben ?_))
  refine tableImpl_append rfl i_bf1d (tableImpl_append rfl i_adp1213 ?_)
  refine tableImpl_append rfl i_ifv6 (tableImpl_append rfl i_adp14 (tableImpl_append rfl i_bhop ?_))
  refine tableImpl_append rfl i_bml (tableImpl_append rfl i_bsc (tableImpl_append rfl i_bpc ?_))
  refine tableImpl_append rfl i_bfr (tableImpl_append rfl i_bcom (tableImpl_append rfl i_btl ?_))
  refine tableImpl_append rfl i_fh (tableImpl_append rfl i_fac (tableImpl_append rfl i_cfc ?_))
  refine tableImpl_append rfl i_cmp10 (tableImpl_append rfl i_reord ?_)
  refine tableImpl_append (hlen_p 19 1) (ps 19 1) (tableImpl_append rfl i_bce4 ?_)
  refine tableImpl_append rfl i_minmax (tableImpl_append rfl i_edticks ?_)
  refine tableImpl_append rfl i_bf2 (tableImpl_append rfl i_adp15 ?_)
  exact ps 20 4

private theorem m6Orch_rephase_of_adp {Γ : Env}
    (hReph : ∀ a m Q X, FullM6OrchAdapters.m6aRephaseSpec a m Q X →
      Γ "full_rephase_m6_hdr" [i64] [] a m Q X) :
    ∀ a m Q X, FullM6Orch.m6aRephaseSpec a m Q X →
      Γ "full_rephase_m6_hdr" [i64] [] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hinv, hdm0, hm, hQ⟩ :=
    FullM6Orch.m6aRephaseSpec_elim hs
  exact hReph _ m Q X (FullM6OrchAdapters.m6aRephaseSpec_of hcfg hext hinv hdm0 hm hQ)

private theorem p3Tail_tableImpl {tPfx tbl : List SpecEntry}
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hc1 : M6Part1Callees tbl)
    (hMemInit : (⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
      fullM6MemInitExactSpec, true⟩ : SpecEntry) ∈ tbl)
    (hCheck : (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissatCheckModelExactSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAnaM6 : (⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRstDue : (⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hRst : (⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩ : SpecEntry) ∈ tbl)
    (hReph : (⟨"full_rephase_m6_hdr", [i64], [],
      FullM6OrchAdapters.m6aRephaseSpec, true⟩ : SpecEntry) ∈ tbl)
    (hDecide : (⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hExt : (⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩ : SpecEntry) ∈ tbl)
    (hTail : ∀ e ∈ m6OrchTailRows solveSpec, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3TailSeg (m6OrchTailRows solveSpec) := by
  have r0 := hTail _ (List.mem_of_getElem? (i := 0) rfl)
  have r1 := hTail _ (List.mem_of_getElem? (i := 1) rfl)
  have r2 := hTail _ (List.mem_of_getElem? (i := 2) rfl)
  have hSearchM6 := envRow_mem hnd _ _ _ _ r0 (fun _ _ _ _ h => fullM6SearchSpec_monoX h)
  have hPre := envRow_mem hnd _ _ _ _ r2 (fun _ _ _ _ h => fullM6PreprocessSpec_monoX h)
  have hPreM6 := envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.preprocessM6)
    (fun _ _ _ _ h => fullM6PreprocessSpec_monoX h)
  have hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Env.ofTable tbl "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X :=
    fun a m Q X hs => Env.ofTable_of_mem r1 hnd (hSolveMonoX a m Q X _ hs)
  unfold p3TailSeg m6OrchTailRows
  refine tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
      wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
    (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
        wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
      (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
          wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
        (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
            wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
          (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
              wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
            (tableImpl_nil (Env.ofTable tbl) [])))))
  · exact full_search_m6_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.propagate)
      (envRow_mem hnd _ _ _ _ hAnaM6 (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
      (envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.reduceM6) (fun _ _ _ _ h => m6ReduceSpec_monoX h))
      (envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.switchModeM6)
        (fun _ _ _ _ h => m6SwitchModeSpec_monoX h))
      (envRow_mem hnd _ _ _ _ hRstDue)
      (envRow_mem hnd _ _ _ _ hRst)
      (envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.reorderM6))
      (m6Orch_rephase_of_adp (envRow_mem hnd _ _ _ _ hReph
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aRephaseSpec_monoX h)))
      (envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.simplifyM6)
        (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
      (envRow_mem hnd _ _ _ _ hDecide (fun _ _ _ _ h => FullM6Hdr.m6HdrDecideSpec_monoX h))
      xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_m6_core_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hMemInit (fun _ _ _ _ h => fullM6MemInitExactSpec_monoX h))
      (envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.parseBody))
      hPreM6 hSearchM6
      (envRow_mem hnd _ _ _ _ hExt)
      (envRow_mem hnd _ _ _ _ hCheck)
      xs m Q (fun _ _ _ _ => False) (hWeaken xs m Q (fun _ _ _ _ => False) hs)
  · exact FullM6Orch.full_preprocess_wp (Env.ofTable tbl) hPreM6 xs m Q (fun _ _ _ _ => False) hs
  · exact full_search_wp (Env.ofTable tbl) hSearchM6 xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_core_wp (Env.ofTable tbl) solveSpec hSolveM6
      xs m Q (fun _ _ _ _ => False) hs

theorem m6RowsPart3Pfx_tPfx_mem {tPfx : List SpecEntry} {i : Nat}
    (h18 : 18 ≤ i) (hi : i < 24) (hit : i < tPfx.length) :
    tPfx[i] ∈ m6RowsPart3Pfx tPfx := by
  unfold m6RowsPart3Pfx
  rcases Nat.lt_or_ge i 19 with h19 | h19
  · (iterate 2 apply List.mem_append_right); apply List.mem_append_left
    exact m6_mem_drop_take_of_lt tPfx h18 h19 hit
  · rcases Nat.lt_or_ge i 20 with h20 | h20
    · (iterate 32 apply List.mem_append_right); apply List.mem_append_left
      exact m6_mem_drop_take_of_lt tPfx h19 h20 hit
    · (iterate 38 apply List.mem_append_right)
      exact m6_mem_drop_take_of_lt tPfx h20 (by omega) hit

theorem m6OrchTail_solve_mem
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6OrchTailRows solveSpec ∧
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6OrchTailRows solveSpec := by
  exact ⟨ List.mem_of_getElem? (i := 1) rfl, List.mem_of_getElem? (i := 4) rfl ⟩

/-- Certifies all `126` functions of `FullM6.m6FnsPart3` in one contiguous `TableImpl`. -/
theorem m6Part3_tableImpl {tPfx tbl : List SpecEntry}
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxOk : TableImpl (Env.ofTable tbl) (m6Orch_fns.take 24) tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hc1 : M6Part1Callees tbl) (hc2 : M6Part2Callees tbl)
    (hMemInit : (⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
      fullM6MemInitExactSpec, true⟩ : SpecEntry) ∈ tbl)
    (hCheck : (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissatCheckModelExactSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAnaM6 : (⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRstDue : (⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hRst : (⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩ : SpecEntry) ∈ tbl)
    (hReph : (⟨"full_rephase_m6_hdr", [i64], [],
      FullM6OrchAdapters.m6aRephaseSpec, true⟩ : SpecEntry) ∈ tbl)
    (hDecide : (⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hExt : (⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPfxOwn : ∀ e ∈ m6RowsPart3Pfx tPfx, e ∈ tbl)
    (hTail : ∀ e ∈ m6OrchTailRows solveSpec, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m6FnsPart3 (m6RowsPart3Pfx tPfx ++ m6OrchTailRows solveSpec) := by
  have hPfxLen : (m6Orch_fns.take 24).length = tPfx.length :=
    (m6_list_len_of_map hPfxSigs).symm
  have h121 : (m6FnsPart3.take 121).length = (m6RowsPart3Pfx tPfx).length := by
    have h1 := congrArg List.length (m6RowsPart3Pfx_sigs hPfxSigs)
    simpa only [List.length_map] using h1.symm
  have ip := m6RowsPart3Pfx_tableImpl hnd hPfxLen hPfxOk htPfx hPfxSpecs hc1 hc2 hPfxOwn
  have it := p3Tail_tableImpl solveSpec hWeaken hSolveMonoX hnd htPfx hPfxSpecs hc1
    hMemInit hCheck hAnaM6 hRstDue hRst hReph hDecide hExt hTail
  rw [← List.take_append_drop 121 m6FnsPart3, p3Tail_eq]
  exact tableImpl_append h121 ip it

/-- Part 3 external callee memberships required by `m6Orch_fns.take 24`. -/
structure M6Part3ExtCallees (tbl : List SpecEntry) : Prop where
  sweepDenseM5 :
    (⟨"full_sweep_dense_m5", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ tbl
  reorderQueueM7 :
    (⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩ :
      SpecEntry) ∈ tbl
  minU64 :
    (⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩ :
      SpecEntry) ∈ tbl
  probeDticks :
    (⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64],
      FullM6Hdr.m6HdrW2aSpec [.bool] [i64], true⟩ : SpecEntry) ∈ tbl
  factor :
    (⟨"full_factor", [i64, i64], [i64], FullM3CongBva.fullFactorHeapSpec, true⟩ :
      SpecEntry) ∈ tbl
  compactNeeded :
    (⟨"full_compact_needed", [i64], [.bool],
      FullM6CompactFlush.fullCompactNeededM6Spec, true⟩ : SpecEntry) ∈ tbl
  compact :
    (⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩ : SpecEntry) ∈ tbl
  eliminateM6 :
    (⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩ :
      SpecEntry) ∈ tbl

theorem m6Part3ExtCallees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m6RowsPart3Pfx tPfx, e ∈ tbl) : M6Part3ExtCallees tbl := by
  have sub_swdm5 : ∀ e ∈ p3SweepDenseM5Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 1 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_fh : ∀ e ∈ p3FactorRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 28 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_cfc : ∀ e ∈ p3CfCompact3Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 29 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_cmp10 : ∀ e ∈ p3Compact10Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 30 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_reord : ∀ e ∈ p3ReorderRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 31 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_minmax : ∀ e ∈ p3SchedMinMaxRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 34 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_bf2 : ∀ e ∈ p3BveFwd2Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 36 apply List.mem_append_right
    exact List.mem_append_left _ h)
  have sub_adp15 : ∀ e ∈ p3Adp15Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m6RowsPart3Pfx; iterate 37 apply List.mem_append_right
    exact List.mem_append_left _ h)
  refine ⟨ sub_swdm5 _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_reord _ (List.mem_of_getElem? (i := 2) rfl)
         , sub_minmax _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_adp15 _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_fh _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_cfc _ (List.mem_of_getElem? (i := 0) rfl)
         , sub_cmp10 _ (List.mem_of_getElem? (i := 9) rfl)
         , sub_bf2 _ (List.mem_of_getElem? (i := 7) rfl) ⟩

end LeanQbe.T.Examples.Kissat.FullM6Proof

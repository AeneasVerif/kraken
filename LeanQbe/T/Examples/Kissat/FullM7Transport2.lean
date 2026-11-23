/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7Transport1
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM7BvaFactorProof
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullFastAdapters
import LeanQbe.T.Examples.Kissat.FullFastTmkLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullBveVarLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat `D-Full` Unified `M7` Part 3 Prefix (`276..404`, `FullM7Transport2`)

Assembles `m7RowsPart3Pfx tPfx tBve` (`129` entries) aligned 1-to-1 with `m7FnsPart3.take 129`,
parameterized cleanly over in-flight `FullM7BveGates` (`43` fns `m7BveAllFns`) via `tBve` and
`FullM6Orch` prefix `tPfx` (`15..20`), proves canonical `sigs`/`noExit` metadata and `TableImpl`
using canonical `Full.fullPropagateSpec` (zero `S1.5` drift), plain `public section`, and `0`
`@[expose]` tags.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7

/-! ## 1. `FullM7BveGates` (`43` Fns) & Cross-Part Part 3 Callees -/

/-- Exact `43`-function `FullM7BveGates` + canonical alias slice inside `FullM7.m7FnsPart3`. -/
def m7BveAllFns : List Fn :=
  FullM7BveGates.m7BveGates_fns.take 10 ++
  ([ m7ForwardSubCanonFn, m7BveCollectCanonFn ] ++
  ((FullM7BveGates.m7BveGates_fns.drop 10).take 20 ++
  ((FullM7BveGates.m7BveGates_fns.drop 30).take 1 ++
  ([ m7BveVarCanonFn ] ++
  (FullM7BveGates.m7BveGates_fns.drop 31 ++ [ m7EliminateM6Fn ])))))

theorem m7BveAllFns_length : m7BveAllFns.length = 43 := by t_kernel_rfl

/-- `SpecEntry` rows required from `tBve` (`43` rows matching `m7BveAllFns`) by external
Part 3 callers (`FullM4VivBce` and `FullM6Orch` simplify). -/
structure M7BveAllTblSpecs (tBve : List SpecEntry) : Prop where
  bveCollect :
    (⟨"full_bve_collect", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ :
      SpecEntry) ∈ tBve
  fwdSub :
    (⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩ :
      SpecEntry) ∈ tBve
  eliminateM6 :
    (⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩ :
      SpecEntry) ∈ tBve

/-- Part 3 prefix row memberships required by the `5`-fn orchestration tail (`FullM7OrchProof0`). -/
structure M7Part3TailCallees (tbl : List SpecEntry) : Prop where
  luckyLateM7 :
    (⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.m7LuckyLateSpec, true⟩ : SpecEntry) ∈ tbl
  switchModeM7 :
    (⟨"full_switch_mode_m7", [i64], [], FullM7Search.m7SwitchModeSpec, true⟩ : SpecEntry) ∈ tbl
  decideM7 :
    (⟨"full_decide_m7", [i64], [i64], FullM7Search.m7DecideSpec, true⟩ : SpecEntry) ∈ tbl

/-! ## 2. Part 3 Prefix Segment Rows (`276..404`, `129` Entries) -/

private def p3Sweep22Rows : List SpecEntry := FullM4Sweep.fullM4SweepSpecTable.take 22
private def p3SweepDenseM5Rows : List SpecEntry :=
  [⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩]
private def p3FwdDedupBinsRows : List SpecEntry := (fullBaseTable.drop 145).take 1
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
private def p3Bve5Rows : List SpecEntry :=
  p3BveResPairRows ++ p3BveWeakenRows ++ p3BveTryBceRows ++ p3BveCommitResRows ++ p3BveExtNeedRows
private def p3InitFreshVarRows : List SpecEntry :=
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
private def p3BvaTryLitM7Rows : List SpecEntry :=
  [⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullBvaHeap.fullBvaTryLitHeapSpec, true⟩]
private def p3FheapPairRows : List SpecEntry :=
  [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩ ]
private def p3FactorM7Rows : List SpecEntry :=
  [⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩]
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
private def p3M7Search14Rows : List SpecEntry :=
  [ ⟨"full_lcg_next_m7", [i64], [i64], FullM7Search.m7LcgNextSpec, true⟩
  , ⟨"full_m7_get64", [i64, i64], [i64], FullM7Search.m7Get64Spec, true⟩
  , ⟨"full_m7_set64", [i64, i64, i64], [], FullM7Search.m7Set64Spec, true⟩
  , ⟨"full_m7_state_init", [i64], [], FullM7Search.m7StateInitSpec, true⟩
  , ⟨"full_tumble_clause_m7", [i64, i32], [.bool], FullM7Search.m7TumbleClauseSpec, true⟩
  , ⟨"full_tumble_clauses_m7", [i64, i64], [i64], FullM7Search.m7TumbleClausesSpec, true⟩
  , ⟨"full_tumble_m7", [i64], [i64], FullM7Search.m7TumbleSpec, true⟩
  , ⟨"full_lucky_polar_m7", [i64], [i64], Full.fullLuckyPolarSpec, true⟩
  , ⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.m7LuckyLateSpec, true⟩
  , ⟨"full_randec_step_m7", [i64], [], FullM7Search.m7RandecStepSpec, true⟩
  , ⟨"full_randec_var_m7", [i64], [i64], FullM7Search.m7RandecVarSpec, true⟩
  , ⟨"full_decide_m7", [i64], [i64], FullM7Search.m7DecideSpec, true⟩
  , ⟨"full_ema_swap_m7", [i64, i64, i64], [], FullM7Search.m7EmaSwapSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], FullM7Search.m7SwitchModeSpec, true⟩ ]
private def p3AdpProbeDticksRows : List SpecEntry :=
  [⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩]

/-- Part 3 prefix rows (`276..404`, `129` entries) aligned 1-to-1 with
`FullM7.m7FnsPart3.take 129`. -/
def m7RowsPart3Pfx (tPfx tBve : List SpecEntry) : List SpecEntry :=
  p3Sweep22Rows ++ (p3SweepDenseM5Rows ++ ((tPfx.drop 15).take 1 ++ (p3FwdDedupBinsRows ++
  (tBve.take 32 ++ (p3Bve5Rows ++ ((tBve.drop 32).take 2 ++ (p3InitFreshVarRows ++
  (p3BvaHopRows ++ (p3BvaMatchLargeRows ++ (p3BvaScanCandsRows ++ (p3BvaPickCandRows ++
  (p3BvaFilterRowRows ++ (p3BvaCommitRows ++ (p3BvaTryLitM7Rows ++ (p3FheapPairRows ++
  (p3FactorM7Rows ++ (p3CfCompact3Rows ++ (p3Compact10Rows ++ (p3ReorderRows ++
  ((tPfx.drop 16).take 1 ++ (p3VivBce4Rows ++ (p3SchedMinMaxRows ++ (p3ElimDticksRows ++
  (tBve.drop 34 ++ (p3M7Search14Rows ++ (p3AdpProbeDticksRows ++
    (tPfx.drop 17).take 4))))))))))))))))))))))))))

/-! ## 3. Part 3 Prefix Function Decomposition & Metadata -/

private def p3Sweep22Fns : List Fn := FullM4Sweep.fullM4Sweep_fns.take 22
private def p3SweepDenseM5Fns : List Fn := (FullM5.m5Fns.drop 200).take 1
private def p3FwdDedupBinsFns : List Fn := (FullM5.m5Fns.drop 201).take 1
private def p3Bve5Fns : List Fn := (FullM5.m5Fns.drop 213).take 5
private def p3InitFreshVarFns : List Fn := [FullM7BvaFactor.m7InitFreshVarFn]
private def p3BvaHopFns : List Fn := (FullM5.m5Fns.drop 220).take 3
private def p3BvaMatchLargeFns : List Fn := (FullM5.m5Fns.drop 223).take 1
private def p3BvaScanCandsFns : List Fn := (FullM5.m5Fns.drop 224).take 1
private def p3BvaPickCandFns : List Fn := FullM6BvaNoHops.m6BvaNoHopsFns
private def p3BvaFilterRowFns : List Fn := (FullM5.m5Fns.drop 226).take 1
private def p3BvaCommitFns : List Fn := (FullM5.m5Fns.drop 227).take 1
private def p3BvaTryLitM7Fns : List Fn := [FullM7BvaFactor.m7BvaTryLitFn]
private def p3FheapPairFns : List Fn := (FullM5.m5Fns.drop 229).take 2
private def p3FactorM7Fns : List Fn := [FullM7BvaFactor.m7FactorFn]
private def p3CfCompact3Fns : List Fn :=
  [ FullM6CompactFlush.m6cfCompactNeededFn
  , FullM6CompactFlush.m6cfCompactFlushFn
  , FullM6CompactFlush.m6cfCompactMarkLiveFn ]
private def p3Compact10Fns : List Fn := (FullM5.m5Fns.drop 235).take 10
private def p3ReorderFns : List Fn := FullM7Reorder.m7ReorderFns
private def p3VivBce4Fns : List Fn := (FullM5.m5Fns.drop 248).take 4
private def p3SchedMinMaxFns : List Fn := (FullM5.m5Fns.drop 252).take 2
private def p3ElimDticksFns : List Fn := [m6CanonicalElimDticksFn]
private def p3M7Search14Fns : List Fn :=
  FullM7Search.m7Search_fns.take 4 ++ FullM7Search.m7Search_fns.drop 5
private def p3AdpProbeDticksFns : List Fn := [m6aProbeDticksM6HdrFn]

private def p3PfxSeg : List Fn :=
  p3Sweep22Fns ++ (p3SweepDenseM5Fns ++ ((m7OrchPfxFns.drop 15).take 1 ++ (p3FwdDedupBinsFns ++
  (m7BveAllFns.take 32 ++ (p3Bve5Fns ++ ((m7BveAllFns.drop 32).take 2 ++ (p3InitFreshVarFns ++
  (p3BvaHopFns ++ (p3BvaMatchLargeFns ++ (p3BvaScanCandsFns ++ (p3BvaPickCandFns ++
  (p3BvaFilterRowFns ++ (p3BvaCommitFns ++ (p3BvaTryLitM7Fns ++ (p3FheapPairFns ++
  (p3FactorM7Fns ++ (p3CfCompact3Fns ++ (p3Compact10Fns ++ (p3ReorderFns ++
  ((m7OrchPfxFns.drop 16).take 1 ++ (p3VivBce4Fns ++ (p3SchedMinMaxFns ++ (p3ElimDticksFns ++
  (m7BveAllFns.drop 34 ++ (p3M7Search14Fns ++ (p3AdpProbeDticksFns ++
    (m7OrchPfxFns.drop 17).take 4))))))))))))))))))))))))))

private theorem p3Pfx_eq : m7FnsPart3.take 129 = p3PfxSeg := by
  unfold FullM7.m7FnsPart3 p3PfxSeg
  rw [m7OrchPfxFns_eq]
  t_kernel_rfl

private theorem bveAllSlice_sigs {tBve : List SpecEntry}
    (hsig : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (off n : Nat) :
    ((tBve.drop off).take n).map (fun e => (e.name, e.as, e.rs)) =
      ((m7BveAllFns.drop off).take n).map Fn.sig := by
  simp only [List.map_take, List.map_drop, hsig]

private theorem bveAllDrop_sigs {tBve : List SpecEntry}
    (hsig : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (off : Nat) :
    (tBve.drop off).map (fun e => (e.name, e.as, e.rs)) =
      (m7BveAllFns.drop off).map Fn.sig := by
  simp only [List.map_drop, hsig]

private theorem bveAllTake_sigs {tBve : List SpecEntry}
    (hsig : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (n : Nat) :
    (tBve.take n).map (fun e => (e.name, e.as, e.rs)) =
      (m7BveAllFns.take n).map Fn.sig := by
  simp only [List.map_take, hsig]

private theorem bveAllSlice_noExit {tBve : List SpecEntry}
    (hno : tBve.all SpecEntry.noExit = true) (off n : Nat) :
    ((tBve.drop off).take n).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_drop (List.mem_of_mem_take he))

private theorem bveAllDrop_noExit {tBve : List SpecEntry}
    (hno : tBve.all SpecEntry.noExit = true) (off : Nat) :
    (tBve.drop off).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_drop he)

private theorem bveAllTake_noExit {tBve : List SpecEntry}
    (hno : tBve.all SpecEntry.noExit = true) (n : Nat) :
    (tBve.take n).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_take he)

theorem m7RowsPart3Pfx_sigs {tPfx tBve : List SpecEntry}
    (hsigP : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hsigB : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7RowsPart3Pfx tPfx tBve).map (fun e => (e.name, e.as, e.rs)) =
      (m7FnsPart3.take 129).map Fn.sig := by
  have s01 : p3Sweep22Rows.map (fun e => (e.name, e.as, e.rs)) = p3Sweep22Fns.map Fn.sig := by
    t_kernel_rfl
  have s02 : p3SweepDenseM5Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3SweepDenseM5Fns.map Fn.sig := by t_kernel_rfl
  have s03 : p3FwdDedupBinsRows.map (fun e => (e.name, e.as, e.rs)) =
      p3FwdDedupBinsFns.map Fn.sig := by t_kernel_rfl
  have s04 : p3Bve5Rows.map (fun e => (e.name, e.as, e.rs)) = p3Bve5Fns.map Fn.sig := by
    t_kernel_rfl
  have s05 : p3InitFreshVarRows.map (fun e => (e.name, e.as, e.rs)) =
      p3InitFreshVarFns.map Fn.sig := by t_kernel_rfl
  have s06 : p3BvaHopRows.map (fun e => (e.name, e.as, e.rs)) = p3BvaHopFns.map Fn.sig := by
    t_kernel_rfl
  have s07 : p3BvaMatchLargeRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaMatchLargeFns.map Fn.sig := by t_kernel_rfl
  have s08 : p3BvaScanCandsRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaScanCandsFns.map Fn.sig := by t_kernel_rfl
  have s09 : p3BvaPickCandRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaPickCandFns.map Fn.sig := by t_kernel_rfl
  have s10 : p3BvaFilterRowRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaFilterRowFns.map Fn.sig := by t_kernel_rfl
  have s11 : p3BvaCommitRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaCommitFns.map Fn.sig := by t_kernel_rfl
  have s12 : p3BvaTryLitM7Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaTryLitM7Fns.map Fn.sig := by t_kernel_rfl
  have s13 : p3FheapPairRows.map (fun e => (e.name, e.as, e.rs)) =
      p3FheapPairFns.map Fn.sig := by t_kernel_rfl
  have s14 : p3FactorM7Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3FactorM7Fns.map Fn.sig := by t_kernel_rfl
  have s15 : p3CfCompact3Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3CfCompact3Fns.map Fn.sig := by t_kernel_rfl
  have s16 : p3Compact10Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3Compact10Fns.map Fn.sig := by t_kernel_rfl
  have s17 : p3ReorderRows.map (fun e => (e.name, e.as, e.rs)) = p3ReorderFns.map Fn.sig := by
    t_kernel_rfl
  have s18 : p3VivBce4Rows.map (fun e => (e.name, e.as, e.rs)) = p3VivBce4Fns.map Fn.sig := by
    t_kernel_rfl
  have s19 : p3SchedMinMaxRows.map (fun e => (e.name, e.as, e.rs)) =
      p3SchedMinMaxFns.map Fn.sig := by t_kernel_rfl
  have s20 : p3ElimDticksRows.map (fun e => (e.name, e.as, e.rs)) =
      p3ElimDticksFns.map Fn.sig := by t_kernel_rfl
  have s21 : p3M7Search14Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3M7Search14Fns.map Fn.sig := by t_kernel_rfl
  have s22 : p3AdpProbeDticksRows.map (fun e => (e.name, e.as, e.rs)) =
      p3AdpProbeDticksFns.map Fn.sig := by t_kernel_rfl
  rw [p3Pfx_eq]
  simp only [m7RowsPart3Pfx, p3PfxSeg, List.map_append, s01, s02, s03, s04, s05, s06, s07, s08,
    s09, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22,
    pfx21Slice_sigs hsigP, bveAllTake_sigs hsigB, bveAllSlice_sigs hsigB, bveAllDrop_sigs hsigB]

theorem m7RowsPart3Pfx_noExit {tPfx tBve : List SpecEntry}
    (hnoP : tPfx.all SpecEntry.noExit = true) (hnoB : tBve.all SpecEntry.noExit = true) :
    (m7RowsPart3Pfx tPfx tBve).all SpecEntry.noExit = true := by
  have n01 : p3Sweep22Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n02 : p3SweepDenseM5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n03 : p3FwdDedupBinsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n04 : p3Bve5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n05 : p3InitFreshVarRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n06 : p3BvaHopRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n07 : p3BvaMatchLargeRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n08 : p3BvaScanCandsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n09 : p3BvaPickCandRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n10 : p3BvaFilterRowRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n11 : p3BvaCommitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n12 : p3BvaTryLitM7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n13 : p3FheapPairRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n14 : p3FactorM7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n15 : p3CfCompact3Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n16 : p3Compact10Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n17 : p3ReorderRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n18 : p3VivBce4Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n19 : p3SchedMinMaxRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n20 : p3ElimDticksRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n21 : p3M7Search14Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n22 : p3AdpProbeDticksRows.all SpecEntry.noExit = true := by t_kernel_rfl
  simp only [m7RowsPart3Pfx, List.all_append, n01, n02, n03, n04, n05, n06, n07, n08, n09, n10,
    n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22,
    pfx21Slice_noExit hnoP, bveAllTake_noExit hnoB, bveAllSlice_noExit hnoB,
    bveAllDrop_noExit hnoB, Bool.and_self]

theorem m7Part3Callees_of_sub {tPfx tBve tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7RowsPart3Pfx tPfx tBve, e ∈ tbl) : M7Part3TailCallees tbl := by
  have sub_s : ∀ e ∈ p3M7Search14Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart3Pfx; (iterate 25 apply List.mem_append_right); exact List.mem_append_left _ h)
  exact ⟨ sub_s _ (List.mem_of_getElem? (i := 8) rfl)
    , sub_s _ (List.mem_of_getElem? (i := 13) rfl)
    , sub_s _ (List.mem_of_getElem? (i := 11) rfl) ⟩

theorem m7RowsPart3Pfx_tPfx_mem {tPfx tBve : List SpecEntry} {i : Nat}
    (h15 : 15 ≤ i) (hi : i < 21) (hit : i < tPfx.length) :
    tPfx[i] ∈ m7RowsPart3Pfx tPfx tBve := by
  unfold m7RowsPart3Pfx
  rcases Nat.lt_or_ge i 16 with h16 | h16
  · (iterate 2 apply List.mem_append_right); apply List.mem_append_left
    exact m7_mem_drop_take_of_lt tPfx h15 h16 hit
  · rcases Nat.lt_or_ge i 17 with h17 | h17
    · (iterate 20 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tPfx h16 h17 hit
    · (iterate 27 apply List.mem_append_right)
      exact m7_mem_drop_take_of_lt tPfx h17 (by omega) hit

theorem m7RowsPart3Pfx_tBve_mem {tPfx tBve : List SpecEntry} {i : Nat}
    (hi : i < 43) (hit : i < tBve.length) :
    tBve[i] ∈ m7RowsPart3Pfx tPfx tBve := by
  unfold m7RowsPart3Pfx
  rcases Nat.lt_or_ge i 32 with h32 | h32
  · (iterate 4 apply List.mem_append_right); apply List.mem_append_left
    have h32' : i < 0 + 32 := by omega
    have he := m7_mem_drop_take_of_lt tBve (Nat.zero_le _) h32' hit
    simpa [List.drop_zero] using he
  · rcases Nat.lt_or_ge i 34 with h34 | h34
    · (iterate 6 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tBve h32 h34 hit
    · (iterate 24 apply List.mem_append_right); apply List.mem_append_left
      have hj : i - 34 < (tBve.drop 34).length := by rw [List.length_drop]; omega
      have hget : (tBve.drop 34)[i - 34]'hj = tBve[i]'hit := by
        rw [List.getElem_drop]; congr 1; omega
      rw [← hget]; exact List.getElem_mem hj

/-! ## 4. Canonical `full_bce_m4` WP Adapter (`schedEnterDenseSpec` + `Full.fullPropagateSpec`) -/

section BceCanonSection

open LeanQbe.T.Examples.Kissat.FullM4VivBce
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics M4Tactics

private theorem bv64_toNat_setWidth32_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

private theorem m7_bce_m4_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have hmx : c.max_vars < 2 ^ 30 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
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
                ticks_p wsort_p phases_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s4 : FullState :=
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
            have hsw4 : FullSparseInvW c F0 F_cur3 s4 :=
              m4_sparseInvW_of_prop_canon hsw3 hlen_p hw_p hperm_p
            have hfl4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfl_p (Nat.le_trans hfl3 hfl_ex)
            fvt_steps
            all_goals first
              | exact hQ 1#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inl rfl)
                  (fun h => by cases h) hm_p
              | exact hQ 20#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inr rfl)
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

end BceCanonSection

/-! ## 5. Part 3 Prefix Segment `TableImpl` Proofs -/

private theorem p3CfCompact3_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hFlush : (⟨"full_flush_trail", [i64], [i64],
      FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈ tbl)
    (hSweep : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p3CfCompact3Fns p3CfCompact3Rows := by
  unfold p3CfCompact3Fns p3CfCompact3Rows
  exact ⟨ SpecEntry.Impl.of (FullM6CompactFlush.full_compact_needed_m6cf_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CompactFlush.full_compact_flush_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFlush) (envRow_mem hnd _ _ _ _ hSweep))
    , SpecEntry.Impl.of (FullM6CompactFlush.full_compact_mark_live_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext)), trivial ⟩

private theorem p3Reorder_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3ReorderRows, e ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p3ReorderFns p3ReorderRows := by
  have hfn : p3ReorderFns =
      [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.full_reorder_weight_m7_body⟩
      , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.full_reorder_sift_m7_body⟩
      , ⟨"full_reorder_queue_m7", [i64], [i64], FullM7Reorder.full_reorder_queue_m7_body⟩ ] :=
    rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p3ReorderRows
  exact ⟨ SpecEntry.Impl.of (FullM7Reorder.full_reorder_weight_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_queue_m7_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderWeightSpec_noExit h))
        (envRow_mem hnd _ _ _ _ hNext)
        (er 1 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderSiftSpec_noExit h))), trivial ⟩

private theorem p3VivBce4_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3VivBce4Rows, e ∈ tbl)
    (hBce : (⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool],
      Full.fullBveTryBceSpec, true⟩ : SpecEntry) ∈ tbl)
    (hEp2 : (⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈ tbl)
    (hEpCl : (⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ : SpecEntry) ∈ tbl)
    (hDelBin : (⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hCol : (⟨"full_bve_collect", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hEd : (⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hReb : (⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3VivBce4Fns p3VivBce4Rows := by
  have hfn : p3VivBce4Fns =
      [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
          FullM4VivBce.full_bce_side_m4_body⟩
      , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.full_bce_pair_m4_body⟩
      , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.full_bce_var_m4_body⟩
      , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.full_bce_m4_body⟩ ] := by t_kernel_rfl
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
    , SpecEntry.Impl.of (m7_bce_m4_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hEd)
        (er 2 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hReb)
        (envRow_mem hnd _ _ _ _ hProp)), trivial ⟩

private theorem p3M7Search14_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3M7Search14Rows, e ∈ tbl)
    (hLog : (⟨"full_log10_q16_m7", [i64], [i64], FullM7Search.m7Log10Q16Spec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hIlog : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl)
    (hHeapDn : (⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNDV : (⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hAsg : (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl)
    (hScan : (⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.fullLuckyScanSpec, true⟩ :
      SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3M7Search14Fns p3M7Search14Rows := by
  have hfn : p3M7Search14Fns =
      [ ⟨"full_lcg_next_m7", [i64], [i64], FullM7Search.full_lcg_next_m7_body⟩
      , ⟨"full_m7_get64", [i64, i64], [i64], FullM7Search.full_m7_get64_body⟩
      , ⟨"full_m7_set64", [i64, i64, i64], [], FullM7Search.full_m7_set64_body⟩
      , ⟨"full_m7_state_init", [i64], [], FullM7Search.full_m7_state_init_body⟩
      , ⟨"full_tumble_clause_m7", [i64, i32], [.bool], FullM7Search.full_tumble_clause_m7_body⟩
      , ⟨"full_tumble_clauses_m7", [i64, i64], [i64], FullM7Search.full_tumble_clauses_m7_body⟩
      , ⟨"full_tumble_m7", [i64], [i64], FullM7Search.full_tumble_m7_body⟩
      , ⟨"full_lucky_polar_m7", [i64], [i64], FullM7Search.full_lucky_polar_m7_body⟩
      , ⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.full_lucky_late_m7_body⟩
      , ⟨"full_randec_step_m7", [i64], [], FullM7Search.full_randec_step_m7_body⟩
      , ⟨"full_randec_var_m7", [i64], [i64], FullM7Search.full_randec_var_m7_body⟩
      , ⟨"full_decide_m7", [i64], [i64], FullM7Search.full_decide_m7_body⟩
      , ⟨"full_ema_swap_m7", [i64, i64, i64], [], FullM7Search.full_ema_swap_m7_body⟩
      , ⟨"full_switch_mode_m7", [i64], [], FullM7Search.full_switch_mode_m7_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have rLcg := er 0 rfl (fun _ _ _ _ h => FullM7Search.m7LcgNextSpec_monoX h)
  have rGet := er 1 rfl (fun _ _ _ _ h => FullM7Search.m7Get64Spec_monoX h)
  have rSet := er 2 rfl (fun _ _ _ _ h => FullM7Search.m7Set64Spec_monoX h)
  have rInit := er 3 rfl (fun _ _ _ _ h => FullM7Search.m7StateInitSpec_monoX h)
  have rTc := er 4 rfl (fun _ _ _ _ h => FullM7Search.m7TumbleClauseSpec_monoX h)
  have rTcs := er 5 rfl (fun _ _ _ _ h => FullM7Search.m7TumbleClausesSpec_monoX h)
  have rPol := er 7 rfl (fun _ _ _ _ h => h)
  have rRv := er 10 rfl (fun _ _ _ _ h => FullM7Search.m7RandecVarSpec_monoX h)
  have rEma := er 12 rfl (fun _ _ _ _ h => FullM7Search.m7EmaSwapSpec_monoX h)
  have rLog := envRow_mem hnd _ _ _ _ hLog (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h)
  have rNext := envRow_mem hnd _ _ _ _ hNext
  have rAsg := envRow_mem hnd _ _ _ _ hAsg
  rw [hfn]; unfold p3M7Search14Rows
  exact ⟨ SpecEntry.Impl.of (FullM7Search.full_lcg_next_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Search.full_m7_get64_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Search.full_m7_set64_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Search.full_m7_state_init_wp (Env.ofTable tbl) rGet rSet)
    , SpecEntry.Impl.of (FullM7Search.full_tumble_clause_m7_wp (Env.ofTable tbl) rLcg)
    , SpecEntry.Impl.of (FullM7Search.full_tumble_clauses_m7_wp (Env.ofTable tbl) rNext rTc)
    , SpecEntry.Impl.of (FullM7Search.full_tumble_m7_wp (Env.ofTable tbl) rTcs)
    , SpecEntry.Impl.of (FullM7Search.full_lucky_polar_m7_wp (Env.ofTable tbl) rNext)
    , SpecEntry.Impl.of (FullM7Search.full_lucky_late_m7_wp (Env.ofTable tbl) rPol
        (envRow_mem hnd _ _ _ _ hScan) rAsg (envRow_mem hnd _ _ _ _ hBt)
        (envRow_mem hnd _ _ _ _ hProp))
    , SpecEntry.Impl.of (FullM7Search.full_randec_step_m7_wp (Env.ofTable tbl) rInit rGet rSet)
    , SpecEntry.Impl.of (FullM7Search.full_randec_var_m7_wp (Env.ofTable tbl)
        rLcg rInit rGet rSet rLog)
    , SpecEntry.Impl.of (FullM7Search.full_decide_m7_wp (Env.ofTable tbl) rRv
        (envRow_mem hnd _ _ _ _ hNDV) rAsg)
    , SpecEntry.Impl.of (FullM7Search.full_ema_swap_m7_wp (Env.ofTable tbl) rInit rGet rSet)
    , SpecEntry.Impl.of (FullM7Search.full_switch_mode_m7_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hIlog) (envRow_mem hnd _ _ _ _ hHeapDn) rEma rLog)
    , trivial ⟩

/-- `AllFns Fn.Wf` for all `134` functions of `FullM7.m7FnsPart3`. -/
theorem m7FnsPart3_wf : AllFns Fn.Wf m7FnsPart3 :=
  FullM6Transport.allFns_of_mem fun f hf => FullM7.m7Fns_wf f (by
    unfold FullM7.m7Fns; exact List.mem_append_right _ hf)

/-- Certifies all `129` prefix functions of `FullM7.m7FnsPart3` against `m7RowsPart3Pfx tPfx tBve`
in `Env.ofTable tbl`, parameterized over `hPfxOk` (`[15..20]`) and `hBveOk` (`43` fns). -/
theorem m7RowsPart3Pfx_tableImpl {tPfx tBve tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxLen : m7OrchPfxFns.length = tPfx.length)
    (hPfxOk : TableImpl (Env.ofTable tbl) m7OrchPfxFns tPfx)
    (hBveLen : m7BveAllFns.length = tBve.length)
    (hBveOk : TableImpl (Env.ofTable tbl) m7BveAllFns tBve)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (htBve : ∀ e ∈ tBve, e ∈ tbl)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hc1 : M7Part1Callees tbl) (hc2 : M7Part2Callees tbl)
    (hOwn : ∀ e ∈ m7RowsPart3Pfx tPfx tBve, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) (m7FnsPart3.take 129) (m7RowsPart3Pfx tPfx tBve) := by
  have sub_sw22 : ∀ e ∈ p3Sweep22Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; exact List.mem_append_left _ h)
  have sub_fwd : ∀ e ∈ p3FwdDedupBinsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 3 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_b5 : ∀ e ∈ p3Bve5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 5 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ifv : ∀ e ∈ p3InitFreshVarRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 7 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bhop : ∀ e ∈ p3BvaHopRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 8 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bml : ∀ e ∈ p3BvaMatchLargeRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 9 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bsc : ∀ e ∈ p3BvaScanCandsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 10 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bpc : ∀ e ∈ p3BvaPickCandRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 11 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bfr : ∀ e ∈ p3BvaFilterRowRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 12 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bcom : ∀ e ∈ p3BvaCommitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 13 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_btl : ∀ e ∈ p3BvaTryLitM7Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 14 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_fh : ∀ e ∈ p3FheapPairRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 15 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_fac : ∀ e ∈ p3FactorM7Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 16 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cfc : ∀ e ∈ p3CfCompact3Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 17 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cmp10 : ∀ e ∈ p3Compact10Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 18 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_reord : ∀ e ∈ p3ReorderRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 19 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bce4 : ∀ e ∈ p3VivBce4Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 21 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_srch14 : ∀ e ∈ p3M7Search14Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 25 apply List.mem_append_right); exact List.mem_append_left _ h)
  have rDef := htPfx _ hPfxSpecs.wstackDefrag
  have rWp := htPfx _ hPfxSpecs.watchPush
  have rRew := htPfx _ hPfxSpecs.rewatchArena
  have rSwp := htPfx _ hPfxSpecs.arenaSweep
  have rBveCol := htBve _ hBveSpecs.bveCollect
  have rSwpVar := sub_sw22 _ (List.mem_of_getElem? (i := 21) rfl)
  have rTryBce := sub_b5 _ (List.mem_of_getElem? (i := 2) rfl)
  have rIfv := sub_ifv _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaML := sub_bml _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaSC := sub_bsc _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaPC := sub_bpc _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaFR := sub_bfr _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaCom := sub_bcom _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaTL := sub_btl _ (List.mem_of_getElem? (i := 0) rfl)
  have rFhUp := sub_fh _ (List.mem_of_getElem? (i := 0) rfl)
  have rFhDn := sub_fh _ (List.mem_of_getElem? (i := 1) rfl)
  have rCmpFl := sub_cfc _ (List.mem_of_getElem? (i := 1) rfl)
  have rCmpMl := sub_cfc _ (List.mem_of_getElem? (i := 2) rfl)
  have rMaxU : (⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩ :
      SpecEntry) ∈ tbl := hOwn _ (by
    unfold m7RowsPart3Pfx; (iterate 22 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  have ps : ∀ off n,
      TableImpl (Env.ofTable tbl) ((m7OrchPfxFns.drop off).take n) ((tPfx.drop off).take n) :=
    tableImpl_drop_take hPfxLen hPfxOk
  have hlen_p : ∀ (off n : Nat),
      ((m7OrchPfxFns.drop off).take n).length = ((tPfx.drop off).take n).length := by
    intro off n; simp [hPfxLen]
  have bs : ∀ off n,
      TableImpl (Env.ofTable tbl) ((m7BveAllFns.drop off).take n) ((tBve.drop off).take n) :=
    tableImpl_drop_take hBveLen hBveOk
  have hlen_b_tk : ∀ (n : Nat), (m7BveAllFns.take n).length = (tBve.take n).length := by
    intro n; simp [hBveLen]
  have hlen_b_sl : ∀ (off n : Nat),
      ((m7BveAllFns.drop off).take n).length = ((tBve.drop off).take n).length := by
    intro off n; simp [hBveLen]
  have hlen_b_dr : ∀ (off : Nat), (m7BveAllFns.drop off).length = (tBve.drop off).length := by
    intro off; simp [hBveLen]
  have ib_tk32 : TableImpl (Env.ofTable tbl) (m7BveAllFns.take 32) (tBve.take 32) := by
    simpa only [List.drop_zero] using bs 0 32
  have ib_dr34 : TableImpl (Env.ofTable tbl) (m7BveAllFns.drop 34) (tBve.drop 34) := by
    have h43 : m7BveAllFns.length = 43 := m7BveAllFns_length
    have he1 : m7BveAllFns.drop 34 = (m7BveAllFns.drop 34).take 9 :=
      (List.take_of_length_le (by rw [List.length_drop, h43]; omega)).symm
    have he2 : tBve.drop 34 = (tBve.drop 34).take 9 :=
      (List.take_of_length_le (by rw [List.length_drop, ← hBveLen, h43]; omega)).symm
    rw [he1, he2]; exact bs 34 9
  have i_sw22 : TableImpl (Env.ofTable tbl) p3Sweep22Fns p3Sweep22Rows :=
    (modTakeSliceTransport FullM4Sweep.fullM4SweepEnv_moduleOk
      FullM4Sweep.fullM4SweepSpecTable_nodup (by t_kernel_rfl) 0 22 (by decide)
      [ FullM4Sweep.fullM4SweepSpecTable[24]'(by decide)
      , FullM4Sweep.fullM4SweepSpecTable[27]'(by decide)
      , FullM4Sweep.fullM4SweepSpecTable[28]'(by decide) ]
      (by t_kernel_rfl)
      (m7_memC (List.getElem_mem _) (m7_memC (List.getElem_mem _) (m7_mem1 (List.getElem_mem _))))
      hnd sub_sw22 (m7_memC hc1.rngNext (m7_memC hc2.addUnit (m7_mem1 hc2.addBin)))).2
  have i_swdm5 : TableImpl (Env.ofTable tbl) p3SweepDenseM5Fns p3SweepDenseM5Rows :=
    m7_oneImpl rfl rfl (FullM5Orch.full_sweep_dense_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rSwpVar))
  have i_fwd : TableImpl (Env.ofTable tbl) p3FwdDedupBinsFns p3FwdDedupBinsRows :=
    (fullSliceTransport 145 1
      [⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩]
      (by t_kernel_rfl) (m7_mem1 (fullRow_at 102 _)) hnd sub_fwd (m7_mem1 hc2.addUnit)).2
  have i_bve5 : TableImpl (Env.ofTable tbl) p3Bve5Fns p3Bve5Rows := by
    have sub_rp : ∀ e ∈ p3BveResPairRows, e ∈ tbl := fun _ h => sub_b5 _ (by
      unfold p3Bve5Rows; (iterate 4 apply List.mem_append_left); exact h)
    have sub_tb : ∀ e ∈ p3BveTryBceRows, e ∈ tbl := fun _ h => sub_b5 _ (by
      unfold p3Bve5Rows; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_right _ h)
    have sub_en : ∀ e ∈ p3BveExtNeedRows, e ∈ tbl := fun _ h => sub_b5 _ (by
      unfold p3Bve5Rows; exact List.mem_append_right _ h)
    have i_rp := (fullSliceTransport 151 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_rp
      (fun _ h => nomatch h)).2
    have i_wk : TableImpl (Env.ofTable tbl) (Full.fullFns.drop 152 |>.take 1) p3BveWeakenRows :=
      m7_oneImpl rfl rfl (FullFast.fast_bve_weaken_tmk_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hc2.extendPush2) (envRow_mem hnd _ _ _ _ hc2.deleteBinary)
        (envRow_mem hnd _ _ _ _ hc2.extendPushCl))
    have i_tb := (fullSliceTransport 153 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_tb
      (fun _ h => nomatch h)).2
    have i_cr : TableImpl (Env.ofTable tbl) (Full.fullFns.drop 154 |>.take 1) p3BveCommitResRows :=
      m7_oneImpl rfl rfl (FullFast.fast_bve_commit_res_tmk_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hc1.allocCl) (envRow_mem hnd _ _ _ _ rWp)
        (envRow_mem hnd _ _ _ _ hc2.addBin) (envRow_mem hnd _ _ _ _ hc2.addUnit))
    have i_en := (fullSliceTransport 155 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_en
      (fun _ h => nomatch h)).2
    have hf : p3Bve5Fns =
        (Full.fullFns.drop 151).take 1 ++ (Full.fullFns.drop 152).take 1 ++
        (Full.fullFns.drop 153).take 1 ++ (Full.fullFns.drop 154).take 1 ++
        (Full.fullFns.drop 155).take 1 := by t_kernel_rfl
    rw [hf]; unfold p3Bve5Rows
    exact tableImpl_append rfl (tableImpl_append rfl (tableImpl_append rfl
      (tableImpl_append rfl i_rp i_wk) i_tb) i_cr) i_en
  have i_ifv : TableImpl (Env.ofTable tbl) p3InitFreshVarFns p3InitFreshVarRows :=
    m7_oneImpl rfl rfl (FullM7BvaFactor.full_init_fresh_var_m7_heap_wp (Env.ofTable tbl))
  have i_bhop : TableImpl (Env.ofTable tbl) p3BvaHopFns p3BvaHopRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      0 3 (by decide) [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_bhop
      (fun _ h => nomatch h)).2
  have i_bml : TableImpl (Env.ofTable tbl) p3BvaMatchLargeFns p3BvaMatchLargeRows :=
    m7_oneImpl rfl rfl (FullBvaHeap.full_bva_match_large_wp (Env.ofTable tbl))
  have i_bsc : TableImpl (Env.ofTable tbl) p3BvaScanCandsFns p3BvaScanCandsRows :=
    m7_oneImpl rfl rfl (FullM4Bva.m4_bva_scan_cands_wp (Env.ofTable tbl))
  have i_bpc : TableImpl (Env.ofTable tbl) p3BvaPickCandFns p3BvaPickCandRows :=
    m7_oneImpl rfl rfl (FullM6BvaNoHops.m6_bva_pick_cand_no_hops_wp (Env.ofTable tbl))
  have i_bfr : TableImpl (Env.ofTable tbl) p3BvaFilterRowFns p3BvaFilterRowRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      4 1 (by decide) [FullM4Bva.m4BvaSpecTable[19]'(by decide)] (by t_kernel_rfl)
      (m7_mem1 (List.getElem_mem _)) hnd sub_bfr (m7_mem1 rBvaML)).2
  have i_bcom : TableImpl (Env.ofTable tbl) p3BvaCommitFns p3BvaCommitRows :=
    m7_oneImpl rfl rfl (FullM5DenseSafe.full_bva_commit_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rDef) (envRow_mem hnd _ _ _ _ rIfv)
      (envRow_mem hnd _ _ _ _ hc2.addBin) (envRow_mem hnd _ _ _ _ hc1.allocCl)
      (envRow_mem hnd _ _ _ _ rWp) (envRow_mem hnd _ _ _ _ hc2.deleteBinary)
      (envRow_mem hnd _ _ _ _ hc1.unwatchLarge))
  have i_btl : TableImpl (Env.ofTable tbl) p3BvaTryLitM7Fns p3BvaTryLitM7Rows :=
    m7_oneImpl rfl rfl (FullM7BvaFactor.full_bva_try_lit_m7_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rBvaSC) (envRow_mem hnd _ _ _ _ rBvaPC)
      (envRow_mem hnd _ _ _ _ rBvaFR) (envRow_mem hnd _ _ _ _ rBvaCom))
  have i_fh : TableImpl (Env.ofTable tbl) p3FheapPairFns p3FheapPairRows := by
    have hfn : p3FheapPairFns =
        [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.full_fheap_up_body⟩
        , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
            FullBvaHeap.full_fheap_down_body⟩ ] := by t_kernel_rfl
    rw [hfn]; unfold p3FheapPairRows
    exact ⟨ SpecEntry.Impl.of (FullBvaHeap.full_fheap_up_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullBvaHeap.full_fheap_down_wp (Env.ofTable tbl)), trivial ⟩
  have i_fac : TableImpl (Env.ofTable tbl) p3FactorM7Fns p3FactorM7Rows :=
    m7_oneImpl rfl rfl (FullM7BvaFactor.full_factor_m7_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rFhUp) (envRow_mem hnd _ _ _ _ rFhDn)
      (envRow_mem hnd _ _ _ _ rBvaTL))
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
      (m7_memC (List.getElem_mem _) <| m7_memC (List.getElem_mem _) <|
        m7_memC (List.getElem_mem _) <| m7_memC (List.getElem_mem _) <|
        m7_memC (List.getElem_mem _) <| m7_mem1 (List.getElem_mem _))
      hnd sub_cmp10
      (m7_memC rCmpFl <| m7_memC rCmpMl <| m7_memC hc1.arenaNext <|
        m7_memC rDef <| m7_memC rWp <| m7_mem1 rRew)).2
  have i_reord := p3Reorder_impl hnd sub_reord hc1.arenaNext
  have i_bce4 := p3VivBce4_impl hnd sub_bce4 rTryBce hc2.extendPush2 hc2.extendPushCl
    hc2.deleteBinary rBveCol hc2.enterDense hc2.rebuildWatches hc1.propagate
  have i_minmax : TableImpl (Env.ofTable tbl) p3SchedMinMaxFns p3SchedMinMaxRows := by
    have hfn : p3SchedMinMaxFns =
        [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.full_min_u64_body⟩
        , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.full_max_u64_body⟩ ] := by
      t_kernel_rfl
    rw [hfn]; unfold p3SchedMinMaxRows
    exact ⟨ SpecEntry.Impl.of (FullFastSched.sched_min_u64_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullFastSched.sched_max_u64_wp (Env.ofTable tbl)), trivial ⟩
  have i_edticks : TableImpl (Env.ofTable tbl) p3ElimDticksFns p3ElimDticksRows :=
    m7_oneImpl rfl rfl (FullM5Orch.full_elim_dticks_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rMaxU))
  have i_srch14 := p3M7Search14_impl hnd sub_srch14 hc1.log10Q16M7 hc1.arenaNext hc1.ilog10
    hc1.heapDown hc2.nextDecVar hc1.assign hc1.backtrack hc1.propagate hc2.luckyScan
  have i_adp15 : TableImpl (Env.ofTable tbl) p3AdpProbeDticksFns p3AdpProbeDticksRows :=
    m7_oneImpl rfl rfl (full_probe_dticks_m6_hdr_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.hdrGetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))
  rw [p3Pfx_eq]; unfold p3PfxSeg m7RowsPart3Pfx
  refine tableImpl_append rfl i_sw22 (tableImpl_append rfl i_swdm5 ?_)
  refine tableImpl_append (hlen_p 15 1) (ps 15 1) (tableImpl_append rfl i_fwd ?_)
  refine tableImpl_append (hlen_b_tk 32) ib_tk32 (tableImpl_append rfl i_bve5 ?_)
  refine tableImpl_append (hlen_b_sl 32 2) (bs 32 2) (tableImpl_append rfl i_ifv ?_)
  refine tableImpl_append rfl i_bhop (tableImpl_append rfl i_bml (tableImpl_append rfl i_bsc ?_))
  refine tableImpl_append rfl i_bpc (tableImpl_append rfl i_bfr (tableImpl_append rfl i_bcom ?_))
  refine tableImpl_append rfl i_btl (tableImpl_append rfl i_fh (tableImpl_append rfl i_fac ?_))
  refine tableImpl_append rfl i_cfc (tableImpl_append rfl i_cmp10 (tableImpl_append rfl i_reord ?_))
  refine tableImpl_append (hlen_p 16 1) (ps 16 1) (tableImpl_append rfl i_bce4 ?_)
  refine tableImpl_append rfl i_minmax (tableImpl_append rfl i_edticks ?_)
  refine tableImpl_append (hlen_b_dr 34) ib_dr34 (tableImpl_append rfl i_srch14 ?_)
  exact tableImpl_append rfl i_adp15 (ps 17 4)

theorem m7Part3TailCallees_of_sub {tPfx tBve tbl : List SpecEntry}
    (hOwnPfx : ∀ e ∈ m7RowsPart3Pfx tPfx tBve, e ∈ tbl) :
    M7Part3TailCallees tbl :=
  ⟨ hOwnPfx _ (by
      unfold m7RowsPart3Pfx; (iterate 25 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 8) rfl))
  , hOwnPfx _ (by
      unfold m7RowsPart3Pfx; (iterate 25 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 13) rfl))
  , hOwnPfx _ (by
      unfold m7RowsPart3Pfx; (iterate 25 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl)) ⟩

end LeanQbe.T.Examples.Kissat.FullM7Proof

module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-2 `PR-W2D` (`RC-22`) Module Assembly & Concrete `Mem 64` UNSAT Non-Vacuity

Assembles all `24` Wave-2 `PR-W2D` (`FullM6BveFwd`) UNSAT-only `Func.wp` proofs into a closed
`48`-row specification table (`24` owned `_m6` functions + `24` canonical externs), proves
unconditional `m6BveFwd_moduleOk : ModuleOk m6BveFwdEnv m6BveFwdModule`, exports canonical
UNSAT-soundness bridges, and establishes concrete `100060`-byte `Mem 64` UNSAT non-vacuity
witnesses (`XPost := fun _ _ _ _ => False`, zero SAT/model proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BveFwd

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open Kraken.Bedrock2.Test

/-! ## 1. Closed `48`-Row Spec Table, `m6BveFwdEnv`, & `ModuleOk` -/

/-- Closed `48`-row specification table matching `m6BveFwd_fns` (`[0..24)`) and
`m6BveFwdExterns` (`[24..48)`). -/
def m6BveFwdSpecTable : List SpecEntry :=
  [ ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩
  , ⟨"full_dense_flush_units_m6", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_fwd_flush_large_m6", [i64], [], fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_fwd_reconnect_irred_m6", [i64], [], fullFwdReconnectIrredM6Spec, true⟩
  , ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32], fullFwdScanLitM6Spec, true⟩
  , ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], fullFwdCheckClM6Spec, true⟩
  , ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩
  , ⟨"full_fwd_collect_sort_m6", [i64], [i64], fullFwdCollectSortM6Spec, true⟩
  , ⟨"full_forward_sub_m6", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
      fullBveMarkAndM6Spec, true⟩
  , ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool], fullBveGetTernM6Spec, true⟩
  , ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
      fullBveMatchTernM6Spec, true⟩
  , ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool], fullBveFindIteM6Spec, true⟩
  , ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], fullBveGatesM6Spec, true⟩
  , ⟨"full_bve_var_m6", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var_key_m6", [i64, i32], [i64], fullBveVarKeyM6Spec, true⟩
  , ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], fullBveHeapUpM6Spec, true⟩
  , ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], fullBveHeapDownM6Spec, true⟩
  , ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩
  , ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩
  , ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve_m6", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClTmkSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  , ⟨"full_find_definition", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  ]

/-- Closed specification environment for `m6BveFwdModule`. -/
def m6BveFwdEnv : Env := Env.ofTable m6BveFwdSpecTable

theorem m6BveFwdSpecTable_len : m6BveFwdSpecTable.length = 48 := by t_kernel_rfl

theorem m6BveFwdSpecTable_nodup : (m6BveFwdSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m6BveFwdSpecTable_noExit : ∀ e ∈ m6BveFwdSpecTable, e.noExit = true := by
  intro e he
  have hall : m6BveFwdSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m6BveFwdSpecTable_sigs :
    (m6BveFwdSpecTable.take 24).map (fun e => (e.name, e.as, e.rs)) =
      m6BveFwd_fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

theorem m6BveFwdSpecTable_ext_sigs :
    (m6BveFwdSpecTable.drop 24).map (fun e => ⟨e.name, e.as, e.rs⟩) = m6BveFwdExterns := by
  t_kernel_rfl

theorem m6BveFwdEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6BveFwdEnv f as bs xs m Q X → m6BveFwdEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6BveFwdSpecTable_noExit

theorem m6BveFwdEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m6BveFwdSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m6BveFwdEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m6BveFwdSpecTable_nodup
      (hno xs m Q X hs)

private theorem m6_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (k : Nat) (hk : m6BveFwdSpecTable[k]? = some ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m6BveFwdEnv nm as bs xs m Q X :=
  m6BveFwdEnv_row (List.mem_of_getElem? hk) hno

private theorem m6BveFwd_allFns_wf : AllFns Fn.Wf m6BveFwdModule.fns :=
  ⟨full_dense_prop_unit_m6_wf, full_dense_flush_units_m6_wf, full_fwd_flush_large_m6_wf,
   full_fwd_reconnect_irred_m6_wf, full_fwd_scan_lit_m6_wf, full_fwd_check_cl_m6_wf,
   full_fwd_connect_subsumer_m6_wf, full_fwd_collect_sort_m6_wf, full_forward_sub_m6_wf,
   full_bve_collect_m6_wf, full_bve_mark_and_m6_wf, full_bve_get_tern_m6_wf,
   full_bve_match_tern_m6_wf, full_bve_find_ite_m6_wf, full_bve_gates_m6_wf,
   full_bve_var_m6_wf, full_bve_var_key_m6_wf, full_bve_heap_up_m6_wf, full_bve_heap_down_m6_wf,
   full_bve_heap_push_m6_wf, full_bve_heap_pop_m6_wf, full_bve_collect_nbrs_m6_wf,
   full_elim_bve_m6_wf, full_eliminate_m6_wf, trivial⟩

private theorem m6_dense_prop_unit_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], full_dense_prop_unit_m6_body⟩
      ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_dense_prop_unit_m6_wp m6BveFwdEnv (m6_row 28 rfl fun _ _ _ _ h => h))

private theorem m6_dense_flush_units_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_dense_flush_units_m6", [i64], [.bool], full_dense_flush_units_m6_body⟩
      ⟨"full_dense_flush_units_m6", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩ :=
  SpecEntry.Impl.of
    (full_dense_flush_units_m6_wp m6BveFwdEnv (m6_row 0 rfl fullDensePropUnitM6Spec_noExit))

private theorem m6_fwd_flush_large_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_fwd_flush_large_m6", [i64], [], full_fwd_flush_large_m6_body⟩
      ⟨"full_fwd_flush_large_m6", [i64], [], fullFwdFlushLargeM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_flush_large_m6_wp m6BveFwdEnv (m6_row 25 rfl fun _ _ _ _ h => h))

private theorem m6_fwd_reconnect_irred_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_fwd_reconnect_irred_m6", [i64], [], full_fwd_reconnect_irred_m6_body⟩
      ⟨"full_fwd_reconnect_irred_m6", [i64], [], fullFwdReconnectIrredM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_reconnect_irred_m6_wp m6BveFwdEnv
    (m6_row 2 rfl fullFwdFlushLargeM6Spec_noExit)
    (m6_row 24 rfl fun _ _ _ _ h => h) (m6_row 26 rfl fun _ _ _ _ h => h))

private theorem m6_fwd_scan_lit_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32], full_fwd_scan_lit_m6_body⟩
      ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32], fullFwdScanLitM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_scan_lit_m6_wp m6BveFwdEnv)

private theorem m6_fwd_check_cl_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], full_fwd_check_cl_m6_body⟩
      ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], fullFwdCheckClM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_check_cl_m6_wp m6BveFwdEnv
    (m6_row 4 rfl fullFwdScanLitM6Spec_noExit)
    (m6_row 27 rfl fun _ _ _ _ h => h) (m6_row 28 rfl fun _ _ _ _ h => h)
    (m6_row 29 rfl fun _ _ _ _ h => h) (m6_row 1 rfl fullDenseFlushUnitsM6Spec_noExit))

private theorem m6_fwd_connect_subsumer_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [], full_fwd_connect_subsumer_m6_body⟩
      ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_connect_subsumer_m6_wp m6BveFwdEnv (m6_row 26 rfl fun _ _ _ _ h => h))

private theorem m6_fwd_collect_sort_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_fwd_collect_sort_m6", [i64], [i64], full_fwd_collect_sort_m6_body⟩
      ⟨"full_fwd_collect_sort_m6", [i64], [i64], fullFwdCollectSortM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_collect_sort_m6_wp m6BveFwdEnv (m6_row 24 rfl fun _ _ _ _ h => h))

private theorem m6_forward_sub_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_forward_sub_m6", [i64, i64], [i64], full_forward_sub_m6_body⟩
      ⟨"full_forward_sub_m6", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
  SpecEntry.Impl.of (full_forward_sub_m6_wp m6BveFwdEnv
    (m6_row 34 rfl fun _ _ _ _ h => h) (m6_row 1 rfl fullDenseFlushUnitsM6Spec_noExit)
    (m6_row 7 rfl fullFwdCollectSortM6Spec_noExit) (m6_row 2 rfl fullFwdFlushLargeM6Spec_noExit)
    (m6_row 5 rfl fullFwdCheckClM6Spec_noExit) (m6_row 6 rfl fullFwdConnectSubsumerM6Spec_noExit)
    (m6_row 24 rfl fun _ _ _ _ h => h) (m6_row 3 rfl fullFwdReconnectIrredM6Spec_noExit))

private theorem m6_bve_collect_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32], full_bve_collect_m6_body⟩
      ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_collect_m6_wp m6BveFwdEnv)

private theorem m6_bve_mark_and_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
        full_bve_mark_and_m6_body⟩
      ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
        fullBveMarkAndM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_mark_and_m6_wp m6BveFwdEnv)

private theorem m6_bve_get_tern_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool], full_bve_get_tern_m6_body⟩
      ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool], fullBveGetTernM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_get_tern_m6_wp m6BveFwdEnv)

private theorem m6_bve_match_tern_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
        full_bve_match_tern_m6_body⟩
      ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
        fullBveMatchTernM6Spec, true⟩ :=
  SpecEntry.Impl.of
    (full_bve_match_tern_m6_wp m6BveFwdEnv (m6_row 11 rfl fullBveGetTernM6Spec_noExit))

private theorem m6_bve_find_ite_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool], full_bve_find_ite_m6_body⟩
      ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool], fullBveFindIteM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_find_ite_m6_wp m6BveFwdEnv
    (m6_row 11 rfl fullBveGetTernM6Spec_noExit) (m6_row 12 rfl fullBveMatchTernM6Spec_noExit))

private theorem m6_bve_gates_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], full_bve_gates_m6_body⟩
      ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], fullBveGatesM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_gates_m6_wp m6BveFwdEnv
    (m6_row 10 rfl fullBveMarkAndM6Spec_noExit) (m6_row 13 rfl fullBveFindIteM6Spec_noExit)
    (m6_row 35 rfl fun _ _ _ _ h => h))

private theorem m6_bve_var_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_var_m6", [i64, i32], [i64], full_bve_var_m6_body⟩
      ⟨"full_bve_var_m6", [i64, i32], [i64], fullBveVarDefSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_var_m6_wp m6BveFwdEnv
    (m6_row 9 rfl fun _ _ _ _ h => h) (m6_row 40 rfl fun _ _ _ _ h => h)
    (m6_row 37 rfl fun _ _ _ _ h => h) (m6_row 31 rfl fun _ _ _ _ h => h)
    (m6_row 14 rfl fullBveGatesM6Spec_noExit) (m6_row 36 rfl fun _ _ _ _ h => h)
    (m6_row 25 rfl fun _ _ _ _ h => h) (m6_row 39 rfl fun _ _ _ _ h => h)
    (m6_row 1 rfl fullDenseFlushUnitsM6Spec_noExit) (m6_row 38 rfl fun _ _ _ _ h => h)
    (m6_row 32 rfl fun _ _ _ _ h => h) (m6_row 30 rfl fun _ _ _ _ h => h)
    (m6_row 33 rfl fun _ _ _ _ h => h))

private theorem m6_bve_var_key_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_var_key_m6", [i64, i32], [i64], full_bve_var_key_m6_body⟩
      ⟨"full_bve_var_key_m6", [i64, i32], [i64], fullBveVarKeyM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_var_key_m6_wp m6BveFwdEnv)

private theorem m6_bve_heap_up_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], full_bve_heap_up_m6_body⟩
      ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], fullBveHeapUpM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_heap_up_m6_wp m6BveFwdEnv)

private theorem m6_bve_heap_down_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], full_bve_heap_down_m6_body⟩
      ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], fullBveHeapDownM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_heap_down_m6_wp m6BveFwdEnv)

private theorem m6_bve_heap_push_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], full_bve_heap_push_m6_body⟩
      ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_heap_push_m6_wp m6BveFwdEnv
    (m6_row 16 rfl fullBveVarKeyM6Spec_noExit) (m6_row 17 rfl fullBveHeapUpM6Spec_noExit)
    (m6_row 18 rfl fullBveHeapDownM6Spec_noExit))

private theorem m6_bve_heap_pop_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], full_bve_heap_pop_m6_body⟩
      ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩ :=
  SpecEntry.Impl.of
    (full_bve_heap_pop_m6_wp m6BveFwdEnv (m6_row 18 rfl fullBveHeapDownM6Spec_noExit))

private theorem m6_bve_collect_nbrs_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64], full_bve_collect_nbrs_m6_body⟩
      ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_collect_nbrs_m6_wp m6BveFwdEnv)

private theorem m6_elim_bve_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_elim_bve_m6", [i64, i64], [i64], full_elim_bve_m6_body⟩
      ⟨"full_elim_bve_m6", [i64, i64], [i64], m3ElimBveSpec, true⟩ :=
  SpecEntry.Impl.of (full_elim_bve_m6_wp m6BveFwdEnv
    (m6_row 1 rfl fullDenseFlushUnitsM6Spec_noExit) (m6_row 19 rfl fullBveHeapPushM6Spec_noExit)
    (m6_row 20 rfl fullBveHeapPopM6Spec_noExit) (m6_row 21 rfl fun _ _ _ _ h => h)
    (m6_row 15 rfl fun _ _ _ _ h => h))

private theorem m6_eliminate_impl :
    SpecEntry.Impl m6BveFwdEnv
      ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m6_body⟩
      ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
  SpecEntry.Impl.of (full_eliminate_m6_wp m6BveFwdEnv
    (m6_row 41 rfl fun _ _ _ _ h => h) (m6_row 42 rfl fun _ _ _ _ h => h)
    (m6_row 43 rfl fun _ _ _ _ h => h) (m6_row 45 rfl fun _ _ _ _ h => h)
    (m6_row 44 rfl fun _ _ _ _ h => h) (m6_row 8 rfl fun _ _ _ _ h => h)
    (m6_row 22 rfl fun _ _ _ _ h => h) (m6_row 46 rfl fun _ _ _ _ h => h)
    (m6_row 47 rfl fun _ _ _ _ h => h))

/-- Unconditional `ModuleOk` certifying all `24/24` owned Wave-2 `PR-W2D` functions of
`m6BveFwdModule` against the closed `48`-row `m6BveFwdEnv`. -/
theorem m6BveFwd_moduleOk : ModuleOk m6BveFwdEnv m6BveFwdModule :=
  Env.ofTable_moduleOk m6BveFwdModule_acyclic m6BveFwd_allFns_wf
    ⟨m6_dense_prop_unit_impl, m6_dense_flush_units_impl, m6_fwd_flush_large_impl,
     m6_fwd_reconnect_irred_impl, m6_fwd_scan_lit_impl, m6_fwd_check_cl_impl,
     m6_fwd_connect_subsumer_impl, m6_fwd_collect_sort_impl, m6_forward_sub_impl,
     m6_bve_collect_impl, m6_bve_mark_and_impl, m6_bve_get_tern_impl,
     m6_bve_match_tern_impl, m6_bve_find_ite_impl, m6_bve_gates_impl, m6_bve_var_impl,
     m6_bve_var_key_impl, m6_bve_heap_up_impl, m6_bve_heap_down_impl, m6_bve_heap_push_impl,
     m6_bve_heap_pop_impl, m6_bve_collect_nbrs_impl, m6_elim_bve_impl, m6_eliminate_impl, trivial⟩

/-! ## 2. Canonical UNSAT-Soundness Bridges -/

/-- Canonical `Full.fullFwdCheckClSpec` satisfaction under `m6BveFwdEnv`. -/
theorem full_fwd_check_cl_m6_canon_ok :
    ∀ a m Q X, fullFwdCheckClSpec a m Q X →
      Func.wp m6BveFwdEnv full_fwd_check_cl_m6_body a m Q X :=
  fun _ _ _ _ h => m6_fwd_check_cl_impl.2 _ _ _ _ (fullFwdCheckClM6Spec_of_canon h)

/-- Canonical `FullFastBveBudgets.fullForwardSubFastSpec` UNSAT soundness under `m6BveFwdEnv`. -/
theorem full_forward_sub_m6_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {budget : BitVec 64} {m : Mem 64}
    (hinv : FullDenseInv c F0 s) (hm : (FullMem c s ⋆ R) m) :
    Func.wp m6BveFwdEnv full_forward_sub_m6_body (c.hdr, budget, ()) m
      (fun (r, ()) m' => ∃ s',
        FullDenseInv c F0 s' ∧ s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.fuel = s.core.fuel ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧
        (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m6_forward_sub_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, hm, fun _ s' _ h1 h2 h3 h4 h5 hm' => ⟨s', h1, h2, h3, h4, h5, hm'⟩⟩

/-- Canonical `Full.fullBveVarSpec` UNSAT soundness under `m6BveFwdEnv` (and `TmkZero`). -/
theorem full_bve_var_m6_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {v : BitVec 32} {m : Mem 64}
    (hinv : FullDenseInv c F0 s) (htmk : TmkZero s) (hv : v.toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m) :
    Func.wp m6BveFwdEnv full_bve_var_m6_body (c.hdr, v, ()) m
      (fun (r, ()) m' => ∃ s',
        FullDenseInv c F0 s' ∧ TmkZero s' ∧ s.core.cur_vars ≤ s'.core.cur_vars ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m6_bve_var_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, htmk, hv, hm, fun _ s' _ h1 h2 h3 h4 h5 h6 hm' =>
      ⟨s', h1, h2, h3, h4, h5, h6, hm'⟩⟩

/-- Canonical `FullM3CongBva.m3ElimBveSpec` UNSAT soundness under `m6BveFwdEnv`. -/
theorem full_elim_bve_m6_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {lim : BitVec 64} {m : Mem 64}
    (hinv : FullDenseInv c F0 s) (htmk : TmkZero s) (hm : (FullMem c s ⋆ R) m) :
    Func.wp m6BveFwdEnv full_elim_bve_m6_body (c.hdr, lim, ()) m
      (fun (r, ()) m' => ∃ s',
        FullDenseInv c F0 s' ∧ TmkZero s' ∧ s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m6_elim_bve_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, htmk, hm, fun _ s' _ h1 h2 h3 h4 h5 hm' =>
      ⟨s', h1, h2, h3, h4, h5, hm'⟩⟩

/-- Canonical `FullFastSched.schedEliminateSpec` sparse-mode UNSAT soundness under
`m6BveFwdEnv`. -/
theorem full_eliminate_m6_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {initial : Bool} {m : Mem 64}
    (hinv : FullSparseInv c F0 s) (hlvl : s.core.cur_level = 0) (hm : (FullMem c s ⋆ R) m) :
    Func.wp m6BveFwdEnv full_eliminate_m6_body (c.hdr, initial, ()) m
      (fun (r, ()) m' => ∃ s',
        FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m6_eliminate_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, hlvl, hm, fun _ s' _ h1 h2 h3 h4 h5 hm' =>
      ⟨s', h1, h2, h3, h4, h5, hm'⟩⟩

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

private theorem nvM6_tmkZero : TmkZero FullM4Sweep.nvM4SweepState := fun v hv => by
  change v < 1 at hv
  obtain rfl : v = 0 := by omega
  decide

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_dense_flush_units_m6`. -/
theorem nv_m6_dense_flush_units :
    Func.wp m6BveFwdEnv full_dense_flush_units_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, ())
      FullM4Sweep.nvM4SweepMem
      (fun (ok, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        (ok = true ∨ ok = false) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m6_dense_flush_units_impl.2 _ _ _ _
    (fullDenseFlushUnitsM6Spec_intro rfl FullM4Sweep.nvM4Sweep_invW hm
      fun ok s' _ hdw _ _ _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', hdw, (by cases ok <;> simp),
          FullM4Sweep.nvM4SweepF0_unsat, hm'⟩)

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_forward_sub_m6`. -/
theorem nv_m6_forward_sub :
    Func.wp m6BveFwdEnv full_forward_sub_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m6_forward_sub_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepState, emp, rfl,
     FullM4Sweep.nvM4Sweep_invW.toDense, hm, fun _ s' _ hd _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `100060`-byte `Mem 64` `r = 20#64` UNSAT non-vacuity (`XPost := False`) for
`full_forward_sub_m6` under an UNSAT-returning `full_fwd_dedup_bins` witness env. -/
theorem nv_m6_forward_sub_unsat20 :
    let Γ20 : Env := fun f as bs xs m Q X =>
      if f = "full_fwd_dedup_bins" then
        ∃ (_ : as = [i64]) (h2 : bs = [.bool]), Q (h2 ▸ (false, ())) m
      else m6BveFwdEnv f as bs xs m Q X
    Func.wp Γ20 full_forward_sub_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState m')
      (fun _ _ _ _ => False) := by
  intro Γ20
  unfold Func.wp full_forward_sub_m6_body
  c0_steps
  refine wp_call_of_spec _ _ ?_
  dsimp only [Γ20]; rw [ite_eq_left rfl]
  refine ⟨rfl, rfl, ?_⟩
  exact ⟨(fun h => by cases h), fun _ =>
    ⟨rfl, FullM4Sweep.nvM4SweepF0_unsat, FullM4Sweep.nvM4SweepMem_ok⟩⟩

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_bve_gates_m6`. -/
theorem nv_m6_bve_gates :
    Func.wp m6BveFwdEnv full_bve_gates_m6_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 0#32, 0#32, ()) FullM4Sweep.nvM4SweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m6_bve_gates_impl.2 _ _ _ _
    (fullBveGatesM6Spec_intro rfl FullM4Sweep.nvM4Sweep_invW nvM6_tmkZero
      (by decide) (by decide) (by decide) (by decide)
      (fun i hi => by change i < 0 at hi; omega)
      (fun j hj => by change j < 0 at hj; omega) hm
      fun s' _ hdw htm _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdw, htm, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩)

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_bve_var_m6`. -/
theorem nv_m6_bve_var :
    Func.wp m6BveFwdEnv full_bve_var_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m6_bve_var_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepState, emp, rfl,
     FullM4Sweep.nvM4Sweep_invW.toDense, nvM6_tmkZero, by decide, hm,
     fun _ s' _ hd htm _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, htm, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_bve_collect_nbrs_m6`. -/
theorem nv_m6_bve_collect_nbrs :
    Func.wp m6BveFwdEnv full_bve_collect_nbrs_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (nn, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        nn.toNat ≤ 1 ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m6_bve_collect_nbrs_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepState, emp, rfl,
     FullM4Sweep.nvM4Sweep_invW.toDense, nvM6_tmkZero, hm,
     fun _ mclr' ws2' m' hl' hnn _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨_, fullDenseInv_with_min_clr_work_stk2 FullM4Sweep.nvM4Sweep_invW.toDense
         hl'.core_ok.min_clr_len_arr hl'.scratch_ok.work_stk2_len,
         nvM6_tmkZero, hnn, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_elim_bve_m6`. -/
theorem nv_m6_elim_bve :
    Func.wp m6BveFwdEnv full_elim_bve_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 100#64, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m6_elim_bve_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepState, emp, rfl,
     FullM4Sweep.nvM4Sweep_invW.toDense, nvM6_tmkZero, hm,
     fun _ s' _ hd htm _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, htm, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Headline concrete `100060`-byte `Mem 64` sparse-mode UNSAT non-vacuity (`XPost := False`,
`0` SAT proofs) for `full_eliminate_m6` under the closed `m6BveFwdEnv`. -/
theorem nv_m6_eliminate :
    Func.wp m6BveFwdEnv full_eliminate_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, true, ())
      FullM4Sweep.nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepSparseState ⋆ emp)
      FullM4Sweep.nvM4SweepSparseMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepSparseMem_ok
  exact m6_eliminate_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepSparseState, emp, rfl,
     FullM4Sweep.nvM4SweepSparse_inv, rfl, hm,
     fun _ s' _ hsp hlvl _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hsp, hlvl, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM6BveFwd

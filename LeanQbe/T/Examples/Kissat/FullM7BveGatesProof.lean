module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof1
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof2
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof3
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof3b
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof4a
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof4b
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof5
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof6
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Master Assembly & UNSAT Non-Vacuity

Assembles the `43`-row `m7BveAllFns` specification table (`39` owned `_m7` fns + `4` canonical
aliases `full_forward_sub`, `full_bve_collect`, `full_bve_var`, `full_eliminate_m6`) and `23`
canonical externs into `m7BveClosedSpecTable` (`66` rows) / `m7BveAllEnv`:
- Proves unconditional `43`-row `m7BveAll_tableImpl` for `Env.ofTable tbl` and general callee
  bridge `m7BveAll_tableImpl_of_callees` (`0` external K6 hypotheses).
- Proves unconditional `SpecEntry.Impl m7BveAllEnv` for `full_k6_solve_m7`, `full_bve_def_k6_m7`,
  `full_bve_gates_m7`, `full_bve_var_m7`, `full_eliminate_m7`, `M7BveAllTblSpecs`,
  UNSAT-soundness bridges, and concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`,
  zero SAT proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

/-! ## 1. `43`-Row `m7BveAllFns` & `66`-Row Closed Spec Table -/

/-- Canonical alias `full_forward_sub` in `m7BveAllFns`. -/
def m7ForwardSubCanonFn : Fn :=
  ⟨"full_forward_sub", [i64, i64], [i64], full_forward_sub_m7_body⟩

/-- Canonical alias `full_bve_collect` in `m7BveAllFns`. -/
def m7BveCollectCanonFn : Fn :=
  ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], full_bve_collect_m7_body⟩

/-- Canonical alias `full_bve_var` in `m7BveAllFns`. -/
def m7BveVarCanonFn : Fn :=
  ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_m7_body⟩

/-- Canonical alias `full_eliminate_m6` in `m7BveAllFns`. -/
def m7EliminateM6CanonFn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m7_body⟩

/-- Exact `43`-function `FullM7BveGates` + canonical alias slice inside `FullM7.m7FnsPart3`. -/
def m7BveAllFns : List Fn :=
  m7BveGates_fns.take 10 ++
  ([ m7ForwardSubCanonFn, m7BveCollectCanonFn ] ++
  ((m7BveGates_fns.drop 10).take 20 ++
  ((m7BveGates_fns.drop 30).take 1 ++
  ([ m7BveVarCanonFn ] ++
  (m7BveGates_fns.drop 31 ++ [ m7EliminateM6CanonFn ])))))

theorem m7BveAllFns_length : m7BveAllFns.length = 43 := by t_kernel_rfl

theorem m7BveAllFns_wf : AllFns Fn.Wf m7BveAllFns :=
  ⟨full_dense_prop_unit_m7_wf, full_dense_flush_units_m7_wf, full_fwd_flush_large_m7_wf,
   full_fwd_reconnect_irred_m7_wf, full_fwd_scan_lit_m7_wf, full_fwd_check_cl_m7_wf,
   full_fwd_connect_subsumer_m7_wf, full_fwd_collect_sort_m7_wf, full_forward_sub_m7_wf,
   full_bve_collect_m7_wf, full_forward_sub_m7_wf, full_bve_collect_m7_wf,
   full_bve_mark_and_m7_wf, full_bve_find_equiv_m7_wf, full_bve_find_and_m7_wf,
   full_bve_get_tern_m7_wf, full_bve_match_tern_m7_wf, full_bve_find_ite_side_m7_wf,
   full_bve_find_ite_m7_wf, full_bve_xor_pat_m7_wf, full_bve_find_xor_m7_wf,
   full_k6_watch_m7_wf, full_k6_assign_m7_wf, full_k6_mtf_m7_wf, full_k6_backtrack_m7_wf,
   full_k6_prop_m7_wf, full_k6_ana_cl_m7_wf, full_k6_analyze_m7_wf, full_k6_solve_m7_wf,
   full_k6_core_m7_wf, full_bve_def_k6_m7_wf, full_bve_gates_m7_wf, full_bve_var_m7_wf,
   full_bve_var_m7_wf, full_bve_var_key_m7_wf, full_bve_heap_up_m7_wf,
   full_bve_heap_down_m7_wf, full_bve_heap_push_m7_wf, full_bve_heap_pop_m7_wf,
   full_bve_collect_nbrs_m7_wf, full_elim_bve_m7_wf, full_eliminate_m7_wf,
   full_eliminate_m7_wf, trivial⟩

/-- `43`-row specification table aligned 1-to-1 with `m7BveAllFns`. -/
def m7BveAllSpecTable : List SpecEntry :=
  [ ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM6Spec, true⟩
  , ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], fullFwdScanLitM7Spec, true⟩
  , ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], fullFwdCheckClM7Spec, true⟩
  , ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩
  , ⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM6Spec, true⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect_m7", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_mark_and_m7", [i64, i32, i32, i32, i32, i32], [.bool],
      fullBveMarkAndM6Spec, true⟩
  , ⟨"full_bve_find_equiv_m7", [i64, i32, i32], [.bool], fullBveFindEquivM7Spec, true⟩
  , ⟨"full_bve_find_and_m7", [i64, i32, i32, i32], [.bool], fullBveFindAndM7Spec, true⟩
  , ⟨"full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool], fullBveGetTernM7Spec, true⟩
  , ⟨"full_bve_match_tern_m7", [i64, i32, i32, i32, i32, i32], [i32],
      fullBveMatchTernM7Spec, true⟩
  , ⟨"full_bve_find_ite_side_m7", [i64, i32, i32, i32, .bool], [.bool],
      fullBveFindIteSideM7Spec, true⟩
  , ⟨"full_bve_find_ite_m7", [i64, i32, i32, i32], [.bool], fullBveFindIteM7Spec, true⟩
  , ⟨"full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32], fullBveXorPatM7Spec, true⟩
  , ⟨"full_bve_find_xor_m7", [i64, i32, i32, i32], [.bool], fullBveFindXorM7Spec, true⟩
  , ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], fullK6WatchM7Spec, true⟩
  , ⟨"full_k6_assign_m7", [i64, i32, i32], [], fullK6AssignM7Spec, true⟩
  , ⟨"full_k6_mtf_m7", [i64, i32], [], fullK6MtfM7Spec, true⟩
  , ⟨"full_k6_backtrack_m7", [i64, i32], [], fullK6BacktrackM7Spec, true⟩
  , ⟨"full_k6_prop_m7", [i64], [i32], fullK6PropM7Spec, true⟩
  , ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], fullK6AnaClM7Spec, true⟩
  , ⟨"full_k6_analyze_m7", [i64, i32], [.bool], fullK6AnalyzeM7Spec, true⟩
  , ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], fullK6SolveM7Spec, true⟩
  , ⟨"full_k6_core_m7", [i64], [], fullK6CoreM7Spec, true⟩
  , ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩
  , ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], fullBveVarKeyM6Spec, true⟩
  , ⟨"full_bve_heap_up_m7", [i64, i64, i32], [], fullBveHeapUpM6Spec, true⟩
  , ⟨"full_bve_heap_down_m7", [i64, i64, i32], [], fullBveHeapDownM6Spec, true⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩
  , ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩
  , ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m7", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩
  ]

/-- `23` extern specification rows matching `m7BveGatesExterns`. -/
def m7BveGatesExternSpecTable : List SpecEntry :=
  [ ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
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

/-- Closed `66`-row specification table (`43` `m7BveAllSpecTable` + `23` externs). -/
def m7BveClosedSpecTable : List SpecEntry :=
  m7BveAllSpecTable ++ m7BveGatesExternSpecTable

/-- Standalone closed specification environment for `m7BveAllFns`. -/
def m7BveAllEnv : Env := Env.ofTable m7BveClosedSpecTable

theorem m7BveAllSpecTable_len : m7BveAllSpecTable.length = 43 := by t_kernel_rfl

theorem m7BveClosedSpecTable_len : m7BveClosedSpecTable.length = 66 := by t_kernel_rfl

theorem m7BveAllSpecTable_sigs :
    m7BveAllSpecTable.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig := by
  t_kernel_rfl

theorem m7BveGatesExternSpecTable_sigs :
    m7BveGatesExternSpecTable.map (fun e => ⟨e.name, e.as, e.rs⟩) = m7BveGatesExterns := by
  t_kernel_rfl

theorem m7BveAllSpecTable_noExit_all :
    m7BveAllSpecTable.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem m7BveAllSpecTable_noExit : ∀ e ∈ m7BveAllSpecTable, e.noExit = true :=
  List.all_eq_true.mp m7BveAllSpecTable_noExit_all

theorem m7BveClosedSpecTable_noExit : ∀ e ∈ m7BveClosedSpecTable, e.noExit = true := by
  intro e he
  have hall : m7BveClosedSpecTable.all SpecEntry.noExit = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m7BveAllSpecTable_nodup : (m7BveAllSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7BveClosedSpecTable_nodup : (m7BveClosedSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7BveAllSpecTable_fwdSub_mem :
    (⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ : SpecEntry) ∈
      m7BveAllSpecTable :=
  List.mem_of_getElem? (i := 10) rfl

theorem m7BveAllSpecTable_bveCollect_mem :
    (⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :
      SpecEntry) ∈ m7BveAllSpecTable :=
  List.mem_of_getElem? (i := 11) rfl

theorem m7BveAllSpecTable_eliminateM6_mem :
    (⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ : SpecEntry) ∈
      m7BveAllSpecTable :=
  List.mem_of_getElem? (i := 42) rfl

/-- Cross-part Part 3 callee memberships matching `FullM7Transport2.M7BveAllTblSpecs`. -/
structure M7BveAllTblSpecs (tBve : List SpecEntry) : Prop where
  bveCollect :
    (⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :
      SpecEntry) ∈ tBve
  fwdSub :
    (⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ : SpecEntry) ∈ tBve
  eliminateM6 :
    (⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ : SpecEntry) ∈ tBve

theorem m7BveAllSpecTable_tblSpecs : M7BveAllTblSpecs m7BveAllSpecTable :=
  ⟨m7BveAllSpecTable_bveCollect_mem, m7BveAllSpecTable_fwdSub_mem,
   m7BveAllSpecTable_eliminateM6_mem⟩

/-! ## 2. Unconditional `43`-Row `TableImpl` -/

private theorem m7_closed_row {Γ : Env} {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hCal : ∀ e ∈ m7BveClosedSpecTable, ∀ a m Q X, e.spec a m Q X → Γ e.name e.as e.rs a m Q X)
    (k : Nat) (hk : m7BveClosedSpecTable[k]? = some ⟨nm, as, bs, sp, true⟩) :
    ∀ xs m Q X, sp xs m Q X → Γ nm as bs xs m Q X :=
  hCal ⟨nm, as, bs, sp, true⟩ (List.mem_of_getElem? hk)

private theorem m7_closed_noExit_spec :
    ∀ e ∈ m7BveClosedSpecTable, ∀ a m Q X, e.spec a m Q X → e.eff a m Q X := by
  intro e he a m Q X hs
  simp only [m7BveClosedSpecTable, m7BveAllSpecTable, m7BveGatesExternSpecTable,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    dsimp only [SpecEntry.eff] <;>
    simp only [↓reduceIte]
  all_goals first
    | exact hs
    | exact fullDensePropUnitM6Spec_noExit a m Q X hs
    | exact fullDenseFlushUnitsM6Spec_noExit a m Q X hs
    | exact fullFwdFlushLargeM6Spec_noExit a m Q X hs
    | exact fullFwdReconnectIrredM6Spec_noExit a m Q X hs
    | exact fullFwdScanLitM7Spec_noExit a m Q X hs
    | exact fullFwdCheckClM7Spec_noExit a m Q X hs
    | exact fullFwdConnectSubsumerM6Spec_noExit a m Q X hs
    | exact fullFwdCollectSortM6Spec_noExit a m Q X hs
    | exact fullBveMarkAndM6Spec_noExit a m Q X hs
    | exact fullBveFindEquivM7Spec_noExit a m Q X hs
    | exact fullBveFindAndM7Spec_noExit a m Q X hs
    | exact fullBveGetTernM7Spec_noExit a m Q X hs
    | exact fullBveMatchTernM7Spec_noExit a m Q X hs
    | exact fullBveFindIteSideM7Spec_noExit a m Q X hs
    | exact fullBveFindIteM7Spec_noExit a m Q X hs
    | exact fullBveXorPatM7Spec_noExit a m Q X hs
    | exact fullBveFindXorM7Spec_noExit a m Q X hs
    | exact fullK6WatchM7Spec_noExit a m Q X hs
    | exact fullK6AssignM7Spec_noExit a m Q X hs
    | exact fullK6MtfM7Spec_noExit a m Q X hs
    | exact fullK6BacktrackM7Spec_noExit a m Q X hs
    | exact fullK6PropM7Spec_noExit a m Q X hs
    | exact fullK6AnaClM7Spec_noExit a m Q X hs
    | exact fullK6AnalyzeM7Spec_noExit a m Q X hs
    | exact fullK6SolveM7Spec_noExit a m Q X hs
    | exact fullK6CoreM7Spec_noExit a m Q X hs
    | exact fullBveGatesM7Spec_noExit a m Q X hs
    | exact fullBveVarKeyM6Spec_noExit a m Q X hs
    | exact fullBveHeapUpM6Spec_noExit a m Q X hs
    | exact fullBveHeapDownM6Spec_noExit a m Q X hs
    | exact fullBveHeapPushM6Spec_noExit a m Q X hs
    | exact fullBveHeapPopM6Spec_noExit a m Q X hs

/-- General `43`-row `TableImpl` over any `Γ` realizing `m7BveClosedSpecTable`. -/
theorem m7BveAll_tableImpl_of_callees {Γ : Env}
    (hCal : ∀ e ∈ m7BveClosedSpecTable, ∀ a m Q X, e.spec a m Q X → Γ e.name e.as e.rs a m Q X) :
    TableImpl Γ m7BveAllFns m7BveAllSpecTable := by
  have i0 : SpecEntry.Impl Γ
      ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], full_dense_prop_unit_m7_body⟩
      ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_dense_prop_unit_m7_wp Γ (m7_closed_row hCal 47 rfl))
  have i1 : SpecEntry.Impl Γ
      ⟨"full_dense_flush_units_m7", [i64], [.bool], full_dense_flush_units_m7_body⟩
      ⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_dense_flush_units_m7_wp Γ (m7_closed_row hCal 0 rfl))
  have i2 : SpecEntry.Impl Γ
      ⟨"full_fwd_flush_large_m7", [i64], [], full_fwd_flush_large_m7_body⟩
      ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_flush_large_m7_wp Γ (m7_closed_row hCal 44 rfl))
  have i3 : SpecEntry.Impl Γ
      ⟨"full_fwd_reconnect_irred_m7", [i64], [], full_fwd_reconnect_irred_m7_body⟩
      ⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_reconnect_irred_m7_wp Γ
      (m7_closed_row hCal 2 rfl) (m7_closed_row hCal 43 rfl) (m7_closed_row hCal 45 rfl))
  have i4 : SpecEntry.Impl Γ
      ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], full_fwd_scan_lit_m7_body⟩
      ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], fullFwdScanLitM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_scan_lit_m7_wp Γ)
  have i5 : SpecEntry.Impl Γ
      ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], full_fwd_check_cl_m7_body⟩
      ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], fullFwdCheckClM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_check_cl_m7_wp Γ
      (m7_closed_row hCal 4 rfl) (m7_closed_row hCal 46 rfl) (m7_closed_row hCal 47 rfl)
      (m7_closed_row hCal 48 rfl) (m7_closed_row hCal 1 rfl))
  have i6 : SpecEntry.Impl Γ
      ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], full_fwd_connect_subsumer_m7_body⟩
      ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_connect_subsumer_m7_wp Γ (m7_closed_row hCal 45 rfl))
  have i7 : SpecEntry.Impl Γ
      ⟨"full_fwd_collect_sort_m7", [i64], [i64], full_fwd_collect_sort_m7_body⟩
      ⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_collect_sort_m7_wp Γ (m7_closed_row hCal 43 rfl))
  have hFwdSub := full_forward_sub_m7_wp Γ
    (m7_closed_row hCal 53 rfl) (m7_closed_row hCal 1 rfl) (m7_closed_row hCal 7 rfl)
    (m7_closed_row hCal 2 rfl) (m7_closed_row hCal 5 rfl) (m7_closed_row hCal 6 rfl)
    (m7_closed_row hCal 43 rfl) (m7_closed_row hCal 3 rfl)
  have i8 : SpecEntry.Impl Γ
      ⟨"full_forward_sub_m7", [i64, i64], [i64], full_forward_sub_m7_body⟩
      ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
    SpecEntry.Impl.of hFwdSub
  have i9 : SpecEntry.Impl Γ
      ⟨"full_bve_collect_m7", [i64, i32, i64, i32], [i32], full_bve_collect_m7_body⟩
      ⟨"full_bve_collect_m7", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :=
    SpecEntry.Impl.of (full_bve_collect_m7_wp Γ)
  have i10 : SpecEntry.Impl Γ m7ForwardSubCanonFn
      ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
    SpecEntry.Impl.of hFwdSub
  have i11 : SpecEntry.Impl Γ m7BveCollectCanonFn
      ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :=
    SpecEntry.Impl.of (full_bve_collect_m7_wp Γ)
  have i12 : SpecEntry.Impl Γ
      ⟨"full_bve_mark_and_m7", [i64, i32, i32, i32, i32, i32], [.bool],
        full_bve_mark_and_m7_body⟩
      ⟨"full_bve_mark_and_m7", [i64, i32, i32, i32, i32, i32], [.bool],
        fullBveMarkAndM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_mark_and_m7_wp Γ)
  have i13 : SpecEntry.Impl Γ
      ⟨"full_bve_find_equiv_m7", [i64, i32, i32], [.bool], full_bve_find_equiv_m7_body⟩
      ⟨"full_bve_find_equiv_m7", [i64, i32, i32], [.bool], fullBveFindEquivM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_equiv_m7_wp Γ)
  have i14 : SpecEntry.Impl Γ
      ⟨"full_bve_find_and_m7", [i64, i32, i32, i32], [.bool], full_bve_find_and_m7_body⟩
      ⟨"full_bve_find_and_m7", [i64, i32, i32, i32], [.bool], fullBveFindAndM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_and_m7_wp Γ)
  have i15 : SpecEntry.Impl Γ
      ⟨"full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool], full_bve_get_tern_m7_body⟩
      ⟨"full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool], fullBveGetTernM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_get_tern_m7_wp Γ)
  have i16 : SpecEntry.Impl Γ
      ⟨"full_bve_match_tern_m7", [i64, i32, i32, i32, i32, i32], [i32],
        full_bve_match_tern_m7_body⟩
      ⟨"full_bve_match_tern_m7", [i64, i32, i32, i32, i32, i32], [i32],
        fullBveMatchTernM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_match_tern_m7_wp Γ)
  have i17 : SpecEntry.Impl Γ
      ⟨"full_bve_find_ite_side_m7", [i64, i32, i32, i32, .bool], [.bool],
        full_bve_find_ite_side_m7_body⟩
      ⟨"full_bve_find_ite_side_m7", [i64, i32, i32, i32, .bool], [.bool],
        fullBveFindIteSideM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_ite_side_m7_wp Γ
      (m7_closed_row hCal 15 rfl) (m7_closed_row hCal 16 rfl))
  have i18 : SpecEntry.Impl Γ
      ⟨"full_bve_find_ite_m7", [i64, i32, i32, i32], [.bool], full_bve_find_ite_m7_body⟩
      ⟨"full_bve_find_ite_m7", [i64, i32, i32, i32], [.bool], fullBveFindIteM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_ite_m7_wp Γ (m7_closed_row hCal 17 rfl))
  have i19 : SpecEntry.Impl Γ
      ⟨"full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32], full_bve_xor_pat_m7_body⟩
      ⟨"full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32], fullBveXorPatM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_xor_pat_m7_wp Γ)
  have i20 : SpecEntry.Impl Γ
      ⟨"full_bve_find_xor_m7", [i64, i32, i32, i32], [.bool], full_bve_find_xor_m7_body⟩
      ⟨"full_bve_find_xor_m7", [i64, i32, i32, i32], [.bool], fullBveFindXorM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_xor_m7_wp Γ (m7_closed_row hCal 19 rfl))
  have i21 : SpecEntry.Impl Γ
      ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], full_k6_watch_m7_body⟩
      ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], fullK6WatchM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_watch_m7_wp Γ)
  have i22 : SpecEntry.Impl Γ
      ⟨"full_k6_assign_m7", [i64, i32, i32], [], full_k6_assign_m7_body⟩
      ⟨"full_k6_assign_m7", [i64, i32, i32], [], fullK6AssignM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_assign_m7_wp Γ)
  have i23 : SpecEntry.Impl Γ
      ⟨"full_k6_mtf_m7", [i64, i32], [], full_k6_mtf_m7_body⟩
      ⟨"full_k6_mtf_m7", [i64, i32], [], fullK6MtfM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_mtf_m7_wp Γ)
  have i24 : SpecEntry.Impl Γ
      ⟨"full_k6_backtrack_m7", [i64, i32], [], full_k6_backtrack_m7_body⟩
      ⟨"full_k6_backtrack_m7", [i64, i32], [], fullK6BacktrackM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_backtrack_m7_wp Γ)
  have i25 : SpecEntry.Impl Γ
      ⟨"full_k6_prop_m7", [i64], [i32], full_k6_prop_m7_body⟩
      ⟨"full_k6_prop_m7", [i64], [i32], fullK6PropM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_prop_m7_wp Γ (m7_closed_row hCal 22 rfl))
  have i26 : SpecEntry.Impl Γ
      ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], full_k6_ana_cl_m7_body⟩
      ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], fullK6AnaClM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_ana_cl_m7_wp Γ)
  have i27 : SpecEntry.Impl Γ
      ⟨"full_k6_analyze_m7", [i64, i32], [.bool], full_k6_analyze_m7_body⟩
      ⟨"full_k6_analyze_m7", [i64, i32], [.bool], fullK6AnalyzeM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_analyze_m7_wp Γ
      (m7_closed_row hCal 21 rfl) (m7_closed_row hCal 22 rfl)
      (m7_closed_row hCal 24 rfl) (m7_closed_row hCal 23 rfl) (m7_closed_row hCal 26 rfl))
  have i28 : SpecEntry.Impl Γ
      ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], full_k6_solve_m7_body⟩
      ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], fullK6SolveM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_solve_m7_wp Γ
      (m7_closed_row hCal 25 rfl) (m7_closed_row hCal 22 rfl)
      (m7_closed_row hCal 24 rfl) (m7_closed_row hCal 27 rfl))
  have i29 : SpecEntry.Impl Γ
      ⟨"full_k6_core_m7", [i64], [], full_k6_core_m7_body⟩
      ⟨"full_k6_core_m7", [i64], [], fullK6CoreM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_core_m7_wp Γ)
  have i30 : SpecEntry.Impl Γ
      ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], full_bve_def_k6_m7_body⟩
      ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_def_k6_m7_wp Γ
      (m7_closed_row hCal 21 rfl) (m7_closed_row hCal 28 rfl) (m7_closed_row hCal 29 rfl))
  have i31 : SpecEntry.Impl Γ
      ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], full_bve_gates_m7_body⟩
      ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_gates_m7_wp Γ
      (m7_closed_row hCal 13 rfl) (m7_closed_row hCal 14 rfl) (m7_closed_row hCal 18 rfl)
      (m7_closed_row hCal 20 rfl) (m7_closed_row hCal 30 rfl))
  have hBveVar := full_bve_var_m7_wp Γ
    (m7_closed_row hCal 9 rfl) (m7_closed_row hCal 58 rfl) (m7_closed_row hCal 55 rfl)
    (m7_closed_row hCal 50 rfl) (m7_closed_row hCal 31 rfl) (m7_closed_row hCal 54 rfl)
    (m7_closed_row hCal 44 rfl) (m7_closed_row hCal 57 rfl) (m7_closed_row hCal 1 rfl)
    (m7_closed_row hCal 56 rfl) (m7_closed_row hCal 51 rfl) (m7_closed_row hCal 49 rfl)
    (m7_closed_row hCal 52 rfl)
  have r32 : SpecEntry.Impl Γ
      ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩
      ⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩ :=
    SpecEntry.Impl.of hBveVar
  have i33 : SpecEntry.Impl Γ m7BveVarCanonFn
      ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ :=
    SpecEntry.Impl.of hBveVar
  have i34 : SpecEntry.Impl Γ
      ⟨"full_bve_var_key_m7", [i64, i32], [i64], full_bve_var_key_m7_body⟩
      ⟨"full_bve_var_key_m7", [i64, i32], [i64], fullBveVarKeyM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_var_key_m7_wp Γ)
  have i35 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_up_m7", [i64, i64, i32], [], full_bve_heap_up_m7_body⟩
      ⟨"full_bve_heap_up_m7", [i64, i64, i32], [], fullBveHeapUpM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_up_m7_wp Γ)
  have i36 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_down_m7", [i64, i64, i32], [], full_bve_heap_down_m7_body⟩
      ⟨"full_bve_heap_down_m7", [i64, i64, i32], [], fullBveHeapDownM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_down_m7_wp Γ)
  have i37 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], full_bve_heap_push_m7_body⟩
      ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_push_m7_wp Γ
      (m7_closed_row hCal 34 rfl) (m7_closed_row hCal 35 rfl) (m7_closed_row hCal 36 rfl))
  have i38 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], full_bve_heap_pop_m7_body⟩
      ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_pop_m7_wp Γ (m7_closed_row hCal 36 rfl))
  have i39 : SpecEntry.Impl Γ
      ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], full_bve_collect_nbrs_m7_body⟩
      ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩ :=
    SpecEntry.Impl.of (full_bve_collect_nbrs_m7_wp Γ)
  have i40 : SpecEntry.Impl Γ
      ⟨"full_elim_bve_m7", [i64, i64], [i64], full_elim_bve_m7_body⟩
      ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :=
    SpecEntry.Impl.of (full_elim_bve_m7_wp Γ
      (m7_closed_row hCal 1 rfl) (m7_closed_row hCal 37 rfl) (m7_closed_row hCal 38 rfl)
      (m7_closed_row hCal 39 rfl) (m7_closed_row hCal 32 rfl))
  have hElim := full_eliminate_m7_wp Γ
    (m7_closed_row hCal 59 rfl) (m7_closed_row hCal 60 rfl) (m7_closed_row hCal 61 rfl)
    (m7_closed_row hCal 63 rfl) (m7_closed_row hCal 62 rfl) (m7_closed_row hCal 8 rfl)
    (m7_closed_row hCal 40 rfl) (m7_closed_row hCal 64 rfl) (m7_closed_row hCal 65 rfl)
  have i41 : SpecEntry.Impl Γ
      ⟨"full_eliminate_m7", [i64, .bool], [i64], full_eliminate_m7_body⟩
      ⟨"full_eliminate_m7", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
    SpecEntry.Impl.of hElim
  have i42 : SpecEntry.Impl Γ m7EliminateM6CanonFn
      ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
    SpecEntry.Impl.of hElim
  exact ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18,
    i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, r32, i33, i34, i35, i36,
    i37, i38, i39, i40, i41, i42, trivial⟩

/-- Unconditional `43`-row `TableImpl` for `Env.ofTable tbl` whenever
`m7BveClosedSpecTable ⊆ tbl` and names are distinct. -/
theorem m7BveAll_tableImpl {tbl : List SpecEntry}
    (hNodup : (tbl.map SpecEntry.name).Nodup)
    (hSub : ∀ e ∈ m7BveClosedSpecTable, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m7BveAllFns m7BveAllSpecTable := by
  refine m7BveAll_tableImpl_of_callees ?_
  intro e he a m Q X hsp
  exact Env.ofTable_of_mem (e := e) (hSub e he) hNodup (m7_closed_noExit_spec e he a m Q X hsp)

/-! ## 3. Unconditional `m7BveAllEnv` Tail Implementations & UNSAT Soundness -/

private theorem m7BveAllEnv_callees :
    ∀ e ∈ m7BveClosedSpecTable, ∀ a m Q X, e.spec a m Q X →
      m7BveAllEnv e.name e.as e.rs a m Q X := fun e he a m Q X hsp =>
  Env.ofTable_of_mem (e := e) he m7BveClosedSpecTable_nodup
    (m7_closed_noExit_spec e he a m Q X hsp)

private theorem m7_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (k : Nat) (hk : m7BveClosedSpecTable[k]? = some ⟨nm, as, bs, sp, true⟩) :
    ∀ xs m Q X, sp xs m Q X → m7BveAllEnv nm as bs xs m Q X :=
  m7_closed_row m7BveAllEnv_callees k hk

/-- Unconditional `full_k6_solve_m7` row implementation under `m7BveAllEnv`. -/
theorem m7_k6_solve_impl :
    SpecEntry.Impl m7BveAllEnv
      ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], full_k6_solve_m7_body⟩
      ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], fullK6SolveM7Spec, true⟩ :=
  SpecEntry.Impl.of (full_k6_solve_m7_wp m7BveAllEnv
    (m7_row 25 rfl) (m7_row 22 rfl) (m7_row 24 rfl) (m7_row 27 rfl))

/-- Unconditional `full_bve_def_k6_m7` row implementation under `m7BveAllEnv`. -/
theorem m7_bve_def_k6_impl :
    SpecEntry.Impl m7BveAllEnv
      ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], full_bve_def_k6_m7_body⟩
      ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_def_k6_m7_wp m7BveAllEnv
    (m7_row 21 rfl) (m7_row 28 rfl) (m7_row 29 rfl))

/-- Unconditional `full_bve_gates_m7` row implementation under `m7BveAllEnv`. -/
theorem m7_bve_gates_impl :
    SpecEntry.Impl m7BveAllEnv
      ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], full_bve_gates_m7_body⟩
      ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩ :=
  SpecEntry.Impl.of (full_bve_gates_m7_wp m7BveAllEnv
    (m7_row 13 rfl) (m7_row 14 rfl) (m7_row 18 rfl) (m7_row 20 rfl) (m7_row 30 rfl))

/-- Unconditional `full_bve_var_m7` row implementation under `m7BveAllEnv`. -/
theorem m7_bve_var_impl :
    SpecEntry.Impl m7BveAllEnv
      ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩
      ⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_var_m7_wp m7BveAllEnv
    (m7_row 9 rfl) (m7_row 58 rfl) (m7_row 55 rfl) (m7_row 50 rfl) (m7_row 31 rfl)
    (m7_row 54 rfl) (m7_row 44 rfl) (m7_row 57 rfl) (m7_row 1 rfl) (m7_row 56 rfl)
    (m7_row 51 rfl) (m7_row 49 rfl) (m7_row 52 rfl))

/-- Unconditional `full_elim_bve_m7` row implementation under `m7BveAllEnv`. -/
theorem m7_elim_bve_impl :
    SpecEntry.Impl m7BveAllEnv
      ⟨"full_elim_bve_m7", [i64, i64], [i64], full_elim_bve_m7_body⟩
      ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :=
  SpecEntry.Impl.of (full_elim_bve_m7_wp m7BveAllEnv
    (m7_row 1 rfl) (m7_row 37 rfl) (m7_row 38 rfl) (m7_row 39 rfl) (m7_row 32 rfl))

/-- Unconditional `full_eliminate_m7` row implementation under `m7BveAllEnv`. -/
theorem m7_eliminate_impl :
    SpecEntry.Impl m7BveAllEnv
      ⟨"full_eliminate_m7", [i64, .bool], [i64], full_eliminate_m7_body⟩
      ⟨"full_eliminate_m7", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
  SpecEntry.Impl.of (full_eliminate_m7_wp m7BveAllEnv
    (m7_row 59 rfl) (m7_row 60 rfl) (m7_row 61 rfl) (m7_row 63 rfl) (m7_row 62 rfl)
    (m7_row 8 rfl) (m7_row 40 rfl) (m7_row 64 rfl) (m7_row 65 rfl))

/-- Canonical `FullFastSched.schedEliminateSpec` sparse-mode UNSAT soundness under
`m7BveAllEnv`. -/
theorem full_eliminate_m7_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {initial : Bool} {m : Mem 64}
    (hinv : FullSparseInv c F0 s) (hlvl : s.core.cur_level = 0) (hm : (FullMem c s ⋆ R) m) :
    Func.wp m7BveAllEnv full_eliminate_m7_body (c.hdr, initial, ()) m
      (fun (r, ()) m' => ∃ s',
        FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m7_eliminate_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, hlvl, hm, fun _ s' _ h1 h2 h3 h4 h5 hm' =>
      ⟨s', h1, h2, h3, h4, h5, hm'⟩⟩

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

private theorem nvM7_tmkZero : TmkZero FullM4Sweep.nvM4SweepState := fun v hv => by
  change v < 1 at hv
  obtain rfl : v = 0 := by omega
  decide

private theorem nvM7_scratch_drop_lt {k : Nat} (hk : k < 1208) :
    (FullM4Sweep.nvM4SweepState.scratch.scratch_buf.drop 1096)[k]?.getD 0#32 = 0#32 := by
  rw [List.getElem?_drop]
  change (FullM4Sweep.nvM4SweepScratchBuf[1096 + k]?).getD 0#32 = 0#32
  unfold FullM4Sweep.nvM4SweepScratchBuf
  rw [List.getElem?_append_left (by rw [List.length_replicate]; omega),
    List.getElem?_replicate]
  simp only [show 1096 + k < 2304 from by omega, ↓reduceIte, Option.getD_some]

private theorem nvM7_k6BufOk :
    K6BufOk (FullM4Sweep.nvM4SweepState.scratch.scratch_buf.drop 1096) := by
  have h15 : (FullM4Sweep.nvM4SweepState.scratch.scratch_buf.drop 1096)[15]?.getD 0#32 = 0#32 :=
    nvM7_scratch_drop_lt (by decide)
  have h1 : (FullM4Sweep.nvM4SweepState.scratch.scratch_buf.drop 1096)[1]?.getD 0#32 = 0#32 :=
    nvM7_scratch_drop_lt (by decide)
  have h14 : (FullM4Sweep.nvM4SweepState.scratch.scratch_buf.drop 1096)[14]?.getD 0#32 = 0#32 :=
    nvM7_scratch_drop_lt (by decide)
  have hlen : (FullM4Sweep.nvM4SweepState.scratch.scratch_buf.drop 1096).length = 23480 := by
    rw [List.length_drop, FullM4Sweep.nvM4SweepState_lengths.2.scratch_buf_len]
    rfl
  exact K6BufOk.mk_of (by rw [h15, hlen]; decide) (by rw [hlen]; decide) (by rw [h1]; decide)
    (by rw [h14, h15]; decide) fun cid hcid => by
      rw [h1, BitVec.toNat_zero] at hcid
      omega

private theorem nvM7_k6_solve_mem_split (c : FullCfg) (s : FullState) (m : Mem 64)
    (hsc_len : 1096 ≤ s.scratch.scratch_buf.length) (hm0 : FullMem c s m) :
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) (c.pScratchBuf + 1096#64 * 4#64) (s.scratch.scratch_buf.drop 1096) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 1096) ⋆ c.pad)) m := by
  have hsb : array (t := i32) c.pScratchBuf s.scratch.scratch_buf =
      (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 1096) ⋆
       array (t := i32) (c.pScratchBuf + 1096#64 * 4#64)
         (s.scratch.scratch_buf.drop 1096)) := by
    have ha := array_append (t := i32) c.pScratchBuf
      (s.scratch.scratch_buf.take 1096) (s.scratch.scratch_buf.drop 1096)
    rw [List.take_append_drop, List.length_take_of_le hsc_len,
      show BitVec.ofNat 64 (Ty.bytes i32 * 1096) = 1096#64 * 4#64 from rfl] at ha
    exact ha
  unfold FullMem FullScratchArrays FullScrDynArrs at hm0
  rw [hsb] at hm0
  exact sep_ac hm0

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_k6_solve_m7` under `m7BveAllEnv`. -/
theorem nv_m7_k6_solve :
    Func.wp m7BveAllEnv full_k6_solve_m7_body
      (FullM4Sweep.nvM4SweepCfg.hdr, FullM4Sweep.nvM4SweepCfg.pScratchBuf + 1096#64 * 4#64,
        10#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (_, ()) m' => ∃ (hdr' : List (BitVec 64)) (kbuf' : List (BitVec 32)),
        K6BufOk kbuf' ∧ nvOneLitF0.Unsat ∧
        ∃ R', (array64 (FullM4Sweep.nvM4SweepCfg.hdr + 32) hdr' ⋆
          array (t := i32) (FullM4Sweep.nvM4SweepCfg.pScratchBuf + 1096#64 * 4#64) kbuf' ⋆ R') m')
      (fun _ _ _ _ => False) := by
  let c := FullM4Sweep.nvM4SweepCfg
  let s := FullM4Sweep.nvM4SweepState
  have hsc_len : 1096 ≤ s.scratch.scratch_buf.length := by
    rw [FullM4Sweep.nvM4SweepState_lengths.2.scratch_buf_len]
    decide
  have hm :=
    nvM7_k6_solve_mem_split c s FullM4Sweep.nvM4SweepMem hsc_len FullM4Sweep.nvM4SweepMem_ok
  exact m7_k6_solve_impl.2 _ _ _ _
    (fullK6SolveM7Spec_intro (Full.hdrTailWords_length c s) nvM7_k6BufOk hm
      fun _ fuel' kb' m' _ hok' _ _ _ _ _ hm' =>
        ⟨(Full.hdrTailWords c s).set 17 fuel', kb', hok', FullM4Sweep.nvM4SweepF0_unsat, _, hm'⟩)

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_bve_def_k6_m7` under `m7BveAllEnv`. -/
theorem nv_m7_bve_def_k6 :
    Func.wp m7BveAllEnv full_bve_def_k6_m7_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 0#32, 0#32, ()) FullM4Sweep.nvM4SweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m7_bve_def_k6_impl.2 _ _ _ _
    (fullBveGatesM7Spec_intro rfl FullM4Sweep.nvM4Sweep_invW nvM7_tmkZero
      (by decide) (by decide) (by decide) (by decide)
      (fun i hi => by change i < 0 at hi; omega)
      (fun j hj => by change j < 0 at hj; omega) hm
      fun s' _ hdw htm _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdw, htm, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩)

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_bve_gates_m7` under `m7BveAllEnv`. -/
theorem nv_m7_bve_gates :
    Func.wp m7BveAllEnv full_bve_gates_m7_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 0#32, 0#32, ()) FullM4Sweep.nvM4SweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m7_bve_gates_impl.2 _ _ _ _
    (fullBveGatesM7Spec_intro rfl FullM4Sweep.nvM4Sweep_invW nvM7_tmkZero
      (by decide) (by decide) (by decide) (by decide)
      (fun i hi => by change i < 0 at hi; omega)
      (fun j hj => by change j < 0 at hj; omega) hm
      fun s' _ hdw htm _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hdw, htm, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩)

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_bve_var_m7` under `m7BveAllEnv`. -/
theorem nv_m7_bve_var :
    Func.wp m7BveAllEnv full_bve_var_m7_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m7_bve_var_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepState, emp, rfl,
     FullM4Sweep.nvM4Sweep_invW.toDense, nvM7_tmkZero, by decide, hm,
     fun _ s' _ hd htm _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, htm, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Headline concrete `100060`-byte `Mem 64` sparse-mode UNSAT non-vacuity (`XPost := False`,
`0` SAT proofs) for `full_eliminate_m7` under `m7BveAllEnv`. -/
theorem nv_m7_eliminate :
    Func.wp m7BveAllEnv full_eliminate_m7_body (FullM4Sweep.nvM4SweepCfg.hdr, true, ())
      FullM4Sweep.nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepSparseState ⋆ emp)
      FullM4Sweep.nvM4SweepSparseMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepSparseMem_ok
  exact m7_eliminate_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepSparseState, emp, rfl,
     FullM4Sweep.nvM4SweepSparse_inv, rfl, hm,
     fun _ s' _ hsp hlvl _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hsp, hlvl, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM7BveGates

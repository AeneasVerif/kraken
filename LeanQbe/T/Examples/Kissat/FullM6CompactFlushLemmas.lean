module

public import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
public import LeanQbe.T.Examples.Kissat.FullM4CompactProof

/-!
# Kissat M6 Compact, Root Trail Flush & Binary Dedup Closed `ModuleOk` & Non-Vacuity

Top-level umbrella proof module for `FullM6CompactFlush` (compaction, root trail flush,
and binary deduplication):
1. Publicly re-exports `FullM6CompactFlush`, `FullM6CompactFlushProof1`, and
   `FullM6CompactFlushProof2` (all `8` parametric `Func.wp` proofs + `TmkZero` variants).
2. Closes the `15`-row `m6CompactFlushSpecTable` (`8` owned functions + `7` external callees,
   all `noExit = true`), `m6CompactFlushEnv`, and `m6CompactFlush_moduleOk`.
3. Proves concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) on
   `nvCompactMem` (`1972`-byte concrete `Mem 64` image with `cur_vars = 2, unassigned = 1`,
   `nvCompactF0.Unsat`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM6CompactFlush

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4Compact
open Kraken.Bedrock2.Test

/-! ## 1. Closed `15`-Row `m6CompactFlushSpecTable`, `m6CompactFlushEnv`, and `ModuleOk` -/

/-- Closed `15`-row specification table for `m6CompactFlushModule` (`8` owned M6 compact/flush/dedup
functions + `7` canonical external callees, all `noExit = true`). -/
@[expose] public def m6CompactFlushSpecTable : List SpecEntry :=
  [ ⟨"full_flush_trail", [i64], [i64], fullFlushTrailSpec, true⟩
  , ⟨"full_sweep_bins_m6cf", [i64], [], fullSweepBinsSpec, true⟩
  , ⟨"full_enter_dense_m6cf", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_compact_needed_m6cf", [i64], [.bool], fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact_flush_m6cf", [i64], [i64], fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live_m6cf", [i64], [], fullCompactMarkLiveSpec, true⟩
  , ⟨"full_extend_push2_m6cf", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  , ⟨"full_extend_push_cl_m6cf", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩ ]

public theorem m6CompactFlushSpecTable_nodup :
    (m6CompactFlushSpecTable.map SpecEntry.name).Nodup := by
  decide

public theorem m6CompactFlushSpecTable_noExit :
    ∀ e ∈ m6CompactFlushSpecTable, e.noExit = true := by
  intro e he
  simp only [m6CompactFlushSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

/-- Closed environment for `m6CompactFlushModule`. -/
@[expose] public def m6CompactFlushEnv : Env := Env.ofTable m6CompactFlushSpecTable

public theorem m6CompactFlushEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6CompactFlushEnv f as bs xs m Q X → m6CompactFlushEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6CompactFlushSpecTable_noExit

private theorem m6cfEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m6CompactFlushSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m6CompactFlushEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m6CompactFlushSpecTable_nodup
      (hno xs m Q X hs)

public theorem m6cf_flush_trail_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_flush_trail", [i64], [i64], full_flush_trail_body⟩
      ⟨"full_flush_trail", [i64], [i64], fullFlushTrailSpec, true⟩ :=
  SpecEntry.Impl.of (full_flush_trail_wp m6CompactFlushEnv
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6cf_sweep_bins_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_sweep_bins_m6cf", [i64], [], full_sweep_bins_m6cf_body⟩
      ⟨"full_sweep_bins_m6cf", [i64], [], fullSweepBinsSpec, true⟩ :=
  SpecEntry.Impl.of (full_sweep_bins_m6cf_wp m6CompactFlushEnv
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6cf_enter_dense_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_enter_dense_m6cf", [i64], [.bool], full_enter_dense_m6cf_body⟩
      ⟨"full_enter_dense_m6cf", [i64], [.bool], schedEnterDenseSpec, true⟩ :=
  SpecEntry.Impl.of (full_enter_dense_m6cf_wp m6CompactFlushEnv
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6cf_compact_needed_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_compact_needed_m6cf", [i64], [.bool], full_compact_needed_m6cf_body⟩
      ⟨"full_compact_needed_m6cf", [i64], [.bool], fullCompactNeededM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_compact_needed_m6cf_wp m6CompactFlushEnv)

public theorem m6cf_compact_flush_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_compact_flush_m6cf", [i64], [i64], full_compact_flush_m6cf_body⟩
      ⟨"full_compact_flush_m6cf", [i64], [i64], fullCompactFlushSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_flush_m6cf_wp m6CompactFlushEnv
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h))
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6cf_compact_mark_live_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_compact_mark_live_m6cf", [i64], [], full_compact_mark_live_m6cf_body⟩
      ⟨"full_compact_mark_live_m6cf", [i64], [], fullCompactMarkLiveSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_mark_live_m6cf_wp m6CompactFlushEnv
    (m6cfEnv_row (by simp [m6CompactFlushSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6cf_extend_push2_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_extend_push2_m6cf", [i64, i32, i32], [.bool], full_extend_push2_m6cf_body⟩
      ⟨"full_extend_push2_m6cf", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩ :=
  SpecEntry.Impl.of (full_extend_push2_m6cf_wp m6CompactFlushEnv)

public theorem m6cf_extend_push_cl_impl :
    SpecEntry.Impl m6CompactFlushEnv
      ⟨"full_extend_push_cl_m6cf", [i64, i32, i32], [.bool], full_extend_push_cl_m6cf_body⟩
      ⟨"full_extend_push_cl_m6cf", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩ :=
  SpecEntry.Impl.of (full_extend_push_cl_m6cf_wp m6CompactFlushEnv)

public theorem m6CompactFlush_allFns_wf : AllFns Fn.Wf m6CompactFlushModule.fns :=
  ⟨full_flush_trail_wf, full_sweep_bins_m6cf_wf, full_enter_dense_m6cf_wf,
    full_compact_needed_m6cf_wf, full_compact_flush_m6cf_wf, full_compact_mark_live_m6cf_wf,
    full_extend_push2_m6cf_wf, full_extend_push_cl_m6cf_wf, trivial⟩

public theorem m6CompactFlush_tableImpl :
    TableImpl m6CompactFlushEnv m6CompactFlushModule.fns m6CompactFlushSpecTable :=
  ⟨m6cf_flush_trail_impl, m6cf_sweep_bins_impl, m6cf_enter_dense_impl,
    m6cf_compact_needed_impl, m6cf_compact_flush_impl, m6cf_compact_mark_live_impl,
    m6cf_extend_push2_impl, m6cf_extend_push_cl_impl, trivial⟩

/-- Headline closed `ModuleOk` certifying all `8` M6 compact/flush/dedup functions in
`m6CompactFlushModule` under `m6CompactFlushEnv` (`0` gaps, `0` SAT proofs). -/
public theorem m6CompactFlush_moduleOk : ModuleOk m6CompactFlushEnv m6CompactFlushModule :=
  Env.ofTable_moduleOk m6CompactFlush_acyclic m6CompactFlush_allFns_wf m6CompactFlush_tableImpl

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNonVacuity

private theorem nvCompactMem_sep : (FullMem nvCompactCfg nvCompactState ⋆ emp) nvCompactMem := by
  rw [sep_emp]; exact nvCompactMem_ok

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_flush_trail`. -/
public theorem nv_m6cf_flush_trail :
    Func.wp m6CompactFlushEnv full_flush_trail_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvCompactF0.Unsat) ∧ nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  m6cf_flush_trail_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactF0, nvCompactState, emp, rfl, nvCompact_sparse, nvCompactMem_sep,
      fun r s' m' hsp hr _ _ _ h20 _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, h20, nvCompactF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_sweep_bins_m6cf`. -/
public theorem nv_m6cf_sweep_bins :
    Func.wp m6CompactFlushEnv full_sweep_bins_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun () m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ nvCompactF0.Unsat ∧
        FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) := by
  obtain ⟨F_cur, hspw⟩ := nvCompact_sparse.exists_witness
  exact m6cf_sweep_bins_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactF0, F_cur, nvCompactState, emp, rfl, hspw.1, hspw.2.1,
      nvCompactMem_sep, fun wvec' wstk' wlen' nb' wsort' m' hlen' _ _ hw' hm' => by
        rw [sep_emp] at hm'
        let s' : FullState :=
          { nvCompactState with
            core := { nvCompactState.core with
              wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64, num_binary := nb' }
            scratch := { nvCompactState.scratch with wsort := wsort' } }
        have hsp' : FullSparseInv nvCompactCfg nvCompactF0 s' :=
          ⟨⟨hlen', F_cur, hw'⟩, hspw.2.2.1, hspw.2.2.2.1, hspw.2.2.2.2.1, hspw.2.2.2.2.2⟩
        exact ⟨s', hsp', nvCompactF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_enter_dense_m6cf`. -/
public theorem nv_m6cf_enter_dense :
    Func.wp m6CompactFlushEnv full_enter_dense_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (ok, ()) m' => ∃ s',
        (if ok then FullDenseInv nvCompactCfg nvCompactF0 s'
         else FullSparseInv nvCompactCfg nvCompactF0 s') ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  m6cf_enter_dense_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactF0, nvCompactState, emp, rfl, nvCompact_sparse, nvCompactMem_sep,
      fun ok s' m' _ _ hd hf hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', by cases ok <;> simp [hd, hf], nvCompactF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_needed_m6cf`. -/
public theorem nv_m6cf_compact_needed :
    Func.wp m6CompactFlushEnv full_compact_needed_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (res, ()) m' =>
        (res = true → nvCompactState.core.cur_vars <
          10 * (nvCompactState.core.cur_vars - nvCompactState.core.unassigned.toNat)) ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg nvCompactState m')
      (fun _ _ _ _ => False) :=
  m6cf_compact_needed_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactState, emp, rfl, nvCompact_lengths, by decide, nvCompactMem_sep,
      fun res hres => ⟨fun ht => (hres ht).2.2.2.2, nvCompactF0_unsat, nvCompactMem_ok⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_flush_m6cf`. -/
public theorem nv_m6cf_compact_flush :
    Func.wp m6CompactFlushEnv full_compact_flush_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvCompactF0.Unsat) ∧ nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  m6cf_compact_flush_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactF0, nvCompactState, emp, rfl, nvCompact_sparse, nvCompactMem_sep,
      fun r s' m' hsp hr _ _ h20 _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, h20, nvCompactF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_mark_live_m6cf`. -/
public theorem nv_m6cf_compact_mark_live :
    Func.wp m6CompactFlushEnv full_compact_mark_live_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun () m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ nvCompactF0.Unsat ∧
        FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) := by
  obtain ⟨F_cur, hspw⟩ := nvCompact_sparse.exists_witness
  exact m6cf_compact_mark_live_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactF0, F_cur, nvCompactState, emp, rfl, hspw, nvCompactMem_sep,
      fun ws1' m' hspw' hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hspw'.toSparse, nvCompactF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_extend_push2_m6cf`. -/
public theorem nv_m6cf_extend_push2 :
    Func.wp m6CompactFlushEnv full_extend_push2_m6cf_body
      (nvCompactCfg.hdr, 0#32, 1#32, ()) nvCompactMem
      (fun (_, ()) m' => ∃ s',
        s'.core = nvCompactState.core ∧ s'.LengthsOk nvCompactCfg ∧
        s'.scratch.extend_len ≤ nvCompactCfg.extend_cap ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  m6cf_extend_push2_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactState, emp, ⟨rfl, Nat.le_refl 0⟩, nvCompact_lengths, nvCompactMem_sep,
      fun _ s' m' hcore hlen' ⟨_, hel', _⟩ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hcore, hlen', hel', nvCompactF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_extend_push_cl_m6cf`. -/
public theorem nv_m6cf_extend_push_cl :
    Func.wp m6CompactFlushEnv full_extend_push_cl_m6cf_body
      (nvCompactCfg.hdr, 0#32, 0#32, ()) nvCompactMem
      (fun (_, ()) m' => ∃ s',
        s'.core = nvCompactState.core ∧ s'.LengthsOk nvCompactCfg ∧
        s'.scratch.extend_len ≤ nvCompactCfg.extend_cap ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  m6cf_extend_push_cl_impl.2 _ _ _ _
    ⟨nvCompactCfg, nvCompactState, emp, ⟨rfl, Nat.le_refl 0⟩, nvCompact_lengths, nvCompactMem_sep,
      fun _ s' m' hcore hlen' ⟨_, hel', _⟩ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hcore, hlen', hel', nvCompactF0_unsat, hm'⟩⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6CompactFlush

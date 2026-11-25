/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof3
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityBcpProof3
import all LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import all LeanQbe.T.Examples.Kissat.FullM6OrchProof0
import all LeanQbe.T.Examples.Kissat.FullM7SearchProof0
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Delayed-Watch BCP & Hot-Loop Caching — Closed `ModuleOk`, `PatchBundle`, & NV
(`FullFidelityBcpProof`)

Plain `public section` (`0` `@[expose]`, `0` `public import all`, `std3` axioms only; private
`import all` solely for upstream unexposed spec/base-table definitions):
1. Closed standalone `22`-row `fidBcpSpecTable`, `fidBcpEnv`, `fidBcpEnv_noExit`,
   `fidBcp_tableImpl`, and `fidBcp_moduleOk : ModuleOk fidBcpEnv fidBcpModule` covering all
   `8` functions + `14` externs of `FullFidelityBcp`.
2. Closed `PatchModule.PatchBundle` (`fidBcpHotPushBundle`, `fidBcpHotPushMod`,
   `fidBcpHotPushEnv`) combining `FullM7BcpHot` + `FullM7HotWatchPush` + `FullFidelityBcp`
   (`full_bcp_hot` rewired to `FullM6BcpS15.fullBcpS15Spec`), proved via
   `PatchModule.patchBundle_moduleOk` (`fidBcpHotPush_moduleOk`, `fidBcpHotPush_acyclic`,
   `fidBcpHotPush_noExit`), UNSAT soundness (`fid_bcp_hot_unsat_sound`), and `MemShrinkV5`
   / `HotWatchPush` framing reuse (`fidBcpHotPushMem_*`, `fid_m7ms_m6_mem_init_4k`).
3. Concrete `Mem 64` `XPost := False` non-vacuity inside closed `fidBcpHotPushEnv`:
   - `nv_fid_bcp_hot` (`FastCore.nvFastPropMem` → `Full.nvOneLitF0.Unsat`)
   - `nv_fid_bcp_delayed` (`delayed_cap = 1`, `nvDelayedMem` → `nvDelayedF0.Unsat`)
   - `nv_fid_flush_del` (`delayed_cap = 1`, `di = 3`, live `full_prop_flush_del_fid` NV)
   - `nv_fid_bcp_hotpush_watch_push` (live `m7WatchPushFastFn` inside `fidBcpHotPushEnv`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
open LeanQbe.T.Examples.Kissat.FullM7MemShrink
open LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. Closed Standalone `22`-Row `fidBcpEnv`, `TableImpl`, & `ModuleOk` -/

/-- Closed `22`-row specification table for `fidBcpModule` (`8` functions + `14` externs). -/
def fidBcpSpecTable : List SpecEntry :=
  [ ⟨"full_heap_down_fid", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_heap_pop_fid", [i64], [i64], Full.fullHeapPopSpec, true⟩
  , ⟨"full_prop_flush_del_fid", [i64, i64], [.bool], fidPropFlushDelSpec, true⟩
  , ⟨"full_propagate_ignore_fid", [i64, i64], [i64],
      FullM6BcpS15.fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_deduce_1uip_fid", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_deduce_1uip_hdr_fid", [i64], [i64], FullM6Orch.m6Deduce1uipHdrSpec, true⟩
  , ⟨"full_next_dec_var_fid", [i64], [i64], Full.fullNextDecVarSpec, true⟩
  , ⟨"m6_hdr_decide_fid_fast", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool], FullM7BcpHot.fullPropChronoHotSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], FullM6Orch.m6AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩
  , ⟨"full_decide_m7", [i64], [i64], FullM7Search.m7DecideSpec, true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩ ]

/-- Closed specification environment for `fidBcpModule`. -/
def fidBcpEnv : Env := Env.ofTable fidBcpSpecTable

theorem fidBcpSpecTable_length : fidBcpSpecTable.length = 22 := by
  simp only [fidBcpSpecTable, List.length_cons, List.length_nil]

theorem fidBcpSpecTable_noExit : ∀ e ∈ fidBcpSpecTable, e.noExit = true := by
  intro e he
  simp only [fidBcpSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fidBcpEnv_noExit :
    ∀ f as bs xs m Q X X', fidBcpEnv f as bs xs m Q X → fidBcpEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fidBcpSpecTable_noExit

theorem fidBcpSpecTable_nodup : (fidBcpSpecTable.map SpecEntry.name).Nodup := by
  show (["full_heap_down_fid", "full_heap_pop_fid", "full_prop_flush_del_fid",
    "full_propagate_ignore_fid", "full_deduce_1uip_fid", "full_deduce_1uip_hdr_fid",
    "full_next_dec_var_fid", "m6_hdr_decide_fid_fast", "full_watch_push", "full_heap_down",
    "full_heap_pop", "full_prop_lit_ovf_hot", "full_prop_chrono_hot", "full_analyze_lit",
    "full_analyze_rsn", "full_analyze_rsn_m6_hdr", "full_clear_ana", "full_otfs_large",
    "full_otfs_bin", "full_otfs_subsume", "full_decide_m7", "m6_hdr_dr_init"] :
    List String).Nodup
  decide

private theorem fidBcpEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : fidBcpSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → fidBcpEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) fidBcpSpecTable_nodup (hno xs m Q X h)

private theorem fidBcp_allFns_wf : AllFns Fn.Wf fidBcpModule.fns :=
  ⟨full_heap_down_fid_wf, full_heap_pop_fid_wf, full_prop_flush_del_fid_wf,
    full_propagate_ignore_fid_wf, full_deduce_1uip_fid_wf, full_deduce_1uip_hdr_fid_wf,
    full_next_dec_var_fid_wf, m6_hdr_decide_fid_fast_wf, trivial⟩

/-- Row-by-row `TableImpl` certifying all `8` functions in `fidBcp_fns` under `fidBcpEnv`. -/
theorem fidBcp_tableImpl :
    TableImpl fidBcpEnv fidBcp_fns fidBcpSpecTable := by
  let hFlush := fidBcpEnv_row_at 2
    ⟨"full_prop_flush_del_fid", [i64, i64], [.bool], fidPropFlushDelSpec, true⟩
  let hPush := fidBcpEnv_row_at 8
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hDown := fidBcpEnv_row_at 9
    ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  let hPop := fidBcpEnv_row_at 10
    ⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩
  let hOvf := fidBcpEnv_row_at 11
    ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  let hChrono := fidBcpEnv_row_at 12
    ⟨"full_prop_chrono_hot", [i64, i64], [.bool], FullM7BcpHot.fullPropChronoHotSpec, true⟩
  let hAlit := fidBcpEnv_row_at 13
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩
  let hArsn := fidBcpEnv_row_at 14
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  let hArsnHdr := fidBcpEnv_row_at 15
    ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], FullM6Orch.m6AnalyzeRsnHdrSpec, true⟩
  let hClear := fidBcpEnv_row_at 16
    ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩
  let hOLarge := fidBcpEnv_row_at 17
    ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  let hOBin := fidBcpEnv_row_at 18
    ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  let hOSub := fidBcpEnv_row_at 19
    ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩
  let hDec := fidBcpEnv_row_at 20
    ⟨"full_decide_m7", [i64], [i64], FullM7Search.m7DecideSpec, true⟩
  let hDr := fidBcpEnv_row_at 21
    ⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩
  exact ⟨.of (full_heap_down_fid_wp fidBcpEnv),
    ⟨.of (full_heap_pop_fid_wp fidBcpEnv hDown),
    ⟨.of (full_prop_flush_del_fid_wp fidBcpEnv hPush),
    ⟨.of (full_propagate_ignore_fid_wp fidBcpEnv hOvf hChrono hFlush),
    ⟨.of (full_deduce_1uip_fid_wp fidBcpEnv hAlit hArsn hClear hOLarge hOBin hOSub),
    ⟨.of (full_deduce_1uip_hdr_fid_wp fidBcpEnv hAlit hArsnHdr hClear hOLarge hOBin hOSub),
    ⟨.of (full_next_dec_var_fid_wp fidBcpEnv hPop),
    ⟨.of (m6_hdr_decide_fid_fast_wp fidBcpEnv hDec hDr), trivial⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed unconditional `ModuleOk` certifying `fidBcpModule` (`8` fns + `14` externs). -/
theorem fidBcp_moduleOk : ModuleOk fidBcpEnv fidBcpModule :=
  Env.ofTable_moduleOk fidBcp_acyclic fidBcp_allFns_wf fidBcp_tableImpl

/-! ## 2. Closed Composed `PatchBundle` (`FullM7BcpHot` + `HotWatchPush` + Delayed BCP) -/

/-- Closed `PatchModule.PatchBundle` composing `FullM7HotWatchPush` (`m7WatchPushFastFn` +
`m7WatchPushSlowFn`) and `FullFidelityBcp` (`fidPropFlushDelFn` + `fidPropagateIgnoreHotFn`)
onto the BCP-level flat base `fidBcpHotPushBaseMod`, rewiring `full_bcp_hot` to `fullBcpS15Spec`. -/
def fidBcpHotPushBundle : PatchBundle where
  baseMod := fidBcpHotPushBaseMod
  baseTable := fidBcpHotPushBaseSpecTable
  baseOk := fidBcpHotPushBase_moduleOk
  repls := [FullM7HotWatchPush.m7WatchPushFastFn, fidPropagateIgnoreHotFn]
  replRows :=
    [ ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
    , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
        FullM6BcpS15.fullPropagateIgnoreS15Spec, true⟩ ]
  befores := fidBcpHotPushBefores
  beforeRows :=
    [ ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool],
        Full.fullWatchPushSpec, true⟩
    , ⟨"full_prop_flush_del_fid", [i64, i64], [.bool], fidPropFlushDelSpec, true⟩ ]
  rewiredRows :=
    [ ⟨"full_bcp_hot", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩ ]

/-- Closed `8`-fn patched module produced by `fidBcpHotPushBundle` (`3` externs, `0` exits). -/
def fidBcpHotPushMod : LeanQbe.T.Module := fidBcpHotPushBundle.patchedMod

/-- Closed specification environment `patchEnv fidBcpHotPushBundle`. -/
def fidBcpHotPushEnv : Env := patchEnv fidBcpHotPushBundle

theorem fidBcpHotPush_acyclic : fidBcpHotPushMod.checkAcyclic = true := by
  t_kernel_rfl

theorem fidBcpHotPush_namesNodup : fidBcpHotPushMod.namesNodup := by
  have hf :
      fidBcpHotPushMod.fns.map Fn.name ++ fidBcpHotPushMod.externs.map Extern.name =
        ["full_watch_push_slow_m6", "full_watch_push_m6", "full_watch_push",
          "full_prop_lit_ovf_hot", "full_prop_chrono_hot", "full_prop_flush_del_fid",
          "full_propagate_ignore_hot", "full_bcp_hot", "full_wstack_defrag_m6",
          "full_wstack_defrag", "full_unwatch_large"] := by
    t_kernel_rfl
  unfold LeanQbe.T.Module.namesNodup LeanQbe.T.Module.names
  rw [hf]
  decide

theorem fidBcpHotPush_noExit :
    ∀ f as bs xs m Q X X',
      fidBcpHotPushEnv f as bs xs m Q X → fidBcpHotPushEnv f as bs xs m Q X' := by
  refine Env.ofTable_noExit fun e he => ?_
  simp only [fidBcpHotPushBundle, PatchBundle.frontTable, fidBcpHotPushBaseSpecTable,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

-- `frontTable` = `rewiredRows ++ replRows ++ beforeRows`:
-- [0] full_bcp_hot, [1] full_watch_push_m6, [2] full_propagate_ignore_hot,
-- [3] full_watch_push_slow_m6, [4] full_prop_flush_del_fid
private theorem hpEnv_front0 {xs m Q X} (h : FullM6BcpS15.fullBcpS15Spec xs m Q X) :
    fidBcpHotPushEnv "full_bcp_hot" [i64] [i64] xs m Q X :=
  Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩

private theorem hpEnv_front1 {xs m Q X} (h : Full.fullWatchPushSpec xs m Q X) :
    fidBcpHotPushEnv "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] xs m Q X :=
  Or.inr ⟨by decide, Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩

private theorem hpEnv_front2 {xs m Q X} (h : FullM6BcpS15.fullPropagateIgnoreS15Spec xs m Q X) :
    fidBcpHotPushEnv "full_propagate_ignore_hot" [i64, i64] [i64] xs m Q X :=
  Or.inr ⟨by decide, Or.inr ⟨by decide, Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩⟩

private theorem hpEnv_front3 {xs m Q X} (h : Full.fullWatchPushSpec xs m Q X) :
    fidBcpHotPushEnv "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] xs m Q X :=
  Or.inr ⟨by decide, Or.inr ⟨by decide, Or.inr ⟨by decide, Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩⟩⟩

private theorem hpEnv_front4 {xs m Q X} (h : fidPropFlushDelSpec xs m Q X) :
    fidBcpHotPushEnv "full_prop_flush_del_fid" [i64, i64] [.bool] xs m Q X :=
  Or.inr ⟨by decide, Or.inr ⟨by decide, Or.inr ⟨by decide,
    Or.inr ⟨by decide, Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩⟩⟩⟩

private theorem hpEnv_base_of_none {f : Sym} {as rs : List Ty}
    (hf : fidBcpHotPushBundle.frontTable.find? (·.name == f) = none)
    {xs m Q X} (h : Env.ofTable fidBcpHotPushBaseSpecTable f as rs xs m Q X) :
    fidBcpHotPushEnv f as rs xs m Q X := by
  change patchEnv fidBcpHotPushBundle f as rs xs m Q X
  rw [patchEnv_base_eq fidBcpHotPushBundle hf]
  exact h

private theorem hpEnv_watchPush {xs m Q X} (h : Full.fullWatchPushSpec xs m Q X) :
    fidBcpHotPushEnv "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X :=
  hpEnv_base_of_none rfl
    (Env.ofTable_of_mem (e := ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩) (by simp [fidBcpHotPushBaseSpecTable])
      fidBcpHotPushBaseSpecTable_nodup h)

private theorem hpEnv_defragM6 {xs m Q X} (h : Full.fullWstackDefragSpec xs m Q X) :
    fidBcpHotPushEnv "full_wstack_defrag_m6" [i64] [] xs m Q X :=
  hpEnv_base_of_none rfl
    (Env.ofTable_of_mem (e := ⟨"full_wstack_defrag_m6", [i64], [],
      Full.fullWstackDefragSpec, true⟩) (by simp [fidBcpHotPushBaseSpecTable])
      fidBcpHotPushBaseSpecTable_nodup h)

private theorem hpEnv_ovfHot {xs m Q X} (h : FullM7BcpHot.fullPropLitOvfHotSpec xs m Q X) :
    fidBcpHotPushEnv "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] xs m Q X :=
  hpEnv_base_of_none rfl
    (Env.ofTable_of_mem (e := ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩) (by simp [fidBcpHotPushBaseSpecTable])
      fidBcpHotPushBaseSpecTable_nodup h)

private theorem hpEnv_chronoHot {xs m Q X} (h : FullM7BcpHot.fullPropChronoHotSpec xs m Q X) :
    fidBcpHotPushEnv "full_prop_chrono_hot" [i64, i64] [.bool] xs m Q X :=
  hpEnv_base_of_none rfl
    (Env.ofTable_of_mem (e := ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
      FullM7BcpHot.fullPropChronoHotSpec, true⟩) (by simp [fidBcpHotPushBaseSpecTable])
      fidBcpHotPushBaseSpecTable_nodup h)

/-- Closed `ModuleOk` certifying the composed `FullM7BcpHot + FullM7HotWatchPush +
FullFidelityBcp` bundle under `patchEnv fidBcpHotPushBundle`
(`PatchModule.patchBundle_moduleOk`). -/
theorem fidBcpHotPush_moduleOk : ModuleOk fidBcpHotPushEnv fidBcpHotPushMod := by
  refine patchBundle_moduleOk fidBcpHotPushBundle fidBcpHotPush_namesNodup
    (by decide)
    (fun fn h => by
      simp only [fidBcpHotPushBundle, fidBcpHotPushBefores, m7HotWatchPushBefore, fidBcpBefores,
        List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (rfl | rfl) | (rfl | rfl)
      · exact FullM7HotWatchPush.m7WatchPushFastFn_wf
      · exact full_propagate_ignore_fid_wf
      · exact FullM7HotWatchPush.m7WatchPushSlowFn_wf
      · exact full_prop_flush_del_fid_wf)
    (by decide)
    (fun fn h => by
      simp only [fidBcpHotPushBundle, fidBcpHotPushBefores, m7HotWatchPushBefore, fidBcpBefores,
        List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (rfl | rfl) | (rfl | rfl) <;> decide)
    (fun fn e hmem hfind => by
      have hfm : fn.name = "full_bcp_hot" ∨ fn.name = "full_watch_push_m6" ∨
          fn.name = "full_propagate_ignore_hot" ∨ fn.name = "full_watch_push_slow_m6" ∨
          fn.name = "full_prop_flush_del_fid" := by
        have hm := List.mem_of_find?_eq_some hfind
        simp only [fidBcpHotPushBundle, PatchBundle.frontTable, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
        have hs := List.find?_some hfind
        simp only [beq_iff_eq] at hs
        have hnm : fn.name = e.name := hs.symm
        rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp [hnm]
      have hfns : fidBcpHotPushBundle.patchedMod.fns =
          [ m7WatchPushSlowFn, m7WatchPushFastFn, fidWatchPushWrapFn,
            ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
              FullM7BcpHot.full_prop_lit_ovf_hot_body⟩,
            ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
              FullM7BcpHot.full_prop_chrono_hot_body⟩,
            fidPropFlushDelFn, fidPropagateIgnoreHotFn,
            ⟨"full_bcp_hot", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩ ] := by t_kernel_rfl
      rw [hfns] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hfm with hnm | hnm | hnm | hnm | hnm
      · have hfn : fn = ⟨"full_bcp_hot", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩ := by
          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd hnm (by decide) | rfl
        have he : e = ⟨"full_bcp_hot", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩ := by
          simp only [hnm] at hfind; exact Option.some.inj hfind.symm
        rw [hfn, he]
        exact .of (full_bcp_hot_s15_wp fidBcpHotPushEnv (fun _ _ _ _ h => hpEnv_front2 h))
      · have hfn : fn = m7WatchPushFastFn := by
          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd hnm (by decide) | rfl
        have he : e = ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
            Full.fullWatchPushSpec, true⟩ := by
          simp only [hnm] at hfind; exact Option.some.inj hfind.symm
        rw [hfn, he]
        exact .of (m7WatchPushFastFn_wp fidBcpHotPushEnv (fun _ _ _ _ h => hpEnv_front3 h))
      · have hfn : fn = fidPropagateIgnoreHotFn := by
          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd hnm (by decide) | rfl
        have he : e = ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
            FullM6BcpS15.fullPropagateIgnoreS15Spec, true⟩ := by
          simp only [hnm] at hfind; exact Option.some.inj hfind.symm
        rw [hfn, he]
        exact .of (full_propagate_ignore_fid_wp fidBcpHotPushEnv
          (fun _ _ _ _ h => hpEnv_ovfHot h) (fun _ _ _ _ h => hpEnv_chronoHot h)
          (fun _ _ _ _ h => hpEnv_front4 h))
      · have hfn : fn = m7WatchPushSlowFn := by
          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd hnm (by decide) | rfl
        have he : e = ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool],
            Full.fullWatchPushSpec, true⟩ := by
          simp only [hnm] at hfind; exact Option.some.inj hfind.symm
        rw [hfn, he]
        exact .of (m7WatchPushSlowFn_wp fidBcpHotPushEnv (fun _ _ _ _ h => hpEnv_defragM6 h))
      · have hfn : fn = fidPropFlushDelFn := by
          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd hnm (by decide) | rfl
        have he : e = ⟨"full_prop_flush_del_fid", [i64, i64], [.bool],
            fidPropFlushDelSpec, true⟩ := by
          simp only [hnm] at hfind; exact Option.some.inj hfind.symm
        rw [hfn, he]
        exact .of (full_prop_flush_del_fid_wp fidBcpHotPushEnv
          (fun _ _ _ _ h => hpEnv_watchPush h)))
    ["full_watch_push_slow_m6", "full_prop_flush_del_fid", "full_propagate_ignore_hot",
      "full_bcp_hot"]
    (fun fn hmem hr hfind => by
      have hbfns : fidBcpHotPushBundle.baseMod.fns =
          [ m6WatchPushFn, fidWatchPushWrapFn,
            ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
              FullM7BcpHot.full_prop_lit_ovf_hot_body⟩,
            ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
              FullM7BcpHot.full_prop_chrono_hot_body⟩,
            ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
              FullM7BcpHot.full_propagate_ignore_hot_body⟩,
            ⟨"full_bcp_hot", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩ ] := by
        t_kernel_rfl
      rw [hbfns] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [fidBcpHotPushBundle, m6WatchPushFn, m7WatchPushFastFn] at hr
      · rfl
      · rfl
      · rfl
      · simp [fidBcpHotPushBundle, fidPropagateIgnoreHotFn] at hr
      · unfold fidBcpHotPushBundle PatchBundle.frontTable at hfind; simp at hfind)
    (fun s hs hnb xs m P E hbase => by
      by_cases hmw : s.1 = "full_watch_push_m6"
      · have hm_eq : s = ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool]) := by
          have hsigs : fidBcpHotPushBundle.baseMod.sigs =
              [ ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool]),
                ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]),
                ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]),
                ("full_prop_chrono_hot", [i64, i64], [.bool]),
                ("full_propagate_ignore_hot", [i64, i64], [i64]),
                ("full_bcp_hot", [i64], [i64]),
                ("full_wstack_defrag_m6", [i64], []),
                ("full_wstack_defrag", [i64], []),
                ("full_unwatch_large", [i64, i32, i32], []) ] := by t_kernel_rfl
          rw [hsigs] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | rfl | exact absurd hmw (by decide)
        rcases s with ⟨s1, s2, s3⟩
        obtain ⟨rfl, rfl, rfl⟩ := hm_eq
        have hsp : Full.fullWatchPushSpec xs m P (fun _ _ _ _ => False) := by
          dsimp only [fidBcpHotPushBundle, fidBcpHotPushBaseSpecTable] at hbase
          rcases hbase with ⟨_, hsp⟩ | ⟨hne, _⟩
          · exact hsp
          · exact absurd ⟨rfl, rfl, rfl⟩ hne
        exact hpEnv_front1 hsp
      · have hnone : fidBcpHotPushBundle.frontTable.find? (·.name == s.1) = none := by
          rw [List.find?_eq_none]
          intro e he
          simp only [fidBcpHotPushBundle, PatchBundle.frontTable, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [beq_iff_eq] <;>
            first | exact fun h => hmw h.symm | exact fun h => hnb (by simp [h])
        exact hpEnv_base_of_none hnone hbase)

/-- Closed `full_bcp_hot` WP inside `fidBcpHotPushEnv` (`fullBcpS15Spec`, `XPost := False`). -/
theorem fid_bcp_hot_bundle_wp :
    ∀ args m Q X, FullM6BcpS15.fullBcpS15Spec args m Q X →
      Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body args m Q X :=
  full_bcp_hot_s15_wp fidBcpHotPushEnv (fun _ _ _ _ h => hpEnv_front2 h)

/-- UNSAT soundness (`XPost := False`) for `full_bcp_hot` inside closed `fidBcpHotPushEnv`:
returning `r = 1#64` at decision level `0` establishes `F0.Unsat`. -/
theorem fid_bcp_hot_unsat_sound (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (m : Mem 64)
    (hlen0 : s.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hdense0 : s.core.dense_mode = 0#64) (hm0 : (FullMem c s ⋆ R) m) :
    Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body (c.hdr, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        ∃ s', s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
          (c.delayed_cap = 0 → s'.scratch.delayed = s.scratch.delayed) ∧
          (r = 1#64 → s'.core.cur_level = 0 → F0.Unsat) ∧
          (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) := by
  apply fid_bcp_hot_bundle_wp
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hw' _ _ hdel0 _ hr _ hr1 _ _ hm' => ?_⟩
  refine ⟨hr, _, hlen', hw', hdel0, fun h1 hl0 => ?_, hm'⟩
  exact hw'.level0_unsat_of_conflOkW hl0 (by
    rcases (hr1 h1).2.2 with ⟨ht, h0, h1', hf0, hf1, hent⟩ | hr
    · exact Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩
    · exact Or.inr hr)

/-! ## 3. `MemShrinkV5` Framing Reuse & Concrete `Mem 64` Non-Vacuities (`XPost := False`) -/

/-- All `21` composed replacement names (`FullM7MemShrinkV5` + `FullM7HotWatchPush` +
`FullFidelityBcp`) are mutually disjoint and ready for full-spine splicing. -/
theorem fidBcpHotPushMemRepls_names_nodup :
    (fidBcpHotPushMemRepls.map Fn.name).Nodup := by
  unfold fidBcpHotPushMemRepls fidBcpHotPushRepls fidBcpRepls
    FullM7HotWatchPush.m7HotWatchPushRepl FullM7MemShrinkV5.m7msRepls
  decide

/-- All `4` helper anchor target names (`m7msBefores ++ m7HotWatchPushBefore ++ fidBcpBefores`)
are mutually disjoint. -/
theorem fidBcpHotPushMemBefores_targets_nodup :
    (fidBcpHotPushMemBefores.map Prod.fst).Nodup := by
  unfold fidBcpHotPushMemBefores fidBcpHotPushBefores fidBcpBefores
    FullM7HotWatchPush.m7HotWatchPushBefore FullM7MemShrinkV5.m7msBefores
  decide

/-- Re-exported `FullM7MemShrinkV5` closed `ModuleOk` + `4K` `MemShrinkM6HdrMem` framing NV
(`XPost := False`) confirming clean prefix separation (`2,304 B` `M6HdrExt` + `4,096 B` core). -/
theorem fid_m7ms_m6_mem_init_4k :
    Func.wp m7msM6Env FullM6Hdr.full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length, 6400#64, 16#64, ())
      nvMs4kInitMem
      (fun (r, ()) m' => ∃ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState),
        r = c.hdr ∧ c.hdr = (0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length) +
          BitVec.ofNat 64 fullM6ExtBytes ∧
        c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧ nvMsUnsatCnf.Unsat ∧
        MsM6HdrExtInitOk ext ∧ MemShrinkM6HdrInv c ext s ∧
        (bytes 0x2000#64 nvMsUnsatBytes ⋆ MemShrinkM6HdrMem c ext s) m')
      (fun _ _ _ _ => False) :=
  nv_m7ms_m6_mem_init_4k

private theorem nv_oneLit_unsat : Full.nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [Full.nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [Full.nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `Mem 64` binary-watch UNSAT non-vacuity (`XPost := False`) for `full_bcp_hot`
inside the closed composed environment `fidBcpHotPushEnv` on `FastCore.nvFastPropMem`. -/
theorem nv_fid_bcp_hot :
    Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body (FastCore.nvFastPropCfg.hdr, ())
      FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧ Full.nvOneLitF0.Unsat ∧
        ∃ s', s'.LengthsOk FastCore.nvFastPropCfg ∧
          FullWitnessInv FastCore.nvFastPropCfg Full.nvOneLitF0 [[0], [1]] s'.core ∧
          s'.scratch.delayed = FastCore.nvFastPropState.scratch.delayed ∧
          FullMem FastCore.nvFastPropCfg s' m')
      (fun _ _ _ _ => False) := by
  apply fid_bcp_hot_bundle_wp
  refine ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], FastCore.nvFastPropState, emp,
    rfl, FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness, rfl,
    by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' _delayed' m' s' hlen' hw' _ _ hdel0 _ hr _ _ _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨hr, nv_oneLit_unsat, s', hlen', hw', hdel0 rfl, hm'⟩

/-- Concrete `Mem 64` non-bailout (`delayed_cap = 1 > 0`, `3`-lit large clause + binary watch)
UNSAT non-vacuity (`XPost := False`) for `full_bcp_hot` inside closed `fidBcpHotPushEnv`. -/
theorem nv_fid_bcp_delayed :
    Func.wp fidBcpHotPushEnv FullM7BcpHot.full_bcp_hot_body (nvDelayedCfg.hdr, ()) nvDelayedMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧ nvDelayedF0.Unsat ∧
        ∃ s', s'.LengthsOk nvDelayedCfg ∧
          FullWitnessInv nvDelayedCfg nvDelayedF0 [[1, 3, 4], [0], [2], [3, 5]] s'.core ∧
          FullMem nvDelayedCfg s' m')
      (fun _ _ _ _ => False) := by
  apply fid_bcp_hot_bundle_wp
  refine ⟨nvDelayedCfg, nvDelayedF0, [[1, 3, 4], [0], [2], [3, 5]], nvDelayedState, emp,
    rfl, nvDelayed_lengths, nvDelayed_witness, rfl, by rw [sep_emp]; exact nvDelayedMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' _delayed' m' s' hlen' hw' _ _ _ _ hr _ _ _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨hr, nvDelayedF0_unsat, s', hlen', hw', hm'⟩

/-- Concrete `Mem 64` non-bailout (`delayed_cap = 1`, `di = 3#64`) linear delayed-watch flush NV
(`XPost := False`) exercising live `full_prop_flush_del_fid` → `full_watch_push` →
`full_watch_push_m6` (`m7WatchPushFastFn`) inside closed `fidBcpHotPushEnv`. -/
theorem nv_fid_flush_del :
    Func.wp fidBcpHotPushEnv full_prop_flush_del_fid_body (nvDelayedCfg.hdr, 3#64, ())
      nvFlushDelMem
      (fun (_ok, ()) m' =>
        nvDelayedF0.Unsat ∧
        ∃ wvec' wstk' wlen' wu' wsort',
          let st' : FullState :=
            { nvFlushDelState with
              core := { nvFlushDelState.core with
                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
              scratch := { nvFlushDelState.scratch with wsort := wsort' } }
          st'.LengthsOk nvDelayedCfg ∧ WatchStackLayout st'.core ∧ FullMem nvDelayedCfg st' m')
      (fun _ _ _ _ => False) :=
  nv_fid_flush_del_of_env fidBcpHotPushEnv (fun _ _ _ _ h => hpEnv_watchPush h)

private theorem nv_oneLit_watch_layout : WatchStackLayout nvOneLitState.core :=
  ⟨fun l hl => by
      change fullWatchOffCore nvOneLitState.core l + fullWatchSizeCore nvOneLitState.core l ≤ 1
      have hcv : nvOneLitState.core.cur_vars = 1 := rfl
      rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide,
   fun l hl hpos => by
      change 0 < fullWatchSizeCore nvOneLitState.core l at hpos
      have hcv : nvOneLitState.core.cur_vars = 1 := rfl
      rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hpos,
   fun l1 _ h1 _ _ hp1 _ => by
      change 0 < fullWatchSizeCore nvOneLitState.core l1 at hp1
      have hcv : nvOneLitState.core.cur_vars = 1 := rfl
      rw [hcv] at h1
      rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp1,
   fun l hl k hk => by
      change k < fullWatchSizeCore nvOneLitState.core l at hk
      have hcv : nvOneLitState.core.cur_vars = 1 := rfl
      rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hk⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for live patched `m7WatchPushFastFn`
(`full_watch_push_m6_body`) inside closed `fidBcpHotPushEnv`. -/
theorem nv_fid_bcp_hotpush_watch_push :
    Func.wp fidBcpHotPushEnv m7WatchPushFastFn.body
      (nvOneLitCfg.hdr, 0#32, 0#32, 0#32, 1#32, ()) nvOneLitMem
      (fun (ok, ()) m' =>
        Full.nvOneLitF0.Unsat ∧ ok = false ∧
        ∃ wvec' wstk' wlen' wu' wsort',
          let s' : FullState :=
            { nvOneLitState with
              core := { nvOneLitState.core with
                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
              scratch := { nvOneLitState.scratch with wsort := wsort' } }
          s'.LengthsOk nvOneLitCfg ∧ WatchStackLayout s'.core ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  refine m7WatchPushFastFn_wp fidBcpHotPushEnv (fun _ _ _ _ h => hpEnv_front3 h) _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nv_oneLit_watch_layout,
      fun _ => by decide, fun h => absurd h (by decide),
      (by rw [sep_emp]; exact nvOneLitMem_ok), ?_⟩
  intro ok wvec' wstk' wlen' wu' wsort' m' s' hlen' hlay' _ hokT _ hm'
  have hokF : ok = false := by
    cases ok
    · rfl
    · exfalso
      obtain ⟨_, _, hsz', _, _, _⟩ := hokT rfl
      have hcv' : s'.core.cur_vars = 1 := rfl
      have h0_lt : 0 < 2 * s'.core.cur_vars := by rw [hcv']; decide
      have hsz0 : fullWatchSize nvOneLitState (0#32).toNat = 0 := rfl
      have hsz1 : 0 < fullWatchSizeCore s'.core 0 := by
        change 0 < fullWatchSize s' (0#32).toNat
        rw [hsz', hsz0]; decide
      have hbd := hlay'.bounds 0 h0_lt
      have hpo := hlay'.pos_off 0 h0_lt hsz1
      have hwl := hlen'.core_ok.wlen_le
      have hwc : nvOneLitCfg.wcap = 1 := rfl
      change fullWatchOffCore s'.core 0 + fullWatchSizeCore s'.core 0 ≤ wlen' at hbd
      change 1 ≤ fullWatchOffCore s'.core 0 at hpo
      change wlen' ≤ nvOneLitCfg.wcap at hwl
      omega
  rw [sep_emp] at hm'
  exact ⟨nv_oneLit_unsat, hokF, wvec', wstk', wlen', wu', wsort', hlen', hlay', hm'⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBcp

end

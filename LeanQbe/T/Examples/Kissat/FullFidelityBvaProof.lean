/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof1a
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2a
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof3a
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof3b
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Upstream `factor.c` Fidelity BVA: Closed `ModuleOk`, `PatchModule` & NV

Combines all `14` parametric `Func.wp` proofs (`Proof0`..`Proof3b`) into:
1. Closed `38`-row `fidBvaSpecTable` (`7` `+` helpers + `7` replacement fns + `24` canonical
   externs, all `noExit = true`, zero edits to `FullM7*`/`FullM8*`/`FullHdr`).
2. `fidBvaEnv`, `fidBvaEnv_noExit`, `fidBva_tableImpl`, headline
   `fidBva_moduleOk : ModuleOk fidBvaEnv fidBvaModule`, plus `PatchModule`-ready
   `fidBvaPatchBefores_tableImpl`, `fidBvaPatchRepls_tableImpl`, and
   `fidBvaPatchHeapRepls_tableImpl` (`FullBvaHeap`/`FullM7Fidelity` compatible).
3. Concrete `Mem 64` non-bailout UNSAT non-vacuity (`XPost := False`) on `fidBvaEnv`:
   - `nv_fid_bva_steps_cap_64` (`scratch_cap = 64 -> 8#32` dynamic matrix rows),
   - `nv_fid_bva_steps_cap_tiny` (`scratch_cap = 0 -> 0#32` graceful fallback),
   - `nv_fid_bva_connect_64` (`full_bva_connect_clauses_fid` on `nvFidBvaMem`),
   - `nv_fid_bva_factor_64` (`full_factor` on `8,192 B` `nvFidBvaMem`, `scratch_cap = 64`),
   - `nv_fid_bva_factor_tiny` (`full_factor` on tiny `nvFidTinyMem`, `scratch_cap = 0`),
   - `nv_fid_probe_m6` (`full_probe_m6` on `nvM6HdrMem`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0HeadStep LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Search
open Kraken.Bedrock2.Test

/-! ## 1. Closed `38`-Row Spec Table, `fidBvaEnv`, & `ModuleOk` -/

section StandaloneModuleOk

/-- Specification rows for the `7` `+`-inserted helpers in `fidBvaHelpers`. -/
def fidBvaPatchBeforeRows : List SpecEntry :=
  [ ⟨"full_bva_steps_cap_fid", [i64], [i32], fidBvaStepsCapSpec, true⟩
  , ⟨"full_bva_clines_fid", [i64], [i64], fidBvaClinesSpec, true⟩
  , ⟨"full_fheap_up_fid", [i64, i64, i64, i32], [], fidFheapUpSpec, true⟩
  , ⟨"full_fheap_down_fid", [i64, i64, i64, i32, i32], [], fidFheapDownSpec, true⟩
  , ⟨"full_bva_count_lit_deg_fid", [i64, i32], [i32], fidBvaCountLitDegSpec, true⟩
  , ⟨"full_bva_connect_clauses_fid", [i64], [], fidBvaConnectClausesSpec, true⟩
  , ⟨"full_bva_match_large_bva_fid", [i64, i32, i32, i32], [.bool],
      fidBvaMatchLargeBvaSpec, true⟩ ]

/-- Anchor-insertion row list matching `fidBvaBefores`. -/
def fidBvaPatchRowBefores : List (Sym × List SpecEntry) :=
  [ ("full_bva_scan_cands", fidBvaPatchBeforeRows) ]

/-- Specification rows for the `7` replacement functions in `fidBvaRepls`. -/
def fidBvaPatchReplRows : List SpecEntry :=
  [ ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], fidBvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], fidBvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], fidBvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fidBvaTryLitSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ ]

/-- Heap-contract replacement rows (using `fullBvaTryLitHeapSpec` for `FullM7Fidelity` splice). -/
def fidBvaPatchHeapReplRows : List SpecEntry :=
  [ ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], fidBvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], fidBvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], fidBvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ ]

/-- Specification rows for all `14` defined functions of `fidBvaModule`. -/
def fidBvaFnRows : List SpecEntry :=
  fidBvaPatchBeforeRows ++ fidBvaPatchReplRows

/-- Specification rows for all `24` external callees of `fidBvaModule`. -/
def fidBvaExtRows : List SpecEntry :=
  [ ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_log10_q16_m7", [i64], [i64], m7Log10Q16Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], fullBackboneSpec, true⟩ ]

/-- Complete `38`-row closed specification table (`14` defined fns + `24` externs). -/
def fidBvaSpecTable : List SpecEntry := fidBvaFnRows ++ fidBvaExtRows

theorem fidBvaSpecTable_length : fidBvaSpecTable.length = 38 := by rfl

theorem fidBvaSpecTable_sigs :
    fidBvaSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidBvaModule.fns.map Fn.sig ++ fidBvaModule.externs.map Extern.sig := by rfl

theorem fidBvaSpecTable_nodup : (fidBvaSpecTable.map SpecEntry.name).Nodup := by
  have heq : fidBvaSpecTable.map SpecEntry.name =
      fidBvaModule.fns.map Fn.name ++ fidBvaModule.externs.map Extern.name := by rfl
  rw [heq]; decide

theorem fidBvaSpecTable_noExit : ∀ e ∈ fidBvaSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp (by rfl : fidBvaSpecTable.all (·.noExit) = true) e he

theorem fidBvaPatchBeforeRows_sigs :
    fidBvaPatchBeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      fidBvaHelpers.map Fn.sig := by rfl

theorem fidBvaPatchReplRows_sigs :
    fidBvaPatchReplRows.map (fun e => (e.name, e.as, e.rs)) =
      fidBvaRepls.map Fn.sig := by rfl

theorem fidBvaPatchHeapReplRows_sigs :
    fidBvaPatchHeapReplRows.map (fun e => (e.name, e.as, e.rs)) =
      fidBvaRepls.map Fn.sig := by rfl

/-- Closed environment induced by `fidBvaSpecTable`. -/
def fidBvaEnv : Env := Env.ofTable fidBvaSpecTable

theorem fidBvaEnv_noExit : ∀ f as bs xs m Q X X',
    fidBvaEnv f as bs xs m Q X → fidBvaEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fidBvaSpecTable_noExit

private theorem fidBvaEnv_row (idx : Nat) (e : SpecEntry)
    (hidx : fidBvaSpecTable[idx]? = some e) (xs : Tup Val e.as) (m : Mem 64) (Q : Post e.rs)
    (X : XPost) (hs : e.eff xs m Q X) : fidBvaEnv e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem (List.mem_of_getElem? hidx) fidBvaSpecTable_nodup hs

private theorem fidRowImpl {Γ : Env} {fn : Fn} {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hn : nm = fn.name) (ha : as = fn.as) (hr : bs = fn.rs)
    (hwp : ∀ xs m Q X, sp xs m Q X → Func.wp Γ (ha ▸ hr ▸ fn.body) xs m Q X) :
    SpecEntry.Impl Γ fn ⟨nm, as, bs, sp, true⟩ := by
  subst hn ha hr
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs => ?_⟩
  dsimp only [SpecEntry.cast, SpecEntry.eff] at hs
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m (hwp xs m Q _ hs)

/-- Parametric `TableImpl` for the `7` `+`-inserted helpers in `fidBvaHelpers`. -/
theorem fidBvaPatchBefores_tableImpl (Γ : Env)
    (hFlush : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X) :
    TableImpl Γ fidBvaHelpers fidBvaPatchBeforeRows := by
  unfold fidBvaHelpers fidBvaPatchBeforeRows
  exact
    ⟨ fidRowImpl rfl rfl rfl (full_bva_steps_cap_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_bva_clines_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_fheap_up_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_fheap_down_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_bva_count_lit_deg_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_bva_connect_clauses_fid_wp Γ hFlush hNext hPush hDeg)
    , fidRowImpl rfl rfl rfl (full_bva_match_large_bva_fid_wp Γ)
    , trivial ⟩

/-- Parametric `TableImpl` for the `7` replacement functions in `fidBvaRepls`
(`fidBvaTryLitSpec` contract on `full_bva_try_lit`). -/
theorem fidBvaPatchRepls_tableImpl (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    (hConn : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hBml : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilt : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hComm : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X)
    (hTry : ∀ a m Q X, fidBvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hInit : ∀ a m Q X, fullInitFreshVarHeapSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hL10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hSc : EnvSpec Γ "full_scale_delta_m5" schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEd : EnvSpec Γ "full_enter_dense" schedEnterDenseSpec)
    (hDl : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCg : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hRw : EnvSpec Γ "full_rebuild_watches" fullRebuildWatchesSpec)
    (hSw : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRd : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBd : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSp : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSb : EnvSpec Γ "full_substitute" fullSubstituteSpec)
    (hTl : EnvSpec Γ "full_probe_tail_m6" m6ProbeTailSpec)
    (hBb : EnvSpec Γ "full_backbone_m6" fullBackboneSpec)
    (hFac : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec) :
    TableImpl Γ fidBvaRepls fidBvaPatchReplRows := by
  unfold fidBvaRepls fidBvaPatchReplRows
  exact
    ⟨ fidRowImpl rfl rfl rfl (full_bva_scan_cands_fid_wp Γ hClines)
    , fidRowImpl rfl rfl rfl (full_bva_pick_cand_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_bva_filter_row_fid_wp Γ hClines hBml)
    , fidRowImpl rfl rfl rfl (full_bva_commit_fid_wp Γ hSteps hDefrag hInit hAddBin
        hAlloc hPush hDelBin hUnw)
    , fidRowImpl rfl rfl rfl (full_bva_try_lit_fid_wp Γ hSteps hScan hPick hFilt hComm)
    , fidRowImpl rfl rfl rfl (full_factor_fid_wp Γ hSteps hConn hDeg hUp hDown hTry)
    , fidRowImpl rfl rfl rfl (full_probe_m6_fid_wp Γ hDt hL10 hSc hViv hEd hDl hCg hRw
        hSw hRd hBd hSp hSb hTl hBb hFac)
    , trivial ⟩

/-- Parametric `TableImpl` for `fidBvaRepls` against `fidBvaPatchHeapReplRows`
(`FullBvaHeap.fullBvaTryLitHeapSpec` contract for `FullM7Fidelity` `PatchModule` splicing). -/
theorem fidBvaPatchHeapRepls_tableImpl (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    (hConn : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hBml : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilt : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hComm : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X)
    (hTry : ∀ a m Q X, fidBvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hInit : ∀ a m Q X, fullInitFreshVarHeapSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hL10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hSc : EnvSpec Γ "full_scale_delta_m5" schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEd : EnvSpec Γ "full_enter_dense" schedEnterDenseSpec)
    (hDl : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCg : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hRw : EnvSpec Γ "full_rebuild_watches" fullRebuildWatchesSpec)
    (hSw : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRd : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBd : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSp : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSb : EnvSpec Γ "full_substitute" fullSubstituteSpec)
    (hTl : EnvSpec Γ "full_probe_tail_m6" m6ProbeTailSpec)
    (hBb : EnvSpec Γ "full_backbone_m6" fullBackboneSpec)
    (hFac : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec) :
    TableImpl Γ fidBvaRepls fidBvaPatchHeapReplRows := by
  unfold fidBvaRepls fidBvaPatchHeapReplRows
  exact
    ⟨ fidRowImpl rfl rfl rfl (full_bva_scan_cands_fid_wp Γ hClines)
    , fidRowImpl rfl rfl rfl (full_bva_pick_cand_fid_wp Γ)
    , fidRowImpl rfl rfl rfl (full_bva_filter_row_fid_wp Γ hClines hBml)
    , fidRowImpl rfl rfl rfl (full_bva_commit_fid_wp Γ hSteps hDefrag hInit hAddBin
        hAlloc hPush hDelBin hUnw)
    , fidRowImpl rfl rfl rfl (full_bva_try_lit_heap_wp Γ hSteps hScan hPick hFilt hComm)
    , fidRowImpl rfl rfl rfl (full_factor_fid_wp Γ hSteps hConn hDeg hUp hDown hTry)
    , fidRowImpl rfl rfl rfl (full_probe_m6_fid_wp Γ hDt hL10 hSc hViv hEd hDl hCg hRw
        hSw hRd hBd hSp hSb hTl hBb hFac)
    , trivial ⟩

private theorem fid_allFns_of_mem {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, fid_allFns_of_mem fun _ hg => h _ (List.mem_cons_of_mem _ hg)⟩

private theorem fid_tableImpl_append {Γ : Env} :
    ∀ {fs₁ fs₂ : List Fn} {r₁ r₂ : List SpecEntry},
      fs₁.length = r₁.length → TableImpl Γ fs₁ r₁ → TableImpl Γ fs₂ r₂ →
      TableImpl Γ (fs₁ ++ fs₂) (r₁ ++ r₂)
  | [], _, [], _, _, _, h2 => h2
  | _ :: _, _, _ :: _, _, hl, ⟨h1h, h1t⟩, h2 =>
    ⟨h1h, fid_tableImpl_append (Nat.succ.inj hl) h1t h2⟩

private theorem fid_tableImpl_exts {Γ : Env} :
    ∀ {fs : List Fn} {rs ext : List SpecEntry},
      fs.length = rs.length → TableImpl Γ fs rs → TableImpl Γ fs (rs ++ ext)
  | [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _, hl, ⟨hh, ht⟩ => ⟨hh, fid_tableImpl_exts (Nat.succ.inj hl) ht⟩

/-- Closed `TableImpl` certifying all `14` functions of `fidBvaModule` against
`fidBvaSpecTable`. -/
theorem fidBva_tableImpl : TableImpl fidBvaEnv fidBvaFns fidBvaSpecTable := by
  let er (i : Nat) (n : Sym) (as bs : List Ty) (sp : Spec as bs)
      (h : fidBvaSpecTable[i]? = some ⟨n, as, bs, sp, true⟩)
      (hm : ∀ a m Q X, sp a m Q X → sp a m Q (fun _ _ _ _ => False)) :
      ∀ a m Q X, sp a m Q X → fidBvaEnv n as bs a m Q X :=
    fun a m Q X hs =>
      fidBvaEnv_row i ⟨n, as, bs, sp, true⟩ h a m Q X (hm a m Q X hs)
  let erW (i : Nat) (n : Sym) (ea bs : List Ty)
      (h : fidBvaSpecTable[i]? = some ⟨n, i64 :: ea, bs, m6HdrW2aSpec ea bs, true⟩) :=
    er i n (i64 :: ea) bs (m6HdrW2aSpec ea bs) h fun _ _ _ _ h => m6HdrW2aSpec_monoX h
  have hFlush := er 21 _ _ _ _ rfl fun a m Q X h => fullFwdFlushLargeM6Spec_noExit a m Q X h
  have hSteps := er 0 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hClines := er 1 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hUp := er 2 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hDown := er 3 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hDeg := er 4 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hConn := er 5 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hBml := er 6 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hScan := er 7 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hPick := er 8 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hFilt := er 9 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hComm := er 10 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hTry := er 11 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hFac := er 12 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hNext := er 14 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hAlloc := er 15 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hDefrag := er 16 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hPush := er 17 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hUnw := er 18 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hAddB := er 19 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hDelB := er 20 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hInit := er 22 _ _ _ _ rfl (fun _ _ _ _ h => h)
  have hb := fidBvaPatchBefores_tableImpl fidBvaEnv hFlush hNext hPush hDeg
  have hr := fidBvaPatchRepls_tableImpl fidBvaEnv hSteps hClines hUp hDown hDeg hConn hBml
    hScan hPick hFilt hComm hTry hDefrag hInit hAddB hAlloc hPush hDelB hUnw
    (erW 23 _ _ _ rfl) (er 24 _ _ _ _ rfl fun _ _ _ _ h => m7Log10Q16Spec_monoX h)
    (er 25 _ _ _ _ rfl (fun _ _ _ _ h => h))
    (er 26 _ _ _ _ rfl fun _ _ _ _ h => m6aVivifySpec_monoX h)
    (er 27 _ _ _ _ rfl (fun _ _ _ _ h => h))
    (erW 28 _ _ _ rfl)
    (er 29 _ _ _ _ rfl (fun _ _ _ _ h => h))
    (er 30 _ _ _ _ rfl (fun _ _ _ _ h => h))
    (erW 31 _ _ _ rfl) (erW 32 _ _ _ rfl) (erW 33 _ _ _ rfl)
    (er 34 _ _ _ _ rfl (fun _ _ _ _ h => h))
    (er 35 _ _ _ _ rfl (fun _ _ _ _ h => h))
    (er 36 _ _ _ _ rfl fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
    (er 37 _ _ _ _ rfl (fun _ _ _ _ h => h))
    hFac
  unfold fidBvaFns fidBvaSpecTable fidBvaFnRows
  exact fid_tableImpl_exts (by rfl) (fid_tableImpl_append (by rfl) hb hr)

/-- Closed `ModuleOk` for the standalone `14`-fn + `24`-extern `fidBvaModule`. -/
theorem fidBva_moduleOk : ModuleOk fidBvaEnv fidBvaModule :=
  Env.ofTable_moduleOk fidBva_acyclic (fid_allFns_of_mem fidBvaFns_wf) fidBva_tableImpl

end StandaloneModuleOk

/-! ## 2. Concrete `Mem 64` Non-Bailout & Graceful-Fallback UNSAT NV (`XPost := False`) -/

section ConcreteNonVacuity

private theorem nvFid_wp {f : Sym} {as rs : List Ty} {sp : Spec as rs} (idx : Nat)
    (hidx : fidBvaSpecTable[idx]? = some ⟨f, as, rs, sp, true⟩) (pre post : List Fn) (fn : Fn)
    (hsplit : fidBvaFns = pre ++ fn :: post) (hname : fn.name = f) (has : fn.as = as)
    (hrs : fn.rs = rs) (body : Func as rs) (hbody : has ▸ hrs ▸ fn.body = body) :
    ∀ (a : Tup Val as) m Q, sp a m Q (fun _ _ _ _ => False) →
      Func.wp fidBvaEnv body a m Q (fun _ _ _ _ => False) := by
  subst has hrs hname hbody; let ⟨_, _, hwp⟩ := fidBva_moduleOk.fnsOk pre fn post hsplit
  exact fun a m Q hs => hwp a m Q _
    (fidBvaEnv_row idx ⟨fn.name, fn.as, fn.rs, sp, true⟩ hidx a m Q (fun _ _ _ _ => False) hs)

/-- Concrete `FullCfg` with `scratch_cap = 64` (`fidStepsCap 64 = 8` dynamic rows). -/
def nvFidBvaCfg : FullCfg where
  hdr := 4096#64
  avail := 2012
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 64
  hbva := rfl
  hmv := by unfold dimacsBound; omega
  hmaxv := by unfold dimacsBound; omega
  hnc := by unfold dimacsBound; omega
  harena := by unfold dimacsBound; omega
  hwcap := by unfold dimacsBound; omega
  hdel := by unfold dimacsBound; omega
  hred := by unfold dimacsBound; omega
  hext := by unfold dimacsBound; omega
  hscr := by unfold dimacsBound; omega
  havail_fit := by decide
  hsize := by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide

/-- Concrete tiny `FullCfg` with `scratch_cap = 0` (`fidStepsCap 0 = 0` graceful fallback). -/
def nvFidTinyCfg : FullCfg where
  hdr := 4096#64
  avail := 1756
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by unfold dimacsBound; omega
  hmaxv := by unfold dimacsBound; omega
  hnc := by unfold dimacsBound; omega
  harena := by unfold dimacsBound; omega
  hwcap := by unfold dimacsBound; omega
  hdel := by unfold dimacsBound; omega
  hred := by unfold dimacsBound; omega
  hext := by unfold dimacsBound; omega
  hscr := by unfold dimacsBound; omega
  havail_fit := by decide
  hsize := by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide

/-- Concrete `FullState` matching `nvFidBvaCfg` (`scratch_cap = 64`). -/
def nvFidBvaState : FullState where
  core := nvBvaDenseState.core
  scratch := { nvBvaDenseState.scratch with scratch_buf := List.replicate 64 0#32 }

/-- Concrete `FullState` matching `nvFidTinyCfg` (`scratch_cap = 0`). -/
def nvFidTinyState : FullState where
  core := nvBvaDenseState.core
  scratch := { nvBvaDenseState.scratch with scratch_buf := [] }

private theorem nvFidBva_invW :
    FullDenseInvW nvFidBvaCfg nvOneLitF0 [[0], [1]] nvFidBvaState := by
  have hw := nvBvaDense_invW
  have hcl : nvFidBvaState.core.LengthsOk nvFidBvaCfg := by
    have h0 := nvOneLit_lengths.core_ok
    exact ⟨h0.1, h0.2, h0.3, h0.4, h0.5, h0.6, h0.7, h0.8, h0.9, h0.10, h0.11, h0.12, h0.13,
      h0.14, h0.15, h0.16, h0.17, h0.18, h0.19, h0.20, h0.21, h0.22, h0.23, h0.24, h0.25⟩
  have hlen : nvFidBvaState.LengthsOk nvFidBvaCfg :=
    ⟨hcl, { nvOneLit_lengths.scratch_ok with scratch_buf_len := by decide }⟩
  have har : FullArenaClausesInv nvFidBvaCfg [[0], [1]] nvFidBvaState.core :=
    ⟨hw.2.1.arena.1, hw.2.1.arena.2, hw.2.1.arena.3, hw.2.1.arena.4, hw.2.1.arena.5⟩
  exact ⟨hlen, { hw.2.1 with arena := har },
    hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩

private theorem nvFidTiny_invW :
    FullDenseInvW nvFidTinyCfg nvOneLitF0 [[0], [1]] nvFidTinyState := by
  have hw := nvBvaDense_invW
  have hcl : nvFidTinyState.core.LengthsOk nvFidTinyCfg := by
    have h0 := nvOneLit_lengths.core_ok
    exact ⟨h0.1, h0.2, h0.3, h0.4, h0.5, h0.6, h0.7, h0.8, h0.9, h0.10, h0.11, h0.12, h0.13,
      h0.14, h0.15, h0.16, h0.17, h0.18, h0.19, h0.20, h0.21, h0.22, h0.23, h0.24, h0.25⟩
  have hlen : nvFidTinyState.LengthsOk nvFidTinyCfg :=
    ⟨hcl, { nvOneLit_lengths.scratch_ok with scratch_buf_len := by decide }⟩
  have har : FullArenaClausesInv nvFidTinyCfg [[0], [1]] nvFidTinyState.core :=
    ⟨hw.2.1.arena.1, hw.2.1.arena.2, hw.2.1.arena.3, hw.2.1.arena.4, hw.2.1.arena.5⟩
  exact ⟨hlen, { hw.2.1 with arena := har },
    hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩

private def nvFidPreMinBytes : List UInt8 :=
  bytesOf (t := i32) nvBvaDenseState.core.min_stk ++
  bytesOf (t := i32) nvBvaDenseState.scratch.glue_used ++
  bytesOf (t := i32) nvBvaDenseState.scratch.last_learned ++
  bytesOf (t := i32) nvBvaDenseState.core.arena ++
  bytesOf (t := i32) nvBvaDenseState.core.wstk ++
  bytesOf (t := i32) nvBvaDenseState.scratch.delayed ++
  bytesOf (t := i32) nvBvaDenseState.scratch.red_refs ++
  bytesOf (t := i32) nvBvaDenseState.scratch.extend_stk

private def nvFidMidBytes : List UInt8 :=
  nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++ nvBlockWvec ++ nvFidPreMinBytes

/-- Serialized bytes for `nvFidBvaState` (`2,012` payload bytes). -/
def nvFidBvaBytes : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++
  bytes64 (Full.hdrTailWords nvFidBvaCfg nvFidBvaState) ++
  nvFidMidBytes ++
  bytesOf (t := i32) nvFidBvaState.scratch.scratch_buf

/-- Serialized bytes for `nvFidTinyState` (`1,756` payload bytes). -/
def nvFidTinyBytes : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++
  bytes64 (Full.hdrTailWords nvFidTinyCfg nvFidTinyState) ++
  nvFidMidBytes

/-- Concrete `Mem 64` witness for `nvFidBvaCfg` (`scratch_cap = 64`). -/
def nvFidBvaMem : Mem 64 := nvFidBvaBytes.At nvFidBvaCfg.hdr

/-- Concrete `Mem 64` witness for `nvFidTinyCfg` (`scratch_cap = 0`). -/
def nvFidTinyMem : Mem 64 := nvFidTinyBytes.At nvFidTinyCfg.hdr

private def nvFidMidPred (cfg : FullCfg) (st : FullState) : Mem 64 → Prop :=
  ((FullCoreByteArrs cfg st.core ⋆ FullScrByteArrs cfg st.scratch ⋆ cfg.padBytes) ⋆
   ((array (t := i32) cfg.pFlags st.core.flags ⋆
     array (t := i32) cfg.pLevel st.core.lvl ⋆
     array (t := i32) cfg.pReason st.core.rsns ⋆
     array (t := i32) cfg.pTrail st.core.trl ⋆
     array (t := i32) cfg.pTrailPos st.core.trail_pos) ⋆ cfg.padU32A) ⋆
   ((array (t := i32) cfg.pTmp st.core.tmp ⋆
     array (t := i32) cfg.pMinClr st.core.min_clr) ⋆
    (array (t := i32) cfg.pHeap st.scratch.heap ⋆
     array (t := i32) cfg.pPos st.scratch.pos ⋆
     array (t := i32) cfg.pShrinkStk st.scratch.shrink_stk) ⋆ cfg.padU32B) ⋆
   ((array (t := i32) cfg.pQPrev st.scratch.q_prev ⋆
     array (t := i32) cfg.pQNext st.scratch.q_next ⋆
     array (t := i32) cfg.pQStamp st.scratch.q_stamp) ⋆
    (array (t := i32) cfg.pFrameTrail st.core.frame_trail ⋆
     array (t := i32) cfg.pFrameDec st.core.frame_dec) ⋆ cfg.padU32C) ⋆
   ((array (t := i32) cfg.pWvec st.core.wvec ⋆
     array (t := i32) cfg.pRepr st.core.repr) ⋆
    FullScrWksArrs cfg st.scratch ⋆
    (array64 cfg.pScore st.scratch.score ⋆
     array64 cfg.pSimSig st.scratch.sim_sig))) ⋆
  (array (t := i32) cfg.pMinStk st.core.min_stk ⋆
   (array (t := i32) cfg.pGlueUsed st.scratch.glue_used ⋆
    array (t := i32) cfg.pLastLearned st.scratch.last_learned) ⋆
   array (t := i32) cfg.pArena st.core.arena ⋆
   array (t := i32) cfg.pWstk st.core.wstk ⋆
   array (t := i32) cfg.pDelayed st.scratch.delayed ⋆
   array (t := i32) cfg.pRedRefs st.scratch.red_refs ⋆
   array (t := i32) cfg.pExtendStk st.scratch.extend_stk)

private theorem nvFidMid_ok :
    nvFidMidBytes.length = 604 ∧ nvFidMidPred nvFidTinyCfg nvFidTinyState
      (nvFidMidBytes.At nvFidTinyCfg.pVals) := by
  let cfg := nvFidTinyCfg; let st := nvFidTinyState
  have hvb : valsBytes cfg.max_vars - 2 * cfg.max_vars = 6 := by decide
  have hmb : markBytes cfg.max_vars - cfg.max_vars = 7 := by decide
  have hu4 : u32FullBytes cfg.max_vars - 4 * cfg.max_vars = 4 := by decide
  have hu8 : u32FullBytes cfg.max_vars - 4 * (cfg.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 cfg.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * cfg.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * cfg.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (cfg.max_vars + 1)) = 8#64 := rfl
  have hBytes : nvBlockBytes.length = 64 ∧
      (FullCoreByteArrs cfg st.core ⋆ FullScrByteArrs cfg st.scratch ⋆ cfg.padBytes)
        (nvBlockBytes.At cfg.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := cfg.pVals) (xs := st.core.vals) 2 6 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := cfg.pWalkVals) (xs := st.scratch.walk_vals)
      2 6 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := cfg.pLitMark) (xs := st.core.lit_mark)
      2 6 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := cfg.pMark) (xs := st.core.mrk) 1 7 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := cfg.pPhases) (xs := st.scratch.phases)
      1 7 rfl (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := cfg.pPhasesTarget) (xs := st.scratch.phases_target)
      1 7 rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := cfg.pPhasesBest) (xs := st.scratch.phases_best)
      1 7 rfl (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := cfg.pWalkBest) (xs := st.scratch.walk_best)
      1 7 rfl (by decide)
    let pB1 : Mem 64 → Prop :=
      region (cfg.pVals + 2#64) 6 ⋆ region (cfg.pWalkVals + 2#64) 6 ⋆
      region (cfg.pLitMark + 2#64) 6 ⋆ region (cfg.pMark + 1#64) 7
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs cfg st.core ⋆
        array (t := i8) cfg.pWalkVals st.scratch.walk_vals) ⋆ pB1) fun _ hm => nv_zip4 hm
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes; rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvBlockU32A.length = 40 ∧
      ((array (t := i32) cfg.pFlags st.core.flags ⋆ array (t := i32) cfg.pLevel st.core.lvl ⋆
        array (t := i32) cfg.pReason st.core.rsns ⋆ array (t := i32) cfg.pTrail st.core.trl ⋆
        array (t := i32) cfg.pTrailPos st.core.trail_pos) ⋆ cfg.padU32A)
        (nvBlockU32A.At cfg.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := cfg.pFlags) (xs := st.core.flags) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := cfg.pLevel) (xs := st.core.lvl) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := cfg.pReason) (xs := st.core.rsns) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := cfg.pTrail) (xs := st.core.trl) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := cfg.pTrailPos) (xs := st.core.trail_pos)
      4 4 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; c0_frame
  have hU32B : nvBlockU32B.length = 40 ∧
      ((array (t := i32) cfg.pTmp st.core.tmp ⋆ array (t := i32) cfg.pMinClr st.core.min_clr) ⋆
        (array (t := i32) cfg.pHeap st.scratch.heap ⋆ array (t := i32) cfg.pPos st.scratch.pos ⋆
         array (t := i32) cfg.pShrinkStk st.scratch.shrink_stk) ⋆ cfg.padU32B)
        (nvBlockU32B.At cfg.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := cfg.pTmp) (xs := st.core.tmp) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := cfg.pHeap) (xs := st.scratch.heap) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := cfg.pPos) (xs := st.scratch.pos) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := cfg.pMinClr) (xs := st.core.min_clr)
      4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := cfg.pShrinkStk) (xs := st.scratch.shrink_stk)
      4 4 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; c0_frame
  have hU32C : nvBlockU32C.length = 40 ∧
      ((array (t := i32) cfg.pQPrev st.scratch.q_prev ⋆
        array (t := i32) cfg.pQNext st.scratch.q_next ⋆
        array (t := i32) cfg.pQStamp st.scratch.q_stamp) ⋆
        (array (t := i32) cfg.pFrameTrail st.core.frame_trail ⋆
         array (t := i32) cfg.pFrameDec st.core.frame_dec) ⋆ cfg.padU32C)
        (nvBlockU32C.At cfg.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := cfg.pQPrev) (xs := st.scratch.q_prev)
      4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := cfg.pQNext) (xs := st.scratch.q_next)
      4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := cfg.pQStamp) (xs := st.scratch.q_stamp)
      4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := cfg.pFrameTrail) (xs := st.core.frame_trail)
      8 0 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := cfg.pFrameDec) (xs := st.core.frame_dec)
      8 0 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      fun _ hm => by c0_frame
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; c0_frame
  have hWvec : nvBlockWvec.length = 80 ∧
      ((array (t := i32) cfg.pWvec st.core.wvec ⋆ array (t := i32) cfg.pRepr st.core.repr) ⋆
        FullScrWksArrs cfg st.scratch ⋆
        (array64 cfg.pScore st.scratch.score ⋆ array64 cfg.pSimSig st.scratch.sim_sig))
        (nvBlockWvec.At cfg.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := cfg.pWvec) (xs := st.core.wvec) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := cfg.pRepr) (xs := st.core.repr) 8 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := cfg.pWsort) (xs := st.scratch.wsort) 8 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := cfg.pWorkStk1) (xs := st.scratch.work_stk1)
      8 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := cfg.pWorkStk2) (xs := st.scratch.work_stk2)
      8 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := cfg.pTarjanMark) (xs := st.scratch.tarjan_mark)
      8 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := cfg.pTarjanReach) (xs := st.scratch.tarjan_reach)
      8 rfl (by decide)
    have h8 := nv_arr64_p (a := cfg.pScore) (xs := st.scratch.score) 8 rfl (by decide)
    have h9 := nv_arr64_p (a := cfg.pSimSig) (xs := st.scratch.sim_sig) 8 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; c0_frame
  have hPre : nvFidPreMinBytes.length = 340 ∧
      (array (t := i32) cfg.pMinStk st.core.min_stk ⋆
        (array (t := i32) cfg.pGlueUsed st.scratch.glue_used ⋆
         array (t := i32) cfg.pLastLearned st.scratch.last_learned) ⋆
        array (t := i32) cfg.pArena st.core.arena ⋆
        array (t := i32) cfg.pWstk st.core.wstk ⋆
        array (t := i32) cfg.pDelayed st.scratch.delayed ⋆
        array (t := i32) cfg.pRedRefs st.scratch.red_refs ⋆
        array (t := i32) cfg.pExtendStk st.scratch.extend_stk)
        (nvFidPreMinBytes.At cfg.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := cfg.pMinStk) (xs := st.core.min_stk) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := cfg.pGlueUsed) (xs := st.scratch.glue_used)
      256 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := cfg.pLastLearned) (xs := st.scratch.last_learned)
      64 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := cfg.pArena) (xs := st.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := cfg.pWstk) (xs := st.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := cfg.pDelayed) (xs := st.scratch.delayed)
      0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := cfg.pRedRefs) (xs := st.scratch.red_refs)
      0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := cfg.pExtendStk) (xs := st.scratch.extend_stk)
      0 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234567 h8 (by decide) (by decide)) fun _ hm => by c0_frame
  have h01 := nv_join_pair hBytes hU32A (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32B (by decide) (by decide)
  have h03 := nv_join_pair h02 hU32C (by decide) (by decide)
  have h04 := nv_join_pair h03 hWvec (by decide) (by decide)
  exact nv_join_pair h04 hPre (by decide) (by decide)

private theorem nvFidBvaMid_ok :
    nvFidMidBytes.length = 604 ∧ nvFidMidPred nvFidBvaCfg nvFidBvaState
      (nvFidMidBytes.At nvFidBvaCfg.pVals) := by
  have hm := nvFidMid_ok
  have hpv : nvFidBvaCfg.pVals = nvFidTinyCfg.pVals := rfl
  have hpred : nvFidMidPred nvFidBvaCfg nvFidBvaState =
      nvFidMidPred nvFidTinyCfg nvFidTinyState := by
    unfold nvFidMidPred FullCoreByteArrs FullScrByteArrs FullScrWksArrs
      FullCfg.padBytes FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C
    rfl
  rw [hpv, hpred]; exact hm

private theorem nvFid_repack (cfg : FullCfg) (st : FullState) (m : Mem 64)
    (hm : ((dimacsState cfg.hdr (BitVec.ofNat 64 cfg.mv) (BitVec.ofNat 64 cfg.nc)
              st.core.d_cur st.core.d_val ⋆
            array64 (cfg.hdr + 32) (Full.hdrTailWords cfg st)) ⋆
           (nvFidMidPred cfg st ⋆
            (array (t := i32) cfg.pScratchBuf st.scratch.scratch_buf ⋆
             region cfg.pSlack cfg.slack))) m) :
    FullMem cfg st m := by
  unfold nvFidMidPred at hm
  unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B
    FullScratchArrays FullScrU32A FullScrMetaArrs FullCoreDynArrs FullScrDynArrs FullCfg.pad
  c0_frame

private theorem nvFidBvaMem_ok : FullMem nvFidBvaCfg nvFidBvaState nvFidBvaMem := by
  have hHdr : (bytes64 [1#64, 2#64, 0#64, 0#64] ++
      bytes64 (Full.hdrTailWords nvFidBvaCfg nvFidBvaState)).length = 1152 ∧
      (dimacsState nvFidBvaCfg.hdr (BitVec.ofNat 64 nvFidBvaCfg.mv)
        (BitVec.ofNat 64 nvFidBvaCfg.nc) nvFidBvaState.core.d_cur nvFidBvaState.core.d_val ⋆
        array64 (nvFidBvaCfg.hdr + 32) (Full.hdrTailWords nvFidBvaCfg nvFidBvaState))
        ((bytes64 [1#64, 2#64, 0#64, 0#64] ++
          bytes64 (Full.hdrTailWords nvFidBvaCfg nvFidBvaState)).At nvFidBvaCfg.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := nvFidBvaCfg.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := nvFidBvaCfg.hdr + 32)
        (xs := Full.hdrTailWords nvFidBvaCfg nvFidBvaState)
        1120 (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by decide)
  have hScr : (bytesOf (t := i32) nvFidBvaState.scratch.scratch_buf).length = 256 ∧
      (array (t := i32) nvFidBvaCfg.pScratchBuf nvFidBvaState.scratch.scratch_buf ⋆
        region nvFidBvaCfg.pSlack nvFidBvaCfg.slack)
        ((bytesOf (t := i32) nvFidBvaState.scratch.scratch_buf).At nvFidBvaCfg.pScratchBuf) := by
    have h9 := nv_arr_p (t := i32) (a := nvFidBvaCfg.pScratchBuf)
      (xs := nvFidBvaState.scratch.scratch_buf) 256 rfl (by decide)
    have h10 : ([] : List UInt8).length = 0 ∧
        region nvFidBvaCfg.pSlack nvFidBvaCfg.slack (([] : List UInt8).At nvFidBvaCfg.pSlack) := by
      have hsl : nvFidBvaCfg.slack = 0 := by
        unfold FullCfg.slack nvFidBvaCfg fullFixedBytes valsBytes markBytes
          u32FullBytes fullMinDepthOf; decide
      rw [hsl]; exact ⟨rfl, ⟨[], rfl, rfl⟩⟩
    have hj := nv_join_pair h9 h10 (by decide) (by decide)
    simpa only [List.append_nil] using hj
  have hMidScr := nv_join_pair nvFidBvaMid_ok hScr (by
    dsimp only [FullCfg.pScratchBuf, FullCfg.pExtendStk, FullCfg.pRedRefs, FullCfg.pDelayed,
      FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, FullCfg.pMinStk,
      FullCfg.pSimSig, FullCfg.pScore, FullCfg.pTarjanReach, FullCfg.pTarjanMark,
      FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, FullCfg.pWvec,
      FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext, FullCfg.pQPrev,
      FullCfg.pShrinkStk, FullCfg.pPos, FullCfg.pHeap, FullCfg.pMinClr, FullCfg.pTmp,
      FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel, FullCfg.pFlags,
      FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget, FullCfg.pPhases,
      FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals, FullCfg.minDepth,
      fullMinDepthOf, valsBytes, markBytes, u32FullBytes]
    decide) (by decide)
  have hp_pv : nvFidBvaCfg.pVals = nvFidBvaCfg.hdr + BitVec.ofNat 64 1152 := rfl
  have hAll := nv_join_pair hHdr hMidScr hp_pv (by decide)
  exact nvFid_repack nvFidBvaCfg nvFidBvaState nvFidBvaMem
    (by simpa [nvFidBvaMem, nvFidBvaBytes, List.append_assoc] using hAll.2)

private theorem nvFidTinyMem_ok : FullMem nvFidTinyCfg nvFidTinyState nvFidTinyMem := by
  have hHdr : (bytes64 [1#64, 2#64, 0#64, 0#64] ++
      bytes64 (Full.hdrTailWords nvFidTinyCfg nvFidTinyState)).length = 1152 ∧
      (dimacsState nvFidTinyCfg.hdr (BitVec.ofNat 64 nvFidTinyCfg.mv)
        (BitVec.ofNat 64 nvFidTinyCfg.nc) nvFidTinyState.core.d_cur nvFidTinyState.core.d_val ⋆
        array64 (nvFidTinyCfg.hdr + 32) (Full.hdrTailWords nvFidTinyCfg nvFidTinyState))
        ((bytes64 [1#64, 2#64, 0#64, 0#64] ++
          bytes64 (Full.hdrTailWords nvFidTinyCfg nvFidTinyState)).At nvFidTinyCfg.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := nvFidTinyCfg.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := nvFidTinyCfg.hdr + 32)
        (xs := Full.hdrTailWords nvFidTinyCfg nvFidTinyState)
        1120 (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by decide)
  have hMidScr := nv_sep_reorg nvFidMid_ok (Q := nvFidMidPred nvFidTinyCfg nvFidTinyState ⋆
      (array (t := i32) nvFidTinyCfg.pScratchBuf nvFidTinyState.scratch.scratch_buf ⋆
       region nvFidTinyCfg.pSlack nvFidTinyCfg.slack)) fun _ hm => by
    have hscr : array (t := i32) nvFidTinyCfg.pScratchBuf nvFidTinyState.scratch.scratch_buf =
        emp := by
      funext k
      simp [array, nvFidTinyState]
    have hslk : region nvFidTinyCfg.pSlack nvFidTinyCfg.slack = emp := by
      have hsl : nvFidTinyCfg.slack = 0 := by
        unfold FullCfg.slack nvFidTinyCfg fullFixedBytes valsBytes markBytes
          u32FullBytes fullMinDepthOf; decide
      rw [hsl]; exact region_zero
    rw [hscr, hslk, sep_emp, sep_emp]; exact hm
  have hp_pv : nvFidTinyCfg.pVals = nvFidTinyCfg.hdr + BitVec.ofNat 64 1152 := rfl
  have hAll := nv_join_pair hHdr hMidScr hp_pv (by decide)
  exact nvFid_repack nvFidTinyCfg nvFidTinyState nvFidTinyMem
    (by simpa [nvFidTinyMem, nvFidTinyBytes, List.append_assoc] using hAll.2)

private theorem nv_f0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 := (CNF.sat_iff_all_mem_sat.mp hα) (cnfClause [0])
    (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 := (CNF.sat_iff_all_mem_sat.mp hα) (cnfClause [1])
    (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvFid_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore nvOneLitState.core → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore nvOneLitState.core = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < nvOneLitState.core.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ nvOneLitState.core.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hi0 i hi]; decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hi0 i hi]; exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hp => by rw [hi0 j hj] at hp; exact absurd hp.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by rw [hi0 i hi]; rfl
      level0_rsn_none := fun i hi _ => by rw [hi0 i hi]; rfl
      frame_trail_lt := fun L hL => by rw [hL0 L hL]; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => absurd rfl (hi0 i hi ▸ hne)
      reason_lit_mem := fun i hi hne => absurd rfl (hi0 i hi ▸ hne) }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by simp only [nvOneLitState, nvOneLitScratch,
      List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some],
      Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

/-- Concrete `Mem 64` non-bailout NV (`XPost := False`): `full_bva_steps_cap_fid` on
`scratch_cap = 64` returns `8#32` dynamic matrix rows. -/
theorem nv_fid_bva_steps_cap_64 :
    Func.wp fidBvaEnv full_bva_steps_cap_fid_body (64#64, ()) nvFidBvaMem
      (fun (r, ()) m' => r = 8#32 ∧ 0 < r.toNat ∧ m' = nvFidBvaMem)
      (fun _ _ _ _ => False) :=
  nvFid_wp 0 rfl (fidBvaFns.take 0) (fidBvaFns.drop 1) fidBvaFns[0]
    rfl rfl rfl rfl full_bva_steps_cap_fid_body rfl
    (64#64, ()) nvFidBvaMem _ ⟨rfl, by decide, rfl⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_bva_steps_cap_fid` on `scratch_cap = 0`
returns `0#32` (graceful tiny-workspace fallback). -/
theorem nv_fid_bva_steps_cap_tiny :
    Func.wp fidBvaEnv full_bva_steps_cap_fid_body (0#64, ()) nvFidTinyMem
      (fun (r, ()) m' => r = 0#32 ∧ m' = nvFidTinyMem)
      (fun _ _ _ _ => False) :=
  nvFid_wp 0 rfl (fidBvaFns.take 0) (fidBvaFns.drop 1) fidBvaFns[0]
    rfl rfl rfl rfl full_bva_steps_cap_fid_body rfl
    (0#64, ()) nvFidTinyMem _ ⟨rfl, rfl⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_bva_connect_clauses_fid` on `nvFidBvaMem`. -/
theorem nv_fid_bva_connect_64 :
    Func.wp fidBvaEnv full_bva_connect_clauses_fid_body (nvFidBvaCfg.hdr, ()) nvFidBvaMem
      (fun _ m' => ∃ s', FullDenseInvW nvFidBvaCfg nvOneLitF0 [[0], [1]] s' ∧
        s'.core.cur_vars = 1 ∧ nvOneLitF0.Unsat ∧ FullMem nvFidBvaCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullMem nvFidBvaCfg nvFidBvaState ⋆ emp) nvFidBvaMem := by
    rw [sep_emp]; exact nvFidBvaMem_ok
  refine nvFid_wp 5 rfl (fidBvaFns.take 5) (fidBvaFns.drop 6) fidBvaFns[5]
    rfl rfl rfl rfl full_bva_connect_clauses_fid_body rfl
    (nvFidBvaCfg.hdr, ()) nvFidBvaMem _
    ⟨nvFidBvaCfg, nvOneLitF0, [[0], [1]], nvFidBvaState, emp, rfl, nvFidBva_invW, hm0,
      fun s' m' hw' hcv _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hw', hcv ▸ rfl, nv_f0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` non-bailout NV (`XPost := False`): `full_factor` on `8,192 B`-ready
`nvFidBvaMem` (`scratch_cap = 64`) returning `1#64`. -/
theorem nv_fid_bva_factor_64 :
    Func.wp fidBvaEnv FullFidelityBva.full_factor_body (nvFidBvaCfg.hdr, 100#64, ()) nvFidBvaMem
      (fun (r, ()) m' => ∃ s', FullDenseInv nvFidBvaCfg nvOneLitF0 s' ∧
        1 ≤ s'.core.cur_vars ∧ r = 1#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvFidBvaCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullMem nvFidBvaCfg nvFidBvaState ⋆ emp) nvFidBvaMem := by
    rw [sep_emp]; exact nvFidBvaMem_ok
  refine nvFid_wp 12 rfl (fidBvaFns.take 12) (fidBvaFns.drop 13) fidBvaFns[12]
    rfl rfl rfl rfl FullFidelityBva.full_factor_body rfl
    (nvFidBvaCfg.hdr, 100#64, ()) nvFidBvaMem _
    ⟨nvFidBvaCfg, nvOneLitF0, nvFidBvaState, emp, rfl, nvFidBva_invW.toDense, hm0,
      fun r s' m' hd' hcv' _ hr' hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd', hcv', hr', nv_f0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_factor` graceful tiny fallback on
`nvFidTinyMem` (`scratch_cap = 0`) returning `1#64`. -/
theorem nv_fid_bva_factor_tiny :
    Func.wp fidBvaEnv FullFidelityBva.full_factor_body
      (nvFidTinyCfg.hdr, 100#64, ()) nvFidTinyMem
      (fun (r, ()) m' => ∃ s', FullDenseInv nvFidTinyCfg nvOneLitF0 s' ∧
        1 ≤ s'.core.cur_vars ∧ r = 1#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvFidTinyCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullMem nvFidTinyCfg nvFidTinyState ⋆ emp) nvFidTinyMem := by
    rw [sep_emp]; exact nvFidTinyMem_ok
  refine nvFid_wp 12 rfl (fidBvaFns.take 12) (fidBvaFns.drop 13) fidBvaFns[12]
    rfl rfl rfl rfl FullFidelityBva.full_factor_body rfl
    (nvFidTinyCfg.hdr, 100#64, ()) nvFidTinyMem _
    ⟨nvFidTinyCfg, nvOneLitF0, nvFidTinyState, emp, rfl, nvFidTiny_invW.toDense, hm0,
      fun r s' m' hd' hcv' _ hr' hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd', hcv', hr', nv_f0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_probe_m6` on `nvM6HdrMem` (`FullM6HdrMem`). -/
theorem nv_fid_probe_m6 :
    Func.wp fidBvaEnv FullFidelityBva.full_probe_m6_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  have hsp : m6ProbeSpec (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
    m6ProbeSpec_of (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok
      nvM6ExtWords_ok nvFid_sparseW).toInv rfl hm0
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩
  exact nvFid_wp 13 rfl (fidBvaFns.take 13) (fidBvaFns.drop 14) fidBvaFns[13]
    rfl rfl rfl rfl FullFidelityBva.full_probe_m6_body rfl
    (nvOneLitCfg.hdr, true, ()) nvM6HdrMem _ hsp

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullFidelityBva

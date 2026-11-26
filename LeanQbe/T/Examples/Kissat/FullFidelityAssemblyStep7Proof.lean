/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7Proof1
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2b
import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
import all LeanQbe.T.Examples.Kissat.FullM7WalkProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof1
import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1b
import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2a
import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2c
import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import LeanQbe.T.Examples.Kissat.FullDefSweep
import LeanQbe.T.Examples.Kissat.FullFastSched
import LeanQbe.T.Examples.Kissat.FullM3Backbone
import LeanQbe.T.Examples.Kissat.FullM3CongBva
import LeanQbe.T.Examples.Kissat.FullM5Orch
import LeanQbe.T.Examples.Kissat.FullM6BveFwd
import LeanQbe.T.Examples.Kissat.FullM6BcpS15
import LeanQbe.T.Examples.Kissat.FullM6S15Bridge
import LeanQbe.T.Examples.Kissat.FullM6Hdr
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
import LeanQbe.T.Examples.Kissat.FullM7Proof
import LeanQbe.T.Examples.Kissat.FullM7Search
import LeanQbe.T.Examples.Kissat.FullM7Walk
import LeanQbe.T.Examples.Kissat.FullM8CoreParity
import LeanQbe.T.Examples.Kissat.FullM8FidV12
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Step-7 Proof (`FullFidelityAssemblyStep7Proof`, `501` fns)

Certifies `FullFidelityAssemblyStep7.fidStep7Module` (`501` fns, `0` externs, `0` exits) via
`PatchModule.patchBundle_moduleOk` + `FullFidelityAssemblyUtil`:
1. Rewires `full_walk_fid_step7_wp` (`FullM7FidelityCore.full_walk_fid_body` under `step7CbInvSpec`,
   alongside `FullFidelityAssemblyStep7Proof0.m8_ana_failed_lit_m6_hdr_step7_wp`).
2. `fidStep7Bundle : PatchBundle` layering `fidStep7Repls` (`20` repls) + `fidStep7Befores`
   (`2` helpers: `full_sort_bin_watches_fid`, `full_bva_upd_lit_fid`) + `fidStep7RewiredRows`
   (`7` caller rewires) onto `fidModule` (`499` fns -> `501` fns).
3. Closed `501/501` `fidStep7_moduleOk`, `fidStep7_tableImpl`, `fidStep7Env_noExit`,
   `fidStep7_solve_bytes_sound`, `fidStep7_solve_bytes_host_sound`, `fidStep7_unsat_nv`
   (`XPost := False`, `std3`), and `fidStep7UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullDefSweep
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM5Orch
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Walk
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0a
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0c
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` Over `fidModule` (`501/501` Fns) -/

/-- Flat `499`-row base specification table for Step 6 (`fidModule`). -/
private abbrev fidEnvTable : List SpecEntry :=
  fidBundle.frontTable ++ fidBundle.baseTable

/-- `7` rewired Step-6 function contracts propagated through Step 7. -/
def fidStep7RewiredRows : List SpecEntry :=
  [ ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
  , ⟨"full_restore_bump_ana_m6_hdr", [i64], [], m6aRestoreBumpAnaSpecP M6ExtW2bPres, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m6aAnaFailedLitSpecP M6ExtW2bPres, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_walk_m7", [i64], [], Full.fullWalkSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [],
      FullFidelityStep7.step7InitFreshVarSpec, true⟩ ]

/-- `20` replacement specification rows matching `FullFidelityStep7.fidStep7Repls`. -/
def fidStep7ReplRows : List SpecEntry :=
  [ ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapOfSpec 8388608, true⟩
  , ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpecP M6ExtW2bPres, true⟩
  , ⟨"full_sort_tmp", [i64], [], step7SortTmpSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩
  , ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], step7CbInvSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], FullFidelityStep7.step7BvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullFidelityStep7.step7BvaTryLitSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveVarKeySpec, true⟩
  , ⟨"full_eliminate_m7", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ ]

/-- `2` inserted helper specification rows matching `FullFidelityStep7.fidStep7Befores`. -/
def fidStep7BeforeRows : List SpecEntry :=
  [ ⟨"full_sort_bin_watches_fid", [i64], [], FullFidelityStep7.step7SortBinWatchesSpec, true⟩
  , ⟨"full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32],
      FullFidelityStep7.step7BvaUpdLitSpec, true⟩ ]

/-- Step-7 `PatchBundle` composing `fidModule` + `FullFidelityStep7` (`501` fns). -/
def fidStep7Bundle : PatchBundle where
  baseMod := fidModule
  baseTable := fidEnvTable
  baseOk := fid_moduleOk
  repls := FullFidelityStep7.fidStep7Repls
  replRows := fidStep7ReplRows
  befores := FullFidelityStep7.fidStep7Befores
  beforeRows := fidStep7BeforeRows
  rewiredRows := fidStep7RewiredRows

/-- Closed `Env` for `fidStep7Module` (`501` fns). -/
def fidStep7Env : Env :=
  patchEnv fidStep7Bundle

theorem fidStep7_externs_empty : fidStep7Module.externs = [] :=
  fid_externs_empty

theorem fidStep7Fns_length : fidStep7Fns.length = 501 := by
  t_kernel_rfl

private def fidStep7FrontNames : List Sym :=
  [ "full_init_state_m5", "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr"
  , "full_min_shrink_m6", "full_analyze_core_m6", "full_walk_m7", "full_init_fresh_var"
  , "full_calc_max_v", "full_calc_scr_cap_m5", "m6_hdr_init", "full_reduce"
  , "full_reduce_m6", "full_bump_analyzed_m6_hdr", "full_sort_tmp", "full_learn_clause"
  , "full_walk_cb_inv_m7", "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr"
  , "full_rebuild_watches", "full_bva_commit", "full_bva_try_lit", "full_factor"
  , "full_bve_var_key_m7", "full_eliminate_m7", "full_eliminate_m6"
  , "full_probe_m6", "full_search_m6"
  , "full_sort_bin_watches_fid", "full_bva_upd_lit_fid" ]

private theorem fidStep7_frontNames_eq :
    fidStep7Bundle.frontTable.map SpecEntry.name = fidStep7FrontNames :=
  rfl

private theorem fidStep7_front_nodup :
    (fidStep7Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep7_frontNames_eq]
  decide

private theorem fidStep7_replSigs_batch :
    [47, 49, 55, 112, 113, 120, 131, 148, 159, 226, 227, 246,
      435, 436, 439, 465, 472, 473, 490, 494].map (fun i => fidFns[i]?.map Fn.sig) =
      [ some ("full_calc_max_v", [i64, i64, i64, i64], [i64])
      , some ("full_calc_scr_cap_m5", [i64], [i64])
      , some ("m6_hdr_init", [i64], [])
      , some ("full_reduce", [i64, .bool], [i64])
      , some ("full_reduce_m6", [i64, .bool], [i64])
      , some ("full_bump_analyzed_m6_hdr", [i64], [])
      , some ("full_sort_tmp", [i64], [])
      , some ("full_learn_clause", [i64, i64], [i64])
      , some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64])
      , some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])
      , some ("full_vivify_m6_hdr", [i64], [i64])
      , some ("full_rebuild_watches", [i64], [i64])
      , some ("full_bva_commit", [i64, i32], [.bool])
      , some ("full_bva_try_lit", [i64, i32, i64], [.bool])
      , some ("full_factor", [i64, i64], [i64])
      , some ("full_bve_var_key_m7", [i64, i32], [i64])
      , some ("full_eliminate_m7", [i64, .bool], [i64])
      , some ("full_eliminate_m6", [i64, .bool], [i64])
      , some ("full_probe_m6", [i64, .bool], [i64])
      , some ("full_search_m6", [i64], [i64]) ] := by
  t_kernel_rfl

private theorem fidStep7_slot {i : Nat} {s : SigEntry}
    (hi : fidFns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidFns, g.sig = s := by
  cases h : fidFns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidStep7Module_replSigs_ok :
    ∀ r ∈ FullFidelityStep7.fidStep7Repls, ∀ g ∈ fidModule.fns,
      r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidFns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidFns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fidStep7_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have hnd : (fidFns.map Fn.name).Nodup :=
      (List.nodup_append.mp fidModule_names_nodup).1
    have heq := nodup_name_eq Fn.name hnd hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [FullFidelityStep7.fidStep7Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (slotSig_at fidStep7_replSigs_batch 0 47
        (some ("full_calc_max_v", [i64, i64, i64, i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 1 49
        (some ("full_calc_scr_cap_m5", [i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 2 55
        (some ("m6_hdr_init", [i64], []))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 3 112
        (some ("full_reduce", [i64, .bool], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 4 113
        (some ("full_reduce_m6", [i64, .bool], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 5 120
        (some ("full_bump_analyzed_m6_hdr", [i64], []))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 6 131
        (some ("full_sort_tmp", [i64], []))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 7 148
        (some ("full_learn_clause", [i64, i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 8 159
        (some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 9 226
        (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 10 227
        (some ("full_vivify_m6_hdr", [i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 11 246
        (some ("full_rebuild_watches", [i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 12 435
        (some ("full_bva_commit", [i64, i32], [.bool]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 13 436
        (some ("full_bva_try_lit", [i64, i32, i64], [.bool]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 14 439
        (some ("full_factor", [i64, i64], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 15 465
        (some ("full_bve_var_key_m7", [i64, i32], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 16 472
        (some ("full_eliminate_m7", [i64, .bool], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 17 473
        (some ("full_eliminate_m6", [i64, .bool], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 18 490
        (some ("full_probe_m6", [i64, .bool], [i64]))) rfl hnm
  · exact hslot (slotSig_at fidStep7_replSigs_batch 19 494
        (some ("full_search_m6", [i64], [i64]))) rfl hnm

theorem fidStep7Module_names_nodup : fidStep7Module.namesNodup :=
  LeanQbe.T.Module.namesNodup_of_checkNamesNodup (by t_kernel_rfl)

private theorem fidStep7Module_patchCallsOk :
    checkPatchCallsOk fidModule FullFidelityStep7.fidStep7Repls
      FullFidelityStep7.fidStep7Befores = true := by
  t_kernel_rfl

private theorem fid7_isSome_find_of_name_mem {tbl : List SpecEntry} {nm : Sym}
    (h : nm ∈ tbl.map SpecEntry.name) : (tbl.find? (·.name == nm)).isSome = true := by
  obtain ⟨e, he, hnm⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hnm⟩

private theorem fidStep7_front_covered :
    ∀ fn, (fn ∈ FullFidelityStep7.fidStep7Repls ∨
        fn ∈ FullFidelityStep7.fidStep7Befores.flatMap Prod.snd) →
      (fidStep7Bundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  refine fid7_isSome_find_of_name_mem ?_
  rw [fidStep7_frontNames_eq]
  rcases hfn with hr | hb
  · simp only [FullFidelityStep7.fidStep7Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [FullFidelityStep7.fidStep7Befores, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide

/-! ## 2. Fast Table Lookup, Elimination, Isolation (`bad`), & Agree Helpers -/

private abbrev Fid7EnvSpec (nm : Sym) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ a m Q X, sp a m Q X → fidStep7Env nm as bs a m Q X

private theorem fid7_find_none_front7 {f : Sym}
    (hf7 : !(fidStep7FrontNames.contains f) = true) :
    fidStep7Bundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names fidStep7_frontNames_eq hf7

private theorem fid7_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep7Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep7Bundle fidStep7_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fid7_of_fidEnv {f : Sym} {as bs : List Ty}
    (hf7 : !(fidStep7FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidEnv f as bs xs m Q X) :
    fidStep7Env f as bs xs m Q X := by
  change patchEnv fidStep7Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 hf7)]
  exact h

private theorem fid7_step6FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidBundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (fid_frontRow i nm sp hi hno a m Q X hs)

private theorem fid7_step5FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep5Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (by
    change patchEnv fidBundle nm as bs a m Q X
    rw [patchEnv_base_eq fidBundle (fid_find_none_front hf6)]
    exact patchEnv_of_front_mem fidStep5Bundle fidStep5_front_nodup
      (List.mem_of_getElem? hi) (hno a m Q X hs))

private theorem fid7_step4FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep4Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (fid_step4FrontRow i nm sp hi hf6 hf5 hno a m Q X hs)

private theorem fid7_step3FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep3Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (fid_step3FrontRow i nm sp hi hf6 hf5 hf4 hno a m Q X hs)

private theorem fid7_step2FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep2Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (fid_step2FrontRow i nm sp hi hf6 hf5 hf4 hf3 hno a m Q X hs)

private theorem fid7_m7Row {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (fid_m7Row hmem hf6 hf5 hf4 hf3 hf2 hf1 hnmf hncp hno a m Q X hs)

private theorem fid7_m7Row_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : m7FidBaseTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp :=
  fid7_m7Row (List.mem_of_getElem? hi) hf7 hf6 hf5 hf4 hf3 hf2 hf1 hnmf hncp hno

private theorem fid7_extraRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : mfExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h)
    (hne : nm ∉ m8CpExclNames := by decide) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7
    (fid_of_fidBase hf6 hf5 hf4 hf3 hf2 hf1 (fid_extraRow i nm as bs sp hi hno hne a m Q X hs))

private theorem fid7_minHelpRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : m8MinHelperRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf7 : !(fidStep7FrontNames.contains nm) = true := by decide)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid7EnvSpec nm sp := fun a m Q X hs =>
  fid7_of_fidEnv hf7 (fid_of_fidBase hf6 hf5 hf4 hf3 hf2 hf1
    (fidBaseEnv_of_minHelp (List.mem_of_getElem? hi)
      (Env.ofTable_of_mem (List.mem_of_getElem? hi) m8MinHelperRows_nodup (hno a m Q X hs))))

private theorem fid7_elim_to_fidBase {nm : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidEnvTable nm as bs xs m Q X)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide) :
    fidBaseEnv nm as bs xs m Q X := by
  change patchEnv fidBundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front hf6)] at h
  exact fid_elim_to_fidBase h hf5 hf4 hf3 hf2 hf1

private theorem fid7_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidEnvTable nm as bs xs m Q X)
    (hf6 : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide)
    (hneSw : !(m8SwNamesLit.contains nm) = true := by decide)
    (hne1 : nm ∉ m8CpExclNames := by decide)
    (hne2 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (hne3 : nm ∉ FullFidelityBase.fidBveHelperRows.map SpecEntry.name := by decide)
    (hne4 : nm ≠ "full_extend_push2" := by decide)
    (hne5 : nm ≠ "full_cong_enq_var" := by decide)
    (hne6 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne7 : nm ≠ "full_cong_worklist" := by decide) :
    sp xs m Q (fun _ _ _ _ => False) :=
  fidBaseEnv_elim_m7Base hmem (fid7_elim_to_fidBase h hf6 hf5 hf4 hf3 hf2 hf1)
    hneEx hneSw hne1 hne2 hne3 hne4 hne5 hne6 hne7

private theorem fid7_of_prefix_mem {nm : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {P : Post bs} {E : XPost}
    {pfx base : List SpecEntry}
    (hmem : ∃ e ∈ pfx, e.name = nm ∧ e.as = as ∧ e.rs = bs)
    (htbl : Env.ofTable (pfx ++ base) nm as bs xs m P E) :
    Env.ofTable pfx nm as bs xs m P E := by
  induction pfx with
  | nil => rcases hmem with ⟨_, h0, _⟩; nomatch h0
  | cons a t ih =>
    rw [List.cons_append] at htbl
    rcases htbl with ⟨hsig, hcast⟩ | ⟨hne, htl⟩
    · exact Or.inl ⟨hsig, hcast⟩
    · rcases hmem with ⟨e', he', hnm', has', hrs'⟩
      rcases List.mem_cons.mp he' with rfl | ht
      · exact absurd ⟨hnm', has', hrs'⟩ hne
      · exact Or.inr ⟨hne, ih ⟨e', ht, hnm', has', hrs'⟩ htl⟩

private def fidStep7SkipNames : List Sym :=
  FullFidelityStep7.fidStep7Repls.map Fn.name ++
    [ "full_init_state_m5", "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr"
    , "full_min_shrink_m6", "full_analyze_core_m6", "full_walk_m7", "full_init_fresh_var" ]

private def fidStep7BadNames : List Sym :=
  [ "full_calc_scr_cap_m5", "full_bump_analyzed_m6_hdr", "full_restore_bump_ana_m6_hdr"
  , "full_ana_failed_lit_m6_hdr", "full_sort_tmp", "full_walk_cb_inv_m7"
  , "full_init_fresh_var", "full_bva_commit", "full_bva_try_lit" ]

private theorem fidStep7_noCallBad_aux :
    checkNoCallBad fidStep7SkipNames fidStep7BadNames fidFns = true := by
  t_kernel_rfl

private theorem fidStep7_noCallBad :
    ∀ fn ∈ fidModule.fns,
      fidStep7Bundle.repls.find? (·.name == fn.name) = none →
      fidStep7Bundle.frontTable.find? (·.name == fn.name) = none →
      noCallInFn fidStep7BadNames fn = true := by
  intro fn hmem hr hfind
  have hcell : (fidStep7SkipNames.contains fn.name || noCallInFn fidStep7BadNames fn) = true :=
    List.all_eq_true.mp fidStep7_noCallBad_aux fn hmem
  rcases (Bool.or_eq_true _ _).mp hcell with hskip | hok
  · exfalso
    have hsub : fidStep7SkipNames.all (fun s => fidStep7FrontNames.contains s) = true := by
      t_kernel_rfl
    have hfront_mem : fn.name ∈ fidStep7FrontNames :=
      List.contains_iff_mem.mp (List.all_eq_true.mp hsub fn.name
        (List.contains_iff_mem.mp hskip))
    have hsome := fid7_isSome_find_of_name_mem (fidStep7_frontNames_eq.symm ▸ hfront_mem)
    change (fidStep7Bundle.frontTable.find? (·.name == fn.name)) = none at hfind
    rw [hfind] at hsome
    cases hsome
  · exact hok

private theorem fidStep7_before_not_in_step6 :
    (fidFns.map Fn.name).contains "full_sort_bin_watches_fid" = false ∧
    (fidFns.map Fn.name).contains "full_bva_upd_lit_fid" = false :=
  ⟨by t_kernel_rfl, by t_kernel_rfl⟩

private theorem fidStep7_agree :
    ∀ s ∈ fidModule.sigs, s.1 ∉ fidStep7BadNames →
      ∀ xs m P E, Env.ofTable fidEnvTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidStep7Bundle s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs hnb xs m P E hBase
  cases hf : fidStep7Bundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidStep7Bundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hsig_in : e.name ∈ fidFns.map Fn.name := by
        have hm := hs
        rw [LeanQbe.T.Module.sigs, fid_externs_empty, List.map_nil, List.append_nil] at hm
        obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
        exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
      have hPush :
          ∀ hmem : e ∈ fidStep7Bundle.frontTable, e.eff xs m P E →
            patchEnv fidStep7Bundle e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidStep7Bundle fidStep7_front_nodup hmem hs'
      have hFail : ∀ nm0 ∈ fidStep7BadNames, e.name = nm0 →
          patchEnv fidStep7Bundle e.name e.as e.rs xs m P E := fun nm0 hnm0 heq =>
        absurd (heq ▸ hnm0) hnb
      have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
      have he0 := he
      simp only [fidStep7Bundle, PatchBundle.frontTable, fidStep7RewiredRows, fidStep7ReplRows,
        fidStep7BeforeRows, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact hPush he0 (fid7_elim_m7Base (List.mem_of_getElem? (i := 50) (by rfl)) hBase)
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · have hs0 := fidBaseEnv_elim_repl (r := fidBaseReplRows[0]'(by decide))
          (List.getElem_mem _) (fid7_elim_to_fidBase hBase)
        exact hPush he0 (m8MinShrinkSpec_monoX hs0)
      · exact hPush he0 (m6HdrAnalyzeSpec_monoX
          (fid7_elim_m7Base (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.analyzeCoreM6) hBase))
      · have hsw := m8SwFlatTable_iff.mp
          (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide)
            (fid7_elim_to_fidBase hBase))
        have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
          (by decide) (by decide) (by decide) hsw
        have hwk : Full.fullWalkSpec xs m P E := by
          cases hm7 with
          | base hne _ => exact absurd (by decide : "full_walk_m7" ∈ mfExclNames) hne
          | extra hex => exact mf_extra_elim (List.mem_of_getElem? (i := 53) rfl) hex
        exact hPush he0 hwk
      · exact hFail _ (by decide) rfl
      · exact hPush he0 (fid7_elim_m7Base m7FidBase_calcMaxV_mem hBase)
      · exact hFail _ (by decide) rfl
      · have hHdrMem : (⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩ : SpecEntry) ∈
            m7FidBaseTable := m7FidBase_part1_mem _ (by
          unfold m7FidRowsPart1; (iterate 11 apply List.mem_append_right)
          exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
        have hsw := m8SwFlatTable_iff.mp
          (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide)
            (fid7_elim_to_fidBase hBase))
        have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
          (by decide) (by decide) (by decide) hsw
        have hhi : m6HdrInitSpec xs m P (fun _ _ _ _ => False) := by
          cases hm7 with
          | base _ hbm => exact m7FidBase_elim_of_mem hHdrMem hbm
          | extra hex => exact mf_extra_elim (List.mem_of_getElem? (i := 0) rfl) hex
        exact hPush he0 hhi
      · change patchEnv fidBundle "full_reduce" [i64, .bool] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        change patchEnv fidStep5Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at hBase
        change patchEnv fidStep4Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at hBase
        change patchEnv fidStep3Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at hBase
        have hrow : fidStep2Bundle.frontTable[4]? =
            some ⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩ := by t_kernel_rfl
        have hf2 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup
          (List.mem_of_getElem? hrow) hf2
        exact hPush he0 hc
      · change patchEnv fidBundle "full_reduce_m6" [i64, .bool] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        change patchEnv fidStep5Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at hBase
        change patchEnv fidStep4Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at hBase
        change patchEnv fidStep3Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at hBase
        have hrow : fidStep2Bundle.frontTable[5]? =
            some ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩ := by t_kernel_rfl
        have hf2 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup
          (List.mem_of_getElem? hrow) hf2
        exact hPush he0 hc
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hPush he0 (fid7_elim_m7Base hc2p.learnClause hBase)
      · exact hFail _ (by decide) rfl
      · change patchEnv fidBundle "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64]
          xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        change patchEnv fidStep5Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at hBase
        have hrow : fidStep4Bundle.frontTable[1]? =
            some ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64],
              m6aVivifyTierSpec, true⟩ := by rfl
        have hf4 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep4_front_nodup
          (List.mem_of_getElem? hrow) hf4
        exact hPush he0 hc
      · change patchEnv fidBundle "full_vivify_m6_hdr" [i64] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        change patchEnv fidStep5Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at hBase
        have hrow : fidStep4Bundle.frontTable[2]? =
            some ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩ := by rfl
        have hf4 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep4_front_nodup
          (List.mem_of_getElem? hrow) hf4
        exact hPush he0 hc
      · change patchEnv fidBundle "full_rebuild_watches" [i64] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        change patchEnv fidStep5Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at hBase
        change patchEnv fidStep4Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at hBase
        change patchEnv fidStep3Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at hBase
        have hrow : fidStep2Bundle.frontTable[21]? =
            some ⟨"full_rebuild_watches", [i64], [i64],
              Full.fullRebuildWatchesSpec, true⟩ := by t_kernel_rfl
        have hf2 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup
          (List.mem_of_getElem? hrow) hf2
        exact hPush he0 hc
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · have hrow : fidBundle.frontTable[5]? =
            some ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩ := by rfl
        have hf6 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fid_front_nodup (List.mem_of_getElem? hrow) hf6
        exact hPush he0 hc
      · change patchEnv fidBundle "full_bve_var_key_m7" [i64, i32] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        have hrow : fidStep5Bundle.frontTable[2]? =
            some ⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveVarKeySpec, true⟩ := by rfl
        have hf5 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep5_front_nodup
          (List.mem_of_getElem? hrow) hf5
        exact hPush he0 hc
      · exact hPush he0 (fid7_elim_m7Base
          (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 41) rfl)) hBase)
      · change patchEnv fidBundle "full_eliminate_m6" [i64, .bool] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        have hrow : fidStep5Bundle.frontTable[4]? =
            some ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ := by rfl
        have hf5 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep5_front_nodup
          (List.mem_of_getElem? hrow) hf5
        exact hPush he0 hc
      · have hrow : fidBundle.frontTable[6]? =
            some ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ := by rfl
        have hf6 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fid_front_nodup (List.mem_of_getElem? hrow) hf6
        exact hPush he0 hc
      · change patchEnv fidBundle "full_search_m6" [i64] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at hBase
        change patchEnv fidStep5Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at hBase
        change patchEnv fidStep4Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at hBase
        change patchEnv fidStep3Bundle _ _ _ xs m P E at hBase
        rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at hBase
        have hrow : fidStep2Bundle.frontTable[25]? =
            some ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ := by t_kernel_rfl
        have hf2 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup
          (List.mem_of_getElem? hrow) hf2
        exact hPush he0 hc
      · have hno := fidStep7_before_not_in_step6.1
        have hm : (fidFns.map Fn.name).contains "full_sort_bin_watches_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno := fidStep7_before_not_in_step6.2
        have hm : (fidFns.map Fn.name).contains "full_bva_upd_lit_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
    · have hne : ∀ e' ∈ fidStep7Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep7_front_nodup he' he
          (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep7Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift fidStep7Bundle.frontTable hne

/-! ## 3. Front-Table Implementation Helpers & `fidStep7_moduleOk` (`501/501`) -/

private theorem fidStep7_fn_eq_before {fn b : Fn} {tgt : Sym} {ins : List Fn}
    (hfn : fn ∈ fidStep7Module.fns)
    (hpair : (tgt, ins) ∈ FullFidelityStep7.fidStep7Befores)
    (hb : b ∈ ins) (htgt : ∃ g0 ∈ fidFns, g0.name = tgt) (hnm : b.name = fn.name) :
    fn = b := by
  have hModNd : (fidStep7Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep7Module_names_nodup).1
  obtain ⟨g0, hg0, hgn⟩ := htgt
  have hbm : b ∈ fidStep7Module.fns := by
    change b ∈ patchFns FullFidelityStep7.fidStep7Repls FullFidelityStep7.fidStep7Befores fidFns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    unfold patchInsAt
    simp only [FullFidelityStep7.fidStep7Befores] at hpair ⊢
    rcases List.mem_cons.mp hpair with h0 | h1
    · obtain ⟨ht0, hi0⟩ := Prod.mk.inj h0
      subst ht0; subst hi0; simp only [hgn]; exact hb
    · obtain ⟨ht1, hi1⟩ := Prod.mk.inj (List.mem_singleton.mp h1)
      subst ht1; subst hi1; simp only [hgn]; exact hb
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fidStep7_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidStep7Module.fns) (hr : r ∈ FullFidelityStep7.fidStep7Repls)
    {idx : Nat} {s : SigEntry} (hslot : fidFns[idx]?.map Fn.sig = some s)
    (hrn : r.name = s.1) (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidStep7Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep7Module_names_nodup).1
  obtain ⟨g, hg, hgs⟩ := fidStep7_slot hslot
  have hrm : r ∈ fidStep7Module.fns :=
    mem_patchFns_of_repl (by decide) hr hg (hrn.trans (congrArg Prod.fst hgs).symm)
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fidStep7_fn_eq_base {fn g : Fn}
    (hfn : fn ∈ fidStep7Module.fns) (idx : Nat) (hi : fidFns[idx]? = some g)
    (hne : FullFidelityStep7.fidStep7Repls.find? (·.name == g.name) = none := by rfl)
    (hnm : g.name = fn.name) : fn = g := by
  have hModNd : (fidStep7Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep7Module_names_nodup).1
  have hg : g ∈ fidFns := List.mem_of_getElem? hi
  have hgm : g ∈ fidStep7Module.fns := by
    change g ∈ patchFns FullFidelityStep7.fidStep7Repls FullFidelityStep7.fidStep7Befores fidFns
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨g, hg, Or.inr (by simp [hne])⟩
  exact nodup_name_eq Fn.name hModNd hfn hgm hnm.symm

private theorem fidStep7_front_impl :
    ∀ fn e, fn ∈ fidStep7Bundle.patchedMod.fns →
      fidStep7Bundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidStep7Env fn e := by
  intro fn e hfn hf
  change fn ∈ fidStep7Module.fns at hfn
  have he : e ∈ fidStep7Bundle.frontTable := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  -- Layer 7 self rows
  have r7CalcMaxV := fid7_frontRow 7 "full_calc_max_v" Full.fullCalcMaxVSpec
  have r7ScrCap := fid7_frontRow 8 "full_calc_scr_cap_m5" (FullM5Orch.fullCalcScrCapOfSpec 8388608)
    rfl (FullM5Orch.fullCalcScrCapOfSpec_noExit 8388608)
  have r7Reduce := fid7_frontRow 10 "full_reduce" Full.fullReduceSpec
  have r7ReduceM6 := fid7_frontRow 11 "full_reduce_m6" m6ReduceSpec
    rfl (fun _ _ _ _ h => m6ReduceSpec_monoX h)
  have r7BumpAna := fid7_frontRow 12 "full_bump_analyzed_m6_hdr"
    (m6aBumpAnalyzedSpecP M6ExtW2bPres) rfl (fun _ _ _ _ h => m6aBumpAnalyzedSpecP_monoXP h)
  have r7Restore := fid7_frontRow 1 "full_restore_bump_ana_m6_hdr"
    (m6aRestoreBumpAnaSpecP M6ExtW2bPres) rfl (fun _ _ _ _ h => m6aRestoreBumpAnaSpecP_monoXP h)
  have r7AnaFailed := fid7_frontRow 2 "full_ana_failed_lit_m6_hdr"
    (m6aAnaFailedLitSpecP M6ExtW2bPres) rfl (fun _ _ _ _ h => m6aAnaFailedLitSpecP_monoXP h)
  have r7MinShrink := fid7_frontRow 3 "full_min_shrink_m6" m8MinShrinkSpec
    rfl (fun _ _ _ _ h => m8MinShrinkSpec_monoX h)
  have r7SortTmp := fid7_frontRow 13 "full_sort_tmp" step7SortTmpSpec
    rfl (fun _ _ _ _ h => step7SortTmpSpec_monoX h)
  have r7Learn := fid7_frontRow 14 "full_learn_clause" Full.fullLearnClauseSpec
  have r7CbInv := fid7_frontRow 15 "full_walk_cb_inv_m7" step7CbInvSpec
    rfl (fun _ _ _ _ h => step7CbInvSpec_noExit _ _ _ _ h)
  have r7VivTier := fid7_frontRow 16 "full_vivify_tier_m6_hdr" m6aVivifyTierSpec
    rfl (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)
  have r7Vivify := fid7_frontRow 17 "full_vivify_m6_hdr" m6aVivifySpec
    rfl (fun _ _ _ _ h => m6aVivifySpec_monoX h)
  have r7SortBin := fid7_frontRow 27 "full_sort_bin_watches_fid"
    FullFidelityStep7.step7SortBinWatchesSpec
    rfl (fun _ _ _ _ h => FullFidelityStep7.step7SortBinWatchesSpec_monoX h)
  have r7Rebuild := fid7_frontRow 18 "full_rebuild_watches" Full.fullRebuildWatchesSpec
  have r7InitFresh := fid7_frontRow 6 "full_init_fresh_var"
    FullFidelityStep7.step7InitFreshVarSpec
    rfl (fun _ _ _ _ h => FullFidelityStep7.step7InitFreshVarSpec_monoX h)
  have r7BvaCommit := fid7_frontRow 19 "full_bva_commit"
    FullFidelityStep7.step7BvaCommitSpec
    rfl (fun _ _ _ _ h => FullFidelityStep7.step7BvaCommitSpec_monoX h)
  have r7BvaTryLit := fid7_frontRow 20 "full_bva_try_lit"
    FullFidelityStep7.step7BvaTryLitSpec
    rfl (fun _ _ _ _ h => FullFidelityStep7.step7BvaTryLitSpec_monoX h)
  have r7BvaUpdLit := fid7_frontRow 28 "full_bva_upd_lit_fid"
    FullFidelityStep7.step7BvaUpdLitSpec
    rfl (fun _ _ _ _ h => FullFidelityStep7.step7BvaUpdLitSpec_monoX h)
  have r7Factor := fid7_frontRow 21 "full_factor" FullBvaHeap.fullFactorHeapSpec
  -- Step 6/5/4/3/2 unchanged rows
  have r6Scan := fid7_step6FrontRow 0 "full_bva_scan_cands" fidBvaScanCandsSpec
  have r6Pick := fid7_step6FrontRow 1 "full_bva_pick_cand" fullBvaPickCandSpec
  have r6Filt := fid7_step6FrontRow 2 "full_bva_filter_row" fidBvaFilterRowSpec
  have r6Steps := fid7_step6FrontRow 7 "full_bva_steps_cap_fid" fidBvaStepsCapSpec
  have r6Up := fid7_step6FrontRow 9 "full_fheap_up_fid" fidFheapUpSpec
  have r6Down := fid7_step6FrontRow 10 "full_fheap_down_fid" fidFheapDownSpec
  have r6Deg := fid7_step6FrontRow 11 "full_bva_count_lit_deg_fid" fidBvaCountLitDegSpec
  have r6Conn := fid7_step6FrontRow 12 "full_bva_connect_clauses_fid" fidBvaConnectClausesSpec
  have r5ElimBve := fid7_step5FrontRow 3 "full_elim_bve_m7" m3ElimBveSpec
  have r4Unwatch := fid7_step4FrontRow 0 "full_unwatch_large" fullUnwatchLargeSpec
  have r4VivCol := fid7_step4FrontRow 6 "full_viv_collect_fid" fullVivCollectFidSpec
  have r4VivCnt := fid7_step4FrontRow 7 "full_viv_count_fid" fullVivCountFidSpec
  have r4VivSort := fid7_step4FrontRow 9 "full_viv_sort_fid" fullVivSortFidSpec
  have r3Cong := fid7_step3FrontRow 19 "full_congruence_dense"
    FullM3CongBva.m3CongruenceDenseSpec
  have r3Sync := fid7_step3FrontRow 20 "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] [])
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rPropBcpS15 : Fid7EnvSpec "full_propagate" FullM6BcpS15.fullBcpS15Spec :=
    fid7_step2FrontRow 1 "full_propagate" FullM6BcpS15.fullBcpS15Spec
  have r2VivCl := fid7_step2FrontRow 13 "full_viv_clause_m6" fullVivClauseM6Spec
  have r2Bone := fid7_step2FrontRow 16 "full_backbone_m6" fullBackboneSpec
  have r2Subst := fid7_step2FrontRow 19 "full_substitute" fullSubstituteSpec
  have r2Enter := fid7_step2FrontRow 20 "full_enter_dense" schedEnterDenseSpec
  have r2Lucky := fid7_step2FrontRow 23 "full_lucky_late_m7" m7LuckyLateSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7LuckyLateSpec_monoX h)
  have r2Deduce := fid7_step2FrontRow 32 "full_deduce_1uip_m6_hdr" m6Deduce1uipHdrSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6Deduce1uipHdrSpec_monoX h)
  have r2Decide := fid7_step2FrontRow 34 "m6_hdr_decide_fid" m6HdrDecideSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrDecideSpec_monoX h)
  -- Base / m7FidBase / mfExtra / minHelper rows
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  have rHdr := fid7_m7Row_at 5 "kissat_parse_header" Kissat.kissatParseHeaderSpec
  have rIsqrt := fid7_m7Row hc1.isqrt
  have rIlog10 := fid7_m7Row hc1.ilog10
  have rRngNext := fid7_m7Row hc1.rngNext
  have rArenaNext := fid7_m7Row hc1.arenaNext
  have rAllocCl := fid7_m7Row hc1.allocCl
  have rBumpVar := fid7_m7Row hc1.bumpVar
  have rBumpDecay := fid7_m7Row hc1.bumpDecay
  have rQueueMtf := fid7_m7Row hc1.queueMtf
  have rTickRel := fid7_m7Row hc1.tickRel
  have rLog10M7 := fid7_m7Row hc1.log10Q16M7
    (hno := fun _ _ _ _ h => m7Log10Q16Spec_monoX h)
  have rScaleM5 := fid7_m7Row hc1.scaleDeltaM5
  have rEma := fid7_m7Row hc1.emaUpdate
  have rScale := fid7_m7Row hc1.scaleDelta
  have rAssignLvl := fid7_m7Row hc1.assignLvl
  have rBacktrack := fid7_m7Row hc1.backtrack
  have rAddCl := fid7_m7Row hc1.addClause
  have rZt1 := fid7_m7Row_at 41 "full_zero_tables1" Full.fullZeroTables1Spec
  have rZt2 := fid7_m7Row_at 42 "full_zero_tables2" Full.fullZeroTables2Spec
  have rFixed := fid7_m7Row_at 43 "full_fixed_bytes" Full.fullFixedBytesSpec
  have rInitHdr := fid7_m7Row_at 45 "full_init_hdr" Full.fullInitHdrSpec
  have rExtCap := fid7_m7Row_at 47 "full_calc_ext_cap_m5" fullCalcExtCapM5Spec
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fullCalcExtCapM5Spec_noExit
  have rInitArenas := fid7_m7Row_at 49 "full_init_arenas" Full.fullInitArenasSpec
  have rRecomp := fid7_m7Row_at 61 "m6_hdr_recompute_tiers" (m6HdrW2aSpec [] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetT1 := fid7_m7Row_at 64 "m6_hdr_get_tier1" (m6HdrW2aSpec [.bool] [i64])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetT2 := fid7_m7Row_at 65 "m6_hdr_get_tier2" (m6HdrW2aSpec [.bool] [i64])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rDelay := fid7_m7Row_at 66 "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rBumpDelay := fid7_m7Row_at 67 "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rReduceDelay := fid7_m7Row_at 68 "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetWm := fid7_m7Row_at 70 "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rSetWm := fid7_m7Row_at 71 "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rDrAllow := fid7_m7Row hc1.hdrDrAllow
    (hno := fun _ _ _ _ h => m6HdrDrAllowSpec_monoX h)
  have rRecompOld := fid7_m7Row_at 89 "full_recompute_tiers" Full.fullRecomputeTiersSpec
  have rSortReds := fid7_m7Row_at 109 "full_sort_reds" Full.fullSortRedsSpec
  have rClearAna := fid7_m7Row_at 115 "full_clear_ana" Full.fullClearAnaSpec
  have rDetNew := fid7_m7Row_at 140 "full_det_new_level" Full.fullDetNewLevelSpec
  have rOneLit := fid7_m7Row_at 141 "full_one_lit_confl" Full.fullOneLitConflSpec
  have rEagerSub := fid7_m7Row_at 142 "full_eager_subsume" Full.fullEagerSubsumeSpec
  have rAnalyzeM6 := fid7_m7Row hc2.analyzeM6
    (hno := fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h)
  have rRephase := fid7_m7Row hc2.rephase
    (hno := fun _ _ _ _ h => m7RephaseSpec_monoX h)
  have rRstDue := fid7_m7Row hc2.restartDue
  have rRst := fid7_m7Row hc2.restart
  have rAddBin := fid7_m7Row_at 178 "full_add_bin" Full.fullAddBinSpec
  have rDelBin := fid7_m7Row hc2.deleteBinary
  have rDefrag := fid7_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)
  have rWatchPush := fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 1) rfl))
  have rSweep := fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 7) rfl))
  have rMarkRsn := fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 8) rfl))
  have rSweepDense := fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 15) rfl))
  have rReorder := fid7_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reorderM6)
  have rProbeTail := fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 17) rfl))
    (hno := fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  have rSimplify := fid7_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.simplifyM6)
    (hno := fun _ _ _ _ h => fullM6SimplifySpec_monoX h)
  have rFwdSub := fid7_m7Row (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 8) rfl))
  have rMinU64 := fid7_m7Row m7FidP3MinU64_mem
  have rElimDt := fid7_m7Row m7FidP3ElimDticks_mem
  have rSwitch := fid7_m7Row hc3.switchModeM7
    (hno := fun _ _ _ _ h => m7SwitchModeSpec_monoX h)
  have rProbeDt := fid7_m7Row hc3p.probeDticks
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rMinMark := fid7_extraRow 5 "full_min_mark" Full.fullMinMarkSpec
  have rSortAna := fid7_extraRow 7 "full_sort_ana_qs_m6" m6SortAnaQsSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6SortAnaQsSpec_monoX h)
  have rWalkTbl := fid7_extraRow 15 "full_walk_init_table_m7" m7InitTableSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7InitTableSpec_noExit h)
  have rWalkEff := fid7_extraRow 16 "full_walk_effort_m7" m7EffortSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7EffortSpec_noExit h)
  have rWalkInit := fid7_extraRow 17 "full_walk_init_vals_m7" m7InitValsSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7InitValsSpec_noExit h)
  have rWalkCol := fid7_extraRow 18 "full_walk_collect_m7" m7CollectSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7CollectSpec_noExit h)
  have rWalkBuild := fid7_extraRow 19 "full_walk_build_occ_m7" m7BuildOccSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7BuildOccSpec_noExit h)
  have rWalkPick := fid7_extraRow 21 "full_walk_pick_m7" m7PickSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7PickSpec_noExit h)
  have rWalkFlip := fid7_extraRow 22 "full_walk_flip_m7" m7FlipSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7FlipSpec_noExit h)
  have rWalkSave := fid7_extraRow 23 "full_walk_save_min_m7" m7SaveMinSpec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m7SaveMinSpec_noExit h)
  have rClearTier := fid7_extraRow 50 "full_viv_clear_tier_m6" fullVivClearTierM6Spec
  have rMinDfs := fid7_minHelpRow 0 "full_min_lit_dfs_m8" m8MinLitDfsSpec
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m8MinLitDfsSpec_monoX h)
  have rShrinkBlk := fid7_minHelpRow 2 "full_shrink_blk_bool_m8" m8ShrinkBlkBoolSpec
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m8ShrinkBlkBoolSpec_monoX h)
  -- Anchor lookups for inserted `befores`
  obtain ⟨gReb, hgReb, hsgReb⟩ := fidStep7_slot (slotSig_at fidStep7_replSigs_batch 11 246
    (some ("full_rebuild_watches", [i64], [i64])))
  have hgtReb : ∃ g ∈ fidFns, g.name = "full_rebuild_watches" :=
    ⟨gReb, hgReb, congrArg Prod.fst hsgReb⟩
  obtain ⟨gFac, hgFac, hsgFac⟩ := fidStep7_slot (slotSig_at fidStep7_replSigs_batch 14 439
    (some ("full_factor", [i64, i64], [i64])))
  have hgtFac : ∃ g ∈ fidFns, g.name = "full_factor" :=
    ⟨gFac, hgFac, congrArg Prod.fst hsgFac⟩
  simp only [fidStep7Bundle, PatchBundle.frontTable, fidStep7RewiredRows, fidStep7ReplRows,
    fidStep7BeforeRows, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · have hfeq := fidStep7_fn_eq_base hfn 51
      (by t_kernel_rfl : fidFns[51]? = some ⟨"full_init_state_m5",
        [i64, i64, i64, i64, i64], [.bool], FullM5Orch.full_init_state_m5_body⟩)
      rfl hnm
    subst hfeq
    exact .of (full_init_state_m5_step7_wp fidStep7Env rHdr rFixed r7CalcMaxV rExtCap
      r7ScrCap rInitArenas rInitHdr rZt1 rZt2)
  · have hfeq := fidStep7_fn_eq_base hfn 121
      (by t_kernel_rfl : fidFns[121]? = some m6aRestoreBumpAnaM6HdrFn) rfl hnm
    subst hfeq
    exact .of (full_restore_bump_ana_m6_hdr_step7_wp fidStep7Env r7BumpAna rClearAna)
  · have hfeq := fidStep7_fn_eq_base hfn 122
      (by t_kernel_rfl : fidFns[122]? = some m8AnaFailedLitM6HdrFn) rfl hnm
    subst hfeq
    exact .of (m8_ana_failed_lit_m6_hdr_step7_wp fidStep7Env rClearAna r7BumpAna rBacktrack
      rAssignLvl rEma)
  · have hfeq := fidStep7_fn_eq_base hfn 140
      (by t_kernel_rfl : fidFns[140]? = some m8MinShrinkM6Fn) rfl hnm
    subst hfeq
    exact .of (full_min_shrink_m6_step7_wp fidStep7Env r7SortTmp rMinMark rMinDfs rShrinkBlk)
  · have hfeq := fidStep7_fn_eq_base hfn 155
      (by t_kernel_rfl : fidFns[155]? = some m8AnalyzeCoreM6Fn) rfl hnm
    subst hfeq
    exact .of (full_analyze_core_m6_step7_wp fidStep7Env rOneLit r7AnaFailed r2Deduce r7Restore
      r7MinShrink rTickRel rEma r7Learn)
  · have hfeq := fidStep7_fn_eq_base hfn 169
      (by t_kernel_rfl : fidFns[169]? = some FullM7FidelityCore.fidWalkM7Fn) rfl hnm
    subst hfeq
    exact .of (full_walk_fid_step7_wp fidStep7Env rWalkInit rWalkCol r7CbInv rWalkTbl rWalkBuild
      rWalkEff rWalkPick rWalkFlip rWalkSave rRngNext)
  · have hfeq := fidStep7_fn_eq_base hfn 419
      (by t_kernel_rfl : fidFns[419]? = some FullM7BvaFactor.m7InitFreshVarFn) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_init_fresh_var_m7_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7CalcMaxVFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 0 47
        (some ("full_calc_max_v", [i64, i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_calc_max_v_step7_wp fidStep7Env rFixed)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7CalcScrCapM5Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 1 49
        (some ("full_calc_scr_cap_m5", [i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_calc_scr_cap_m5_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7M6HdrInitFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 2 55
        (some ("m6_hdr_init", [i64], []))) rfl hnm
    subst hfeq
    exact .of (m6_hdr_init_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7ReduceFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 3 112
        (some ("full_reduce", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_reduce_step7_wp fidStep7Env
      (fun ⟨x, ⟨⟩⟩ m Q X hQ => rIsqrt (x, ()) m Q X fun r hsq _ _ =>
        hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq))
      rIlog10 rArenaNext
      (by
        rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
        exact rRecompOld (c.hdr, ()) m Q X ⟨c, s, R, rfl, hlen, hm,
          fun _ s' m' hc hlen' hp hm' => by
            rcases s' with ⟨c', sc'⟩; change c' = s.core at hc; subst hc
            exact hQ sc' m' hlen'.scratch_ok hp.1.1 hp.1.2 hp.2.2.1 hm'⟩)
      (by
        rintro ⟨h, sf, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hm, hQ⟩
        exact rMarkRsn (c.hdr, sf, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hm,
          fun ar' m' hl' hr' hp' hrm' hw' hm' =>
            hQ ar' m' hl' hr' hp' (fun hsf idx hidx => hrm' hsf idx hidx) hw' hm'⟩)
      (by
        rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, hQ⟩
        exact rSortReds (c.hdr, n, ()) m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm,
          fun rr' m' hrr hm' =>
            hQ { s.scratch with red_refs := rr' } m'
              { hlen.scratch_ok with red_refs_len := hrr } rfl rfl rfl hm'⟩)
      (by
        rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hle, hm, hQ⟩
        have hmx : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
        have hcl_bd : s.core.cur_level < 2 ^ 64 := by
          have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
          have := hlen.core_ok.cur_vars_le; omega
        have htg_bd : tgt.toNat < s.core.cur_level → tgt.toNat < c.max_vars := by
          intro _; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
          have := hlen.core_ok.cur_vars_le; omega
        exact rBacktrack (c.hdr, tgt, ()) m Q X ⟨c, s, R, rfl, hlen, hcl_bd, htg_bd,
          hw.trail_lits_lt, hm,
          fun va lv rs tr tp te pr cl un sc m' hl' _ _ hcl' hps _ _ _ hwt _ hm' => by
            have hmin : cl = tgt.toNat := hcl'.trans (Nat.min_eq_right hle)
            subst hmin
            exact hQ va lv rs tr tp te pr un sc m' hl' (hwt F0 Fc hw hle)
              hps.1.1 hps.1.2 hps.2.2.1 hm'⟩)
      (FullM6S15Bridge.s15_to_dwPropagate rPropBcpS15)
      (by
        rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm, hQ⟩
        exact rSweep (c.hdr, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm,
          fun r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm' =>
            hQ r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'⟩))
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7ReduceM6Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 4 113
        (some ("full_reduce_m6", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_reduce_m6_step7_wp
      fidStep7Env rIsqrt rLog10M7 rArenaNext rRecomp rSetWm
      rMarkRsn rSortReds rBacktrack rPropBcpS15 rSweep)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7BumpAnalyzedM6HdrFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 5 120
        (some ("full_bump_analyzed_m6_hdr", [i64], []))) rfl hnm
    subst hfeq
    exact .of (full_bump_analyzed_m6_hdr_step7_wp fidStep7Env rDelay rDrAllow rBumpDelay
      rReduceDelay rSortAna rBumpVar rQueueMtf rBumpDecay)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7SortTmpFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 6 131
        (some ("full_sort_tmp", [i64], []))) rfl hnm
    subst hfeq
    exact .of (full_sort_tmp_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7LearnClauseFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 7 148
        (some ("full_learn_clause", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_learn_clause_step7_wp
      fidStep7Env rBacktrack rAssignLvl rDetNew rDefrag
      r7Reduce rAddCl rEagerSub)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7WalkCbInvM7Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 8 159
        (some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_walk_cb_inv_m7_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7VivifyTierM6HdrFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 9 226
        (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_vivify_tier_m6_hdr_step7_wp
      fidStep7Env rBacktrack r4VivCol r4VivCnt
      r4VivSort r2VivCl rPropBcpS15 rClearTier)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7VivifyM6HdrFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 10 227
        (some ("full_vivify_m6_hdr", [i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_vivify_m6_hdr_step7_wp
      fidStep7Env rBacktrack rGetT1 rGetT2 r3Sync rDelay
      rGetWm r7VivTier rBumpDelay rReduceDelay)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7RebuildWatchesFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 11 246
        (some ("full_rebuild_watches", [i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_rebuild_watches_step7_wp
      fidStep7Env rSweep rPropBcpS15 r7SortBin)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7BvaCommitFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 12 435
        (some ("full_bva_commit", [i64, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_bva_commit_step7_wp fidStep7Env r6Steps rDefrag
      r7InitFresh rAddBin rAllocCl rWatchPush rDelBin r4Unwatch)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7BvaTryLitFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 13 436
        (some ("full_bva_try_lit", [i64, i32, i64], [.bool]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_bva_try_lit_step7_wp fidStep7Env r6Steps r6Scan r6Pick
      r6Filt r7BvaCommit)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7FactorFn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 14 439
        (some ("full_factor", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_factor_step7_wp fidStep7Env r6Steps r6Conn r6Up r6Down
      r7BvaTryLit r7BvaUpdLit)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7BveVarKeyM7Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 15 465
        (some ("full_bve_var_key_m7", [i64, i32], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_bve_var_key_m7_m8_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7EliminateM7Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 16 472
        (some ("full_eliminate_m7", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_eliminate_m7_step7_wp
      fidStep7Env rElimDt rIlog10 rScale r2Enter rFwdSub
      rMinU64 r5ElimBve r7Factor r7Rebuild)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7EliminateM6Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 17 473
        (some ("full_eliminate_m6", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_eliminate_m6_step7_wp
      fidStep7Env rElimDt rLog10M7 rScale r2Enter rFwdSub
      r5ElimBve r7Rebuild)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7ProbeM6Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 18 490
        (some ("full_probe_m6", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_probe_m6_step7_wp
      fidStep7Env rProbeDt rLog10M7 rScaleM5 r7Vivify r2Enter
      rDelay r3Cong r7Rebuild rGetWm rSetWm rReduceDelay rBumpDelay rSweepDense r2Subst
      rProbeTail r2Bone r7Factor)
  · have hfeq := fidStep7_fn_eq_repl hfn (r := FullFidelityStep7.fidStep7SearchM6Fn)
      (by simp [FullFidelityStep7.fidStep7Repls])
      (slotSig_at fidStep7_replSigs_batch 19 494
        (some ("full_search_m6", [i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_search_m6_step7_wp
      fidStep7Env r2Lucky rSetWm rPropBcpS15 rAnalyzeM6
      r7ReduceM6 rSwitch rRstDue rRst rReorder rRephase rSimplify r2Decide)
  · have hfeq := fidStep7_fn_eq_before hfn
      (b := FullFidelityStep7.fidStep7SortBinWatchesFn)
      (tgt := "full_rebuild_watches") (ins := [FullFidelityStep7.fidStep7SortBinWatchesFn])
      (by simp [FullFidelityStep7.fidStep7Befores]) (by simp) hgtReb hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_sort_bin_watches_fid_step7_wp fidStep7Env)
  · have hfeq := fidStep7_fn_eq_before hfn
      (b := FullFidelityStep7.fidStep7BvaUpdLitFn)
      (tgt := "full_factor") (ins := [FullFidelityStep7.fidStep7BvaUpdLitFn])
      (by simp [FullFidelityStep7.fidStep7Befores]) (by simp) hgtFac hnm
    subst hfeq
    exact .of (FullFidelityStep7.full_bva_upd_lit_fid_step7_wp fidStep7Env r6Deg r6Up r6Down)

/-- Closed `501/501` `ModuleOk` for `FullFidelityAssemblyStep7.fidStep7Module` under
`fidStep7Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep7_moduleOk : ModuleOk fidStep7Env fidStep7Module := by
  change ModuleOk (patchEnv fidStep7Bundle) fidStep7Bundle.patchedMod
  refine patchBundle_moduleOk fidStep7Bundle fidStep7Module_names_nodup
    fidStep7Module_replSigs_ok ?_ fidStep7Module_patchCallsOk fidStep7_front_covered
    fidStep7_front_impl fidStep7BadNames fidStep7_noCallBad fidStep7_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact FullFidelityStep7.fidStep7Repls_wf fn hr
  · exact FullFidelityStep7.fidStep7Befores_wf fn hb

/-! ## 4. `TableImpl`, Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

/-- Closed `501`-row specification table aligned 1-to-1 with `fidStep7Module.fns`. -/
def fidStep7SpecTable : List SpecEntry :=
  fidStep7Module.fns.map fun fn =>
    ((fidStep7Bundle.frontTable ++ fidEnvTable).find? (·.name == fn.name)).getD
      ⟨fn.name, fn.as, fn.rs, fun _ _ _ _ => False, true⟩

private theorem fidStep7SpecTable_sigs :
    fidStep7SpecTable.map (fun e => (e.name, e.as, e.rs)) = fidStep7Module.fns.map Fn.sig := by
  t_kernel_rfl

private theorem fidStep7SpecTable_nodup : (fidStep7SpecTable.map SpecEntry.name).Nodup := by
  have heq : fidStep7SpecTable.map SpecEntry.name = fidStep7Module.fns.map Fn.name := by
    have hs := congrArg (List.map Prod.fst) fidStep7SpecTable_sigs
    simpa only [List.map_map, Function.comp_def, Fn.sig] using hs
  rw [heq]
  exact (List.nodup_append.mp fidStep7Module_names_nodup).1

private theorem fidStep7_tableImpl_aux :
    ∀ {pre fs : List Fn} {rs : List SpecEntry},
      fidStep7Module.fns = pre ++ fs →
      rs.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
      (∀ r ∈ rs, r ∈ fidStep7SpecTable) →
      (∀ r ∈ fidStep7SpecTable, ∀ xs m Q X, r.eff xs m Q X →
        fidStep7Env r.name r.as r.rs xs m Q X) →
      TableImpl fidStep7Env fs rs
  | _, [], [], _, _, _, _ => trivial
  | _, [], _ :: _, _, hs, _, _ => by simp at hs
  | _, _ :: _, [], _, hs, _, _ => by simp at hs
  | pre, f :: fs, r :: rs, hsplit, hs, hsub, hLift => by
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨hs_hd, hs_tl⟩ := hs
    have hr_mem : r ∈ fidStep7SpecTable := hsub r List.mem_cons_self
    rcases r with ⟨rn, ra, rr, rsp, rnx⟩
    dsimp only at hs_hd
    have hnm : rn = f.name := congrArg Prod.fst hs_hd
    have has : ra = f.as := congrArg (Prod.fst ∘ Prod.snd) hs_hd
    have hrs : rr = f.rs := congrArg (Prod.snd ∘ Prod.snd) hs_hd
    have hfn_ok := fidStep7_moduleOk.fnsOk pre f fs hsplit
    refine ⟨?_, fidStep7_tableImpl_aux (pre := pre ++ [f])
      (by simpa [List.append_assoc] using hsplit) hs_tl
      (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hLift⟩
    refine ⟨⟨hnm, has, hrs⟩, fun xs m Q X heff => ?_⟩
    subst hnm; subst has; subst hrs
    exact hfn_ok.2.2 xs m Q X (hLift _ hr_mem xs m Q X heff)

/-- Closed `TableImpl` certifying all `501` functions of `fidStep7Module`. -/
theorem fidStep7_tableImpl :
    TableImpl fidStep7Env fidStep7Module.fns fidStep7SpecTable := by
  refine fidStep7_tableImpl_aux (pre := []) rfl fidStep7SpecTable_sigs (fun _ h => h) ?_
  intro r hr xs m Q X heff
  dsimp only [fidStep7SpecTable] at hr
  obtain ⟨fn, hfn, heq⟩ := List.mem_map.mp hr
  cases hf : (fidStep7Bundle.frontTable ++ fidEnvTable).find? (·.name == fn.name) with
  | some e =>
    rw [hf, Option.getD_some] at heq
    subst heq
    exact fid_env_ofTable_find_some hf heff
  | none =>
    exfalso
    have hn : (fidStep7Module.fns.all fun g =>
        ((fidStep7Bundle.frontTable ++ fidEnvTable).find?
          (·.name == g.name)).isSome) = true := by
      t_kernel_rfl
    have hsome := List.all_eq_true.mp hn fn hfn
    simp [hf] at hsome

theorem fidStep7Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep7Env f as bs xs m Q X → fidStep7Env f as bs xs m Q X' := by
  refine patchEnv_noExit_of fidStep7Bundle ?_ ?_
  · change (fidStep7RewiredRows ++ fidStep7ReplRows ++ fidStep7BeforeRows).all
      SpecEntry.noExit = true
    decide
  · change (fidBundle.frontTable ++ (fidStep5Bundle.frontTable ++ (fidStep4Bundle.frontTable ++
      (fidStep3Bundle.frontTable ++ (fidStep2Bundle.frontTable ++
        (fidStep1ReplRows ++ fidBaseSpecTable)))))).all SpecEntry.noExit = true
    rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
      List.all_append, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide,
      ⟨by decide, fidBaseSpecTable_noExit⟩⟩⟩⟩⟩⟩

private theorem fidStep7_front_noSolveBytes :
    fidStep7Bundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : "kissat_solve_bytes" ∈ fidStep7FrontNames :=
    fidStep7_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
  exact absurd hm (by decide)

theorem fidStep7Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep7Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidStep7Bundle fidStep7_front_noSolveBytes
    (fun _ _ _ _ hs => fidEnv_solve_bytes_of hs) a m Q X

theorem fidStep7_solveBytes_mem : m6oSolveBytesFn ∈ fidStep7Module.fns :=
  patchBundle_solveBytes_mem fidStep7Bundle fid_solveBytes_mem fun r hr => by
    change r ∈ FullFidelityStep7.fidStep7Repls at hr
    simp only [FullFidelityStep7.fidStep7Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep7Module` (`501` fns, `XPost := False`). -/
theorem fidStep7_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep7Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep7_moduleOk fidStep7_solveBytes_mem
    (fun _ _ _ _ hs => fidStep7Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep7Module`. -/
theorem fidStep7_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  FullFidelityAssemblyUtil.fid_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep7Module`. -/
theorem fidStep7_unsat_nv :
    Func.wp fidStep7Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep7_moduleOk fidStep7_solveBytes_mem
    (fun _ _ _ _ hs => fidStep7Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep7_moduleOk`. -/
theorem fidStep7Module_acyclic : fidStep7Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep7_moduleOk

/-- Canonical Gate-1 Step-7 `KissatUnsatPkg` (`fidStep7Module`, `fidInlPolicy`). -/
def fidStep7UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep7Module fidInlPolicy fidStep7_solveBytes_mem
    fidStep7Env fidStep7_moduleOk fidStep7Env_noExit
    (fun _ _ _ _ hs => fidStep7Env_solve_bytes_of hs)

/-! ## 5. Additive Thin Spec Interface for `fidStep7Env` (`0` `import all` Needed Down-Stream) -/

def fidStep7BaseSpecTable : List SpecEntry :=
  fidStep7Bundle.frontTable ++ fidStep7Bundle.baseTable

theorem fidStep7Base_eq_env : Env.ofTable fidStep7BaseSpecTable = fidStep7Env := by
  unfold fidStep7BaseSpecTable fidStep7Env patchEnv
  rfl

theorem fidStep7Base_moduleOk :
    ModuleOk (Env.ofTable fidStep7BaseSpecTable) fidStep7Module :=
  fidStep7_moduleOk

theorem fidStep7Base_noExit :
    ∀ f as bs xs m Q X X',
      Env.ofTable fidStep7BaseSpecTable f as bs xs m Q X →
      Env.ofTable fidStep7BaseSpecTable f as bs xs m Q X' :=
  fidStep7Env_noExit

theorem fidStep7BaseSpecTable_noExit :
    fidStep7BaseSpecTable.all SpecEntry.noExit = true := by
  unfold fidStep7BaseSpecTable
  rw [List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · change (fidStep7RewiredRows ++ fidStep7ReplRows ++ fidStep7BeforeRows).all
      SpecEntry.noExit = true
    decide
  · change (fidBundle.frontTable ++ (fidStep5Bundle.frontTable ++ (fidStep4Bundle.frontTable ++
      (fidStep3Bundle.frontTable ++ (fidStep2Bundle.frontTable ++
        (fidStep1ReplRows ++ fidBaseSpecTable)))))).all SpecEntry.noExit = true
    rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
      List.all_append, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide,
      ⟨by decide, fidBaseSpecTable_noExit⟩⟩⟩⟩⟩⟩

theorem fidStep7Base_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      Env.ofTable fidStep7BaseSpecTable "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fidStep7Env_solve_bytes_of

theorem fidStep7Env_elim_walkEffort {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_walk_effort_m7" [i64, i64] [i64] xs m Q X) :
    FullM7Walk.m7EffortSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_walk_effort_m7" [i64, i64] [i64] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide)
    (fid7_elim_to_fidBase h))
  have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
    (by decide) (by decide) (by decide) hsw
  have hrow : m7FidBaseTable[156]? =
      some ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.m7EffortSpec, true⟩ := rfl
  cases hm7 with
  | base _ hb => exact m7FidBase_elim_of_mem (List.mem_of_getElem? hrow) hb
  | extra hex => exact mf_extra_elim (List.mem_of_getElem? (i := 16) rfl) hex

theorem fidStep7_m7EffortSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost}
    (h : FullM7Walk.m7EffortSpec xs m Q X) :
    FullM7Walk.m7EffortSpec xs m Q X' := by
  unfold FullM7Walk.m7EffortSpec at h ⊢
  exact h

theorem fidStep7_m7EffortSpec_elim {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : FullM7Walk.m7EffortSpec xs m Q X) :
    SafetySlice.spec (as := [i64, i64]) (rs := [i64]) fullSafetySlice
      (fun c (h, _mf, ()) _ => h = c.hdr)
      (fun _ _ (r, ()) s s' => s' = s ∧ 500000 ≤ r.toNat ∧ r.toNat ≤ 40000000)
      xs m Q X := by
  unfold FullM7Walk.m7EffortSpec at h
  exact h

theorem fidStep7Env_elim_watchPushSlow {xs : Tup Val [i64, i32, i32, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep7Env "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] xs m Q X) :
    Full.fullWatchPushSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_watch_push_slow_m6"
    [i64, i32, i32, i32, i32] [.bool] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  change patchEnv fidBundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h
  have hmem : (⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ fidStep2Bundle.frontTable :=
    List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hf2 := fid7_of_prefix_mem ⟨_, hmem, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup hmem hf2
  exact hc

theorem fidStep7Env_elim_watchPushM6 {xs : Tup Val [i64, i32, i32, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep7Env "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] xs m Q X) :
    Full.fullWatchPushSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_watch_push_m6"
    [i64, i32, i32, i32, i32] [.bool] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  change patchEnv fidBundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h
  have hmem : (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ fidStep2Bundle.frontTable :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr List.mem_cons_self)))
  have hf2 := fid7_of_prefix_mem ⟨_, hmem, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup hmem hf2
  exact hc

theorem fidStep7Env_elim_deleteBinSide {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidStep7Env "full_delete_bin_side" [i64, i32, i32] [] xs m Q X) :
    Full.fullDeleteBinSideSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_delete_bin_side" [i64, i32, i32] [] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  have hrow : m7FidBaseTable[176]? =
      some ⟨"full_delete_bin_side", [i64, i32, i32], [],
        Full.fullDeleteBinSideSpec, true⟩ := rfl
  exact fid7_elim_m7Base (List.mem_of_getElem? hrow) h

theorem fidStep7Env_elim_bvaCommit {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep7Env "full_bva_commit" [i64, i32] [.bool] xs m Q X) :
    FullFidelityStep7.step7BvaCommitSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[19]? =
      some ⟨"full_bva_commit", [i64, i32], [.bool],
        FullFidelityStep7.step7BvaCommitSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup (List.mem_of_getElem? hrow) hf7
  have hc' : FullFidelityStep7.step7BvaCommitSpec xs m Q (fun _ _ _ _ => False) := hc
  exact FullFidelityStep7.step7BvaCommitSpec_monoX hc'

theorem fidStep7Env_wstackDefragM6 :
    ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      fidStep7Env "full_wstack_defrag_m6" [i64] [] a m Q X :=
  fid7_m7Row (m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem).wstackDefragM6

theorem fidStep7Env_watchPushSlowM6 :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      fidStep7Env "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs => fid7_of_fidEnv (by decide) (by
    change patchEnv fidBundle "full_watch_push_slow_m6" _ _ a m Q X
    rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))]
    change patchEnv fidStep5Bundle _ _ _ a m Q X
    rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))]
    change patchEnv fidStep4Bundle _ _ _ a m Q X
    rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))]
    change patchEnv fidStep3Bundle _ _ _ a m Q X
    rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))]
    exact patchEnv_of_front_mem fidStep2Bundle fidStep2_front_nodup
      (e := ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool],
        Full.fullWatchPushSpec, true⟩)
      (List.mem_append.mpr (Or.inr List.mem_cons_self)) hs)

theorem fidStep7Env_bvaStepsCap :
    ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      fidStep7Env "full_bva_steps_cap_fid" [i64] [i32] a m Q X :=
  fid7_step6FrontRow 7 "full_bva_steps_cap_fid" fidBvaStepsCapSpec

theorem fidStep7Env_wstackDefrag :
    ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      fidStep7Env "full_wstack_defrag" [i64] [] a m Q X :=
  fid7_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)

theorem fidStep7Env_initFreshVar :
    ∀ a m Q X, FullFidelityStep7.step7InitFreshVarSpec a m Q X →
      fidStep7Env "full_init_fresh_var" [i64, i32] [] a m Q X :=
  fid7_frontRow 6 "full_init_fresh_var" FullFidelityStep7.step7InitFreshVarSpec
    rfl (fun _ _ _ _ h => FullFidelityStep7.step7InitFreshVarSpec_monoX h)

theorem fidStep7Env_addBin :
    ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      fidStep7Env "full_add_bin" [i64, i32, i32] [i64] a m Q X :=
  fid7_m7Row_at 178 "full_add_bin" Full.fullAddBinSpec

theorem fidStep7Env_allocCl :
    ∀ a m Q X, Full.fullAllocClSpec a m Q X →
      fidStep7Env "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).allocCl

theorem fidStep7Env_watchPush :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      fidStep7Env "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X :=
  fid7_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.watchPush)

theorem fidStep7Env_deleteBinary :
    ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      fidStep7Env "full_delete_binary" [i64, i32, i32] [] a m Q X :=
  fid7_m7Row (m7Part2Callees_of_sub m7FidBase_part2_mem).deleteBinary

theorem fidStep7Env_unwatchLarge :
    ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      fidStep7Env "full_unwatch_large" [i64, i32, i32] [] a m Q X :=
  fid7_step4FrontRow 0 "full_unwatch_large" Full.fullUnwatchLargeSpec

theorem fidStep7Env_arenaNext :
    ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      fidStep7Env "full_arena_next" [i64, i32] [i32] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).arenaNext

theorem fidStep7Env_arenaSweep :
    ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      fidStep7Env "full_arena_sweep" [i64] [i64] a m Q X :=
  fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 7) rfl))

theorem fidStep7Env_sweepBinsRangeM6 :
    ∀ a m Q X, FullM6WatchGc.fullSweepBinsRangeSpec a m Q X →
      fidStep7Env "full_sweep_bins_range_m6" [i64, i64] [] a m Q X :=
  fid7_m7Row (m7FidBase_part1_mem _ (by
    unfold m7FidRowsPart1
    (iterate 18 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl)))
    (hno := fun _ _ _ _ h => FullM6WatchGc.fullSweepBinsRangeSpec_xirrel h)

theorem fidStep7Env_sweepCopy :
    ∀ a m Q X, Full.fullSweepCopySpec a m Q X →
      fidStep7Env "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] a m Q X :=
  fid7_m7Row (m7FidBase_part1_mem _ (by
    unfold m7FidRowsPart1
    (iterate 23 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)))

theorem fidStep7Env_moveRedEndM6 :
    ∀ a m Q X, FullM6WatchGc.fullMoveRedEndSpec a m Q X →
      fidStep7Env "full_move_red_end_m6" [i64, i64, i64] [] a m Q X :=
  fid7_m7Row (m7FidBase_part1_mem _ (by
    unfold m7FidRowsPart1
    (iterate 25 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl)))
    (hno := fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndSpec_xirrel h)

theorem fidStep7Env_rewatchRangeM6 :
    ∀ a m Q X, FullM6WatchGc.fullRewatchRangeSpec a m Q X →
      fidStep7Env "full_rewatch_range_m6" [i64, i64, i64] [.bool] a m Q X :=
  fid7_m7Row (m7FidBase_part1_mem _ (by
    unfold m7FidRowsPart1
    (iterate 19 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)))
    (hno := fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)

theorem fidStep7Env_backtrack :
    ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      fidStep7Env "full_backtrack" [i64, i64] [] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).backtrack

theorem fidStep7Env_hdrRecomputeTiers :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      fidStep7Env "m6_hdr_recompute_tiers" [i64] [] a m Q X :=
  fid7_m7Row_at 61 "m6_hdr_recompute_tiers" (m6HdrW2aSpec [] [])
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_markReasons :
    ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      fidStep7Env "full_mark_reasons" [i64, .bool] [] a m Q X :=
  fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 8) rfl))

theorem fidStep7Env_isqrt :
    ∀ a m Q X, Full.fullIsqrtSpec a m Q X →
      fidStep7Env "full_isqrt" [i64] [i64] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).isqrt

theorem fidStep7Env_sortReds :
    ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
      fidStep7Env "full_sort_reds" [i64, i64] [] a m Q X :=
  fid7_m7Row_at 109 "full_sort_reds" Full.fullSortRedsSpec

theorem fidStep7Env_log10Q16M7 :
    ∀ a m Q X, m7Log10Q16Spec a m Q X →
      fidStep7Env "full_log10_q16_m7" [i64] [i64] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).log10Q16M7
    (hno := fun _ _ _ _ h => m7Log10Q16Spec_monoX h)

theorem fidStep7Env_hdrSetWatermark :
    ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      fidStep7Env "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X :=
  fid7_m7Row_at 71 "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_hdrGetWatermark :
    ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      fidStep7Env "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X :=
  fid7_m7Row_at 70 "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64])
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_congExtractBinaries :
    ∀ a m Q X, FullM6CongSubst.m6CongExtractBinariesSpec a m Q X →
      fidStep7Env "full_cong_extract_binaries" [i64, i64] [i64] a m Q X :=
  fid7_m7Row (m7Part2CongCallees_of_sub m7FidBase_part2_mem).extBin

theorem fidStep7Env_congFindUnitsEquivs :
    ∀ a m Q X, FullM6CongSubst.m6CongFindUnitsEquivsSpec a m Q X →
      fidStep7Env "full_cong_find_units_equivs" [i64] [i64] a m Q X :=
  fid7_m7Row (m7Part2CongCallees_of_sub m7FidBase_part2_mem).findUE

theorem fidStep7Env_probeDticksM6Hdr :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      fidStep7Env "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X :=
  fid7_m7Row (m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem).probeDticks
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_scaleDeltaM5 :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      fidStep7Env "full_scale_delta_m5" [i64, i64] [i64] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).scaleDeltaM5

theorem fidStep7Env_hdrDelaying :
    ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      fidStep7Env "m6_hdr_delaying" [i64, i64] [.bool] a m Q X :=
  fid7_m7Row_at 66 "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool])
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_hdrReduceDelay :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      fidStep7Env "m6_hdr_reduce_delay" [i64, i64] [] a m Q X :=
  fid7_m7Row_at 68 "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] [])
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_hdrBumpDelay :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      fidStep7Env "m6_hdr_bump_delay" [i64, i64] [] a m Q X :=
  fid7_m7Row_at 67 "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] [])
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)

theorem fidStep7Env_sweepDenseM6 :
    ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      fidStep7Env "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X :=
  fid7_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 15) rfl))

theorem fidStep7Env_sortBinWatches :
    ∀ a m Q X, FullFidelityStep7.step7SortBinWatchesSpec a m Q X →
      fidStep7Env "full_sort_bin_watches_fid" [i64] [] a m Q X :=
  fid7_frontRow 27 "full_sort_bin_watches_fid" FullFidelityStep7.step7SortBinWatchesSpec rfl
    (fun _ _ _ _ h => FullFidelityStep7.step7SortBinWatchesSpec_monoX h)

theorem fidStep7Env_vivifyM6Hdr :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      fidStep7Env "full_vivify_m6_hdr" [i64] [i64] a m Q X :=
  fid7_frontRow 17 "full_vivify_m6_hdr" m6aVivifySpec rfl
    (fun _ _ _ _ h => m6aVivifySpec_monoX h)

theorem fidStep7Env_bvaTryLit :
    ∀ a m Q X, FullFidelityStep7.step7BvaTryLitSpec a m Q X →
      fidStep7Env "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X :=
  fid7_frontRow 20 "full_bva_try_lit" FullFidelityStep7.step7BvaTryLitSpec rfl
    (fun _ _ _ _ h => FullFidelityStep7.step7BvaTryLitSpec_monoX h)

theorem fidStep7Env_fheapUp :
    ∀ a m Q X, FullFidelityBva.fidFheapUpSpec a m Q X →
      fidStep7Env "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X :=
  fid7_step6FrontRow 9 "full_fheap_up_fid" fidFheapUpSpec

theorem fidStep7Env_fheapDown :
    ∀ a m Q X, FullFidelityBva.fidFheapDownSpec a m Q X →
      fidStep7Env "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X :=
  fid7_step6FrontRow 10 "full_fheap_down_fid" fidFheapDownSpec

theorem fidStep7Env_bvaCountLitDeg :
    ∀ a m Q X, FullFidelityBva.fidBvaCountLitDegSpec a m Q X →
      fidStep7Env "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X :=
  fid7_step6FrontRow 11 "full_bva_count_lit_deg_fid" fidBvaCountLitDegSpec

theorem fidStep7Env_bvaConnectClauses :
    ∀ a m Q X, FullFidelityBva.fidBvaConnectClausesSpec a m Q X →
      fidStep7Env "full_bva_connect_clauses_fid" [i64] [] a m Q X :=
  fid7_step6FrontRow 12 "full_bva_connect_clauses_fid" fidBvaConnectClausesSpec

theorem fidStep7Env_congExtract :
    ∀ a m Q X, FullFidelityCong.fidCongExtractSpec a m Q X →
      fidStep7Env "full_cong_extract" [i64, i64, i64] [i64] a m Q X :=
  fid7_step3FrontRow 5 "full_cong_extract" FullFidelityCong.fidCongExtractSpec

theorem fidStep7Env_congWorklist :
    ∀ a m Q X, FullFidelityCong.fidCongWorklistSpec a m Q X →
      fidStep7Env "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X :=
  fid7_step3FrontRow 8 "full_cong_worklist" FullFidelityCong.fidCongWorklistSpec

theorem fidStep7Env_congFwdSubsume :
    ∀ a m Q X, FullM6CongSubst.m6CongFwdSubsumeSpec a m Q X →
      fidStep7Env "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X :=
  fid7_step3FrontRow 9 "full_cong_fwd_subsume" FullM6CongSubst.m6CongFwdSubsumeSpec

theorem fidStep7Env_congExtractIteAll :
    ∀ a m Q X, FullFidelityCong.fidCongExtractIteAllSpec a m Q X →
      fidStep7Env "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X :=
  fid7_step3FrontRow 18 "full_cong_extract_ite_all_m7"
    FullFidelityCong.fidCongExtractIteAllSpec

theorem fidStep7Env_propagate :
    ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      fidStep7Env "full_propagate" [i64] [i64] a m Q X :=
  fid7_step2FrontRow 1 "full_propagate" FullM6BcpS15.fullBcpS15Spec

theorem fidStep7Env_flushTrail :
    ∀ a m Q X, FullM6CompactFlush.fullFlushTrailSpec a m Q X →
      fidStep7Env "full_flush_trail" [i64] [i64] a m Q X :=
  fid7_step2FrontRow 3 "full_flush_trail" FullM6CompactFlush.fullFlushTrailSpec

theorem fidStep7Env_backboneM6 :
    ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      fidStep7Env "full_backbone_m6" [i64, i64] [i64] a m Q X :=
  fid7_step2FrontRow 16 "full_backbone_m6" fullBackboneSpec

theorem fidStep7Env_transitiveM6 :
    ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      fidStep7Env "full_transitive_m6" [i64, i64] [i64] a m Q X :=
  fid7_step2FrontRow 17 "full_transitive_m6" FullFastBveBudgets.fullTransitiveFastSpec

theorem fidStep7Env_substitute :
    ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      fidStep7Env "full_substitute" [i64] [i64] a m Q X :=
  fid7_step2FrontRow 19 "full_substitute" fullSubstituteSpec

theorem fidStep7Env_enterDense :
    ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      fidStep7Env "full_enter_dense" [i64] [.bool] a m Q X :=
  fid7_step2FrontRow 20 "full_enter_dense" schedEnterDenseSpec

theorem fidStep7Env_elim_propFlushDel {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep7Env "full_prop_flush_del_fid" [i64, i64] [.bool] xs m Q X) :
    FullFidelityBcp.fidPropFlushDelSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_prop_flush_del_fid" [i64, i64] [.bool] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  change patchEnv fidBundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h
  have hrow : fidStep2Bundle.frontTable[36]? =
      some ⟨"full_prop_flush_del_fid", [i64, i64], [.bool],
        FullFidelityBcp.fidPropFlushDelSpec, true⟩ := by t_kernel_rfl
  have hf2 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep2_front_nodup
    (List.mem_of_getElem? hrow) hf2
  have hc' : FullFidelityBcp.fidPropFlushDelSpec xs m Q (fun _ _ _ _ => False) := hc
  exact FullFidelityBcp.fidPropFlushDelSpec_monoX hc'

theorem fidStep7Env_elim_reduceM6 {xs : Tup Val [i64, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_reduce_m6" [i64, .bool] [i64] xs m Q X) :
    m6ReduceSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[11]? =
      some ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup
    (List.mem_of_getElem? hrow) hf7
  have hc' : m6ReduceSpec xs m Q (fun _ _ _ _ => False) := hc
  exact m6ReduceSpec_monoX hc'

theorem fidStep7Env_elim_congruenceDense {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_congruence_dense" [i64, i64] [i64] xs m Q X) :
    FullM3CongBva.m3CongruenceDenseSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_congruence_dense" [i64, i64] [i64] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  change patchEnv fidBundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h
  have hrow : fidStep3Bundle.frontTable[19]? =
      some ⟨"full_congruence_dense", [i64, i64], [i64],
        FullM3CongBva.m3CongruenceDenseSpec, true⟩ := by t_kernel_rfl
  have hf3 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep3_front_nodup
    (List.mem_of_getElem? hrow) hf3
  exact hc

theorem fidStep7Env_elim_rebuildWatches {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_rebuild_watches" [i64] [i64] xs m Q X) :
    Full.fullRebuildWatchesSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[18]? =
      some ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup
    (List.mem_of_getElem? hrow) hf7
  exact hc

theorem fidStep7Env_elim_factor {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_factor" [i64, i64] [i64] xs m Q X) :
    FullBvaHeap.fullFactorHeapSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[21]? =
      some ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup
    (List.mem_of_getElem? hrow) hf7
  exact hc

theorem fidStep7Env_elim_probeM6 {xs : Tup Val [i64, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_probe_m6" [i64, .bool] [i64] xs m Q X) :
    m6ProbeSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[25]? =
      some ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup
    (List.mem_of_getElem? hrow) hf7
  have hc' : m6ProbeSpec xs m Q (fun _ _ _ _ => False) := hc
  exact m6ProbeSpec_monoX hc'

theorem fidStep7Env_elim_arenaSweepM6 {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_arena_sweep_m6" [i64] [i64] xs m Q X) :
    Full.fullArenaSweepSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_arena_sweep_m6" [i64] [i64] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  exact fid7_elim_m7Base (m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem).arenaSweepM6 h

theorem fidStep7Env_elim_compactNeeded {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep7Env "full_compact_needed" [i64] [.bool] xs m Q X) :
    FullM4Compact.fullCompactNeededSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_compact_needed" [i64] [.bool] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide)
    (fid7_elim_to_fidBase h))
  have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
    (by decide) (by decide) (by decide) hsw
  cases hm7 with
  | base hne _ => exact absurd (by decide : "full_compact_needed" ∈ mfExclNames) hne
  | extra hex => exact mf_extra_elim (List.mem_of_getElem? (i := 52) rfl) hex

theorem fidStep7Env_elim_compactFlush {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_compact_flush" [i64] [i64] xs m Q X) :
    FullM4Compact.fullCompactFlushSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_compact_flush" [i64] [i64] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  have hmem : (⟨"full_compact_flush", [i64], [i64],
      FullM4Compact.fullCompactFlushSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part3Pfx_mem _ (by
      unfold m7FidRowsPart3Pfx
      (iterate 17 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  exact fid7_elim_m7Base hmem h

private def sigsAtSorted7 (i : Nat) : List Nat → List Fn → List SigEntry
  | [], _ => []
  | _, [] => []
  | k :: ks, f :: fs =>
    if i == k then f.sig :: sigsAtSorted7 (i + 1) ks fs
    else sigsAtSorted7 (i + 1) (k :: ks) fs

private theorem sigsAtSorted7_getElem? :
    ∀ (fs : List Fn) (i : Nat) (pairs : List (Nat × SigEntry)),
      (pairs.map Prod.fst).Pairwise (· < ·) →
      (∀ q ∈ pairs, i ≤ q.1) →
      sigsAtSorted7 i (pairs.map Prod.fst) fs = pairs.map Prod.snd →
      ∀ p ∈ pairs, fs[p.1 - i]?.map Fn.sig = some p.2
  | [], _, [], _, _, _, _, hp => nomatch hp
  | [], _, _ :: _, _, _, h, _, _ => by simp [sigsAtSorted7] at h
  | _ :: _, _, [], _, _, _, _, hp => nomatch hp
  | f :: fs, i, hd :: tl, hsort, hall, h, p, hp => by
    simp only [sigsAtSorted7, List.map_cons] at h
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hsort
    have hi_hd : i ≤ hd.1 := hall hd List.mem_cons_self
    by_cases heq : i = hd.1
    · simp only [heq, beq_self_eq_true, ↓reduceIte, List.cons.injEq] at h
      rcases List.mem_cons.mp hp with rfl | htl
      · simp [heq, h.1]
      · have hlt : hd.1 < p.1 := hsort.1 p.1 ⟨p, htl, rfl⟩
        have h' : sigsAtSorted7 (i + 1) (tl.map Prod.fst) fs = tl.map Prod.snd := by
          rw [heq]; exact h.2
        have ih := sigsAtSorted7_getElem? fs (i + 1) tl hsort.2
          (fun q hq => by have := hsort.1 q.1 ⟨q, hq, rfl⟩; omega) h' p htl
        have hsub : p.1 - i = (p.1 - (i + 1)) + 1 := by omega
        rw [hsub]; simpa using ih
    · have hne : (i == hd.1) = false := beq_false_of_ne heq
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
      have hall' : ∀ q ∈ hd :: tl, i + 1 ≤ q.1 := fun q hq => by
        rcases List.mem_cons.mp hq with rfl | htl
        · omega
        · have := hsort.1 q.1 ⟨q, htl, rfl⟩; omega
      have ih := sigsAtSorted7_getElem? fs (i + 1) (hd :: tl)
        (by simpa [List.map_cons, List.pairwise_cons, List.mem_map] using hsort)
        hall' h p hp
      have hp_ge : i + 1 ≤ p.1 := hall' p hp
      have hsub : p.1 - i = (p.1 - (i + 1)) + 1 := by omega
      rw [hsub]; simpa using ih

theorem fidStep7_noCallBvaUpdLit_tail :
    checkNoCallBad ["full_factor"] ["full_bva_upd_lit_fid"]
      (fidStep7Module.fns.drop 441) = true := by
  t_kernel_rfl

/-- Sorted `(slot, sig)` table covering all `11` Step-9 replacements, `full_zero_tables1`
(`before` anchor), and all transitive callees in `fidStep7Module.fns`. -/
@[expose] def fidStep7_step9_sigPairs : List (Nat × SigEntry) :=
  [ (8, ("full_isqrt", [i64], [i64]))
  , (11, ("full_arena_next", [i64, i32], [i32]))
  , (12, ("full_alloc_cl", [i64, i32, i32, .bool], [i64]))
  , (18, ("full_wstack_defrag", [i64], []))
  , (19, ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]))
  , (32, ("full_log10_q16_m7", [i64], [i64]))
  , (33, ("full_scale_delta_m5", [i64, i64], [i64]))
  , (40, ("full_backtrack", [i64, i64], []))
  , (42, ("full_zero_tables1", [i64], []))
  , (62, ("m6_hdr_recompute_tiers", [i64], []))
  , (67, ("m6_hdr_delaying", [i64, i64], [.bool]))
  , (68, ("m6_hdr_bump_delay", [i64, i64], []))
  , (69, ("m6_hdr_reduce_delay", [i64, i64], []))
  , (71, ("m6_hdr_get_watermark", [i64, i64], [i64]))
  , (72, ("m6_hdr_set_watermark", [i64, i64, i64], []))
  , (81, ("full_unwatch_large", [i64, i32, i32], []))
  , (84, ("full_prop_flush_del_fid", [i64, i64], [.bool]))
  , (88, ("full_propagate", [i64], [i64]))
  , (93, ("full_sweep_bins_range_m6", [i64, i64], []))
  , (94, ("full_rewatch_range_m6", [i64, i64, i64], [.bool]))
  , (99, ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]))
  , (103, ("full_move_red_end_m6", [i64, i64, i64], []))
  , (104, ("full_arena_sweep_m6", [i64], [i64]))
  , (106, ("full_arena_sweep", [i64], [i64]))
  , (107, ("full_mark_reasons", [i64, .bool], []))
  , (108, ("full_flush_trail", [i64], [i64]))
  , (111, ("full_sort_reds", [i64, i64], []))
  , (113, ("full_reduce_m6", [i64, .bool], [i64]))
  , (183, ("full_add_bin", [i64, i32, i32], [i64]))
  , (184, ("full_delete_binary", [i64, i32, i32], []))
  , (227, ("full_vivify_m6_hdr", [i64], [i64]))
  , (235, ("full_backbone_m6", [i64, i64], [i64]))
  , (238, ("full_transitive_m6", [i64, i64], [i64]))
  , (244, ("full_substitute", [i64], [i64]))
  , (245, ("full_enter_dense", [i64], [.bool]))
  , (246, ("full_sort_bin_watches_fid", [i64], []))
  , (247, ("full_rebuild_watches", [i64], [i64]))
  , (263, ("full_cong_extract_binaries", [i64, i64], [i64]))
  , (264, ("full_cong_find_units_equivs", [i64], [i64]))
  , (265, ("full_cong_extract", [i64, i64, i64], [i64]))
  , (271, ("full_cong_worklist", [i64, i64, i64, i64], [i64]))
  , (274, ("full_cong_fwd_subsume", [i64, i64], [i64]))
  , (287, ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]))
  , (288, ("full_congruence_dense", [i64, i64], [i64]))
  , (348, ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  , (420, ("full_init_fresh_var", [i64, i32], []))
  , (425, ("full_bva_steps_cap_fid", [i64], [i32]))
  , (427, ("full_fheap_up_fid", [i64, i64, i64, i32], []))
  , (428, ("full_fheap_down_fid", [i64, i64, i64, i32, i32], []))
  , (429, ("full_bva_count_lit_deg_fid", [i64, i32], [i32]))
  , (430, ("full_bva_connect_clauses_fid", [i64], []))
  , (436, ("full_bva_commit", [i64, i32], [.bool]))
  , (437, ("full_bva_try_lit", [i64, i32, i64], [.bool]))
  , (440, ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32]))
  , (441, ("full_factor", [i64, i64], [i64]))
  , (442, ("full_compact_needed", [i64], [.bool]))
  , (443, ("full_compact_flush", [i64], [i64]))
  , (490, ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
  , (492, ("full_probe_m6", [i64, .bool], [i64])) ]

private theorem fidStep7_step9_sigs_batch :
    sigsAtSorted7 0 (fidStep7_step9_sigPairs.map Prod.fst) fidStep7Module.fns =
      fidStep7_step9_sigPairs.map Prod.snd := by
  t_kernel_rfl

theorem fidStep7_step9_sig_at {p : Nat × SigEntry} (hp : p ∈ fidStep7_step9_sigPairs) :
    fidStep7Module.fns[p.1]?.map Fn.sig = some p.2 := by
  simpa using sigsAtSorted7_getElem? fidStep7Module.fns 0 fidStep7_step9_sigPairs
    (by decide) (fun _ _ => Nat.zero_le _) fidStep7_step9_sigs_batch p hp

theorem fidStep7_step8_slots_ok :
    ( ((fidStep7Module.fns[161]?.map Fn.sig == some ("full_walk_effort_m7", [i64, i64], [i64])) &&
        ([] : List SigEntry).all fun d =>
          ((fidStep7Module.fns.take 161).map Fn.sig).contains d) &&
      ((fidStep7Module.fns[16]?.map Fn.sig ==
          some ("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool])) &&
        ([("full_wstack_defrag_m6", [i64], [])] : List SigEntry).all fun d =>
          ((fidStep7Module.fns.take 16).map Fn.sig).contains d) &&
      ((fidStep7Module.fns[17]?.map Fn.sig ==
          some ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool])) &&
        ([("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool])] :
          List SigEntry).all fun d =>
            ((fidStep7Module.fns.take 17).map Fn.sig).contains d) &&
      ((fidStep7Module.fns[181]?.map Fn.sig ==
          some ("full_delete_bin_side", [i64, i32, i32], [])) &&
        ([] : List SigEntry).all fun d =>
          ((fidStep7Module.fns.take 181).map Fn.sig).contains d) &&
      ((fidStep7Module.fns[436]?.map Fn.sig ==
          some ("full_bva_commit", [i64, i32], [.bool])) &&
        ([ ("full_bva_steps_cap_fid", [i64], [i32])
         , ("full_wstack_defrag", [i64], [])
         , ("full_init_fresh_var", [i64, i32], [])
         , ("full_add_bin", [i64, i32, i32], [i64])
         , ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
         , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
         , ("full_delete_binary", [i64, i32, i32], [])
         , ("full_unwatch_large", [i64, i32, i32], []) ] : List SigEntry).all fun d =>
           ((fidStep7Module.fns.take 436).map Fn.sig).contains d) ) = true := by
  t_kernel_rfl

@[expose] def fidStep7FnNames : List Sym :=
  [ "kissat_is_ws", "kissat_is_digit", "kissat_skip_ws_comments", "kissat_skip_ws1"
  , "kissat_read_nat", "kissat_parse_header", "kissat_next_lit", "kissat_check_model"
  , "full_isqrt", "full_ilog10", "full_rng_next", "full_arena_next", "full_alloc_cl"
  , "full_wsort_sift", "full_wstack_radix_sort_m6", "full_wstack_defrag_m6"
  , "full_watch_push_slow_m6", "full_watch_push_m6", "full_wstack_defrag", "full_watch_push"
  , "full_heap_up", "full_heap_down", "full_heap_push", "full_heap_pop", "full_rescale_m6"
  , "full_rescale", "full_bump_var", "full_bump_decay", "full_queue_renumber", "full_queue_mtf"
  , "full_tick_rel", "full_log10_q16", "full_log10_q16_m7", "full_scale_delta_m5"
  , "full_ema_update", "full_scale_delta", "full_assign_lvl", "full_assign"
  , "full_save_target_best", "full_backtrack_raw_m5", "full_backtrack", "full_add_clause"
  , "full_zero_tables1", "full_zero_tables2", "full_fixed_bytes", "full_init_ptrs"
  , "full_init_hdr", "full_calc_max_v", "full_calc_ext_cap_m5", "full_calc_scr_cap_m5"
  , "full_init_arenas", "full_init_state_m5", "full_init_state", "full_m6_hdr_sizeof"
  , "full_m6_ext_sizeof", "m6_hdr_init", "m6_hdr_reset", "m6_ext_ensure_init", "m6_hdr_ext_ready"
  , "full_m6_mem_init", "m6_hdr_sync_legacy_tiers", "m6_hdr_recompute_tiers_mode"
  , "m6_hdr_recompute_tiers", "m6_hdr_update_tier_limits", "m6_hdr_record_used"
  , "m6_hdr_get_tier1", "m6_hdr_get_tier2", "m6_hdr_delaying", "m6_hdr_bump_delay"
  , "m6_hdr_reduce_delay", "m6_hdr_reset_delay", "m6_hdr_get_watermark", "m6_hdr_set_watermark"
  , "m6_hdr_add_ticks", "m6_hdr_dr_init", "m6_hdr_dr_update", "m6_hdr_dr_allow", "full_skip_cl"
  , "full_ingest_cl", "full_find_repl", "full_assign_level", "full_unwatch_large"
  , "full_prop_lit_ovf_hot", "full_prop_chrono_hot", "full_prop_flush_del_fid"
  , "full_propagate_ignore_hot", "full_bcp_hot", "full_propagate_ignore", "full_propagate"
  , "full_parse_body_m6", "full_parse_body", "full_recompute_tiers", "full_lit_rank_m6"
  , "full_sweep_bins_range_m6", "full_rewatch_range_m6", "full_rewatch_arena_m6", "full_lit_rank"
  , "full_sweep_bins_m6cf", "full_sweep_bins", "full_sweep_copy", "full_rewatch_arena"
  , "full_move_red_pass2_m6", "full_move_red_end_buf_m6", "full_move_red_end_m6"
  , "full_arena_sweep_m6", "full_mark_reasons_m6", "full_arena_sweep", "full_mark_reasons"
  , "full_flush_trail", "full_red_less", "full_red_sift", "full_sort_reds", "full_reduce"
  , "full_reduce_m6", "full_analyze_lit", "full_analyze_rsn", "full_analyze_rsn_m6_hdr"
  , "full_clear_ana", "full_ana_sift_m6", "full_sort_ana_qs_m6", "full_bump_analyzed_m6_hdr"
  , "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr", "full_otfs_large"
  , "full_otfs_bin", "full_otfs_subsume", "full_min_mark", "full_tmp_less", "full_sort_tmp_sift"
  , "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp", "full_min_lit_dfs_m6"
  , "full_min_lit_m6", "full_shrink_lower_m6", "full_shrink_blk_bool_m6", "full_shrink_blk_m6"
  , "full_min_lit_dfs_m8", "full_shrink_lower_m8", "full_shrink_blk_bool_m8", "full_min_shrink_m6"
  , "full_deduce_1uip_m6", "full_min_shrink", "full_deduce_1uip", "full_deduce_1uip_m6_hdr"
  , "full_det_new_level", "full_one_lit_confl", "full_eager_subsume", "full_learn_clause"
  , "full_bump_sift_m7", "full_bump_sort_stamps_m7", "full_bump_reasons_m7", "full_bump_analyzed"
  , "full_restore_bump_ana_m5", "full_analyze", "full_analyze_core_m6", "full_analyze_m6_hdr"
  , "full_next_dec_var", "m6_hdr_decide", "full_walk_cb_inv_m7", "full_walk_init_table_m7"
  , "full_walk_effort_m7", "full_walk_init_vals_m7", "full_walk_collect_m7"
  , "full_walk_build_occ_m7", "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7"
  , "full_walk_save_min_m7", "full_walk_m7", "full_warmup_m7", "full_walk_warmup_m7"
  , "full_warmup", "full_walk", "full_rephase", "full_restart_due", "full_restart"
  , "full_extend_push2", "full_extend_push_cl", "full_extend", "full_has_bin"
  , "full_delete_bin_side", "full_add_bin_m6", "full_add_bin", "full_delete_binary"
  , "full_set_inactive", "full_add_unit", "full_lucky_scan", "full_lucky_polar", "full_lucky"
  , "full_hbr_dom", "full_probe_prop_lit", "full_probe_prop", "full_probe_flush_hbr"
  , "full_probe_assume_pair", "full_probe_run", "full_viv_unreason_m6", "full_viv_watch_rank_m6"
  , "full_viv_best_watch_m6", "full_viv_simplify_m6", "full_viv_commit_m6"
  , "full_viv_mark_garb_m6", "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6"
  , "full_viv_deduce_m6", "full_viv_best_implied_m6", "full_viv_reestablish_m6"
  , "full_viv_inst_check_m6", "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
  , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6", "full_viv_clause_m6"
  , "full_viv_tier_match_m6", "full_viv_collect_m6", "full_viv_count_m6", "full_viv_keys_m6"
  , "full_viv_sort_sched_m6", "full_viv_clear_tier_m6", "full_vivify_m6", "full_viv_collect_fid"
  , "full_viv_count_fid", "full_viv_sort2_fid", "full_viv_sort_fid", "full_vivify_tier_m6_hdr"
  , "full_vivify_m6_hdr", "full_prioritize_binaries_m6", "full_backbone_sched_m6"
  , "full_backbone_keep_m6", "full_backbone_unwind_m6", "full_backbone_prop_m6"
  , "full_backbone_analyze_m6", "full_backbone_round_m6", "full_backbone_m6", "full_trans_lit_m6"
  , "full_trans_sort_m6", "full_transitive_m6", "full_tarjan_pop_scc", "full_tarjan_scc"
  , "full_subst_elim_vars", "full_subst_rewrite_bins", "full_subst_rewrite_ar", "full_substitute"
  , "full_enter_dense", "full_sort_bin_watches_fid", "full_rebuild_watches", "full_cong_find"
  , "full_cong_merge", "full_cong_mark_trail", "full_cong_unit_fold", "full_cong_equiv_fold"
  , "full_has_ternary", "full_sort_u32", "full_cong_extract_ite", "full_cong_emit_xor"
  , "full_cong_has_clause_k", "full_cong_emit_xor4", "full_cong_extract_xor_k"
  , "full_cong_try_xor_ite", "full_cong_count_bins", "full_cong_eb_match"
  , "full_cong_extract_binaries", "full_cong_find_units_equivs", "full_cong_extract"
  , "full_cong_and_match", "full_cong_xor_match", "full_cong_enq_var", "full_cong_eval_gate"
  , "full_cong_work_step", "full_cong_worklist", "full_cong_sift_pairs_fid"
  , "full_cong_sort_pairs_fid", "full_cong_fwd_subsume", "full_cong_ht_hash_ent_m7"
  , "full_cong_ht_init_m7", "full_cong_ht_grow_m7", "full_cong_ht_grow_clear_m7"
  , "full_cong_ht_lookup_m7", "full_cong_ht_insert_m7", "full_cong_u64_sift_m7"
  , "full_cong_u64_sort_m7", "full_cong_bsearch_u64_m7", "full_cong_copy_condbin_m7"
  , "full_cong_extract_condeq_m7", "full_cong_merge_condeq_m7", "full_cong_extract_ite_all_m7"
  , "full_congruence_dense", "full_k512_init", "full_k512_watch", "full_k512_assign"
  , "full_k512_add_clause", "full_k512_mtf", "full_k512_backtrack", "full_k512_propagate"
  , "full_k512_ana_clause", "full_k512_analyze", "full_k512_solve", "full_k512_flip"
  , "full_k512_add_live", "full_m4_sweep_cone", "full_m4_sweep_refine_sig"
  , "full_m4_sweep_rand_phases", "full_m4_sweep_flip_round", "full_m4_sweep_sim"
  , "full_m4_sweep_rearm", "full_m4_sweep_build_pht", "full_m4_sweep_units"
  , "full_m4_sweep_classes", "full_m4_sweep_var", "full_sweep_dense_m5", "full_m6_max_v"
  , "full_k6_add_ticks", "full_k6_init", "full_k6_watch", "full_k6_assign", "full_k6_add_clause"
  , "full_k6_mtf", "full_k6_backtrack", "full_k6_propagate", "full_k6_ana_clause"
  , "full_k6_analyze", "full_k6_solve", "full_k6_flip", "full_k512_add_live_m6"
  , "full_m6_dense_prop_lit", "full_m6_dense_prop", "full_m6_sweep_cone"
  , "full_m6_sweep_refine_sig", "full_m6_sweep_rand_phases", "full_m6_sweep_solve"
  , "full_m6_sweep_flip_round", "full_m6_sweep_sim", "full_m6_sweep_rearm"
  , "full_m6_sweep_build_pht", "full_m6_extract_pht", "full_m6_refine_partition"
  , "full_m6_sweep_units", "full_m6_sweep_classes", "full_m6_els_ar", "full_m6_els_lit"
  , "full_m6_els_fold", "full_m6_dense_els", "full_m6_sweep_var", "full_m6_cand_sift"
  , "full_m6_collect_cands", "full_m6_sweep_vars", "full_sweep_dense_m6", "full_fwd_dedup_bins"
  , "full_dense_prop_unit_m7", "full_dense_flush_units_m7", "full_fwd_flush_large_m7"
  , "full_fwd_reconnect_irred_m7", "full_fwd_scan_lit_m7", "full_fwd_check_cl_m7"
  , "full_fwd_connect_subsumer_m7", "full_fwd_collect_sort_m7", "full_forward_sub_m7"
  , "full_bve_collect_m7", "full_forward_sub", "full_bve_collect", "full_bve_mark_and_m7"
  , "full_bve_find_equiv_m7", "full_bve_find_and_m7", "full_bve_get_tern_m7"
  , "full_bve_match_tern_m7", "full_bve_find_ite_side_m7", "full_bve_find_ite_m7"
  , "full_bve_xor_pat_m7", "full_bve_find_xor_m7", "full_k6_watch_m7", "full_k6_assign_m7"
  , "full_k6_mtf_m7", "full_k6_backtrack_m7", "full_k6_prop_m7", "full_k6_ana_cl_m7"
  , "full_k6_analyze_m7", "full_k6_solve_m7", "full_k6_core_m7", "full_bve_def_k6_m7"
  , "full_bve_gates_m7", "full_bve_resolve_pair", "full_bve_weaken", "full_bve_try_bce"
  , "full_bve_commit_res", "full_bve_ext_need", "full_bve_find_equiv_m8", "full_bve_find_and_m8"
  , "full_bve_match_tern_m8", "full_bve_find_ite_side_m8", "full_bve_find_ite_m8"
  , "full_k6_watch_m8", "full_k6_assign_m8", "full_k6_mtf_m8", "full_k6_backtrack_m8"
  , "full_k6_prop_m8", "full_k6_ana_cl_m8", "full_k6_analyze_m8", "full_k6_solve_m8"
  , "full_k6_core_m8", "full_k6_extract_and_solve_m8", "full_bve_def_k6_m8", "full_bve_k6_mv_fid"
  , "full_fid_k6_add_ticks", "full_k6_watch_fid", "full_k6_assign_fid", "full_k6_mtf_fid"
  , "full_k6_backtrack_fid", "full_k6_prop_fid", "full_k6_ana_cl_fid", "full_k6_analyze_fid"
  , "full_k6_solve_fid", "full_k6_core_fid", "full_k6_extract_and_solve_fid"
  , "full_bve_certify_unit_fid", "full_bve_def_k6_fid", "full_bve_gates_fid", "full_bve_var_m7"
  , "full_bve_var", "full_init_fresh_var", "full_bva_hop1", "full_bva_hop2", "full_bva_hop3"
  , "full_bva_match_large", "full_bva_steps_cap_fid", "full_bva_clines_fid", "full_fheap_up_fid"
  , "full_fheap_down_fid", "full_bva_count_lit_deg_fid", "full_bva_connect_clauses_fid"
  , "full_bva_match_large_bva_fid", "full_bva_scan_cands", "full_bva_pick_cand"
  , "full_bva_match_large_fid", "full_bva_filter_row", "full_bva_commit", "full_bva_try_lit"
  , "full_fheap_up", "full_fheap_down", "full_bva_upd_lit_fid", "full_factor"
  , "full_compact_needed", "full_compact_flush", "full_compact_mark_live"
  , "full_compact_assign_map", "full_compact_record_ext", "full_compact_bins"
  , "full_compact_arena", "full_compact_vars", "full_compact_sift_q", "full_compact_vmtf"
  , "full_compact_sift_h", "full_compact_heap", "full_compact", "full_reorder_weight_m7"
  , "full_reorder_sift_m7", "full_reorder_sift_fid", "full_reorder_queue_m7", "full_reorder_m6"
  , "full_bce_side_m4", "full_bce_pair_m4", "full_bce_var_m4", "full_bce_m4", "full_min_u64"
  , "full_max_u64", "full_elim_dticks", "full_bve_var_key_m7", "full_bve_heap_up_m7"
  , "full_bve_heap_down_m7", "full_bve_heap_push_m7", "full_bve_heap_pop_m7"
  , "full_bve_collect_nbrs_m7", "full_elim_bve_m7", "full_eliminate_m7", "full_eliminate_m6"
  , "full_lcg_next_m7", "full_m7_get64", "full_m7_set64", "full_m7_state_init"
  , "full_tumble_clause_m7", "full_tumble_clauses_m7", "full_tumble_m7", "full_lucky_polar_m7"
  , "full_lucky_late_m7", "full_randec_step_m7", "full_randec_var_m7", "full_decide_m7"
  , "full_ema_swap_m7", "full_switch_mode_m7", "full_probe_dticks_m6_hdr", "full_probe_tail_m6"
  , "full_probe_m6", "full_preprocess_m6", "full_simplify_m6", "m6_hdr_decide_fid"
  , "full_search_m6", "kissat_solve_bytes_m6", "full_preprocess", "full_search"
  , "kissat_solve_bytes" ]

theorem fidStep7Module_map_name :
    fidStep7Module.fns.map Fn.name = fidStep7FnNames := by
  t_kernel_rfl

-- Additive Step-10 callee & elim exports (`0` `import all` needed down-stream)
theorem fidStep7Env_tickRel :
    ∀ a m Q X, Full.fullTickRelSpec a m Q X → fidStep7Env "full_tick_rel" [i64] [] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).tickRel

theorem fidStep7Env_emaUpdate :
    ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      fidStep7Env "full_ema_update" [i64, i64] [] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).emaUpdate
theorem fidStep7Env_assignLvl :
    ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      fidStep7Env "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).assignLvl
theorem fidStep7Env_addClause :
    ∀ a m Q X, Full.fullAddClauseSpec a m Q X →
      fidStep7Env "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X :=
  fid7_m7Row (m7FidPart1Callees_of_sub m7FidBase_part1_mem).addClause
theorem fidStep7Env_restoreBumpAnaM6Hdr :
    ∀ a m Q X, m6aRestoreBumpAnaSpecP M6ExtW2bPres a m Q X →
      fidStep7Env "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X :=
  fid7_frontRow 1 "full_restore_bump_ana_m6_hdr" (m6aRestoreBumpAnaSpecP M6ExtW2bPres) rfl
    (fun _ _ _ _ h => m6aRestoreBumpAnaSpecP_monoXP h)
theorem fidStep7Env_anaFailedLitM6Hdr :
    ∀ a m Q X, m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      fidStep7Env "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X :=
  fid7_frontRow 2 "full_ana_failed_lit_m6_hdr" (m6aAnaFailedLitSpecP M6ExtW2bPres) rfl
    (fun _ _ _ _ h => m6aAnaFailedLitSpecP_monoXP h)
theorem fidStep7Env_minShrinkM6 :
    ∀ a m Q X, m8MinShrinkSpec a m Q X → fidStep7Env "full_min_shrink_m6" [i64] [] a m Q X :=
  fid7_frontRow 3 "full_min_shrink_m6" m8MinShrinkSpec rfl
    (fun _ _ _ _ h => m8MinShrinkSpec_monoX h)
theorem fidStep7Env_deduce1uipM6Hdr :
    ∀ a m Q X, FullM7Proof.m7Deduce1uipHdrSpec a m Q X →
      fidStep7Env "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X :=
  fid7_step2FrontRow 32 "full_deduce_1uip_m6_hdr" m6Deduce1uipHdrSpec (by t_kernel_rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6Deduce1uipHdrSpec_monoX h)
theorem fidStep7Env_detNewLevel :
    ∀ a m Q X, Full.fullDetNewLevelSpec a m Q X →
      fidStep7Env "full_det_new_level" [i64, i64] [i64] a m Q X :=
  fid7_m7Row_at 140 "full_det_new_level" Full.fullDetNewLevelSpec
theorem fidStep7Env_oneLitConfl :
    ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      fidStep7Env "full_one_lit_confl" [i64] [i64] a m Q X :=
  fid7_m7Row_at 141 "full_one_lit_confl" Full.fullOneLitConflSpec
theorem fidStep7Env_eagerSubsume :
    ∀ a m Q X, Full.fullEagerSubsumeSpec a m Q X →
      fidStep7Env "full_eager_subsume" [i64, i64] [] a m Q X :=
  fid7_m7Row_at 142 "full_eager_subsume" Full.fullEagerSubsumeSpec
theorem fidStep7Env_vivClauseM6 :
    ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      fidStep7Env "full_viv_clause_m6" [i64, i32] [i64] a m Q X :=
  fid7_step2FrontRow 13 "full_viv_clause_m6" fullVivClauseM6Spec
theorem fidStep7Env_vivClearTierM6 :
    ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      fidStep7Env "full_viv_clear_tier_m6" [i64, i64] [] a m Q X :=
  fid7_extraRow 50 "full_viv_clear_tier_m6" fullVivClearTierM6Spec
theorem fidStep7Env_vivCollectFid :
    ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      fidStep7Env "full_viv_collect_fid" [i64, i64] [i64] a m Q X :=
  fid7_step4FrontRow 6 "full_viv_collect_fid" fullVivCollectFidSpec
theorem fidStep7Env_vivCountFid :
    ∀ a m Q X, fullVivCountFidSpec a m Q X →
      fidStep7Env "full_viv_count_fid" [i64, i64] [] a m Q X :=
  fid7_step4FrontRow 7 "full_viv_count_fid" fullVivCountFidSpec
theorem fidStep7Env_vivSortFid :
    ∀ a m Q X, fullVivSortFidSpec a m Q X →
      fidStep7Env "full_viv_sort_fid" [i64, i64] [] a m Q X :=
  fid7_step4FrontRow 9 "full_viv_sort_fid" fullVivSortFidSpec
theorem fidStep7Env_bveK6MvFid :
    ∀ a m Q X, FullFidelityBve.fidBveK6MvSpec a m Q X →
      fidStep7Env "full_bve_k6_mv_fid" [i64] [i64] a m Q X :=
  fid7_step5FrontRow 6 "full_bve_k6_mv_fid" FullFidelityBve.fidBveK6MvSpec (by t_kernel_rfl)
    (by decide) (by decide) FullFidelityBve.fidBveK6MvSpec_noExit
theorem fidStep7Env_k6ExtractSolveFid :
    ∀ a m Q X, FullFidelityBve.fidK6ExtractSolveSpec a m Q X →
      fidStep7Env "full_k6_extract_and_solve_fid"
        [i64, i32, i32, i32, .bool, i32] [.bool] a m Q X :=
  fid7_step5FrontRow 17 "full_k6_extract_and_solve_fid" FullFidelityBve.fidK6ExtractSolveSpec
    (by t_kernel_rfl) (by decide) (by decide) FullFidelityBve.fidK6ExtractSolveSpec_noExit
theorem fidStep7Env_bveCertifyUnitFid :
    ∀ a m Q X, FullFidelityBve.fidBveCertifyUnitSpec a m Q X →
      fidStep7Env "full_bve_certify_unit_fid" [i64, i32, i32, i32, i32, i32] [.bool] a m Q X :=
  fid7_step5FrontRow 18 "full_bve_certify_unit_fid" FullFidelityBve.fidBveCertifyUnitSpec
    (by t_kernel_rfl) (by decide) (by decide) FullFidelityBve.fidBveCertifyUnitSpec_noExit

theorem fidStep7Env_elim_analyzeCoreM6 {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_analyze_core_m6" [i64] [i64] xs m Q X) : m6HdrAnalyzeSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[4]? =
      some ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup (List.mem_of_getElem? hrow) hf7
  exact m6HdrAnalyzeSpec_monoX hc

theorem fidStep7Env_elim_vivifyTierM6Hdr {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep7Env "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] xs m Q X) :
    m6aVivifyTierSpec xs m Q X := by
  have hrow : fidStep7Bundle.frontTable[16]? =
      some ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩ := rfl
  have hf7 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep7_front_nodup (List.mem_of_getElem? hrow) hf7
  exact m6aVivifyTierSpec_monoX (X := fun _ _ _ _ => False) hc

theorem fidStep7Env_elim_congHasClauseK {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep7Env "full_cong_has_clause_k" [i64, i32] [.bool] xs m Q X) :
    FullM6CongSubst.m6CongHasClauseKSpec xs m Q X := by
  change patchEnv fidStep7Bundle "full_cong_has_clause_k" [i64, i32] [.bool] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  change patchEnv fidBundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h
  have hrow : fidStep3Bundle.frontTable[2]? =
      some ⟨"full_cong_has_clause_k", [i64, i32], [.bool],
        FullM6CongSubst.m6CongHasClauseKSpec, true⟩ := by t_kernel_rfl
  have hf3 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep3_front_nodup (List.mem_of_getElem? hrow) hf3
  exact hc

theorem fidStep7Env_elim_bveDefK6Fid {xs : Tup Val [i64, i32, i32, i32]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidStep7Env "full_bve_def_k6_fid" [i64, i32, i32, i32] [] xs m Q X) :
    m8BveGatesSpec xs m Q (fun _ _ _ _ => False) := by
  change patchEnv fidStep7Bundle "full_bve_def_k6_fid" [i64, i32, i32, i32] [] xs m Q X at h
  rw [patchEnv_base_eq fidStep7Bundle (fid7_find_none_front7 (by decide))] at h
  change patchEnv fidBundle _ _ _ xs m Q X at h
  rw [patchEnv_base_eq fidBundle (fid_find_none_front (by decide))] at h
  have hrow : fidStep5Bundle.frontTable[19]? =
      some ⟨"full_bve_def_k6_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩ := by
    t_kernel_rfl
  have hf5 := fid7_of_prefix_mem ⟨_, List.mem_of_getElem? hrow, rfl, rfl, rfl⟩ h
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidStep5_front_nodup (List.mem_of_getElem? hrow) hf5
  exact hc

@[expose] def fidStep7_step10_sigPairs : List (Nat × SigEntry) :=
  [ (30, ("full_tick_rel", [i64], [])), (34, ("full_ema_update", [i64, i64], []))
  , (36, ("full_assign_lvl", [i64, i32, i32, i32], []))
  , (41, ("full_add_clause", [i64, i32, i32, .bool], [i64]))
  , (121, ("full_restore_bump_ana_m6_hdr", [i64], []))
  , (122, ("full_ana_failed_lit_m6_hdr", [i64], [i64]))
  , (140, ("full_min_shrink_m6", [i64], []))
  , (144, ("full_deduce_1uip_m6_hdr", [i64], [i64]))
  , (145, ("full_det_new_level", [i64, i64], [i64]))
  , (146, ("full_one_lit_confl", [i64], [i64]))
  , (147, ("full_eager_subsume", [i64, i64], []))
  , (155, ("full_analyze_core_m6", [i64], [i64]))
  , (214, ("full_viv_clause_m6", [i64, i32], [i64]))
  , (220, ("full_viv_clear_tier_m6", [i64, i64], []))
  , (222, ("full_viv_collect_fid", [i64, i64], [i64]))
  , (223, ("full_viv_count_fid", [i64, i64], []))
  , (225, ("full_viv_sort_fid", [i64, i64], []))
  , (226, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))
  , (257, ("full_cong_has_clause_k", [i64, i32], [.bool]))
  , (403, ("full_bve_k6_mv_fid", [i64], [i64]))
  , (414, ("full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool]))
  , (415, ("full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool]))
  , (416, ("full_bve_def_k6_fid", [i64, i32, i32, i32], [])) ]

private theorem fidStep7_step10_sigs_batch :
    sigsAtSorted7 0 (fidStep7_step10_sigPairs.map Prod.fst) fidStep7Module.fns =
      fidStep7_step10_sigPairs.map Prod.snd := by
  t_kernel_rfl

theorem fidStep7_step10_sig_at {p : Nat × SigEntry} (hp : p ∈ fidStep7_step10_sigPairs) :
    fidStep7Module.fns[p.1]?.map Fn.sig = some p.2 := by
  simpa using sigsAtSorted7_getElem? fidStep7Module.fns 0 fidStep7_step10_sigPairs
    (by decide) (fun _ _ => Nat.zero_le _) fidStep7_step10_sigs_batch p hp

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

end

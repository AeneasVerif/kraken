/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof1a
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof1b
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2a
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof3a
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof3b
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBvaProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import LeanQbe.T.Examples.Kissat.FullDefSweep
import LeanQbe.T.Examples.Kissat.FullFastSched
import LeanQbe.T.Examples.Kissat.FullM3Backbone
import LeanQbe.T.Examples.Kissat.FullM3CongBva
import LeanQbe.T.Examples.Kissat.FullM6BveFwd
import LeanQbe.T.Examples.Kissat.FullM6Hdr
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Examples.Kissat.FullM7Proof
import LeanQbe.T.Examples.Kissat.FullM7Search
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof (`FullFidelityAssemblyProof`, `499` fns)

Certifies the final Gate-1 `FullFidelityAssembly.fidModule` (`499` fns, `0` externs, `0` exits)
via `PatchModule.patchBundle_moduleOk` + `FullFidelityAssemblyUtil`:
1. `fidBundle : PatchBundle` layering `FullFidelityBva`'s `fidBvaRepls` (`7` repls) +
   `fidBvaBefores` (`7` helpers) onto `fidStep5Module` (`492` fns), isolating the `5` upgraded
   inner BVA contracts (`full_bva_scan_cands`, `full_bva_pick_cand`, `full_bva_filter_row`,
   `full_bva_commit`, `full_bva_try_lit`) while preserving `FullBvaHeap.fullFactorHeapSpec` and
   `FullM6Orch.m6ProbeSpec`.
2. Closed `499/499` `fid_moduleOk : ModuleOk fidEnv fidModule`, `fid_tableImpl`, `fidEnv_noExit`,
   `fid_solve_bytes_sound`, `fid_solve_bytes_host_sound`, `fid_unsat_nv` (`XPost := False`,
   `std3`), and `fidUnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssembly

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
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` Over `fidStep5Module` (`499/499` Fns) -/

/-- Flat `492`-row base specification table for Step 5. -/
private abbrev fidStep5EnvTable : List SpecEntry :=
  fidStep5Bundle.frontTable ++ fidStep5Bundle.baseTable

/-- Canonical Gate-1 `PatchBundle` composing `fidStep5Module` + `FullFidelityBva`. -/
def fidBundle : PatchBundle where
  baseMod := fidStep5Module
  baseTable := fidStep5EnvTable
  baseOk := fidStep5_moduleOk
  repls := fidBvaRepls
  replRows := fidBvaPatchReplRows
  befores := fidBvaBefores
  beforeRows := fidBvaPatchBeforeRows

/-- Closed `Env` for `fidModule` (`499` fns). -/
def fidEnv : Env :=
  patchEnv fidBundle

theorem fid_externs_empty : fidModule.externs = [] :=
  fidStep5_externs_empty

theorem fidFns_length : fidFns.length = 499 := by
  t_kernel_rfl

private def fidFrontNames : List Sym :=
  [ "full_bva_scan_cands", "full_bva_pick_cand", "full_bva_filter_row"
  , "full_bva_commit", "full_bva_try_lit", "full_factor", "full_probe_m6"
  , "full_bva_steps_cap_fid", "full_bva_clines_fid", "full_fheap_up_fid"
  , "full_fheap_down_fid", "full_bva_count_lit_deg_fid"
  , "full_bva_connect_clauses_fid", "full_bva_match_large_bva_fid" ]

private theorem fid_frontNames_eq :
    fidBundle.frontTable.map SpecEntry.name = fidFrontNames :=
  rfl

private theorem fid_front_nodup :
    (fidBundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fid_frontNames_eq]
  decide

private theorem fid_replSigs_batch :
    [424, 425, 427, 428, 429, 432, 483].map (fun i => fidStep5Fns[i]?.map Fn.sig) =
      [ some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32])
      , some ("full_bva_pick_cand", [i64, i32, i32], [i32])
      , some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32])
      , some ("full_bva_commit", [i64, i32], [.bool])
      , some ("full_bva_try_lit", [i64, i32, i64], [.bool])
      , some ("full_factor", [i64, i64], [i64])
      , some ("full_probe_m6", [i64, .bool], [i64]) ] := by
  t_kernel_rfl

private theorem fid_slot {i : Nat} {s : SigEntry}
    (hi : fidStep5Fns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep5Fns, g.sig = s := by
  cases h : fidStep5Fns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidModule_replSigs_ok :
    ∀ r ∈ fidBvaRepls, ∀ g ∈ fidStep5Module.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidStep5Fns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidStep5Fns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fid_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have hnd : (fidStep5Fns.map Fn.name).Nodup :=
      (List.nodup_append.mp fidStep5Module_names_nodup).1
    have heq := nodup_name_eq Fn.name hnd hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [fidBvaRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (slotSig_at fid_replSigs_batch 0 424 _) rfl hnm
  · exact hslot (slotSig_at fid_replSigs_batch 1 425 _) rfl hnm
  · exact hslot (slotSig_at fid_replSigs_batch 2 427 _) rfl hnm
  · exact hslot (slotSig_at fid_replSigs_batch 3 428 _) rfl hnm
  · exact hslot (slotSig_at fid_replSigs_batch 4 429 _) rfl hnm
  · exact hslot (slotSig_at fid_replSigs_batch 5 432 _) rfl hnm
  · exact hslot (slotSig_at fid_replSigs_batch 6 483 _) rfl hnm

theorem fidModule_names_nodup : fidModule.namesNodup :=
  LeanQbe.T.Module.namesNodup_of_checkNamesNodup (by t_kernel_rfl)

private theorem fidModule_patchCallsOk :
    checkPatchCallsOk fidStep5Module fidBvaRepls fidBvaBefores = true := by
  t_kernel_rfl

private theorem fid_isSome_find_of_name_mem {tbl : List SpecEntry} {nm : Sym}
    (h : nm ∈ tbl.map SpecEntry.name) : (tbl.find? (·.name == nm)).isSome = true := by
  obtain ⟨e, he, hnm⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hnm⟩

private theorem fid_front_covered :
    ∀ fn, (fn ∈ fidBvaRepls ∨ fn ∈ fidBvaBefores.flatMap Prod.snd) →
      (fidBundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  refine fid_isSome_find_of_name_mem ?_
  rw [fid_frontNames_eq]
  rcases hfn with hr | hb
  · simp only [fidBvaRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [fidBvaBefores, fidBvaHelpers, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 2. Fast Table Lookup, Elimination, Isolation (`bad`), & Agree Helpers -/

private abbrev FidEnvSpec (nm : Sym) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ a m Q X, sp a m Q X → fidEnv nm as bs a m Q X

private theorem fid_find_none_of_names {tbl : List SpecEntry} {nms : List Sym}
    (hmap : tbl.map SpecEntry.name = nms) {f : Sym}
    (hf : !(nms.contains f) = true) :
    tbl.find? (·.name == f) = none := by
  apply List.find?_eq_none.mpr
  intro e he hbeq
  have hm : nms.contains f = true :=
    List.contains_iff_mem.mpr (hmap ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he))
  have hnot : nms.contains f = false := by
    cases hc : nms.contains f
    · rfl
    · rw [hc] at hf; exact absurd hf (by decide)
  exact Bool.false_ne_true (hnot.symm.trans hm)

private theorem fid_find_none_front {f : Sym}
    (hf : !(fidFrontNames.contains f) = true) :
    fidBundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names fid_frontNames_eq hf

private theorem fid_find_none_front5 {f : Sym}
    (hf5 : !(fidStep5FrontNames.contains f) = true) :
    fidStep5Bundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names fidStep5_frontNames_eq hf5

private theorem fid_find_none_front4 {f : Sym}
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains f) = true) :
    fidStep4Bundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names rfl hf4

private theorem fid_find_none_front3 {f : Sym}
    (hf3 : !(fidStep3FrontNames.contains f) = true) :
    fidStep3Bundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names fidStep3_frontNames_eq hf3

private theorem fid_find_none_front2 {f : Sym}
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true) :
    fidStep2Bundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names rfl hf2

private theorem fid_find_none_front1 {f : Sym}
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true) :
    fidStep1Bundle.frontTable.find? (·.name == f) = none :=
  fid_find_none_of_names (by simp [fidStep1Bundle, PatchBundle.frontTable]) hf1

private theorem fid_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidBundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs =>
  patchEnv_of_front_mem fidBundle fid_front_nodup (List.mem_of_getElem? hi) (hno a m Q X hs)

private theorem fid_step4FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep4Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidBundle nm as bs a m Q X
  rw [patchEnv_base_eq fidBundle (fid_find_none_front hf)]
  change patchEnv fidStep5Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 hf5)]
  exact patchEnv_of_front_mem fidStep4Bundle fidStep4_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fid_step3FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep3Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidBundle nm as bs a m Q X
  rw [patchEnv_base_eq fidBundle (fid_find_none_front hf)]
  change patchEnv fidStep5Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 hf5)]
  change patchEnv fidStep4Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 hf4)]
  exact patchEnv_of_front_mem fidStep3Bundle fidStep3_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fid_step2FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep2Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidBundle nm as bs a m Q X
  rw [patchEnv_base_eq fidBundle (fid_find_none_front hf)]
  change patchEnv fidStep5Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 hf5)]
  change patchEnv fidStep4Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 hf4)]
  change patchEnv fidStep3Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 hf3)]
  exact patchEnv_of_front_mem fidStep2Bundle fidStep2_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fid_of_fidBase {f : Sym} {as bs : List Ty}
    (hf : !(fidFrontNames.contains f) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains f) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains f) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv f as bs xs m Q X) :
    fidEnv f as bs xs m Q X := by
  change patchEnv fidBundle f as bs xs m Q X
  rw [patchEnv_base_eq fidBundle (fid_find_none_front hf)]
  change patchEnv fidStep5Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 hf5)]
  change patchEnv fidStep4Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 hf4)]
  change patchEnv fidStep3Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 hf3)]
  change patchEnv fidStep2Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep2Bundle (fid_find_none_front2 hf2)]
  change patchEnv fidStep1Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep1Bundle (fid_find_none_front1 hf1)]
  exact h

private theorem fid_m7Row {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs =>
  fid_of_fidBase hf hf5 hf4 hf3 hf2 hf1
    (fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hmem hno a m Q X hs)))

private theorem fid_m7Row_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : m7FidBaseTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp :=
  fid_m7Row (List.mem_of_getElem? hi) hf hf5 hf4 hf3 hf2 hf1 hnmf hncp hno

private theorem fid_baseRow_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidBaseSpecTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs =>
  fid_of_fidBase hf hf5 hf4 hf3 hf2 hf1
    (Env.ofTable_of_mem (List.mem_of_getElem? hi) fidBaseSpecTable_nodup (hno a m Q X hs))

private theorem fid_elim_to_fidBase {nm : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep5EnvTable nm as bs xs m Q X)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide) :
    fidBaseEnv nm as bs xs m Q X := by
  change patchEnv fidStep5Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 hf5)] at h
  change patchEnv fidStep4Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 hf4)] at h
  change patchEnv fidStep3Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 hf3)] at h
  change patchEnv fidStep2Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep2Bundle (fid_find_none_front2 hf2)] at h
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle (fid_find_none_front1 hf1)] at h
  exact h

private theorem fid_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep5EnvTable nm as bs xs m Q X)
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
  fidBaseEnv_elim_m7Base hmem (fid_elim_to_fidBase h hf5 hf4 hf3 hf2 hf1)
    hneEx hneSw hne1 hne2 hne3 hne4 hne5 hne6 hne7

private def fidBadNames : List Sym :=
  [ "full_bva_scan_cands", "full_bva_pick_cand", "full_bva_filter_row"
  , "full_bva_commit", "full_bva_try_lit"
  , "full_bva_steps_cap_fid", "full_bva_clines_fid", "full_fheap_up_fid"
  , "full_fheap_down_fid", "full_bva_count_lit_deg_fid"
  , "full_bva_connect_clauses_fid", "full_bva_match_large_bva_fid" ]

private theorem fid_noCallBad_aux :
    checkNoCallBad (fidBvaRepls.map Fn.name) fidBadNames fidStep5Fns = true := by
  t_kernel_rfl

private theorem fid_noCallBad :
    ∀ fn ∈ fidStep5Module.fns,
      fidBundle.repls.find? (·.name == fn.name) = none →
      fidBundle.frontTable.find? (·.name == fn.name) = none →
      noCallInFn fidBadNames fn = true := by
  intro fn hmem hr hfind
  have hcell : ((fidBvaRepls.map Fn.name).contains fn.name ||
      noCallInFn fidBadNames fn) = true :=
    List.all_eq_true.mp fid_noCallBad_aux fn hmem
  rcases (Bool.or_eq_true _ _).mp hcell with hskip | hok
  · rw [List.contains_iff_mem] at hskip
    obtain ⟨r, hr', hrnm⟩ := List.mem_map.mp hskip
    have hsome : (fidBvaRepls.find? (·.name == fn.name)).isSome = true :=
      List.find?_isSome.mpr ⟨r, hr', beq_iff_eq.mpr hrnm⟩
    change (fidBvaRepls.find? (·.name == fn.name)) = none at hr
    rw [hr] at hsome; cases hsome
  · exact hok

private theorem fid_agree :
    ∀ s ∈ fidStep5Module.sigs, s.1 ∉ fidBadNames →
      ∀ xs m P E, Env.ofTable fidStep5EnvTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidBundle s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs hnb xs m P E hBase
  cases hf : fidBundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidBundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hPush :
          ∀ hmem : e ∈ fidBundle.frontTable, e.eff xs m P E →
            patchEnv fidBundle e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidBundle fid_front_nodup hmem hs'
      have hFail : ∀ nm0 ∈ fidBadNames, e.name = nm0 →
          patchEnv fidBundle e.name e.as e.rs xs m P E := fun nm0 hnm0 heq =>
        absurd (heq ▸ hnm0) hnb
      have he0 := he
      simp only [fidBundle, PatchBundle.frontTable, fidBvaPatchReplRows, fidBvaPatchBeforeRows,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hPush he0 (by
          have hmem : fidBaseSpecTable[409]? = some
              ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩ := by
            t_kernel_rfl
          exact (m8cp_ofTable_sig_elim fidBaseSpecTable_nodup (List.mem_of_getElem? hmem)
            (fid_elim_to_fidBase hBase)).2.2)
      · exact hPush he0 (m6ProbeSpec_monoX (fid_elim_m7Base m7FidBase_probeM6_mem hBase))
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
      · exact hFail _ (by decide) rfl
    · have hne : ∀ e' ∈ fidBundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fid_front_nodup he' he (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidBundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift fidBundle.frontTable hne

/-! ## 3. Front-Table Implementation Helpers & `fid_moduleOk` (`499/499`) -/

private theorem fid_fn_eq_before {fn b : Fn}
    (hfn : fn ∈ fidModule.fns) (hb : b ∈ fidBvaHelpers)
    (htgt : ∃ g0 ∈ fidStep5Fns, g0.name = "full_bva_scan_cands")
    (hnm : b.name = fn.name) : fn = b := by
  have hModNd : (fidModule.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidModule_names_nodup).1
  obtain ⟨g0, hg0, hgn⟩ := htgt
  have hbm : b ∈ fidModule.fns := by
    change b ∈ patchFns fidBvaRepls fidBvaBefores fidStep5Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    unfold patchInsAt
    simp only [fidBvaBefores, List.find?, hgn, beq_self_eq_true]
    exact hb
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fid_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidModule.fns) (hr : r ∈ fidBvaRepls)
    {idx : Nat} {s : SigEntry} (hslot : fidStep5Fns[idx]?.map Fn.sig = some s)
    (hrn : r.name = s.1) (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidModule.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidModule_names_nodup).1
  obtain ⟨g, hg, hgs⟩ := fid_slot hslot
  have hrm : r ∈ fidModule.fns :=
    mem_patchFns_of_repl (by decide) hr hg (hrn.trans (congrArg Prod.fst hgs).symm)
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fid_front_impl :
    ∀ fn e, fn ∈ fidBundle.patchedMod.fns →
      fidBundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidEnv fn e := by
  intro fn e hfn hf
  change fn ∈ fidModule.fns at hfn
  change fidBundle.frontTable.find? (·.name == fn.name) = some e at hf
  have he : e ∈ fidBundle.frontTable := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  have rScan := fid_frontRow 0 "full_bva_scan_cands" fidBvaScanCandsSpec
  have rPick := fid_frontRow 1 "full_bva_pick_cand" fullBvaPickCandSpec
  have rFilt := fid_frontRow 2 "full_bva_filter_row" fidBvaFilterRowSpec
  have rComm := fid_frontRow 3 "full_bva_commit" fidBvaCommitSpec
  have rTry := fid_frontRow 4 "full_bva_try_lit" fidBvaTryLitSpec
  have rFac := fid_frontRow 5 "full_factor" FullBvaHeap.fullFactorHeapSpec
  have rSteps := fid_frontRow 7 "full_bva_steps_cap_fid" fidBvaStepsCapSpec
  have rClines := fid_frontRow 8 "full_bva_clines_fid" fidBvaClinesSpec
  have rUp := fid_frontRow 9 "full_fheap_up_fid" fidFheapUpSpec
  have rDown := fid_frontRow 10 "full_fheap_down_fid" fidFheapDownSpec
  have rDeg := fid_frontRow 11 "full_bva_count_lit_deg_fid" fidBvaCountLitDegSpec
  have rConn := fid_frontRow 12 "full_bva_connect_clauses_fid" fidBvaConnectClausesSpec
  have rBml := fid_frontRow 13 "full_bva_match_large_bva_fid" fidBvaMatchLargeBvaSpec
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have rArenaNext := fid_m7Row_at 11 "full_arena_next" Full.fullArenaNextSpec
  have rAllocCl := fid_m7Row_at 12 "full_alloc_cl" Full.fullAllocClSpec
  have rDefrag := fid_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)
  have rWatchPush := fid_m7Row_at 18 "full_watch_push" Full.fullWatchPushSpec
  have rLog10 := fid_m7Row hc1.log10Q16M7 (hno := fun _ _ _ _ h => m7Log10Q16Spec_monoX h)
  have rScale := fid_m7Row hc1.scaleDeltaM5
  have rDelaying := fid_m7Row_at 66 "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rBumpDelay := fid_m7Row_at 67 "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rReduceDelay := fid_m7Row_at 68 "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rSetWm := fid_m7Row_at 71 "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rUnwatch := fid_step4FrontRow 0 "full_unwatch_large" fullUnwatchLargeSpec
  have rViv := fid_step4FrontRow 2 "full_vivify_m6_hdr" m6aVivifySpec
    rfl (by decide) (by decide) (fun _ _ _ _ h => m6aVivifySpec_monoX h)
  have rAddBin := fid_m7Row_at 178 "full_add_bin" Full.fullAddBinSpec
  have rDelBin := fid_m7Row_at 179 "full_delete_binary" Full.fullDeleteBinarySpec
  have rBackbone := fid_step2FrontRow 16 "full_backbone_m6" FullM3Backbone.fullBackboneSpec
  have rSubst := fid_step2FrontRow 19 "full_substitute" Full.fullSubstituteSpec
  have rEnterDense := fid_step2FrontRow 20 "full_enter_dense" FullFastSched.schedEnterDenseSpec
  have rReb := fid_step2FrontRow 21 "full_rebuild_watches" Full.fullRebuildWatchesSpec
  have rCong := fid_step3FrontRow 19 "full_congruence_dense"
    FullM3CongBva.m3CongruenceDenseSpec
  have rSweepDense := fid_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 15) rfl))
  have rFlushLarge := fid_m7Row (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 2) rfl))
    (hno := fun a m Q X h => fullFwdFlushLargeM6Spec_noExit a m Q X h)
  have rInitFresh := fid_m7Row m7FidP3InitFreshVar_mem
  have rProbeDt := fid_baseRow_at 458 "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64])
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rProbeTail := fid_m7Row (m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 17) rfl))
    (hno := fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  obtain ⟨g0, hg0, hsg0⟩ := fid_slot (slotSig_at fid_replSigs_batch 0 424
    (some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32])))
  have hgt : ∃ g ∈ fidStep5Fns, g.name = "full_bva_scan_cands" :=
    ⟨g0, hg0, congrArg Prod.fst hsg0⟩
  simp only [fidBundle, PatchBundle.frontTable, fidBvaPatchReplRows, fidBvaPatchBeforeRows,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaScanCandsFn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 0 424
        (some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_bva_scan_cands_fid_wp fidEnv rClines)
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaPickCandFn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 1 425
        (some ("full_bva_pick_cand", [i64, i32, i32], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_bva_pick_cand_fid_wp fidEnv)
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaFilterRowFn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 2 427
        (some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_bva_filter_row_fid_wp fidEnv rClines rBml)
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaCommitFn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 3 428
        (some ("full_bva_commit", [i64, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (full_bva_commit_fid_wp fidEnv rSteps rDefrag rInitFresh rAddBin rAllocCl
      rWatchPush rDelBin rUnwatch)
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaTryLitFn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 4 429
        (some ("full_bva_try_lit", [i64, i32, i64], [.bool]))) rfl hnm
    subst hfeq
    exact .of (full_bva_try_lit_fid_wp fidEnv rSteps rScan rPick rFilt rComm)
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaFactorFn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 5 432 (some ("full_factor", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_factor_fid_wp fidEnv rSteps rConn rDeg rUp rDown rTry)
  · have hfeq := fid_fn_eq_repl hfn (r := fidBvaProbeM6Fn) (by simp [fidBvaRepls])
      (slotSig_at fid_replSigs_batch 6 483 (some ("full_probe_m6", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_probe_m6_fid_wp fidEnv rProbeDt rLog10 rScale rViv rEnterDense rDelaying
      rCong rReb rSetWm rReduceDelay rBumpDelay rSweepDense rSubst rProbeTail rBackbone rFac)
  · have hfeq := fid_fn_eq_before hfn (b := fidBvaStepsCapFn) (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bva_steps_cap_fid_wp fidEnv)
  · have hfeq := fid_fn_eq_before hfn (b := fidBvaClinesFn) (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bva_clines_fid_wp fidEnv)
  · have hfeq := fid_fn_eq_before hfn (b := fidFheapUpFn) (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_fheap_up_fid_wp fidEnv)
  · have hfeq := fid_fn_eq_before hfn (b := fidFheapDownFn) (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_fheap_down_fid_wp fidEnv)
  · have hfeq := fid_fn_eq_before hfn (b := fidBvaCountLitDegFn) (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bva_count_lit_deg_fid_wp fidEnv)
  · have hfeq := fid_fn_eq_before hfn (b := fidBvaConnectClausesFn)
      (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bva_connect_clauses_fid_wp fidEnv rFlushLarge rArenaNext rWatchPush rDeg)
  · have hfeq := fid_fn_eq_before hfn (b := fidBvaMatchLargeBvaFn)
      (by simp [fidBvaHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bva_match_large_bva_fid_wp fidEnv)

/-- Closed `499/499` `ModuleOk` for `FullFidelityAssembly.fidModule` under
`fidEnv` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fid_moduleOk : ModuleOk fidEnv fidModule := by
  change ModuleOk (patchEnv fidBundle) fidBundle.patchedMod
  refine patchBundle_moduleOk fidBundle fidModule_names_nodup fidModule_replSigs_ok
    ?_ fidModule_patchCallsOk fid_front_covered fid_front_impl fidBadNames fid_noCallBad fid_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact fidBvaRepls_wf fn hr
  · exact fidBvaBefores_wf fn hb

/-! ## 4. `TableImpl`, Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

/-- Closed `499`-row specification table aligned 1-to-1 with `fidModule.fns` via head-first
lookup into `fidBundle.frontTable ++ fidStep5EnvTable`. -/
def fidSpecTable : List SpecEntry :=
  fidModule.fns.map fun fn =>
    ((fidBundle.frontTable ++ fidStep5EnvTable).find? (·.name == fn.name)).getD
      ⟨fn.name, fn.as, fn.rs, fun _ _ _ _ => False, true⟩

private theorem fid_env_ofTable_find_some {tbl : List SpecEntry} {nm : Sym} {e : SpecEntry}
    (hf : tbl.find? (·.name == nm) = some e)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : e.eff xs m Q X) : Env.ofTable tbl e.name e.as e.rs xs m Q X := by
  induction tbl with
  | nil => simp at hf
  | cons hd tl ih =>
    simp only [List.find?] at hf
    by_cases hnm : (hd.name == nm) = true
    · simp only [hnm, Option.some.injEq] at hf
      subst hf
      exact Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩
    · have hne_b : (hd.name == nm) = false := Bool.eq_false_iff.mpr hnm
      simp only [hne_b] at hf
      have hne : hd.name ≠ e.name := by
        have h1 : hd.name ≠ nm := by simpa [beq_iff_eq] using hnm
        have h2 : e.name = nm :=
          beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
        exact h2 ▸ h1
      rw [Env.ofTable_cons_ne hne]
      exact ih hf

private theorem fidSpecTable_sigs :
    fidSpecTable.map (fun e => (e.name, e.as, e.rs)) = fidModule.fns.map Fn.sig := by
  t_kernel_rfl

private theorem fidSpecTable_nodup : (fidSpecTable.map SpecEntry.name).Nodup := by
  have heq : fidSpecTable.map SpecEntry.name = fidModule.fns.map Fn.name := by
    have hs := congrArg (List.map Prod.fst) fidSpecTable_sigs
    simpa only [List.map_map, Function.comp_def, Fn.sig] using hs
  rw [heq]
  exact (List.nodup_append.mp fidModule_names_nodup).1

private theorem fid_tableImpl_aux :
    ∀ {pre fs : List Fn} {rs : List SpecEntry},
      fidModule.fns = pre ++ fs →
      rs.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
      (∀ r ∈ rs, r ∈ fidSpecTable) →
      (∀ r ∈ fidSpecTable, ∀ xs m Q X, r.eff xs m Q X → fidEnv r.name r.as r.rs xs m Q X) →
      TableImpl fidEnv fs rs
  | _, [], [], _, _, _, _ => trivial
  | _, [], _ :: _, _, hs, _, _ => by simp at hs
  | _, _ :: _, [], _, hs, _, _ => by simp at hs
  | pre, f :: fs, r :: rs, hsplit, hs, hsub, hLift => by
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨hs_hd, hs_tl⟩ := hs
    have hr_mem : r ∈ fidSpecTable := hsub r List.mem_cons_self
    rcases r with ⟨rn, ra, rr, rsp, rnx⟩
    dsimp only at hs_hd
    have hnm : rn = f.name := congrArg Prod.fst hs_hd
    have has : ra = f.as := congrArg (Prod.fst ∘ Prod.snd) hs_hd
    have hrs : rr = f.rs := congrArg (Prod.snd ∘ Prod.snd) hs_hd
    have hfn_ok := fid_moduleOk.fnsOk pre f fs hsplit
    refine ⟨?_, fid_tableImpl_aux (pre := pre ++ [f]) (by simpa [List.append_assoc] using hsplit)
      hs_tl (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hLift⟩
    refine ⟨⟨hnm, has, hrs⟩, fun xs m Q X heff => ?_⟩
    subst hnm; subst has; subst hrs
    exact hfn_ok.2.2 xs m Q X (hLift _ hr_mem xs m Q X heff)

/-- Closed `TableImpl` certifying all `499` functions of `fidModule` against `fidSpecTable`. -/
theorem fid_tableImpl :
    TableImpl fidEnv fidModule.fns fidSpecTable := by
  refine fid_tableImpl_aux (pre := []) rfl fidSpecTable_sigs (fun _ h => h) ?_
  intro r hr xs m Q X heff
  dsimp only [fidSpecTable] at hr
  obtain ⟨fn, hfn, heq⟩ := List.mem_map.mp hr
  cases hf : (fidBundle.frontTable ++ fidStep5EnvTable).find? (·.name == fn.name) with
  | some e =>
    rw [hf, Option.getD_some] at heq
    subst heq
    exact fid_env_ofTable_find_some hf heff
  | none =>
    exfalso
    have hn : (fidModule.fns.all fun g =>
        ((fidBundle.frontTable ++ fidStep5EnvTable).find? (·.name == g.name)).isSome) = true := by
      t_kernel_rfl
    have hsome := List.all_eq_true.mp hn fn hfn
    simp [hf] at hsome

theorem fidEnv_noExit :
    ∀ f as bs xs m Q X X',
      fidEnv f as bs xs m Q X → fidEnv f as bs xs m Q X' := by
  refine patchEnv_noExit_of fidBundle ?_ ?_
  · change (fidBvaPatchReplRows ++ fidBvaPatchBeforeRows).all SpecEntry.noExit = true
    decide
  · change (fidStep5Bundle.frontTable ++ (fidStep4Bundle.frontTable ++
      (fidStep3Bundle.frontTable ++ (fidStep2Bundle.frontTable ++
        (fidStep1ReplRows ++ fidBaseSpecTable))))).all SpecEntry.noExit = true
    rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide,
      ⟨by decide, fidBaseSpecTable_noExit⟩⟩⟩⟩⟩

private theorem fid_front_noSolveBytes :
    fidBundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : "kissat_solve_bytes" ∈ fidFrontNames :=
    fid_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
  exact absurd hm (by decide)

theorem fidEnv_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidBundle fid_front_noSolveBytes
    (fun _ _ _ _ hs => fidStep5Env_solve_bytes_of hs) a m Q X

theorem fid_solveBytes_mem : m6oSolveBytesFn ∈ fidModule.fns :=
  patchBundle_solveBytes_mem fidBundle fidStep5_solveBytes_mem fun r hr => by
    change r ∈ fidBvaRepls at hr
    simp only [fidBvaRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidModule` (`499` fns, `XPost := False`). -/
theorem fid_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fid_moduleOk fid_solveBytes_mem
    (fun _ _ _ _ hs => fidEnv_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidModule`. -/
theorem fid_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidModule`. -/
theorem fid_unsat_nv :
    Func.wp fidEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fid_moduleOk fid_solveBytes_mem
    (fun _ _ _ _ hs => fidEnv_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fid_moduleOk`. -/
theorem fidModule_acyclic : fidModule.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fid_moduleOk

/-- Canonical Gate-1 `KissatUnsatPkg` (`fidModule`, `fidInlPolicy`). -/
def fidUnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidModule fidInlPolicy fid_solveBytes_mem
    fidEnv fid_moduleOk fidEnv_noExit
    (fun _ _ _ _ hs => fidEnv_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssembly

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
public import LeanQbe.T.Examples.Kissat.FullM3Backbone
public import LeanQbe.T.Examples.Kissat.FullM3CongBva
public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM7Search
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
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
import LeanQbe.T.Examples.Kissat.FullM6Hdr
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Examples.Kissat.FullM7Proof
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
    (hi : m7FidBaseTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
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

/-! ## 5. Additive Thin Spec Interface for Step-12 (`0` `import all` Down-Stream) -/

private theorem fid_step5FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep5Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidBundle nm as bs a m Q X
  rw [patchEnv_base_eq fidBundle (fid_find_none_front hf)]
  exact patchEnv_of_front_mem fidStep5Bundle fidStep5_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fid_step1FrontRow (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hfind : fidStep1Bundle.frontTable.find? (·.name == nm) =
      some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
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
  change patchEnv fidStep2Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep2Bundle (fid_find_none_front2 hf2)]
  exact patchEnv_of_front_mem fidStep1Bundle fidStep1_front_nodup
    (List.mem_of_find?_eq_some hfind) (hno a m Q X hs)

private theorem fid_mfExtraRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : mfExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf : !(fidFrontNames.contains nm) = true := by decide)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hne : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    FidEnvSpec nm sp := fun a m Q X hs =>
  fid_of_fidBase hf hf5 hf4 hf3 hf2 hf1 (fid_extraRow i nm as bs sp hi hno hne a m Q X hs)

-- Step 1..5 front / extra / base / m7FidBase intro exports (52)
theorem fidEnv_bveGatesFid :
    ∀ a m Q X, FullM8CoreParity.m8BveGatesSpec a m Q X →
      fidEnv "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X :=
  fid_step5FrontRow 5 "full_bve_gates_fid" m8BveGatesSpec (by t_kernel_rfl)
    (by decide) (fun _ _ _ _ h => m8BveGatesSpec_noExit _ _ _ _ h)

theorem fidEnv_congExtractXorK :
    ∀ a m Q X, FullFidelityCong.fidCongExtractXorKSpec a m Q X →
      fidEnv "full_cong_extract_xor_k" [i64, i32, i32, i64, i64] [i64] a m Q X :=
  fid_step3FrontRow 3 "full_cong_extract_xor_k" FullFidelityCong.fidCongExtractXorKSpec

theorem fidEnv_congTryXorIte :
    ∀ a m Q X, FullFidelityCong.fidCongTryXorIteSpec a m Q X →
      fidEnv "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] a m Q X :=
  fid_step3FrontRow 4 "full_cong_try_xor_ite" FullFidelityCong.fidCongTryXorIteSpec

theorem fidEnv_luckyLateM7 :
    ∀ a m Q X, FullM7Search.m7LuckyLateSpec a m Q X →
      fidEnv "full_lucky_late_m7" [i64] [i64] a m Q X :=
  fid_step2FrontRow 23 "full_lucky_late_m7" FullM7Search.m7LuckyLateSpec (by t_kernel_rfl)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h)

theorem fidEnv_propagateIgnore :
    ∀ a m Q X, FullM6BcpS15.fullPropagateIgnoreS15Spec a m Q X →
      fidEnv "full_propagate_ignore" [i64, i64] [i64] a m Q X :=
  fid_step2FrontRow 30 "full_propagate_ignore" FullM6BcpS15.fullPropagateIgnoreS15Spec

theorem fidEnv_m6CollectCands :
    ∀ a m Q X, FullM6Sweep.m6CollectCandsSpec a m Q X →
      fidEnv "full_m6_collect_cands" [i64] [i32] a m Q X :=
  fid_step1FrontRow "full_m6_collect_cands" FullM6Sweep.m6CollectCandsSpec

theorem fidEnv_m6MaxV :
    ∀ a m Q X, FullM6Sweep.m6MaxVSpec a m Q X →
      fidEnv "full_m6_max_v" [i64] [i64] a m Q X :=
  fid_baseRow_at 302 "full_m6_max_v" FullM6Sweep.m6MaxVSpec

theorem fidEnv_k6Init :
    ∀ a m Q X, FullM6Sweep.k6InitSpec a m Q X →
      fidEnv "full_k6_init" [i64, i32] [] a m Q X :=
  fid_baseRow_at 304 "full_k6_init" FullM6Sweep.k6InitSpec

theorem fidEnv_k6AddClause :
    ∀ a m Q X, FullM6Sweep.k6AddClauseSpec a m Q X →
      fidEnv "full_k6_add_clause" [i64, i64, i32] [.bool] a m Q X :=
  fid_baseRow_at 307 "full_k6_add_clause" FullM6Sweep.k6AddClauseSpec

theorem fidEnv_m6DenseProp :
    ∀ a m Q X, FullM6Sweep.m6DensePropSpec a m Q X →
      fidEnv "full_m6_dense_prop" [i64] [.bool] a m Q X :=
  fid_baseRow_at 317 "full_m6_dense_prop" FullM6Sweep.m6DensePropSpec

theorem fidEnv_m6SweepRefineSig :
    ∀ a m Q X, FullM6Sweep.m6SweepRefineSigSpec a m Q X →
      fidEnv "full_m6_sweep_refine_sig" [i64, i32, i32] [] a m Q X :=
  fid_baseRow_at 319 "full_m6_sweep_refine_sig" FullM6Sweep.m6SweepRefineSigSpec

theorem fidEnv_m6SweepSolve :
    ∀ a m Q X, FullM6Sweep.m6SweepSolveSpec a m Q X →
      fidEnv "full_m6_sweep_solve" [i64, i32, i64] [i64] a m Q X :=
  fid_baseRow_at 321 "full_m6_sweep_solve" FullM6Sweep.m6SweepSolveSpec

theorem fidEnv_m6SweepFlipRound :
    ∀ a m Q X, FullM6Sweep.m6SweepFlipRoundSpec a m Q X →
      fidEnv "full_m6_sweep_flip_round" [i64, i32] [i32] a m Q X :=
  fid_baseRow_at 322 "full_m6_sweep_flip_round" FullM6Sweep.m6SweepFlipRoundSpec

theorem fidEnv_m6SweepVar :
    ∀ a m Q X, FullM6Sweep.m6SweepVarSpec a m Q X →
      fidEnv "full_m6_sweep_var" [i64, i32, i64] [i64] a m Q X :=
  fid_baseRow_at 334 "full_m6_sweep_var" FullM6Sweep.m6SweepVarSpec

theorem fidEnv_vivBestImpliedM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivBestImpliedM6Spec a m Q X →
      fidEnv "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X :=
  fid_mfExtraRow 35 "full_viv_best_implied_m6" FullM6VivBackbone.fullVivBestImpliedM6Spec

theorem fidEnv_vivFinishM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivFinishM6Spec a m Q X →
      fidEnv "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X :=
  fid_mfExtraRow 39 "full_viv_finish_m6" FullM6VivBackbone.fullVivFinishM6Spec

theorem fidEnv_vivL0SimpM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivL0SimpM6Spec a m Q X →
      fidEnv "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X :=
  fid_mfExtraRow 42 "full_viv_l0_simp_m6" FullM6VivBackbone.fullVivL0SimpM6Spec

theorem fidEnv_vivReusePrefixM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivReusePrefixM6Spec a m Q X →
      fidEnv "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X :=
  fid_mfExtraRow 43 "full_viv_reuse_prefix_m6" FullM6VivBackbone.fullVivReusePrefixM6Spec

theorem fidEnv_vivTierMatchM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivTierMatchM6Spec a m Q X →
      fidEnv "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X :=
  fid_mfExtraRow 45 "full_viv_tier_match_m6" FullM6VivBackbone.fullVivTierMatchM6Spec

theorem fidEnv_kissatSkipWsComments :
    ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      fidEnv "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X :=
  fid_m7Row_at 2 "kissat_skip_ws_comments" kissatSkipWsCommentsSpec

theorem fidEnv_kissatNextLit :
    ∀ a m Q X, kissatNextLitSpec a m Q X →
      fidEnv "kissat_next_lit" [i64, i64] [i64] a m Q X :=
  fid_m7Row_at 6 "kissat_next_lit" kissatNextLitSpec

theorem fidEnv_heapPush :
    ∀ a m Q X, Full.fullHeapPushSpec a m Q X →
      fidEnv "full_heap_push" [i64, i32] [] a m Q X :=
  fid_m7Row_at 21 "full_heap_push" Full.fullHeapPushSpec

theorem fidEnv_assign :
    ∀ a m Q X, Full.fullAssignSpec a m Q X →
      fidEnv "full_assign" [i64, i32, i32] [] a m Q X :=
  fid_m7Row_at 36 "full_assign" Full.fullAssignSpec

theorem fidEnv_backtrackRawM5 :
    ∀ a m Q X, FullM5HeurCore.fullBacktrackRawSpec a m Q X →
      fidEnv "full_backtrack_raw_m5" [i64, i64] [] a m Q X :=
  fid_m7Row_at 38 "full_backtrack_raw_m5" FullM5HeurCore.fullBacktrackRawSpec

theorem fidEnv_skipCl :
    ∀ a m Q X, Full.fullSkipClSpec a m Q X →
      fidEnv "full_skip_cl" [i64, i64] [.bool] a m Q X :=
  fid_m7Row_at 76 "full_skip_cl" Full.fullSkipClSpec

theorem fidEnv_analyzeRsn :
    ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      fidEnv "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X :=
  fid_m7Row_at 113 "full_analyze_rsn" Full.fullAnalyzeRsnSpec

theorem fidEnv_otfsLarge :
    ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      fidEnv "full_otfs_large" [i64, i32, i32] [.bool] a m Q X :=
  fid_m7Row_at 121 "full_otfs_large" Full.fullOtfsLargeSpec

theorem fidEnv_otfsBin :
    ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      fidEnv "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X :=
  fid_m7Row_at 122 "full_otfs_bin" Full.fullOtfsBinSpec

theorem fidEnv_otfsSubsume :
    ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      fidEnv "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X :=
  fid_m7Row_at 123 "full_otfs_subsume" Full.fullOtfsSubsumeSpec

theorem fidEnv_setInactive :
    ∀ a m Q X, Full.fullSetInactiveSpec a m Q X →
      fidEnv "full_set_inactive" [i64, i32, i32] [] a m Q X :=
  fid_m7Row_at 180 "full_set_inactive" Full.fullSetInactiveSpec

theorem fidEnv_addUnit :
    ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      fidEnv "full_add_unit" [i64, i32] [.bool] a m Q X :=
  fid_m7Row_at 181 "full_add_unit" Full.fullAddUnitSpec

theorem fidEnv_prioritizeBinariesM6 :
    ∀ a m Q X, FullM6VivBackbone.fullPrioritizeBinariesM6Spec a m Q X →
      fidEnv "full_prioritize_binaries_m6" [i64] [.bool] a m Q X :=
  fid_m7Row_at 219 "full_prioritize_binaries_m6" FullM6VivBackbone.fullPrioritizeBinariesM6Spec

theorem fidEnv_backboneKeepM6 :
    ∀ a m Q X, FullM6VivBackbone.fullBackboneKeepM6Spec a m Q X →
      fidEnv "full_backbone_keep_m6" [i64, i64] [] a m Q X :=
  fid_m7Row_at 221 "full_backbone_keep_m6" FullM6VivBackbone.fullBackboneKeepM6Spec

theorem fidEnv_backboneRoundM6 :
    ∀ a m Q X, FullM6VivBackbone.fullBackboneRoundM6Spec a m Q X →
      fidEnv "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X :=
  fid_m7Row_at 225 "full_backbone_round_m6" FullM6VivBackbone.fullBackboneRoundM6Spec

theorem fidEnv_congFind :
    ∀ a m Q X, Full.fullCongFindSpec a m Q X →
      fidEnv "full_cong_find" [i64, i32] [i32] a m Q X :=
  fid_m7Row_at 238 "full_cong_find" Full.fullCongFindSpec

theorem fidEnv_congUnitFold :
    ∀ a m Q X, FullM3CongBva.m3CongUnitFoldSpec a m Q X →
      fidEnv "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X :=
  fid_m7Row_at 241 "full_cong_unit_fold" FullM3CongBva.m3CongUnitFoldSpec

theorem fidEnv_congEquivFold :
    ∀ a m Q X, FullM3CongBva.m3CongEquivFoldSpec a m Q X →
      fidEnv "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X :=
  fid_m7Row_at 242 "full_cong_equiv_fold" FullM3CongBva.m3CongEquivFoldSpec

theorem fidEnv_sortU32 :
    ∀ a m Q X, Full.fullSortU32Spec a m Q X →
      fidEnv "full_sort_u32" [i64, i32] [] a m Q X :=
  fid_m7Row_at 244 "full_sort_u32" Full.fullSortU32Spec

theorem fidEnv_congCountBins :
    ∀ a m Q X, FullM6CongSubst.m6CongCountBinsSpec a m Q X →
      fidEnv "full_cong_count_bins" [i64] [] a m Q X :=
  fid_m7Row_at 250 "full_cong_count_bins" FullM6CongSubst.m6CongCountBinsSpec

theorem fidEnv_congXorMatch :
    ∀ a m Q X, FullM6CongSubst.m6CongXorMatchSpec a m Q X →
      fidEnv "full_cong_xor_match" [i64, i32, i32] [i32] a m Q X :=
  fid_m7Row_at 256 "full_cong_xor_match" FullM6CongSubst.m6CongXorMatchSpec

theorem fidEnv_fwdDedupBins :
    ∀ a m Q X, Full.fullFwdDedupBinsSpec a m Q X →
      fidEnv "full_fwd_dedup_bins" [i64] [.bool] a m Q X :=
  fid_m7Row_at 300 "full_fwd_dedup_bins" Full.fullFwdDedupBinsSpec

theorem fidEnv_denseFlushUnitsM7 :
    ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      fidEnv "full_dense_flush_units_m7" [i64] [.bool] a m Q X :=
  fid_m7Row_at 302 "full_dense_flush_units_m7" FullM6BveFwd.fullDenseFlushUnitsM6Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit

theorem fidEnv_fwdFlushLargeM7 :
    ∀ a m Q X, FullM6BveFwd.fullFwdFlushLargeM6Spec a m Q X →
      fidEnv "full_fwd_flush_large_m7" [i64] [] a m Q X :=
  fid_m7Row_at 303 "full_fwd_flush_large_m7" FullM6BveFwd.fullFwdFlushLargeM6Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM6BveFwd.fullFwdFlushLargeM6Spec_noExit

theorem fidEnv_fwdReconnectIrredM7 :
    ∀ a m Q X, FullM6BveFwd.fullFwdReconnectIrredM6Spec a m Q X →
      fidEnv "full_fwd_reconnect_irred_m7" [i64] [] a m Q X :=
  fid_m7Row_at 304 "full_fwd_reconnect_irred_m7" FullM6BveFwd.fullFwdReconnectIrredM6Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM6BveFwd.fullFwdReconnectIrredM6Spec_noExit

theorem fidEnv_fwdCheckClM7 :
    ∀ a m Q X, FullM7BveGates.fullFwdCheckClM7Spec a m Q X →
      fidEnv "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X :=
  fid_m7Row_at 306 "full_fwd_check_cl_m7" FullM7BveGates.fullFwdCheckClM7Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM7BveGates.fullFwdCheckClM7Spec_noExit

theorem fidEnv_fwdConnectSubsumerM7 :
    ∀ a m Q X, FullM6BveFwd.fullFwdConnectSubsumerM6Spec a m Q X →
      fidEnv "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X :=
  fid_m7Row_at 307 "full_fwd_connect_subsumer_m7" FullM6BveFwd.fullFwdConnectSubsumerM6Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM6BveFwd.fullFwdConnectSubsumerM6Spec_noExit

theorem fidEnv_fwdCollectSortM7 :
    ∀ a m Q X, FullM6BveFwd.fullFwdCollectSortM6Spec a m Q X →
      fidEnv "full_fwd_collect_sort_m7" [i64] [i64] a m Q X :=
  fid_m7Row_at 308 "full_fwd_collect_sort_m7" FullM6BveFwd.fullFwdCollectSortM6Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM6BveFwd.fullFwdCollectSortM6Spec_noExit

theorem fidEnv_bveCollectM7 :
    ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      fidEnv "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X :=
  fid_m7Row_at 310 "full_bve_collect_m7" Full.fullBveCollectSpec

theorem fidEnv_bveGatesM7 :
    ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      fidEnv "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X :=
  fid_m7Row_at 332 "full_bve_gates_m7" FullM7BveGates.fullBveGatesM7Spec rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM7BveGates.fullBveGatesM7Spec_noExit

theorem fidEnv_bveResolvePair :
    ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      fidEnv "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X :=
  fid_m7Row_at 333 "full_bve_resolve_pair" Full.fullBveResolvePairSpec

theorem fidEnv_bveWeaken :
    ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      fidEnv "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X :=
  fid_m7Row_at 334 "full_bve_weaken" FullFastBveBudgets.fullBveWeakenTmkSpec

theorem fidEnv_bveExtNeed :
    ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      fidEnv "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X :=
  fid_m7Row_at 337 "full_bve_ext_need" Full.fullBveExtNeedSpec

-- Step 1..5 / mfExtra / m7FidBase elim exports (27)
private theorem fid_peel_to_step5 {f : Sym} {as bs : List Ty}
    (hf : !(fidFrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidEnv f as bs xs m Q X) : Env.ofTable fidStep5EnvTable f as bs xs m Q X := by
  change patchEnv fidBundle f as bs xs m Q X at h
  rwa [patchEnv_base_eq fidBundle (fid_find_none_front hf)] at h

theorem fidEnv_elim_zeroTables2 {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : fidEnv "full_zero_tables2" [i64] [] xs m Q X) : Full.fullZeroTables2Spec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 42) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_initHdr {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidEnv "full_init_hdr" [i64, i64, i64, i64] [] xs m Q X) :
    Full.fullInitHdrSpec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 45) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_parseBodyM6 {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_parse_body_m6" [i64, i64] [i64] xs m Q X) :
    Full.fullParseBodySpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change Env.ofTable (fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep2Bundle.frontTable.find? (·.name == "full_parse_body_m6") =
      some ⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩ := by
    t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_extend {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : fidEnv "full_extend" [i64] [] xs m Q X) : Full.fullExtendSpec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 174) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_luckyScan {xs : Tup Val [i64, .bool, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_lucky_scan" [i64, .bool, .bool] [i64] xs m Q X) :
    Full.fullLuckyScanSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change Env.ofTable (fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep2Bundle.frontTable.find? (·.name == "full_lucky_scan") =
      some ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.fullLuckyScanSpec, true⟩ := by
    t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_m6SweepCone {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_m6_sweep_cone" [i64, i32] [i64] xs m Q X) :
    FullM6Sweep.m6SweepConeSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change patchEnv fidStep2Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep2Bundle (fid_find_none_front2 (by decide))] at h5
  change Env.ofTable (fidStep1Bundle.frontTable ++ fidStep1Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep1Bundle.frontTable.find? (·.name == "full_m6_sweep_cone") =
      some ⟨"full_m6_sweep_cone", [i64, i32], [i64], FullM6Sweep.m6SweepConeSpec, true⟩ := by
    t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_saveTargetBest {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : fidEnv "full_save_target_best" [i64] [] xs m Q X) :
    Full.fullSaveTargetBestSpec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 37) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_backtrack {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : fidEnv "full_backtrack" [i64, i64] [] xs m Q X) : Full.fullBacktrackSpec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 39) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_deduce1uipM6 {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_deduce_1uip_m6" [i64] [i64] xs m Q X) :
    Full.fullDeduce1uipSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change Env.ofTable (fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep2Bundle.frontTable.find? (·.name == "full_deduce_1uip_m6") =
      some ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ := by
    t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_deduce1uipM6Hdr {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_deduce_1uip_m6_hdr" [i64] [i64] xs m Q X) :
    FullM6Orch.m6Deduce1uipHdrSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change Env.ofTable (fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep2Bundle.frontTable.find? (·.name == "full_deduce_1uip_m6_hdr") =
      some ⟨"full_deduce_1uip_m6_hdr", [i64], [i64],
        FullM6Orch.m6Deduce1uipHdrSpec, true⟩ := by
    t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_oneLitConfl {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_one_lit_confl" [i64] [i64] xs m Q X) :
    Full.fullOneLitConflSpec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 141) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_vivSort2Fid {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidEnv "full_viv_sort2_fid" [i64, i64, i64] [] xs m Q X) :
    FullFidelityVivK6.fullVivSort2FidSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change Env.ofTable (fidStep4Bundle.frontTable ++ fidStep4Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep4Bundle.frontTable.find? (·.name == "full_viv_sort2_fid") =
      some ⟨"full_viv_sort2_fid", [i64, i64, i64], [],
        FullFidelityVivK6.fullVivSort2FidSpec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_vivSortFid {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidEnv "full_viv_sort_fid" [i64, i64] [] xs m Q X) :
    FullFidelityVivK6.fullVivSortFidSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change Env.ofTable (fidStep4Bundle.frontTable ++ fidStep4Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep4Bundle.frontTable.find? (·.name == "full_viv_sort_fid") =
      some ⟨"full_viv_sort_fid", [i64, i64], [],
        FullFidelityVivK6.fullVivSortFidSpec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_vivClauseM6 {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_viv_clause_m6" [i64, i32] [i64] xs m Q X) :
    FullM6VivBackbone.fullVivClauseM6Spec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change Env.ofTable (fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep2Bundle.frontTable.find? (·.name == "full_viv_clause_m6") =
      some ⟨"full_viv_clause_m6", [i64, i32], [i64],
        FullM6VivBackbone.fullVivClauseM6Spec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_backboneSchedM6 {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_backbone_sched_m6" [i64] [i64] xs m Q X) :
    FullM6VivBackbone.fullBackboneSchedM6Spec xs m Q X :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 220) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_backboneM6 {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_backbone_m6" [i64, i64] [i64] xs m Q X) :
    FullM3Backbone.fullBackboneSpec xs m Q X := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change Env.ofTable (fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep2Bundle.frontTable.find? (·.name == "full_backbone_m6") =
      some ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩ := by
    t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_densePropUnitM7 {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidEnv "full_dense_prop_unit_m7" [i64, i32] [.bool] xs m Q X) :
    FullM6BveFwd.fullDensePropUnitM6Spec xs m Q (fun _ _ _ _ => False) := by
  have hmem : fidBaseSpecTable[340]? = some
      ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool],
        FullM6BveFwd.fullDensePropUnitM6Spec, true⟩ := by t_kernel_rfl
  exact (m8cp_ofTable_sig_elim fidBaseSpecTable_nodup (List.mem_of_getElem? hmem)
    (fid_elim_to_fidBase (fid_peel_to_step5 (by decide) h))).2.2

theorem fidEnv_elim_forwardSubM7 {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_forward_sub_m7" [i64, i64] [i64] xs m Q X) :
    FullFastBveBudgets.fullForwardSubFastSpec xs m Q (fun _ _ _ _ => False) :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 309) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_bveCommitRes {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X) :
    FullFastBveBudgets.fullBveCommitResTmkSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : fidBaseSpecTable[375]? = some
      ⟨"full_bve_commit_res", [i64, i64, i64], [i64],
        FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩ := by t_kernel_rfl
  exact (m8cp_ofTable_sig_elim fidBaseSpecTable_nodup (List.mem_of_getElem? hmem)
    (fid_elim_to_fidBase (fid_peel_to_step5 (by decide) h))).2.2

theorem fidEnv_elim_bveVarM7 {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_bve_var_m7" [i64, i32] [i64] xs m Q X) :
    FullFastBveBudgets.fullBveVarDefSpec xs m Q (fun _ _ _ _ => False) := by
  have h5 := fid_peel_to_step5 (by decide) h
  change Env.ofTable (fidStep5Bundle.frontTable ++ fidStep5Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep5Bundle.frontTable.find? (·.name == "full_bve_var_m7") =
      some ⟨"full_bve_var_m7", [i64, i32], [i64],
        FullFastBveBudgets.fullBveVarDefSpec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_congWorkStep {xs : Tup Val [i64, i64, i64, i64, i32]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] xs m Q X) :
    FullM6CongSubst.m6CongWorkStepSpec xs m Q (fun _ _ _ _ => False) := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change Env.ofTable (fidStep3Bundle.frontTable ++ fidStep3Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep3Bundle.frontTable.find? (·.name == "full_cong_work_step") =
      some ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
        FullM6CongSubst.m6CongWorkStepSpec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_addClause {xs : Tup Val [i64, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X) :
    Full.fullAddClauseSpec xs m Q (fun _ _ _ _ => False) :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 40) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_sweepCopy {xs : Tup Val [i64, i64, i64, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] xs m Q X) :
    Full.fullSweepCopySpec xs m Q (fun _ _ _ _ => False) :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 97) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_vivSortCountsM6 {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidEnv "full_viv_sort_counts_m6" [i64, i32] [] xs m Q X) :
    FullM6VivBackbone.fullVivSortCountsM6Spec xs m Q (fun _ _ _ _ => False) := by
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat (by decide) (by decide)
    (by decide) (fid_elim_to_fidBase (fid_peel_to_step5 (by decide) h)))
  have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
    (by decide) (by decide) (by decide) hsw
  have hrow : m7FidBaseTable[205]? = some
      ⟨"full_viv_sort_counts_m6", [i64, i32], [],
        FullM6VivBackbone.fullVivSortCountsM6Spec, true⟩ := rfl
  cases hm7 with
  | base _ hb => exact m7FidBase_elim_of_mem (List.mem_of_getElem? hrow) hb
  | extra hex => exact mf_extra_elim (List.mem_of_getElem? (i := 40) rfl) hex

theorem fidEnv_elim_transSortM6 {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidEnv "full_trans_sort_m6" [i64, i64] [] xs m Q X) :
    FullM6VivBackbone.fullTransSortM6Spec xs m Q (fun _ _ _ _ => False) :=
  fid_elim_m7Base (List.mem_of_getElem? (i := 228) rfl) (fid_peel_to_step5 (by decide) h)

theorem fidEnv_elim_m6SweepSim {xs : Tup Val [i64, i32, i64]} {m : Mem 64}
    {Q : Post [i32]} {X : XPost}
    (h : fidEnv "full_m6_sweep_sim" [i64, i32, i64] [i32] xs m Q X) :
    FullM6Sweep.m6SweepSimSpec xs m Q (fun _ _ _ _ => False) := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change patchEnv fidStep2Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep2Bundle (fid_find_none_front2 (by decide))] at h5
  change Env.ofTable (fidStep1Bundle.frontTable ++ fidStep1Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep1Bundle.frontTable.find? (·.name == "full_m6_sweep_sim") =
      some ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32],
        FullM6Sweep.m6SweepSimSpec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

theorem fidEnv_elim_m6SweepVars {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidEnv "full_m6_sweep_vars" [i64, i64, i64] [i64] xs m Q X) :
    FullM6Sweep.m6SweepVarsSpec xs m Q (fun _ _ _ _ => False) := by
  have h5 := fid_peel_to_step5 (by decide) h
  change patchEnv fidStep5Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep5Bundle (fid_find_none_front5 (by decide))] at h5
  change patchEnv fidStep4Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep4Bundle (fid_find_none_front4 (by decide))] at h5
  change patchEnv fidStep3Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep3Bundle (fid_find_none_front3 (by decide))] at h5
  change patchEnv fidStep2Bundle _ _ _ xs m Q X at h5
  rw [patchEnv_base_eq fidStep2Bundle (fid_find_none_front2 (by decide))] at h5
  change Env.ofTable (fidStep1Bundle.frontTable ++ fidStep1Bundle.baseTable) _ _ _ xs m Q X at h5
  have hfind : fidStep1Bundle.frontTable.find? (·.name == "full_m6_sweep_vars") =
      some ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64],
        FullM6Sweep.m6SweepVarsSpec, true⟩ := by t_kernel_rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h5

end LeanQbe.T.Examples.Kissat.FullFidelityAssembly

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice
public import LeanQbe.T.Examples.Kissat.FullFidelityTiersProof
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof1a
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof1b
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof2a
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof2b
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof3a
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof3a0
import LeanQbe.T.Examples.Kissat.FullFidelityCongProof3b
import LeanQbe.T.Examples.Kissat.FullFidelityCongProofHt
import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice0
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice
import all LeanQbe.T.Examples.Kissat.FullFidelityTiersProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7AnalyzeHdrProof
import all LeanQbe.T.Examples.Kissat.FullM6OrchProof0
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullM6CongSubst
import LeanQbe.T.Examples.Kissat.FullM7Proof
import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Examples.Kissat.FullM7CongIte
import LeanQbe.T.Examples.Kissat.FullM8FidV12
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 3 (`FullFidelityAssemblyStep3Proof`)

Certifies `FullFidelityAssemblyStep3.fidStep3Module` (`474` fns, `0` externs, `0` exits) via
`PatchModule.patchBundle_moduleOk` + `FullFidelityAssemblyUtil`:
1. `fidStep3Bundle : PatchBundle` layering `FullFidelityCong` (`19` repls + `3` befores +
   `1` rewire `full_cong_work_step`) and `FullFidelityTiers` (`2` repls:
   `m6_hdr_sync_legacy_tiers`, `full_analyze_rsn_m6_hdr`) onto `fidStep2Module` (`471` fns).
2. Closed `474/474` `fidStep3_moduleOk : ModuleOk fidStep3Env fidStep3Module`,
   `fidStep3Env_noExit`, `fidStep3_solve_bytes_sound`, `fidStep3_solve_bytes_host_sound`,
   `fidStep3_unsat_nv` (`XPost := False`, `std3`), and `fidStep3UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullFidelityTiers
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` Over `fidStep2Module` (`474/474` Fns) -/

/-- The `21` `SpecEntry` rows corresponding to `fidStep3Repls` (`19` Cong + `2` Tiers). -/
def fidStep3ReplRows : List SpecEntry :=
  fidCongReplRows ++ fidTiersSpecs

/-- Flat `471`-row base specification table for Step 2. -/
private abbrev fidStep2EnvTable : List SpecEntry :=
  fidStep2Bundle.frontTable ++ fidStep2Bundle.baseTable

/-- Step-3 `PatchBundle` composing `fidStep2Module` + `FullFidelityCong` + `FullFidelityTiers`. -/
def fidStep3Bundle : PatchBundle where
  baseMod := fidStep2Module
  baseTable := fidStep2EnvTable
  baseOk := fidStep2_moduleOk
  repls := fidStep3Repls
  replRows := fidStep3ReplRows
  befores := fidCongBefores
  beforeRows := fidCongBeforeRows
  rewiredRows := fidCongRewireRows

/-- Closed `Env` for `fidStep3Module` (`474` fns). -/
def fidStep3Env : Env :=
  patchEnv fidStep3Bundle

theorem fidStep3_externs_empty : fidStep3Module.externs = [] :=
  fidStep2_externs_empty

theorem fidStep3Fns_length : fidStep3Fns.length = 474 := by
  t_kernel_rfl

private def fidStep3ReplNames : List Sym :=
  [ "full_cong_emit_xor", "full_cong_has_clause_k", "full_cong_extract_xor_k"
  , "full_cong_try_xor_ite", "full_cong_extract", "full_cong_and_match"
  , "full_cong_eval_gate", "full_cong_worklist", "full_cong_fwd_subsume"
  , "full_cong_ht_hash_ent_m7", "full_cong_ht_init_m7", "full_cong_ht_grow_m7"
  , "full_cong_ht_grow_clear_m7", "full_cong_ht_lookup_m7", "full_cong_ht_insert_m7"
  , "full_cong_copy_condbin_m7", "full_cong_merge_condeq_m7", "full_cong_extract_ite_all_m7"
  , "full_congruence_dense", "m6_hdr_sync_legacy_tiers", "full_analyze_rsn_m6_hdr" ]

private def fidStep3FrontNames : List Sym :=
  "full_cong_work_step" :: fidStep3ReplNames ++
    [ "full_cong_emit_xor4", "full_cong_sift_pairs_fid", "full_cong_sort_pairs_fid" ]

private def fidStep3Bad : List Sym :=
  [ "full_cong_emit_xor", "full_cong_extract_xor_k", "full_cong_try_xor_ite", "full_cong_extract"
  , "full_cong_and_match", "full_cong_eval_gate", "full_cong_worklist", "full_cong_ht_hash_ent_m7"
  , "full_cong_ht_init_m7", "full_cong_ht_grow_m7", "full_cong_ht_grow_clear_m7"
  , "full_cong_ht_lookup_m7", "full_cong_ht_insert_m7", "full_cong_copy_condbin_m7"
  , "full_cong_merge_condeq_m7", "full_cong_extract_ite_all_m7" ]

private theorem fidStep3_replNames_eq : fidStep3Repls.map Fn.name = fidStep3ReplNames :=
  rfl

private theorem fidStep3_frontNames_eq :
    fidStep3Bundle.frontTable.map SpecEntry.name = fidStep3FrontNames :=
  rfl

private theorem fidStep3_front_nodup :
    (fidStep3Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep3_frontNames_eq]
  decide

private theorem fidStep3_replSigs_batch :
    [251, 252, 253, 254, 259, 260, 263, 265, 266, 267, 268, 269, 270, 271, 272, 276, 278, 279,
      280, 60, 116].map (fun i => fidStep2Fns[i]?.map Fn.sig) =
      [ some ("full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64])
      , some ("full_cong_has_clause_k", [i64, i32], [.bool])
      , some ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64])
      , some ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64])
      , some ("full_cong_extract", [i64, i64, i64], [i64])
      , some ("full_cong_and_match", [i64, i32, i32], [.bool])
      , some ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64])
      , some ("full_cong_worklist", [i64, i64, i64, i64], [i64])
      , some ("full_cong_fwd_subsume", [i64, i64], [i64])
      , some ("full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64])
      , some ("full_cong_ht_init_m7", [i64, i64, i64, i64], [i64])
      , some ("full_cong_ht_grow_m7", [i64, i64], [i64])
      , some ("full_cong_ht_grow_clear_m7", [i64, i64], [i64])
      , some ("full_cong_ht_lookup_m7", [i64, i64, i32, i32], [i32])
      , some ("full_cong_ht_insert_m7", [i64, i64, i32], [i32])
      , some ("full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64])
      , some ("full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32])
      , some ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32])
      , some ("full_congruence_dense", [i64, i64], [i64])
      , some ("m6_hdr_sync_legacy_tiers", [i64], [])
      , some ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]) ] := by
  t_kernel_rfl

private theorem fidStep3_slot {i : Nat} {s : SigEntry}
    (hi : fidStep2Fns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep2Fns, g.sig = s := by
  cases h : fidStep2Fns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidStep3Module_replSigs_ok :
    ∀ r ∈ fidStep3Repls, ∀ g ∈ fidStep2Module.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidStep2Fns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidStep2Fns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fidStep3_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have hnd : (fidStep2Fns.map Fn.name).Nodup :=
      (List.nodup_append.mp fidStep2Module_names_nodup).1
    have heq := nodup_name_eq Fn.name hnd hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [fidStep3Repls, fidCongRepls, fidTiersRepls, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (slotSig_at fidStep3_replSigs_batch 0 251 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 1 252 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 2 253 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 3 254 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 4 259 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 5 260 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 6 263 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 7 265 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 8 266 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 9 267 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 10 268 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 11 269 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 12 270 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 13 271 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 14 272 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 15 276 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 16 278 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 17 279 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 18 280 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 19 60 _) rfl hnm
  · exact hslot (slotSig_at fidStep3_replSigs_batch 20 116 _) rfl hnm

theorem fidStep3Module_names_nodup : fidStep3Module.namesNodup :=
  LeanQbe.T.Module.namesNodup_of_checkNamesNodup (by t_kernel_rfl)

private theorem fidStep3Module_patchCallsOk :
    checkPatchCallsOk fidStep2Module fidStep3Repls fidCongBefores = true := by
  t_kernel_rfl

private theorem fidStep3_isSome_find_of_name_mem {tbl : List SpecEntry} {nm : Sym}
    (h : nm ∈ tbl.map SpecEntry.name) : (tbl.find? (·.name == nm)).isSome = true := by
  obtain ⟨e, he, hnm⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hnm⟩

private theorem fidStep3_front_covered :
    ∀ fn, (fn ∈ fidStep3Repls ∨ fn ∈ fidCongBefores.flatMap Prod.snd) →
      (fidStep3Bundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  refine fidStep3_isSome_find_of_name_mem ?_
  rw [fidStep3_frontNames_eq]
  rcases hfn with hr | hb
  · simp only [fidStep3Repls, fidCongRepls, fidTiersRepls, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [fidCongBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide

private theorem fidStep3_noCallBad_filter :
    (fidStep2Fns.filter fun fn =>
      !fidStep3ReplNames.contains fn.name && !fidStep3FrontNames.contains fn.name).all
      (noCallInFn fidStep3Bad) = true := by
  t_kernel_rfl

private theorem fidStep3_none_not_contains {tbl : List Sym} {nm : Sym}
    (hnone : ∀ x ∈ tbl, x ≠ nm) : tbl.contains nm = false := by
  induction tbl with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨(hnone hd List.mem_cons_self).symm, ih fun y hy => hnone y (List.mem_cons_of_mem _ hy)⟩

private theorem fidStep3_noCallBad :
    ∀ fn ∈ fidStep2Module.fns,
      fidStep3Repls.find? (·.name == fn.name) = none →
      fidStep3Bundle.frontTable.find? (·.name == fn.name) = none →
      noCallInFn fidStep3Bad fn = true := by
  intro fn hmem hr hf
  have hnr : fidStep3ReplNames.contains fn.name = false := by
    refine fidStep3_none_not_contains fun nm hnm => ?_
    rw [← fidStep3_replNames_eq] at hnm
    obtain ⟨r, hr_mem, rfl⟩ := List.mem_map.mp hnm
    intro heq
    have h1 := List.find?_eq_none.mp hr r hr_mem
    simp [heq] at h1
  have hnf : fidStep3FrontNames.contains fn.name = false := by
    refine fidStep3_none_not_contains fun nm hnm => ?_
    rw [← fidStep3_frontNames_eq] at hnm
    obtain ⟨e, he_mem, rfl⟩ := List.mem_map.mp hnm
    intro heq
    have h1 := List.find?_eq_none.mp hf e he_mem
    simp [heq] at h1
  exact List.all_eq_true.mp fidStep3_noCallBad_filter fn
    (List.mem_filter.mpr ⟨hmem, by rw [hnr, hnf]; rfl⟩)

/-! ## 2. Fast Table Lookup, Elimination, & Spec Agree Helpers -/

private abbrev Fid3EnvSpec (nm : Sym) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ a m Q X, sp a m Q X → fidStep3Env nm as bs a m Q X

private theorem fidStep3_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep3Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid3EnvSpec nm sp := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep3Bundle fidStep3_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep3_of_fidBase {f : Sym} {as bs : List Ty}
    (hf3 : !(fidStep3FrontNames.contains f) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv f as bs xs m Q X) :
    fidStep3Env f as bs xs m Q X := by
  have hnot3 : fidStep3Bundle.frontTable.find? (·.name == f) = none := by
    apply List.find?_eq_none.mpr
    intro e he hbeq
    have hnm : e.name = f := beq_iff_eq.mp hbeq
    have hm : fidStep3FrontNames.contains f = true :=
      List.contains_iff_mem.mpr (fidStep3_frontNames_eq ▸ (hnm ▸ List.mem_map_of_mem he))
    have hnot : fidStep3FrontNames.contains f = false := by
      cases hc : fidStep3FrontNames.contains f
      · rfl
      · rw [hc] at hf3; exact absurd hf3 (by decide)
    exact Bool.false_ne_true (hnot.symm.trans hm)
  have hnot2 : fidStep2Bundle.frontTable.find? (·.name == f) = none := by
    apply List.find?_eq_none.mpr
    intro e he hbeq
    have hnm : e.name = f := beq_iff_eq.mp hbeq
    have hm : (fidStep2Bundle.frontTable.map SpecEntry.name).contains f = true :=
      List.contains_iff_mem.mpr (hnm ▸ List.mem_map_of_mem he)
    have hnot : (fidStep2Bundle.frontTable.map SpecEntry.name).contains f = false := by
      cases hc : (fidStep2Bundle.frontTable.map SpecEntry.name).contains f
      · rfl
      · rw [hc] at hf2; exact absurd hf2 (by decide)
    exact Bool.false_ne_true (hnot.symm.trans hm)
  have hnot1 : fidStep1Bundle.frontTable.find? (·.name == f) = none := by
    apply List.find?_eq_none.mpr
    intro e he hbeq
    have hnm : e.name = f := beq_iff_eq.mp hbeq
    have hm : (fidStep1ReplRows.map SpecEntry.name).contains f = true :=
      List.contains_iff_mem.mpr
        (hnm ▸ List.mem_map_of_mem (by simpa [fidStep1Bundle, PatchBundle.frontTable] using he))
    have hnot : (fidStep1ReplRows.map SpecEntry.name).contains f = false := by
      cases hc : (fidStep1ReplRows.map SpecEntry.name).contains f
      · rfl
      · rw [hc] at hf1; exact absurd hf1 (by decide)
    exact Bool.false_ne_true (hnot.symm.trans hm)
  change patchEnv fidStep3Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep3Bundle hnot3]
  change patchEnv fidStep2Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep2Bundle hnot2]
  change patchEnv fidStep1Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep1Bundle hnot1]
  exact h

private theorem fidStep3_m7BaseRow {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hf3 : !(fidStep3FrontNames.contains f) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    (hnmf : f ∉ mfExclNames := by decide)
    (hncp : f ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid3EnvSpec f sp := fun a m Q X hs =>
  fidStep3_of_fidBase hf3 hf2 hf1
    (fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hmem hno a m Q X hs)))

private theorem fidStep3_extraRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : mfExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid3EnvSpec nm sp := fun a m Q X hs =>
  fidStep3_of_fidBase hf3 hf2 hf1 (fid_extraRow i nm as bs sp hi hno hncp a m Q X hs)

private theorem fidStep3_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep2EnvTable nm as bs xs m Q X)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : fidStep1ReplRows.find? (·.name == nm) = none := by decide)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide)
    (hneSw : !(m8SwNamesLit.contains nm) = true := by decide)
    (hne1 : nm ∉ m8CpExclNames := by decide)
    (hne2 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (hne3 : nm ∉ fidBveHelperRows.map SpecEntry.name := by decide)
    (hne4 : nm ≠ "full_extend_push2" := by decide)
    (hne5 : nm ≠ "full_cong_enq_var" := by decide)
    (hne6 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne7 : nm ≠ "full_cong_worklist" := by decide) :
    sp xs m Q (fun _ _ _ _ => False) := by
  have hnot2 : fidStep2Bundle.frontTable.find? (·.name == nm) = none := by
    apply List.find?_eq_none.mpr
    intro e he hbeq
    have hnm : e.name = nm := beq_iff_eq.mp hbeq
    have hm : (fidStep2Bundle.frontTable.map SpecEntry.name).contains nm = true :=
      List.contains_iff_mem.mpr (hnm ▸ List.mem_map_of_mem he)
    have hnot : (fidStep2Bundle.frontTable.map SpecEntry.name).contains nm = false := by
      cases hc : (fidStep2Bundle.frontTable.map SpecEntry.name).contains nm
      · rfl
      · rw [hc] at hf2; exact absurd hf2 (by decide)
    exact Bool.false_ne_true (hnot.symm.trans hm)
  change patchEnv fidStep2Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep2Bundle hnot2] at h
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle hf1] at h
  exact fidBaseEnv_elim_m7Base hmem h hneEx hneSw hne1 hne2 hne3 hne4 hne5 hne6 hne7

private theorem fidStep3_before_not_in_step2 :
    (fidStep2Fns.map Fn.name).contains "full_cong_emit_xor4" = false ∧
    (fidStep2Fns.map Fn.name).contains "full_cong_sift_pairs_fid" = false ∧
    (fidStep2Fns.map Fn.name).contains "full_cong_sort_pairs_fid" = false :=
  ⟨by t_kernel_rfl, by t_kernel_rfl, by t_kernel_rfl⟩

private theorem fidStep3_agree :
    ∀ s ∈ fidStep2Module.sigs, s.1 ∉ fidStep3Bad →
      ∀ xs m P E, Env.ofTable fidStep2EnvTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidStep3Bundle s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs hnb xs m P E hBase
  cases hf : fidStep3Bundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidStep3Bundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hsig_in : e.name ∈ fidStep2Fns.map Fn.name := by
        have hm := hs
        rw [LeanQbe.T.Module.sigs, fidStep2_externs_empty, List.map_nil, List.append_nil] at hm
        obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
        exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
      have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
      have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
      have hPush :
          ∀ hmem : e ∈ fidStep3Bundle.frontTable, e.eff xs m P E →
            patchEnv fidStep3Bundle e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidStep3Bundle fidStep3_front_nodup hmem hs'
      have hWorkStep_b : (⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM6CongSubst.m6CongWorkStepSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_part2_mem _ (by
          unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
          exact List.mem_append_left _ (List.mem_of_getElem? (i := 14) rfl))
      have hHasClK_b : (⟨"full_cong_has_clause_k", [i64, i32], [.bool], m6CongHasClauseKSpec,
          true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_part2_mem _ (by
          unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
          exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
      have hSync_b : (⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [],
          true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_part1_mem _ (by
          unfold m7FidRowsPart1; (iterate 11 apply List.mem_append_right)
          exact List.mem_append_left _ (List.mem_of_getElem? (i := 7) rfl))
      have hArsn_b : (⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool],
          FullM7Proof.m7AnalyzeRsnHdrSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 10) rfl)
      have he0 := he
      simp only [fidStep3Bundle, PatchBundle.frontTable, fidCongRewireRows, fidStep3ReplRows,
        fidCongReplRows, fidTiersSpecs, fidCongBeforeRows, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hPush he0 (fidStep3_elim_m7Base hWorkStep_b hBase)
      · exact absurd (by decide : "full_cong_emit_xor" ∈ fidStep3Bad) hnb
      · exact hPush he0 (fidStep3_elim_m7Base hHasClK_b hBase)
      · exact absurd (by decide : "full_cong_extract_xor_k" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_try_xor_ite" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_extract" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_and_match" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_eval_gate" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_worklist" ∈ fidStep3Bad) hnb
      · exact hPush he0 (fidStep3_elim_m7Base hc2c.fwdSub hBase)
      · exact absurd (by decide : "full_cong_ht_hash_ent_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_ht_init_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_ht_grow_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_ht_grow_clear_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_ht_lookup_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_ht_insert_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_copy_condbin_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_merge_condeq_m7" ∈ fidStep3Bad) hnb
      · exact absurd (by decide : "full_cong_extract_ite_all_m7" ∈ fidStep3Bad) hnb
      · exact hPush he0 (fidStep3_elim_m7Base hc2p.congruenceDense hBase)
      · exact hPush he0 (fidStep3_elim_m7Base hSync_b hBase)
      · have hsp : m6AnalyzeRsnHdrSpec xs m P E := fidStep3_elim_m7Base hArsn_b hBase
        exact hPush he0 hsp
      · have hno : (fidStep2Fns.map Fn.name).contains "full_cong_emit_xor4" = false :=
          fidStep3_before_not_in_step2.1
        have hm : (fidStep2Fns.map Fn.name).contains "full_cong_emit_xor4" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno : (fidStep2Fns.map Fn.name).contains "full_cong_sift_pairs_fid" = false :=
          fidStep3_before_not_in_step2.2.1
        have hm : (fidStep2Fns.map Fn.name).contains "full_cong_sift_pairs_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno : (fidStep2Fns.map Fn.name).contains "full_cong_sort_pairs_fid" = false :=
          fidStep3_before_not_in_step2.2.2
        have hm : (fidStep2Fns.map Fn.name).contains "full_cong_sort_pairs_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
    · have hne : ∀ e' ∈ fidStep3Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep3_front_nodup he' he (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep3Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift fidStep3Bundle.frontTable hne

/-! ## 3. Front-Table Implementation Helpers & `fidStep3_moduleOk` (`474/474`) -/

private theorem fidStep3_fn_eq_before {fn b : Fn} {tgt : Sym} {ins : List Fn}
    (hfn : fn ∈ fidStep3Module.fns)
    (hpair : (tgt, ins) ∈ fidCongBefores)
    (hb : b ∈ ins)
    (htgt : ∃ g0 ∈ fidStep2Fns, g0.name = tgt)
    (hnm : b.name = fn.name) : fn = b := by
  have hModNd : (fidStep3Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep3Module_names_nodup).1
  obtain ⟨g0, hg0, hgn⟩ := htgt
  have hbm : b ∈ fidStep3Module.fns := by
    change b ∈ patchFns fidStep3Repls fidCongBefores fidStep2Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    unfold patchInsAt
    simp only [fidCongBefores] at hpair ⊢
    rcases List.mem_cons.mp hpair with h0 | h1
    · obtain ⟨ht0, hi0⟩ := Prod.mk.inj h0
      subst ht0; subst hi0
      simp only [hgn]
      exact hb
    · obtain ⟨ht1, hi1⟩ := Prod.mk.inj (List.mem_singleton.mp h1)
      subst ht1; subst hi1
      simp only [hgn]
      exact hb
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fidStep3_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidStep3Module.fns) (hr : r ∈ fidStep3Repls)
    {idx : Nat} {s : SigEntry} (hslot : fidStep2Fns[idx]?.map Fn.sig = some s)
    (hrn : r.name = s.1) (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidStep3Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep3Module_names_nodup).1
  obtain ⟨g, hg, hgs⟩ := fidStep3_slot hslot
  have hrm : r ∈ fidStep3Module.fns :=
    mem_patchFns_of_repl (by decide) hr hg (hrn.trans (congrArg Prod.fst hgs).symm)
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fidStep3_fn_eq_base {fn g : Fn}
    (hfn : fn ∈ fidStep3Module.fns) (idx : Nat)
    (hi : fidStep2Fns[idx]? = some g)
    (hne : fidStep3Repls.find? (·.name == g.name) = none := by rfl)
    (hnm : g.name = fn.name) : fn = g := by
  have hModNd : (fidStep3Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep3Module_names_nodup).1
  have hg : g ∈ fidStep2Fns := List.mem_of_getElem? hi
  have hgm : g ∈ fidStep3Module.fns := by
    change g ∈ patchFns fidStep3Repls fidCongBefores fidStep2Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨g, hg, Or.inr (by simp [hne])⟩
  exact nodup_name_eq Fn.name hModNd hfn hgm hnm.symm

private theorem fidStep3_front_impl :
    ∀ fn e, fn ∈ fidStep3Bundle.patchedMod.fns →
      fidStep3Bundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidStep3Env fn e := by
  intro fn e hfn hf
  change fn ∈ fidStep3Module.fns at hfn
  have he : e ∈ fidStep3Bundle.frontTable := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
  have hSortU32_b : (⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 53 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have hHasBin_b : (⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 30 apply List.mem_append_right)
      exact List.mem_append_left _ List.mem_cons_self)
  have hCountBins_b : (⟨"full_cong_count_bins", [i64], [], m6CongCountBinsSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 5) rfl))
  have hFind_b : (⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 49 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have hUnitFold_b : (⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  have hEquivFold_b : (⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      m3CongEquivFoldSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
  have hXorM_b : (⟨"full_cong_xor_match", [i64, i32, i32], [i32], m6CongXorMatchSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl))
  have hU64Sort_b : (⟨"full_cong_u64_sort_m7", [i64, i64], [], m7U64SortSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 56 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  have hExtCondeq_b : (⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64],
      m7ExtractCondeqSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 56 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 4) rfl))
  have hRec_b : (⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part1_mem _ (by
      unfold m7FidRowsPart1; (iterate 11 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl))
  have rSortU32 := fidStep3_m7BaseRow hSortU32_b
  have rHasTern := fidStep3_m7BaseRow m8cp_hasTernary_mem
  have rNext := fidStep3_m7BaseRow hc1.arenaNext
  have rHasBin := fidStep3_m7BaseRow hHasBin_b
  have rCountBins := fidStep3_m7BaseRow hCountBins_b
  have rFind := fidStep3_m7BaseRow hFind_b
  have rUnitFold := fidStep3_m7BaseRow hUnitFold_b
  have rEquivFold := fidStep3_m7BaseRow hEquivFold_b
  have rXorM := fidStep3_m7BaseRow hXorM_b
  have rEnqVar : Fid3EnvSpec "full_cong_enq_var" m8CongEnqVarSpec :=
    fun a m Q X h => fidStep3_of_fidBase (by decide) (by decide) (by decide)
      (fidBaseEnv_of_m8Sw (by decide)
        (M8FidV123t2Env.base (by decide) (M8FidV12Env.enqVar a m Q X h)))
  have rAddUnit := fidStep3_m7BaseRow hc2.addUnit
  have rU64Sort := fidStep3_m7BaseRow hU64Sort_b (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h => sp_u64Sort_noExit _ _ _ _ h)
  have rExtCondeq := fidStep3_m7BaseRow hExtCondeq_b
  have rExtBin := fidStep3_m7BaseRow hc2c.extBin
  have rFindUE := fidStep3_m7BaseRow hc2c.findUE
  have rEmitXor := fidStep3_frontRow 1 "full_cong_emit_xor" fidCongEmitXorSpec
  have rHasClK := fidStep3_frontRow 2 "full_cong_has_clause_k" m6CongHasClauseKSpec
  have rExtXorK := fidStep3_frontRow 3 "full_cong_extract_xor_k" fidCongExtractXorKSpec
  have rTryXI := fidStep3_frontRow 4 "full_cong_try_xor_ite" fidCongTryXorIteSpec
  have rExtract := fidStep3_frontRow 5 "full_cong_extract" fidCongExtractSpec
  have rAndM := fidStep3_frontRow 6 "full_cong_and_match" fidCongAndMatchSpec
  have rEvalG := fidStep3_frontRow 7 "full_cong_eval_gate" fidCongEvalGateSpec
  have rWork := fidStep3_frontRow 8 "full_cong_worklist" fidCongWorklistSpec
  have rFwdSub := fidStep3_frontRow 9 "full_cong_fwd_subsume" m6CongFwdSubsumeSpec
  have rHashEnt := fidStep3_frontRow 10 "full_cong_ht_hash_ent_m7" fidCongHtHashEntSpec
  have rHtGrow := fidStep3_frontRow 12 "full_cong_ht_grow_m7" fidCongHtGrowSpec
  have rCopyCb := fidStep3_frontRow 16 "full_cong_copy_condbin_m7" fidCongCopyCondbinLv0Spec
  have rMergeCe := fidStep3_frontRow 17 "full_cong_merge_condeq_m7" fidCongMergeCondeqSpec
  have rExtIteAll := fidStep3_frontRow 18 "full_cong_extract_ite_all_m7" fidCongExtractIteAllSpec
  have rEmitXor4 := fidStep3_frontRow 22 "full_cong_emit_xor4" fidCongEmitXor4Spec
  have rSiftPairs := fidStep3_frontRow 23 "full_cong_sift_pairs_fid" fidCongSiftPairsSpec
  have rSortPairs := fidStep3_frontRow 24 "full_cong_sort_pairs_fid" fidCongSortPairsSpec
  have rEnsure := fidStep3_extraRow 1 "m6_ext_ensure_init" m6ExtEnsureInitSpec
    rfl (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  have rLit := fidStep3_m7BaseRow hc2p.analyzeLit
  have rRec := fidStep3_m7BaseRow hRec_b (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  simp only [fidStep3Bundle, PatchBundle.frontTable, fidCongRewireRows, fidStep3ReplRows,
    fidCongReplRows, fidTiersSpecs, fidCongBeforeRows, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hfeq := fidStep3_fn_eq_base hfn 264
      (by t_kernel_rfl : fidStep2Fns[264]? = some FullM6CongSubst.full_cong_work_step) rfl hnm
    subst hfeq
    exact .of (workStep_wp_of_inactive_eval fidStep3Env rFind
      (fun hIn => rEvalG _ _ _ _ (m6CongEvalGateSpec_inactive_to_fid hIn)))
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongEmitXorFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 0 251
        (some ("full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_emit_xor_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHasClauseKFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 1 252
        (some ("full_cong_has_clause_k", [i64, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (full_cong_has_clause_k_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongExtractXorKFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 2 253
        (some ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_extract_xor_k_wp fidStep3Env rSortU32 rHasClK rEmitXor4)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongTryXorIteFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 3 254
        (some ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_try_xor_ite_wp fidStep3Env rHasTern rEmitXor)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongExtractFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 4 259
        (some ("full_cong_extract", [i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_extract_wp fidStep3Env rNext rHasBin rCountBins rTryXI rExtXorK)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongAndMatchFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 5 260
        (some ("full_cong_and_match", [i64, i32, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (full_cong_and_match_wp fidStep3Env rFind)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongEvalGateFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 6 263
        (some ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_eval_gate_wp fidStep3Env rFind rSortU32 rUnitFold rEquivFold
      rAndM rXorM rEnqVar)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongWorklistFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 7 265
        (some ("full_cong_worklist", [i64, i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_worklist_wp fidStep3Env rFind rEvalG)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongFwdSubsumeFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 8 266
        (some ("full_cong_fwd_subsume", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_fwd_subsume_wp fidStep3Env rNext rAddUnit rFind rSortPairs)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHtHashEntFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 9 267
        (some ("full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_ht_hash_ent_m7_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHtInitFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 10 268
        (some ("full_cong_ht_init_m7", [i64, i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_ht_init_m7_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHtGrowFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 11 269
        (some ("full_cong_ht_grow_m7", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_ht_grow_m7_wp fidStep3Env rHashEnt)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHtGrowClearFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 12 270
        (some ("full_cong_ht_grow_clear_m7", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_ht_grow_clear_m7_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHtLookupFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 13 271
        (some ("full_cong_ht_lookup_m7", [i64, i64, i32, i32], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_cong_ht_lookup_m7_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongHtInsertFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 14 272
        (some ("full_cong_ht_insert_m7", [i64, i64, i32], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_cong_ht_insert_m7_wp fidStep3Env rHashEnt rHtGrow)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongCopyCondbinFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 15 276
        (some ("full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_cong_copy_condbin_m7_wp fidStep3Env rU64Sort)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongMergeCondeqFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 16 278
        (some ("full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_cong_merge_condeq_m7_wp fidStep3Env)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongExtractIteAllFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 17 279
        (some ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_cong_extract_ite_all_m7_wp fidStep3Env rCopyCb rExtCondeq rMergeCe)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidCongruenceDenseFn)
      (by simp [fidStep3Repls, fidCongRepls])
      (slotSig_at fidStep3_replSigs_batch 18 280
        (some ("full_congruence_dense", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_congruence_dense_wp fidStep3Env rExtBin rFindUE rExtract rExtIteAll
      rWork rFwdSub)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidSyncLegacyTiersFn)
      (by simp [fidStep3Repls, fidTiersRepls])
      (slotSig_at fidStep3_replSigs_batch 19 60
        (some ("m6_hdr_sync_legacy_tiers", [i64], []))) rfl hnm
    subst hfeq
    exact .of (fid_sync_legacy_tiers_wp fidStep3Env rEnsure)
  · have hfeq := fidStep3_fn_eq_repl hfn (r := fidAnalyzeRsnFn)
      (by simp [fidStep3Repls, fidTiersRepls])
      (slotSig_at fidStep3_replSigs_batch 20 116
        (some ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (fid_analyze_rsn_wp fidStep3Env rLit rRec)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep3_slot (slotSig_at fidStep3_replSigs_batch 2 253
      (some ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64])))
    have hfeq := fidStep3_fn_eq_before hfn List.mem_cons_self List.mem_cons_self
      ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_cong_emit_xor4_wp fidStep3Env)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep3_slot (slotSig_at fidStep3_replSigs_batch 8 266
      (some ("full_cong_fwd_subsume", [i64, i64], [i64])))
    have hfeq := fidStep3_fn_eq_before hfn (List.mem_cons_of_mem _ List.mem_cons_self)
      List.mem_cons_self ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_cong_sift_pairs_fid_wp fidStep3Env)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep3_slot (slotSig_at fidStep3_replSigs_batch 8 266
      (some ("full_cong_fwd_subsume", [i64, i64], [i64])))
    have hfeq := fidStep3_fn_eq_before hfn (List.mem_cons_of_mem _ List.mem_cons_self)
      (List.mem_cons_of_mem _ List.mem_cons_self) ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_cong_sort_pairs_fid_wp fidStep3Env rSiftPairs)

/-- Closed `474/474` `ModuleOk` for `FullFidelityAssemblyStep3.fidStep3Module` under
`fidStep3Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep3_moduleOk : ModuleOk fidStep3Env fidStep3Module := by
  change ModuleOk (patchEnv fidStep3Bundle) fidStep3Bundle.patchedMod
  refine patchBundle_moduleOk fidStep3Bundle fidStep3Module_names_nodup
    fidStep3Module_replSigs_ok ?_ fidStep3Module_patchCallsOk fidStep3_front_covered
    fidStep3_front_impl fidStep3Bad fidStep3_noCallBad fidStep3_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact fidStep3Repls_wf fn hr
  · exact fidCongBefores_wf fn hb

/-! ## 4. Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

theorem fidStep3Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep3Env f as bs xs m Q X → fidStep3Env f as bs xs m Q X' := by
  refine patchEnv_noExit_of fidStep3Bundle ?_ ?_
  · change (fidCongRewireRows ++ (fidCongReplRows ++ fidTiersSpecs) ++ fidCongBeforeRows).all
      SpecEntry.noExit = true
    decide
  · change (fidStep2Bundle.frontTable ++ (fidStep1ReplRows ++ fidBaseSpecTable)).all
      SpecEntry.noExit = true
    rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨by decide, ⟨by decide, fidBaseSpecTable_noExit⟩⟩

private theorem fidStep3_front_noSolveBytes :
    fidStep3Bundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = "kissat_solve_bytes" := beq_iff_eq.mp hbeq
  have hm : "kissat_solve_bytes" ∈ fidStep3FrontNames :=
    fidStep3_frontNames_eq ▸ (hnm ▸ List.mem_map_of_mem he)
  exact absurd hm (by decide)

theorem fidStep3Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep3Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidStep3Bundle fidStep3_front_noSolveBytes
    (fun _ _ _ _ hs => fidStep2Env_solve_bytes_of hs) a m Q X

theorem fidStep3_solveBytes_mem : m6oSolveBytesFn ∈ fidStep3Module.fns :=
  patchBundle_solveBytes_mem fidStep3Bundle fidStep2_solveBytes_mem fun r hr => by
    change r ∈ fidStep3Repls at hr
    simp only [fidStep3Repls, fidCongRepls, fidTiersRepls, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep3Module` (`474` fns, `XPost := False`). -/
theorem fidStep3_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep3Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep3_moduleOk fidStep3_solveBytes_mem
    (fun _ _ _ _ hs => fidStep3Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep3Module`. -/
theorem fidStep3_solve_bytes_host_sound
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
  fid_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep3Module`. -/
theorem fidStep3_unsat_nv :
    Func.wp fidStep3Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep3_moduleOk fidStep3_solveBytes_mem
    (fun _ _ _ _ hs => fidStep3Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep3_moduleOk`. -/
theorem fidStep3Module_acyclic : fidStep3Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep3_moduleOk

/-- Canonical `KissatUnsatPkg` for Step-3 (`fidStep3Module`, `fidInlPolicy`). -/
def fidStep3UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep3Module fidInlPolicy fidStep3_solveBytes_mem
    fidStep3Env fidStep3_moduleOk fidStep3Env_noExit
    (fun _ _ _ _ hs => fidStep3Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3

end

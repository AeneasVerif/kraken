/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof
import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0a
import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof1a
import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof1b
import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof2
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import LeanQbe.T.Examples.Kissat.FullM4Bva
import LeanQbe.T.Examples.Kissat.FullM6Hdr
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullM6Sweep
import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 4 (`FullFidelityAssemblyStep4Proof`)

Certifies `FullFidelityAssemblyStep4.fidStep4Module` (`478` fns, `0` externs, `0` exits) via
`PatchModule.patchBundle_moduleOk_sameSpecs` + `FullFidelityAssemblyUtil`:
1. `fidStep4Bundle : PatchBundle` layering `FullFidelityVivK6`'s `fidVivK6Repls` (`6` repls)
   + `fidVivK6Befores` (`4` helpers) onto `fidStep3Module` (`474` fns), preserving every shared
   contract (`fullUnwatchLargeSpec`, `m6aVivifyTierSpec`, `m6aVivifySpec`, `k6PropagateSpec`,
   `m8K6CoreSpec`, `m4BvaCommitSpec`).
2. Closed `478/478` `fidStep4_moduleOk : ModuleOk fidStep4Env fidStep4Module`,
   `fidStep4Env_noExit`, `fidStep4_solve_bytes_sound`, `fidStep4_solve_bytes_host_sound`,
   `fidStep4_unsat_nv` (`XPost := False`, `std3`), and `fidStep4UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Bva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` Over `fidStep3Module` (`478/478` Fns) -/

/-- Flat `474`-row base specification table for Step 3. -/
private abbrev fidStep3EnvTable : List SpecEntry :=
  fidStep3Bundle.frontTable ++ fidStep3Bundle.baseTable

/-- Step-4 `PatchBundle` composing `fidStep3Module` + `FullFidelityVivK6`. -/
def fidStep4Bundle : PatchBundle where
  baseMod := fidStep3Module
  baseTable := fidStep3EnvTable
  baseOk := fidStep3_moduleOk
  repls := fidVivK6Repls
  replRows := fidVivK6ReplRows
  befores := fidVivK6Befores
  beforeRows := fidVivK6BeforeRows

/-- Closed `Env` for `fidStep4Module` (`478` fns). -/
def fidStep4Env : Env :=
  patchEnv fidStep4Bundle

theorem fidStep4_externs_empty : fidStep4Module.externs = [] :=
  fidStep3_externs_empty

theorem fidStep4Fns_length : fidStep4Fns.length = 478 := by
  t_kernel_rfl

private def fidStep4FrontNames : List Sym :=
  [ "full_unwatch_large", "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr"
  , "full_k6_propagate", "full_k6_core_m8", "full_bva_commit"
  , "full_viv_collect_fid", "full_viv_count_fid"
  , "full_viv_sort2_fid", "full_viv_sort_fid" ]

private theorem fidStep4_frontNames_eq :
    fidStep4Bundle.frontTable.map SpecEntry.name = fidStep4FrontNames :=
  rfl

private theorem fidStep4_front_nodup :
    (fidStep4Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep4_frontNames_eq]
  decide

private theorem fidStep4_replSigs_batch :
    [81, 222, 223, 315, 395, 410].map (fun i => fidStep3Fns[i]?.map Fn.sig) =
      [ some ("full_unwatch_large", [i64, i32, i32], [])
      , some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])
      , some ("full_vivify_m6_hdr", [i64], [i64])
      , some ("full_k6_propagate", [i64], [i32])
      , some ("full_k6_core_m8", [i64], [])
      , some ("full_bva_commit", [i64, i32], [.bool]) ] := by
  t_kernel_rfl

private theorem fidStep4_slot {i : Nat} {s : SigEntry}
    (hi : fidStep3Fns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep3Fns, g.sig = s := by
  cases h : fidStep3Fns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidStep4Module_replSigs_ok :
    ∀ r ∈ fidVivK6Repls, ∀ g ∈ fidStep3Module.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidStep3Fns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidStep3Fns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fidStep4_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have hnd : (fidStep3Fns.map Fn.name).Nodup :=
      (List.nodup_append.mp fidStep3Module_names_nodup).1
    have heq := nodup_name_eq Fn.name hnd hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (slotSig_at fidStep4_replSigs_batch 0 81 _) rfl hnm
  · exact hslot (slotSig_at fidStep4_replSigs_batch 1 222 _) rfl hnm
  · exact hslot (slotSig_at fidStep4_replSigs_batch 2 223 _) rfl hnm
  · exact hslot (slotSig_at fidStep4_replSigs_batch 3 315 _) rfl hnm
  · exact hslot (slotSig_at fidStep4_replSigs_batch 4 395 _) rfl hnm
  · exact hslot (slotSig_at fidStep4_replSigs_batch 5 410 _) rfl hnm

theorem fidStep4Module_names_nodup : fidStep4Module.namesNodup :=
  LeanQbe.T.Module.namesNodup_of_checkNamesNodup (by t_kernel_rfl)

private theorem fidStep4Module_patchCallsOk :
    checkPatchCallsOk fidStep3Module fidVivK6Repls fidVivK6Befores = true := by
  t_kernel_rfl

private theorem fidStep4_isSome_find_of_name_mem {tbl : List SpecEntry} {nm : Sym}
    (h : nm ∈ tbl.map SpecEntry.name) : (tbl.find? (·.name == nm)).isSome = true := by
  obtain ⟨e, he, hnm⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hnm⟩

private theorem fidStep4_front_covered :
    ∀ fn, (fn ∈ fidVivK6Repls ∨ fn ∈ fidVivK6Befores.flatMap Prod.snd) →
      (fidStep4Bundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  refine fidStep4_isSome_find_of_name_mem ?_
  rw [fidStep4_frontNames_eq]
  rcases hfn with hr | hb
  · simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [fidVivK6Befores, fidVivHelpers, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide

/-! ## 2. Fast Table Lookup, Elimination, & Spec Agree Helpers -/

private abbrev Fid4EnvSpec (nm : Sym) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ a m Q X, sp a m Q X → fidStep4Env nm as bs a m Q X

private theorem fidStep4_find_none_front4 {f : Sym}
    (hf4 : !(fidStep4FrontNames.contains f) = true) :
    fidStep4Bundle.frontTable.find? (·.name == f) = none := by
  apply List.find?_eq_none.mpr
  intro e he hbeq
  have hnm : e.name = f := beq_iff_eq.mp hbeq
  have hm : fidStep4FrontNames.contains f = true :=
    List.contains_iff_mem.mpr (fidStep4_frontNames_eq ▸ (hnm ▸ List.mem_map_of_mem he))
  have hnot : fidStep4FrontNames.contains f = false := by
    cases hc : fidStep4FrontNames.contains f
    · rfl
    · rw [hc] at hf4; exact absurd hf4 (by decide)
  exact Bool.false_ne_true (hnot.symm.trans hm)

private theorem fidStep4_find_none_front3 {f : Sym}
    (hf3 : !(fidStep3FrontNames.contains f) = true) :
    fidStep3Bundle.frontTable.find? (·.name == f) = none := by
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

private theorem fidStep4_find_none_front2 {f : Sym}
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true) :
    fidStep2Bundle.frontTable.find? (·.name == f) = none := by
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

private theorem fidStep4_find_none_front1 {f : Sym}
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true) :
    fidStep1Bundle.frontTable.find? (·.name == f) = none := by
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

private theorem fidStep4_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep4Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid4EnvSpec nm sp := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep4Bundle fidStep4_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep4_step3FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep3Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf4 : !(fidStep4FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid4EnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidStep4Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fidStep4_find_none_front4 hf4)]
  exact patchEnv_of_front_mem fidStep3Bundle fidStep3_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep4_step2FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep2Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf4 : !(fidStep4FrontNames.contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid4EnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidStep4Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fidStep4_find_none_front4 hf4)]
  change patchEnv fidStep3Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep3Bundle (fidStep4_find_none_front3 hf3)]
  exact patchEnv_of_front_mem fidStep2Bundle fidStep2_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep4_of_fidBase {f : Sym} {as bs : List Ty}
    (hf4 : !(fidStep4FrontNames.contains f) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains f) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv f as bs xs m Q X) :
    fidStep4Env f as bs xs m Q X := by
  change patchEnv fidStep4Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fidStep4_find_none_front4 hf4)]
  change patchEnv fidStep3Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep3Bundle (fidStep4_find_none_front3 hf3)]
  change patchEnv fidStep2Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep2Bundle (fidStep4_find_none_front2 hf2)]
  change patchEnv fidStep1Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep1Bundle (fidStep4_find_none_front1 hf1)]
  exact h

private theorem fidStep4_m7BaseRow {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hf4 : !(fidStep4FrontNames.contains f) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains f) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    (hnmf : f ∉ mfExclNames := by decide)
    (hncp : f ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid4EnvSpec f sp := fun a m Q X hs =>
  fidStep4_of_fidBase hf4 hf3 hf2 hf1
    (fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hmem hno a m Q X hs)))

private theorem fidStep4_m7Row_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : m7FidBaseTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf4 : !(fidStep4FrontNames.contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid4EnvSpec nm sp :=
  fidStep4_m7BaseRow (List.mem_of_getElem? hi) hf4 hf3 hf2 hf1 hnmf hncp hno

private theorem fidStep4_elim_to_fidBase {nm : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep3EnvTable nm as bs xs m Q X)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide) :
    fidBaseEnv nm as bs xs m Q X := by
  change patchEnv fidStep3Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep3Bundle (fidStep4_find_none_front3 hf3)] at h
  change patchEnv fidStep2Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep2Bundle (fidStep4_find_none_front2 hf2)] at h
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle (fidStep4_find_none_front1 hf1)] at h
  exact h

private theorem fidStep4_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep3EnvTable nm as bs xs m Q X)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide)
    (hneSw : !(m8SwNamesLit.contains nm) = true := by decide)
    (hne1 : nm ∉ m8CpExclNames := by decide)
    (hne2 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (hne3 : nm ∉ fidBveHelperRows.map SpecEntry.name := by decide)
    (hne4 : nm ≠ "full_extend_push2" := by decide)
    (hne5 : nm ≠ "full_cong_enq_var" := by decide)
    (hne6 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne7 : nm ≠ "full_cong_worklist" := by decide) :
    sp xs m Q (fun _ _ _ _ => False) :=
  fidBaseEnv_elim_m7Base hmem (fidStep4_elim_to_fidBase h hf3 hf2 hf1)
    hneEx hneSw hne1 hne2 hne3 hne4 hne5 hne6 hne7

private theorem fidStep4_elim_k6Prop {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (h : Env.ofTable fidStep3EnvTable "full_k6_propagate" [i64] [i32] xs m Q X) :
    k6PropagateSpec xs m Q (fun _ _ _ _ => False) := by
  have hb := fidStep4_elim_to_fidBase h
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide) hb)
  have hof := m8Sw_elim_sweep_gen (by decide : "full_k6_propagate" ∈ m8SwNamesLit) hsw
  have hr : (⟨"full_k6_propagate", [i64], [i32], k6PropagateSpec, true⟩ : SpecEntry) ∈
      m8SweepEnvRows :=
    List.mem_of_getElem? (i := 8) (by rfl : m8SweepEnvRows[8]? = some _)
  obtain ⟨_, _, hc⟩ := m8Sw_ofTable_sig_elim m8SweepEnvRows_nodup hr hof
  exact hc

private theorem fidStep4_elim_k6CoreM8 {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : Env.ofTable fidStep3EnvTable "full_k6_core_m8" [i64] [] xs m Q X) :
    m8K6CoreSpec xs m Q (fun _ _ _ _ => False) := by
  have hb := fidStep4_elim_to_fidBase h
  rcases ofTable_patchRows_elim fidBaseReplRows_sigs_match fidBase_befDisj hb with
    hr | hbef | ⟨_, _, hsw⟩
  · rcases hr with ⟨r, hr, hnm, _⟩
    have hm : "full_k6_core_m8" ∈ fidBaseReplRows.map SpecEntry.name :=
      hnm ▸ List.mem_map_of_mem hr
    exact absurd hm (by decide)
  · rcases hbef with ⟨p, hp, b, hb_p, hnm, has, hrs, hcast⟩
    simp only [fidBaseBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have hm : "full_k6_core_m8" ∈ m8MinHelperRows.map SpecEntry.name :=
        hnm ▸ List.mem_map_of_mem hb_p
      exact absurd hm (by decide)
    · have hr : (⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩ : SpecEntry) ∈
          fidBveHelperRows :=
        List.mem_of_getElem? (i := 13) (by rfl : fidBveHelperRows[13]? = some _)
      have hnd := fidBveHelperRows_nodup
      have hbe := nodup_name_eq SpecEntry.name hnd hb_p hr hnm
      subst hbe
      cases has; cases hrs
      exact hcast
  · have hm : "full_k6_core_m8" ∈ m8SwFlatTable.map SpecEntry.name := by
      obtain ⟨e, he, hnm, _⟩ := env_ofTable_mem_elim hsw
      exact hnm ▸ List.mem_map_of_mem he
    have hno : "full_k6_core_m8" ∉ m8SwFlatTable.map SpecEntry.name := by
      have hs := congrArg (List.map Prod.fst) m8SwFlatTable_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hs
      change m8SwFlatTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name at hs
      rw [hs]
      exact fidBase_not_in_sw "full_k6_core_m8" (by decide)
    exact absurd hm hno

private theorem fidStep4_before_not_in_step3 :
    (fidStep3Fns.map Fn.name).contains "full_viv_collect_fid" = false ∧
    (fidStep3Fns.map Fn.name).contains "full_viv_count_fid" = false ∧
    (fidStep3Fns.map Fn.name).contains "full_viv_sort2_fid" = false ∧
    (fidStep3Fns.map Fn.name).contains "full_viv_sort_fid" = false :=
  ⟨by t_kernel_rfl, by t_kernel_rfl, by t_kernel_rfl, by t_kernel_rfl⟩

private theorem fidStep4_agree :
    ∀ s ∈ fidStep3Module.sigs,
      ∀ xs m P E, Env.ofTable fidStep3EnvTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidStep4Bundle s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs xs m P E hBase
  cases hf : fidStep4Bundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidStep4Bundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hsig_in : e.name ∈ fidStep3Fns.map Fn.name := by
        have hm := hs
        rw [LeanQbe.T.Module.sigs, fidStep3_externs_empty, List.map_nil, List.append_nil] at hm
        obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
        exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
      have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
      have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
      have hPush :
          ∀ hmem : e ∈ fidStep4Bundle.frontTable, e.eff xs m P E →
            patchEnv fidStep4Bundle e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidStep4Bundle fidStep4_front_nodup hmem hs'
      have he0 := he
      simp only [fidStep4Bundle, PatchBundle.frontTable, fidVivK6ReplRows, fidVivK6BeforeRows,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hPush he0 (fidStep4_elim_m7Base hc1.unwatchLarge hBase)
      · change patchEnv fidStep3Bundle "full_vivify_tier_m6_hdr"
          [i64, i64, i64, i64] [i64] xs m P E at hBase
        rw [patchEnv_base_eq fidStep3Bundle (by decide)] at hBase
        have hf2 : fidStep2Bundle.frontTable[15]? = some
            ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩ :=
          rfl
        have hFront2 : Env.ofTable fidStep2Bundle.frontTable "full_vivify_tier_m6_hdr"
            [i64, i64, i64, i64] [i64] xs m P E := by
          have hStep : ∀ (pfx : List SpecEntry),
              (∃ e ∈ pfx, e.name = "full_vivify_tier_m6_hdr" ∧
                e.as = [i64, i64, i64, i64] ∧ e.rs = [i64]) →
              Env.ofTable (pfx ++ fidStep2Bundle.baseTable) "full_vivify_tier_m6_hdr"
                [i64, i64, i64, i64] [i64] xs m P E →
              Env.ofTable pfx "full_vivify_tier_m6_hdr"
                [i64, i64, i64, i64] [i64] xs m P E := by
            intro pfx hm htbl
            induction pfx with
            | nil => rcases hm with ⟨_, hmem, _⟩; nomatch hmem
            | cons a t ih =>
              rw [List.cons_append] at htbl
              rcases htbl with ⟨hsig, hcast⟩ | ⟨hne, htl⟩
              · exact Or.inl ⟨hsig, hcast⟩
              · rcases hm with ⟨e', he', hnm', has', hrs'⟩
                rcases List.mem_cons.mp he' with rfl | ht
                · exact absurd ⟨hnm', has', hrs'⟩ hne
                · exact Or.inr ⟨hne, ih ⟨e', ht, hnm', has', hrs'⟩ htl⟩
          exact hStep fidStep2Bundle.frontTable
            ⟨_, List.mem_of_getElem? hf2, rfl, rfl, rfl⟩ hBase
        obtain ⟨_, _, hc⟩ :=
          m8cp_ofTable_sig_elim fidStep2_front_nodup (List.mem_of_getElem? hf2) hFront2
        exact hPush he0 hc
      · exact hPush he0 (fidStep4_elim_m7Base hc2p.vivifyM6Hdr hBase)
      · exact hPush he0 (fidStep4_elim_k6Prop hBase)
      · exact hPush he0 (fidStep4_elim_k6CoreM8 hBase)
      · exact hPush he0 (fidStep4_elim_m7Base m7FidBase_bvaCommit_mem hBase)
      · have hno : (fidStep3Fns.map Fn.name).contains "full_viv_collect_fid" = false :=
          fidStep4_before_not_in_step3.1
        have hm : (fidStep3Fns.map Fn.name).contains "full_viv_collect_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno : (fidStep3Fns.map Fn.name).contains "full_viv_count_fid" = false :=
          fidStep4_before_not_in_step3.2.1
        have hm : (fidStep3Fns.map Fn.name).contains "full_viv_count_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno : (fidStep3Fns.map Fn.name).contains "full_viv_sort2_fid" = false :=
          fidStep4_before_not_in_step3.2.2.1
        have hm : (fidStep3Fns.map Fn.name).contains "full_viv_sort2_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno : (fidStep3Fns.map Fn.name).contains "full_viv_sort_fid" = false :=
          fidStep4_before_not_in_step3.2.2.2
        have hm : (fidStep3Fns.map Fn.name).contains "full_viv_sort_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
    · have hne : ∀ e' ∈ fidStep4Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep4_front_nodup he' he (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep4Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift fidStep4Bundle.frontTable hne

/-! ## 3. Front-Table Implementation Helpers & `fidStep4_moduleOk` (`478/478`) -/

private theorem fidStep4_fn_eq_before {fn b : Fn}
    (hfn : fn ∈ fidStep4Module.fns) (hb : b ∈ fidVivHelpers)
    (htgt : ∃ g0 ∈ fidStep3Fns, g0.name = "full_vivify_tier_m6_hdr")
    (hnm : b.name = fn.name) : fn = b := by
  have hModNd : (fidStep4Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep4Module_names_nodup).1
  obtain ⟨g0, hg0, hgn⟩ := htgt
  have hbm : b ∈ fidStep4Module.fns := by
    change b ∈ patchFns fidVivK6Repls fidVivK6Befores fidStep3Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    unfold patchInsAt
    simp only [fidVivK6Befores, List.find?, hgn, beq_self_eq_true]
    exact hb
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fidStep4_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidStep4Module.fns) (hr : r ∈ fidVivK6Repls)
    {idx : Nat} {s : SigEntry} (hslot : fidStep3Fns[idx]?.map Fn.sig = some s)
    (hrn : r.name = s.1) (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidStep4Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep4Module_names_nodup).1
  obtain ⟨g, hg, hgs⟩ := fidStep4_slot hslot
  have hrm : r ∈ fidStep4Module.fns :=
    mem_patchFns_of_repl (by decide) hr hg (hrn.trans (congrArg Prod.fst hgs).symm)
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fidStep4_front_impl :
    ∀ fn e, fn ∈ fidStep4Bundle.patchedMod.fns →
      fidStep4Bundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidStep4Env fn e := by
  intro fn e hfn hf
  change fn ∈ fidStep4Module.fns at hfn
  have he : e ∈ fidStep4Bundle.frontTable := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  have rArenaNext := fidStep4_m7Row_at 11 "full_arena_next" Full.fullArenaNextSpec
  have rAllocCl := fidStep4_m7Row_at 12 "full_alloc_cl" Full.fullAllocClSpec
  have rDefrag := fidStep4_m7Row_at 17 "full_wstack_defrag" Full.fullWstackDefragSpec
  have rWPush := fidStep4_m7Row_at 18 "full_watch_push" Full.fullWatchPushSpec
  have rBacktrack := fidStep4_m7Row_at 39 "full_backtrack" Full.fullBacktrackSpec
  have rSync := fidStep4_step3FrontRow 20 "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] [])
    rfl (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rDelaying := fidStep4_m7Row_at 66 "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rBumpDelay := fidStep4_m7Row_at 67 "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rReduceDelay := fidStep4_m7Row_at 68 "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] [])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetWm := fidStep4_m7Row_at 70 "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64])
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rProp := fidStep4_step2FrontRow 1 "full_propagate" FullM6BcpS15.fullBcpS15Spec
  have rAddBin := fidStep4_m7Row_at 178 "full_add_bin" Full.fullAddBinSpec
  have rDelBin := fidStep4_m7Row_at 179 "full_delete_binary" Full.fullDeleteBinarySpec
  have rVivClause := fidStep4_step2FrontRow 13 "full_viv_clause_m6"
    FullM6VivBackbone.fullVivClauseM6Spec
  have rTierMatch := fidStep4_m7Row_at 210 "full_viv_tier_match_m6"
    FullM6VivBackbone.fullVivTierMatchM6Spec
  have rClearTier := fidStep4_m7Row_at 215 "full_viv_clear_tier_m6"
    FullM6VivBackbone.fullVivClearTierM6Spec
  have rInitFresh := fidStep4_m7BaseRow m7FidP3InitFreshVar_mem
  have rUnwatch := fidStep4_frontRow 0 "full_unwatch_large" fullUnwatchLargeSpec
  have rVivTier := fidStep4_frontRow 1 "full_vivify_tier_m6_hdr" m6aVivifyTierSpec
    rfl (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)
  have rCollect := fidStep4_frontRow 6 "full_viv_collect_fid" fullVivCollectFidSpec
  have rCount := fidStep4_frontRow 7 "full_viv_count_fid" fullVivCountFidSpec
  have rSort2 := fidStep4_frontRow 8 "full_viv_sort2_fid" fullVivSort2FidSpec
  have rSort := fidStep4_frontRow 9 "full_viv_sort_fid" fullVivSortFidSpec
  simp only [fidStep4Bundle, PatchBundle.frontTable, fidVivK6ReplRows, fidVivK6BeforeRows,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hfeq := fidStep4_fn_eq_repl hfn (r := fidUnwatchLargeFn)
      (by simp [fidVivK6Repls])
      (slotSig_at fidStep4_replSigs_batch 0 81
        (some ("full_unwatch_large", [i64, i32, i32], []))) rfl hnm
    subst hfeq
    exact .of (full_unwatch_large_fid_wp fidStep4Env)
  · have hfeq := fidStep4_fn_eq_repl hfn (r := fidVivifyTierHdrFn)
      (by simp [fidVivK6Repls])
      (slotSig_at fidStep4_replSigs_batch 1 222
        (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_vivify_tier_m6_hdr_fid_wp fidStep4Env
      rBacktrack rCollect rCount rSort rVivClause rProp rClearTier)
  · have hfeq := fidStep4_fn_eq_repl hfn (r := fidVivifyHdrFn)
      (by simp [fidVivK6Repls])
      (slotSig_at fidStep4_replSigs_batch 2 223
        (some ("full_vivify_m6_hdr", [i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_vivify_m6_hdr_fid_wp fidStep4Env
      rBacktrack rSync rDelaying rGetWm rVivTier rBumpDelay rReduceDelay)
  · have hfeq := fidStep4_fn_eq_repl hfn (r := fidK6PropagateFn)
      (by simp [fidVivK6Repls])
      (slotSig_at fidStep4_replSigs_batch 3 315
        (some ("full_k6_propagate", [i64], [i32]))) rfl hnm
    subst hfeq
    exact .of (full_k6_propagate_fid_wp fidStep4Env)
  · have hfeq := fidStep4_fn_eq_repl hfn (r := fidK6CoreM8Fn)
      (by simp [fidVivK6Repls])
      (slotSig_at fidStep4_replSigs_batch 4 395
        (some ("full_k6_core_m8", [i64], []))) rfl hnm
    subst hfeq
    exact .of (full_k6_core_m8_fid_wp fidStep4Env)
  · have hfeq := fidStep4_fn_eq_repl hfn (r := fidBvaCommitFn)
      (by simp [fidVivK6Repls])
      (slotSig_at fidStep4_replSigs_batch 5 410
        (some ("full_bva_commit", [i64, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (full_bva_commit_fid_wp fidStep4Env
      rDefrag rInitFresh rAddBin rAllocCl rWPush rDelBin rUnwatch)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep4_slot (slotSig_at fidStep4_replSigs_batch 1 222
      (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])))
    have hfeq := fidStep4_fn_eq_before hfn List.mem_cons_self
      ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_viv_collect_fid_wp fidStep4Env rArenaNext rTierMatch)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep4_slot (slotSig_at fidStep4_replSigs_batch 1 222
      (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])))
    have hfeq := fidStep4_fn_eq_before hfn (List.mem_cons_of_mem _ List.mem_cons_self)
      ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_viv_count_fid_wp fidStep4Env)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep4_slot (slotSig_at fidStep4_replSigs_batch 1 222
      (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])))
    have hfeq := fidStep4_fn_eq_before hfn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_viv_sort2_fid_wp fidStep4Env)
  · obtain ⟨g0, hg0, hsg0⟩ := fidStep4_slot (slotSig_at fidStep4_replSigs_batch 1 222
      (some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64])))
    have hfeq := fidStep4_fn_eq_before hfn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))
      ⟨g0, hg0, congrArg Prod.fst hsg0⟩ hnm
    subst hfeq
    exact .of (full_viv_sort_fid_wp fidStep4Env rSort2)

/-- Closed `478/478` `ModuleOk` for `FullFidelityAssemblyStep4.fidStep4Module` under
`fidStep4Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep4_moduleOk : ModuleOk fidStep4Env fidStep4Module := by
  change ModuleOk (patchEnv fidStep4Bundle) fidStep4Bundle.patchedMod
  refine patchBundle_moduleOk_sameSpecs fidStep4Bundle fidStep4Module_names_nodup
    fidStep4Module_replSigs_ok ?_ fidStep4Module_patchCallsOk fidStep4_front_covered
    fidStep4_front_impl fidStep4_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact fidVivK6Repls_wf fn hr
  · exact fidVivK6Befores_wf fn hb

/-! ## 4. Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

theorem fidStep4Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep4Env f as bs xs m Q X → fidStep4Env f as bs xs m Q X' := by
  refine patchEnv_noExit_of fidStep4Bundle ?_ ?_
  · change (fidVivK6ReplRows ++ fidVivK6BeforeRows).all SpecEntry.noExit = true
    decide
  · change (fidStep3Bundle.frontTable ++
      (fidStep2Bundle.frontTable ++ (fidStep1ReplRows ++ fidBaseSpecTable))).all
      SpecEntry.noExit = true
    rw [List.all_append, List.all_append, List.all_append,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨by decide, ⟨by decide, ⟨by decide, fidBaseSpecTable_noExit⟩⟩⟩

private theorem fidStep4_front_noSolveBytes :
    fidStep4Bundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = "kissat_solve_bytes" := beq_iff_eq.mp hbeq
  have hm : "kissat_solve_bytes" ∈ fidStep4FrontNames :=
    fidStep4_frontNames_eq ▸ (hnm ▸ List.mem_map_of_mem he)
  exact absurd hm (by decide)

theorem fidStep4Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep4Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidStep4Bundle fidStep4_front_noSolveBytes
    (fun _ _ _ _ hs => fidStep3Env_solve_bytes_of hs) a m Q X

theorem fidStep4_solveBytes_mem : m6oSolveBytesFn ∈ fidStep4Module.fns :=
  patchBundle_solveBytes_mem fidStep4Bundle fidStep3_solveBytes_mem fun r hr => by
    change r ∈ fidVivK6Repls at hr
    simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep4Module` (`478` fns, `XPost := False`). -/
theorem fidStep4_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep4Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep4_moduleOk fidStep4_solveBytes_mem
    (fun _ _ _ _ hs => fidStep4Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep4Module`. -/
theorem fidStep4_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep4Module`. -/
theorem fidStep4_unsat_nv :
    Func.wp fidStep4Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep4_moduleOk fidStep4_solveBytes_mem
    (fun _ _ _ _ hs => fidStep4Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep4_moduleOk`. -/
theorem fidStep4Module_acyclic : fidStep4Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep4_moduleOk

/-- Canonical `KissatUnsatPkg` for Step-4 (`fidStep4Module`, `fidInlPolicy`). -/
def fidStep4UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep4Module fidInlPolicy fidStep4_solveBytes_mem
    fidStep4Env fidStep4_moduleOk fidStep4Env_noExit
    (fun _ _ _ _ hs => fidStep4Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4

end

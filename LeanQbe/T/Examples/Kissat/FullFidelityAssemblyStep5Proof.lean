/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof
import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6a
import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6b
import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6c
import LeanQbe.T.Examples.Kissat.FullFidelityBveProofCert
import LeanQbe.T.Examples.Kissat.FullFidelityBveProofVar0
import LeanQbe.T.Examples.Kissat.FullFidelityBveProofVar
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
import LeanQbe.T.Examples.Kissat.FullFastSched
import LeanQbe.T.Examples.Kissat.FullM3CongBva
import LeanQbe.T.Examples.Kissat.FullM6BveFwd
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullM6Sweep
import LeanQbe.T.Examples.Kissat.FullM7BveGates
import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Examples.Kissat.FullM7Proof
import LeanQbe.T.Examples.Kissat.FullM7Search
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 5 (`FullFidelityAssemblyStep5Proof`)

Certifies `FullFidelityAssemblyStep5.fidStep5Module` (`492` fns, `0` externs, `0` exits) via
`PatchModule.patchBundle_moduleOk_sameSpecs` + `FullFidelityAssemblyUtil`:
1. `fidStep5Bundle : PatchBundle` layering `fidStep5Repls` (`6` repls) + `fidStep5Befores`
   (`14` helpers before `"full_bve_gates_fid"`) onto `fidStep4Module` (`478` fns), preserving every
   shared contract (`fullBveVarDefSpec`, `m8BveVarKeySpec`, `m3ElimBveSpec`, `schedEliminateSpec`,
   `m8BveGatesSpec`).
2. Closed `492/492` `fidStep5_moduleOk : ModuleOk fidStep5Env fidStep5Module`,
   `fidStep5Env_noExit`, `fidStep5_solve_bytes_sound`, `fidStep5_solve_bytes_host_sound`,
   `fidStep5_unsat_nv` (`XPost := False`, `std3`), and `fidStep5UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` Over `fidStep4Module` (`492/492` Fns) -/

/-- Flat `478`-row base specification table for Step 4. -/
private abbrev fidStep4EnvTable : List SpecEntry :=
  fidStep4Bundle.frontTable ++ fidStep4Bundle.baseTable

/-- `14` new helper specification rows matching `fidStep5NewHelpers`. -/
def fidStep5NewHelperRows : List SpecEntry :=
  (FullFidelityBve.fidBveHelperRows.drop 5).take 14

/-- `6` replacement specification rows matching `fidStep5Repls`. -/
def fidStep5ReplRows : List SpecEntry :=
  fidBveReplRows ++
    [⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩]

/-- Step-5 `PatchBundle` composing `fidStep4Module` + `FullFidelityBve`. -/
def fidStep5Bundle : PatchBundle where
  baseMod := fidStep4Module
  baseTable := fidStep4EnvTable
  baseOk := fidStep4_moduleOk
  repls := fidStep5Repls
  replRows := fidStep5ReplRows
  befores := fidStep5Befores
  beforeRows := fidStep5NewHelperRows

/-- Closed `Env` for `fidStep5Module` (`492` fns). -/
def fidStep5Env : Env :=
  patchEnv fidStep5Bundle

theorem fidStep5_externs_empty : fidStep5Module.externs = [] :=
  fidStep4_externs_empty

theorem fidStep5Fns_length : fidStep5Fns.length = 492 := by
  t_kernel_rfl

private def fidStep5FrontNames : List Sym :=
  [ "full_bve_var_m7", "full_bve_var", "full_bve_var_key_m7"
  , "full_elim_bve_m7", "full_eliminate_m6", "full_bve_gates_fid"
  , "full_bve_k6_mv_fid", "full_fid_k6_add_ticks", "full_k6_watch_fid"
  , "full_k6_assign_fid", "full_k6_mtf_fid", "full_k6_backtrack_fid"
  , "full_k6_prop_fid", "full_k6_ana_cl_fid", "full_k6_analyze_fid"
  , "full_k6_solve_fid", "full_k6_core_fid", "full_k6_extract_and_solve_fid"
  , "full_bve_certify_unit_fid", "full_bve_def_k6_fid" ]

private theorem fidStep5_frontNames_eq :
    fidStep5Bundle.frontTable.map SpecEntry.name = fidStep5FrontNames :=
  rfl

private theorem fidStep5_front_nodup :
    (fidStep5Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep5_frontNames_eq]
  decide

private theorem fidStep5_replSigs_batch :
    [403, 404, 444, 450, 452, 402].map (fun i => fidStep4Fns[i]?.map Fn.sig) =
      [ some ("full_bve_var_m7", [i64, i32], [i64])
      , some ("full_bve_var", [i64, i32], [i64])
      , some ("full_bve_var_key_m7", [i64, i32], [i64])
      , some ("full_elim_bve_m7", [i64, i64], [i64])
      , some ("full_eliminate_m6", [i64, .bool], [i64])
      , some ("full_bve_gates_fid", [i64, i32, i32, i32], []) ] := by
  t_kernel_rfl

private theorem fidStep5_slot {i : Nat} {s : SigEntry}
    (hi : fidStep4Fns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep4Fns, g.sig = s := by
  cases h : fidStep4Fns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidStep5Module_replSigs_ok :
    ∀ r ∈ fidStep5Repls, ∀ g ∈ fidStep4Module.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidStep4Fns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidStep4Fns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fidStep5_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have hnd : (fidStep4Fns.map Fn.name).Nodup :=
      (List.nodup_append.mp fidStep4Module_names_nodup).1
    have heq := nodup_name_eq Fn.name hnd hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [fidStep5Repls, fidBveRepls, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (slotSig_at fidStep5_replSigs_batch 0 403 _) rfl hnm
  · exact hslot (slotSig_at fidStep5_replSigs_batch 1 404 _) rfl hnm
  · exact hslot (slotSig_at fidStep5_replSigs_batch 2 444 _) rfl hnm
  · exact hslot (slotSig_at fidStep5_replSigs_batch 3 450 _) rfl hnm
  · exact hslot (slotSig_at fidStep5_replSigs_batch 4 452 _) rfl hnm
  · exact hslot (slotSig_at fidStep5_replSigs_batch 5 402 _) rfl hnm

theorem fidStep5Module_names_nodup : fidStep5Module.namesNodup :=
  LeanQbe.T.Module.namesNodup_of_checkNamesNodup (by t_kernel_rfl)

private theorem fidStep5Module_patchCallsOk :
    checkPatchCallsOk fidStep4Module fidStep5Repls fidStep5Befores = true := by
  t_kernel_rfl

private theorem fidStep5_isSome_find_of_name_mem {tbl : List SpecEntry} {nm : Sym}
    (h : nm ∈ tbl.map SpecEntry.name) : (tbl.find? (·.name == nm)).isSome = true := by
  obtain ⟨e, he, hnm⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hnm⟩

private theorem fidStep5_front_covered :
    ∀ fn, (fn ∈ fidStep5Repls ∨ fn ∈ fidStep5Befores.flatMap Prod.snd) →
      (fidStep5Bundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  refine fidStep5_isSome_find_of_name_mem ?_
  rw [fidStep5_frontNames_eq]
  rcases hfn with hr | hb
  · simp only [fidStep5Repls, fidBveRepls, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [fidStep5Befores, fidStep5NewHelpers, FullFidelityBve.fidBveHelpers,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.drop_succ_cons,
      List.drop_zero, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide

/-! ## 2. Fast Table Lookup, Elimination, & Spec Agree Helpers -/

private abbrev Fid5EnvSpec (nm : Sym) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ a m Q X, sp a m Q X → fidStep5Env nm as bs a m Q X

private theorem fidStep5_find_none_of_names {tbl : List SpecEntry} {nms : List Sym}
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

private theorem fidStep5_find_none_front5 {f : Sym}
    (hf5 : !(fidStep5FrontNames.contains f) = true) :
    fidStep5Bundle.frontTable.find? (·.name == f) = none :=
  fidStep5_find_none_of_names fidStep5_frontNames_eq hf5

private theorem fidStep5_find_none_front4 {f : Sym}
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains f) = true) :
    fidStep4Bundle.frontTable.find? (·.name == f) = none :=
  fidStep5_find_none_of_names rfl hf4

private theorem fidStep5_find_none_front3 {f : Sym}
    (hf3 : !(fidStep3FrontNames.contains f) = true) :
    fidStep3Bundle.frontTable.find? (·.name == f) = none :=
  fidStep5_find_none_of_names fidStep3_frontNames_eq hf3

private theorem fidStep5_find_none_front2 {f : Sym}
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true) :
    fidStep2Bundle.frontTable.find? (·.name == f) = none :=
  fidStep5_find_none_of_names rfl hf2

private theorem fidStep5_find_none_front1 {f : Sym}
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true) :
    fidStep1Bundle.frontTable.find? (·.name == f) = none :=
  fidStep5_find_none_of_names (by simp [fidStep1Bundle, PatchBundle.frontTable]) hf1

private theorem fidStep5_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep5Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid5EnvSpec nm sp := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep5Bundle fidStep5_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep5_of_fidBase {f : Sym} {as bs : List Ty}
    (hf5 : !(fidStep5FrontNames.contains f) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains f) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv f as bs xs m Q X) :
    fidStep5Env f as bs xs m Q X := by
  change patchEnv fidStep5Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep5Bundle (fidStep5_find_none_front5 hf5)]
  change patchEnv fidStep4Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fidStep5_find_none_front4 hf4)]
  change patchEnv fidStep3Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep3Bundle (fidStep5_find_none_front3 hf3)]
  change patchEnv fidStep2Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep2Bundle (fidStep5_find_none_front2 hf2)]
  change patchEnv fidStep1Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep1Bundle (fidStep5_find_none_front1 hf1)]
  exact h

private theorem fidStep5_baseRow_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidBaseSpecTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid5EnvSpec nm sp := fun a m Q X hs =>
  fidStep5_of_fidBase hf5 hf4 hf3 hf2 hf1
    (Env.ofTable_of_mem (List.mem_of_getElem? hi) fidBaseSpecTable_nodup (hno a m Q X hs))

private theorem fidStep5_m7BveRow (k : Nat) (hk : k < m7FidBveRows.length)
    {nm : Sym} {as bs : List Ty} (sp : Spec as bs)
    (heq : m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid5EnvSpec nm sp := fun a m Q X hs =>
  fidStep5_of_fidBase hf5 hf4 hf3 hf2 hf1
    (fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf
      (m7FidBase_row_mem (m7FidBase_bve_mem _ (heq ▸ List.getElem_mem hk)) hno a m Q X hs)))

private theorem fidStep5_step2FrontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep2Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid5EnvSpec nm sp := fun a m Q X hs => by
  change patchEnv fidStep5Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep5Bundle (fidStep5_find_none_front5 hf5)]
  change patchEnv fidStep4Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep4Bundle (fidStep5_find_none_front4 hf4)]
  change patchEnv fidStep3Bundle nm as bs a m Q X
  rw [patchEnv_base_eq fidStep3Bundle (fidStep5_find_none_front3 hf3)]
  exact patchEnv_of_front_mem fidStep2Bundle fidStep2_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep5_m7Row {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hf5 : !(fidStep5FrontNames.contains nm) = true := by decide)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid5EnvSpec nm sp := fun a m Q X hs =>
  fidStep5_of_fidBase hf5 hf4 hf3 hf2 hf1
    (fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hmem hno a m Q X hs)))

private theorem fidStep5_elim_to_fidBase {nm : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep4EnvTable nm as bs xs m Q X)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains nm) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide) :
    fidBaseEnv nm as bs xs m Q X := by
  change patchEnv fidStep4Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep4Bundle (fidStep5_find_none_front4 hf4)] at h
  change patchEnv fidStep3Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep3Bundle (fidStep5_find_none_front3 hf3)] at h
  change patchEnv fidStep2Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep2Bundle (fidStep5_find_none_front2 hf2)] at h
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle (fidStep5_find_none_front1 hf1)] at h
  exact h

private theorem fidStep5_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep4EnvTable nm as bs xs m Q X)
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
  fidBaseEnv_elim_m7Base hmem (fidStep5_elim_to_fidBase h hf4 hf3 hf2 hf1)
    hneEx hneSw hne1 hne2 hne3 hne4 hne5 hne6 hne7

private theorem fidStep5_elim_baseRepl {r : SpecEntry} (hr : r ∈ fidBaseReplRows)
    {xs : Tup Val r.as} {m : Mem 64} {Q : Post r.rs} {X : XPost}
    (h : Env.ofTable fidStep4EnvTable r.name r.as r.rs xs m Q X)
    (hf4 : !((fidStep4Bundle.frontTable.map SpecEntry.name).contains r.name) = true := by decide)
    (hf3 : !(fidStep3FrontNames.contains r.name) = true := by decide)
    (hf2 : !((fidStep2Bundle.frontTable.map SpecEntry.name).contains r.name) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains r.name = true := by decide) :
    r.eff xs m Q X :=
  fidBaseEnv_elim_repl hr (fidStep5_elim_to_fidBase h hf4 hf3 hf2 hf1)

private theorem fidStep5_elim_baseBveGates {xs : Tup Val [i64, i32, i32, i32]}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (h : Env.ofTable fidStep4EnvTable "full_bve_gates_fid" [i64, i32, i32, i32] [] xs m Q X) :
    m8BveGatesSpec xs m Q (fun _ _ _ _ => False) := by
  have hb := fidStep5_elim_to_fidBase h
  have hmem : fidBaseSpecTable[393]? =
      some ⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩ := by
    t_kernel_rfl
  exact (m8cp_ofTable_sig_elim fidBaseSpecTable_nodup (List.mem_of_getElem? hmem) hb).2.2

private theorem fidStep5_before_not_in_step4 :
    fidStep5NewHelpers.all (fun fn => !(fidStep4Fns.map Fn.name).contains fn.name) = true := by
  t_kernel_rfl

private theorem fidStep5_agree :
    ∀ s ∈ fidStep4Module.sigs,
      ∀ xs m P E, Env.ofTable fidStep4EnvTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidStep5Bundle s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs xs m P E hBase
  cases hf : fidStep5Bundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidStep5Bundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hsig_in : e.name ∈ fidStep4Fns.map Fn.name := by
        have hm := hs
        rw [LeanQbe.T.Module.sigs, fidStep4_externs_empty, List.map_nil, List.append_nil] at hm
        obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
        exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
      have hPush :
          ∀ hmem : e ∈ fidStep5Bundle.frontTable, e.eff xs m P E →
            patchEnv fidStep5Bundle e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidStep5Bundle fidStep5_front_nodup hmem hs'
      have hBefFail : ∀ nm0 ∈ fidStep5NewHelpers.map Fn.name,
          e.name = nm0 → patchEnv fidStep5Bundle e.name e.as e.rs xs m P E := by
        intro nm0 hnm0 heq0
        have hno : (fidStep4Fns.map Fn.name).contains nm0 = false := by
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hnm0
          have ha := List.all_eq_true.mp fidStep5_before_not_in_step4 g hg
          simpa using ha
        have hm : (fidStep4Fns.map Fn.name).contains nm0 = true :=
          List.contains_iff_mem.mpr (heq0 ▸ hsig_in)
        rw [hno] at hm; cases hm
      have he0 := he
      simp only [fidStep5Bundle, PatchBundle.frontTable, fidStep5ReplRows, fidStep5NewHelperRows,
        fidBveReplRows, FullFidelityBve.fidBveHelperRows, List.cons_append, List.nil_append,
        List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hPush he0 (fidStep5_elim_m7Base m7FidBase_bveVar_mem hBase)
      · exact hPush he0 (fidStep5_elim_m7Base
          (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl)) hBase)
      · exact hPush he0 (fidStep5_elim_baseRepl
          (List.mem_of_getElem? (i := 2) (by rfl : fidBaseReplRows[2]? = some _)) hBase)
      · exact hPush he0 (fidStep5_elim_m7Base m7FidBase_elimBveM7_mem hBase)
      · exact hPush he0 (fidStep5_elim_m7Base
          (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 42) rfl)) hBase)
      · exact hPush he0 (fidStep5_elim_baseBveGates hBase)
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
      · exact hBefFail _ (by decide) rfl
    · have hne : ∀ e' ∈ fidStep5Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep5_front_nodup he' he (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep5Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift fidStep5Bundle.frontTable hne

/-! ## 3. Front-Table Implementation Helpers & `fidStep5_moduleOk` (`492/492`) -/

private theorem fidStep5_fn_eq_before {fn b : Fn}
    (hfn : fn ∈ fidStep5Module.fns) (hb : b ∈ fidStep5NewHelpers)
    (htgt : ∃ g0 ∈ fidStep4Fns, g0.name = "full_bve_gates_fid")
    (hnm : b.name = fn.name) : fn = b := by
  have hModNd : (fidStep5Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep5Module_names_nodup).1
  obtain ⟨g0, hg0, hgn⟩ := htgt
  have hbm : b ∈ fidStep5Module.fns := by
    change b ∈ patchFns fidStep5Repls fidStep5Befores fidStep4Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    unfold patchInsAt
    simp only [fidStep5Befores, List.find?, hgn, beq_self_eq_true]
    exact hb
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fidStep5_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidStep5Module.fns) (hr : r ∈ fidStep5Repls)
    {idx : Nat} {s : SigEntry} (hslot : fidStep4Fns[idx]?.map Fn.sig = some s)
    (hrn : r.name = s.1) (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidStep5Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep5Module_names_nodup).1
  obtain ⟨g, hg, hgs⟩ := fidStep5_slot hslot
  have hrm : r ∈ fidStep5Module.fns :=
    mem_patchFns_of_repl (by decide) hr hg (hrn.trans (congrArg Prod.fst hgs).symm)
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fidStep5_front_impl :
    ∀ fn e, fn ∈ fidStep5Bundle.patchedMod.fns →
      fidStep5Bundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidStep5Env fn e := by
  intro fn e hfn hf
  change fn ∈ fidStep5Module.fns at hfn
  change fidStep5Bundle.frontTable.find? (·.name == fn.name) = some e at hf
  have he : e ∈ fidStep5Bundle.frontTable := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  have rVarM7 := fidStep5_frontRow 0 "full_bve_var_m7" FullFastBveBudgets.fullBveVarDefSpec
  have rGatesFid := fidStep5_frontRow 5 "full_bve_gates_fid" m8BveGatesSpec
    (by t_kernel_rfl) m8BveGatesSpec_noExit
  have rK6Mv := fidStep5_frontRow 6 "full_bve_k6_mv_fid" fidBveK6MvSpec
    (by t_kernel_rfl) fidBveK6MvSpec_noExit
  have rAddTicks := fidStep5_frontRow 7 "full_fid_k6_add_ticks" fidK6AddTicksSpec
    (by t_kernel_rfl) fidK6AddTicksSpec_noExit
  have rWatch := fidStep5_frontRow 8 "full_k6_watch_fid" fidK6WatchSpec
    (by t_kernel_rfl) fidK6WatchSpec_noExit
  have rAssign := fidStep5_frontRow 9 "full_k6_assign_fid" fidK6AssignSpec
    (by t_kernel_rfl) fidK6AssignSpec_noExit
  have rMtf := fidStep5_frontRow 10 "full_k6_mtf_fid" fidK6MtfSpec
    (by t_kernel_rfl) fidK6MtfSpec_noExit
  have rBt := fidStep5_frontRow 11 "full_k6_backtrack_fid" fidK6BacktrackSpec
    (by t_kernel_rfl) fidK6BacktrackSpec_noExit
  have rProp := fidStep5_frontRow 12 "full_k6_prop_fid" fidK6PropSpec
    (by t_kernel_rfl) fidK6PropSpec_noExit
  have rAnaCl := fidStep5_frontRow 13 "full_k6_ana_cl_fid" fidK6AnaClSpec
    (by t_kernel_rfl) fidK6AnaClSpec_noExit
  have rAnalyze := fidStep5_frontRow 14 "full_k6_analyze_fid" fidK6AnalyzeSpec
    (by t_kernel_rfl) fidK6AnalyzeSpec_noExit
  have rSolve := fidStep5_frontRow 15 "full_k6_solve_fid" fidK6SolveSpec
    (by t_kernel_rfl) fidK6SolveSpec_noExit
  have rCore := fidStep5_frontRow 16 "full_k6_core_fid" fidK6CoreSpec
    (by t_kernel_rfl) fidK6CoreSpec_noExit
  have rExtSolve := fidStep5_frontRow 17 "full_k6_extract_and_solve_fid" fidK6ExtractSolveSpec
    (by t_kernel_rfl) fidK6ExtractSolveSpec_noExit
  have rCertUnit := fidStep5_frontRow 18 "full_bve_certify_unit_fid" fidBveCertifyUnitSpec
    (by t_kernel_rfl) fidBveCertifyUnitSpec_noExit
  have rDefK6 := fidStep5_frontRow 19 "full_bve_def_k6_fid" m8BveGatesSpec
    (by t_kernel_rfl) m8BveGatesSpec_noExit
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have rMaxV := fidStep5_baseRow_at 302 "full_m6_max_v" m6MaxVSpec
  have rK6Init := fidStep5_baseRow_at 304 "full_k6_init" k6InitSpec
  have rK6Add := fidStep5_baseRow_at 307 "full_k6_add_clause" k6AddClauseSpec
  have rK6Solve := fidStep5_baseRow_at 313 "full_k6_solve" k6SolveSpec
  have rEquiv := fidStep5_baseRow_at 377 "full_bve_find_equiv_m8" m8BveFindEquivSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    m8BveFindEquivSpec_noExit
  have rAnd := fidStep5_baseRow_at 378 "full_bve_find_and_m8" m8BveFindAndSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    m8BveFindAndSpec_noExit
  have rIte := fidStep5_baseRow_at 381 "full_bve_find_ite_m8" m8BveFindIteSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    m8BveFindIteSpec_noExit
  have rHeapPush := fidStep5_baseRow_at 438 "full_bve_heap_push_m7" m8BveHeapPushSpec
    (by t_kernel_rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    m8BveHeapPushSpec_noExit
  have rCollect := fidStep5_m7BveRow 9 (by decide) fullBveCollectSpec
  have rExtNeed := fidStep5_m7Row (m7FidP3Bve5_mem (i := 4) (by decide))
  have rWeaken := fidStep5_m7Row (m7FidP3Bve5_mem (i := 1) (by decide))
  have rSetInact := fidStep5_m7Row hc2.setInactive
  have rGatesM7 := fidStep5_m7BveRow 31 (by decide) fullBveGatesM7Spec
    (hno := fullBveGatesM7Spec_noExit)
  have rResPair := fidStep5_m7Row (m7FidP3Bve5_mem (i := 0) (by decide))
  have rAssignLvl := fidStep5_m7Row hc1.assignLvl
  have rDefrag := fidStep5_m7Row (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)
  have rCommit := fidStep5_m7Row (m7FidP3Bve5_mem (i := 3) (by decide))
  have rFlushUnits := fidStep5_m7BveRow 1 (by decide) fullDenseFlushUnitsM6Spec
    (hno := fullDenseFlushUnitsM6Spec_noExit)
  have rPop := fidStep5_m7BveRow 38 (by decide) fullBveHeapPopM6Spec
    (hno := fullBveHeapPopM6Spec_noExit)
  have rNbrs := fidStep5_m7BveRow 39 (by decide) m3ElimCollectNbrsSpec
  have rElimBve := fidStep5_frontRow 3 "full_elim_bve_m7" FullM3CongBva.m3ElimBveSpec
  have rDticks := fidStep5_m7Row m7FidP3ElimDticks_mem
  have rLog10 := fidStep5_m7Row hc1.log10Q16M7 (hno := fun _ _ _ _ h => m7Log10Q16Spec_monoX h)
  have rScale := fidStep5_m7Row hc1.scaleDelta
  have rEnter := fidStep5_step2FrontRow 20 "full_enter_dense" FullFastSched.schedEnterDenseSpec
  have rMinU64 := fidStep5_m7Row m7FidP3MinU64_mem
  have rFwd := fidStep5_m7BveRow 10 (by decide) fullForwardSubFastSpec
  have rReb := fidStep5_step2FrontRow 21 "full_rebuild_watches" Full.fullRebuildWatchesSpec
  obtain ⟨g0, hg0, hsg0⟩ := fidStep5_slot (slotSig_at fidStep5_replSigs_batch 5 402
    (some ("full_bve_gates_fid", [i64, i32, i32, i32], [])))
  have hgt : ∃ g ∈ fidStep4Fns, g.name = "full_bve_gates_fid" := ⟨g0, hg0, congrArg Prod.fst hsg0⟩
  simp only [fidStep5Bundle, PatchBundle.frontTable, fidStep5ReplRows, fidStep5NewHelperRows,
    fidBveReplRows, FullFidelityBve.fidBveHelperRows, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hfeq := fidStep5_fn_eq_repl hfn (r := FullFidelityBve.fidBveVarM7Fn)
      (by simp [fidStep5Repls, fidBveRepls])
      (slotSig_at fidStep5_replSigs_batch 0 403
        (some ("full_bve_var_m7", [i64, i32], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_bve_var_m7_fid_wp fidStep5Env rCollect rExtNeed rWeaken rSetInact
      rGatesFid rGatesM7 rResPair rAssignLvl rDefrag rCommit rFlushUnits)
  · have hfeq := fidStep5_fn_eq_repl hfn (r := FullFidelityBve.fidBveVarFn)
      (by simp [fidStep5Repls, fidBveRepls])
      (slotSig_at fidStep5_replSigs_batch 1 404
        (some ("full_bve_var", [i64, i32], [i64]))) rfl hnm
    subst hfeq
    exact .of (FullFidelityBve.full_bve_var_fid_wp fidStep5Env rVarM7)
  · have hfeq := fidStep5_fn_eq_repl hfn (r := m8BveVarKeyM7Fn)
      (by simp [fidStep5Repls, fidBveRepls])
      (slotSig_at fidStep5_replSigs_batch 2 444
        (some ("full_bve_var_key_m7", [i64, i32], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_bve_var_key_m7_m8_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_repl hfn (r := fidElimBveM7Fn)
      (by simp [fidStep5Repls, fidBveRepls])
      (slotSig_at fidStep5_replSigs_batch 3 450
        (some ("full_elim_bve_m7", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_elim_bve_m7_fid_wp fidStep5Env rPop rNbrs rVarM7 rFlushUnits rHeapPush)
  · have hfeq := fidStep5_fn_eq_repl hfn (r := fidEliminateM6Fn)
      (by simp [fidStep5Repls, fidBveRepls])
      (slotSig_at fidStep5_replSigs_batch 4 452
        (some ("full_eliminate_m6", [i64, .bool], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_eliminate_m6_fid_wp fidStep5Env rDticks rLog10 rScale rEnter rMinU64
      rFwd rElimBve rReb)
  · have hfeq := fidStep5_fn_eq_repl hfn (r := FullFidelityBve.fidBveGatesFn)
      (by simp [fidStep5Repls])
      (slotSig_at fidStep5_replSigs_batch 5 402
        (some ("full_bve_gates_fid", [i64, i32, i32, i32], []))) rfl hnm
    subst hfeq
    exact .of (full_bve_gates_fid_wp fidStep5Env rEquiv rAnd rIte rDefK6)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidBveK6MvFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bve_k6_mv_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6AddTicksFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_fid_k6_add_ticks_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6WatchFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_watch_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6AssignFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_assign_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6MtfFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_mtf_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6BacktrackFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_backtrack_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6PropFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_prop_fid_wp fidStep5Env rAddTicks rAssign)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6AnaClFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_ana_cl_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6AnalyzeFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_analyze_fid_wp fidStep5Env rAnaCl rBt rMtf rAssign rWatch)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6SolveFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_solve_fid_wp fidStep5Env rBt rAssign rProp rAnalyze)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6CoreFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_core_fid_wp fidStep5Env)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidK6ExtractSolveFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_k6_extract_and_solve_fid_wp fidStep5Env rK6Mv rWatch rSolve rCore)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidBveCertifyUnitFn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bve_certify_unit_fid_wp fidStep5Env rMaxV rK6Init rK6Add rK6Solve rAssignLvl)
  · have hfeq := fidStep5_fn_eq_before hfn (b := fidBveDefK6Fn)
      (by simp [fidStep5NewHelpers, FullFidelityBve.fidBveHelpers]) hgt hnm
    subst hfeq
    exact .of (full_bve_def_k6_fid_wp fidStep5Env rK6Mv rExtSolve rCertUnit)

/-- Closed `492/492` `ModuleOk` for `FullFidelityAssemblyStep5.fidStep5Module` under
`fidStep5Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep5_moduleOk : ModuleOk fidStep5Env fidStep5Module := by
  change ModuleOk (patchEnv fidStep5Bundle) fidStep5Bundle.patchedMod
  refine patchBundle_moduleOk_sameSpecs fidStep5Bundle fidStep5Module_names_nodup
    fidStep5Module_replSigs_ok ?_ fidStep5Module_patchCallsOk fidStep5_front_covered
    fidStep5_front_impl fidStep5_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact fidStep5Repls_wf fn hr
  · exact fidStep5Befores_wf fn hb

/-! ## 4. Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

theorem fidStep5Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep5Env f as bs xs m Q X → fidStep5Env f as bs xs m Q X' := by
  refine patchEnv_noExit_of fidStep5Bundle ?_ ?_
  · change (fidStep5ReplRows ++ fidStep5NewHelperRows).all SpecEntry.noExit = true
    decide
  · change (fidStep4Bundle.frontTable ++ (fidStep3Bundle.frontTable ++
      (fidStep2Bundle.frontTable ++ (fidStep1ReplRows ++ fidBaseSpecTable)))).all
      SpecEntry.noExit = true
    rw [List.all_append, List.all_append, List.all_append, List.all_append,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, fidBaseSpecTable_noExit⟩⟩⟩⟩

private theorem fidStep5_front_noSolveBytes :
    fidStep5Bundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : "kissat_solve_bytes" ∈ fidStep5FrontNames :=
    fidStep5_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
  exact absurd hm (by decide)

theorem fidStep5Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep5Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidStep5Bundle fidStep5_front_noSolveBytes
    (fun _ _ _ _ hs => fidStep4Env_solve_bytes_of hs) a m Q X

theorem fidStep5_solveBytes_mem : m6oSolveBytesFn ∈ fidStep5Module.fns :=
  patchBundle_solveBytes_mem fidStep5Bundle fidStep4_solveBytes_mem fun r hr => by
    change r ∈ fidStep5Repls at hr
    simp only [fidStep5Repls, fidBveRepls, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep5Module` (`492` fns, `XPost := False`). -/
theorem fidStep5_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep5Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep5_moduleOk fidStep5_solveBytes_mem
    (fun _ _ _ _ hs => fidStep5Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep5Module`. -/
theorem fidStep5_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep5Module`. -/
theorem fidStep5_unsat_nv :
    Func.wp fidStep5Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep5_moduleOk fidStep5_solveBytes_mem
    (fun _ _ _ _ hs => fidStep5Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep5_moduleOk`. -/
theorem fidStep5Module_acyclic : fidStep5Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep5_moduleOk

/-- Canonical `KissatUnsatPkg` for Step-5 (`fidStep5Module`, `fidInlPolicy`). -/
def fidStep5UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep5Module fidInlPolicy fidStep5_solveBytes_mem
    fidStep5Env fidStep5_moduleOk fidStep5Env_noExit
    (fun _ _ _ _ hs => fidStep5Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5

end

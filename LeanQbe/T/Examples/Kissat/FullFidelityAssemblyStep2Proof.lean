/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep2S15
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof
import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParity
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyPart1
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
import all LeanQbe.T.Examples.Kissat.FullM7Transport0
import all LeanQbe.T.Examples.Kissat.FullM7Transport1
import all LeanQbe.T.Examples.Kissat.FullM7Proof
import all LeanQbe.T.Examples.Kissat.FullM7AnalyzeHdrProof
import all LeanQbe.T.Examples.Kissat.FullM6OrchProof0
import all LeanQbe.T.Examples.Kissat.FullM6Proof0a
import all LeanQbe.T.Examples.Kissat.FullM6Proof0b
import all LeanQbe.T.Examples.Kissat.FullM6Proof0c
import LeanQbe.T.Examples.Kissat.FullFastSched
import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
import LeanQbe.T.Examples.Kissat.FullM3Backbone
import LeanQbe.T.Examples.Kissat.FullM4VivBce
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
import LeanQbe.T.Examples.Kissat.FullM6LuckyS15
import LeanQbe.T.Examples.Kissat.FullM6S15Bridge
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 2 (`FullFidelityAssemblyStep2Proof`)

Certifies `FullFidelityAssemblyStep2.fidStep2Module` (`471` fns, `0` externs, `0` exits) via
`PatchModule.patchBundle_moduleOk` + `FullFidelityAssemblyUtil`:
1. `fidStep2Bundle : PatchBundle` layering Option-A `FullFidelityBcp.fidBcpHotPushRepls` (`9`)
   + `fidBcpHotPushBefores` (`2`) atop `fidStep1Module` (`469` fns), upgrading
   `full_propagate_ignore_hot` / `full_propagate_ignore` to `fullPropagateIgnoreS15Spec` and
   rewiring all `26` `full_bcp_hot` / `full_propagate` / caller rows (`fullBcpS15Spec`).
2. Closed `471/471` `fidStep2_moduleOk : ModuleOk fidStep2Env fidStep2Module`,
   `fidStep2Env_noExit`, `fidStep2_solve_bytes_sound`, `fidStep2_solve_bytes_host_sound`,
   `fidStep2_unsat_nv` (`XPost := False`, `std3`), and `fidStep2UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6S15Bridge
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` Over `fidStep1Module` (`471/471` Fns) -/

/-- Helper rows inserted before `"full_watch_push_m6"` and `"full_propagate_ignore_hot"`. -/
def fidStep2BeforeRows : List SpecEntry :=
  [ ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_prop_flush_del_fid", [i64, i64], [.bool], fidPropFlushDelSpec, true⟩ ]

/-- The `9` `SpecEntry` rows corresponding to `FullFidelityBcp.fidBcpHotPushRepls`. -/
def fidStep2ReplRows : List SpecEntry :=
  [ ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      FullM6BcpS15.fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64],
      FullM6BcpS15.fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], FullM6Orch.m6Deduce1uipHdrSpec, true⟩
  , ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩
  , ⟨"m6_hdr_decide_fid", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩ ]

/-- The `26` `full_bcp_hot` / `full_propagate` + untouched caller rows rewired to `S1.5`. -/
def fidStep2RewiredRows : List SpecEntry :=
  [ ⟨"full_bcp_hot", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  , ⟨"full_propagate", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.fullFlushTrailSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], FullM6Orch.m6ReduceSpec, true⟩
  , ⟨"full_warmup_m7", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_warmup", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.fullLuckyScanSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], Full.fullLuckySpec, true⟩
  , ⟨"full_probe_flush_hbr", [i64, i64], [i64], Full.fullProbeFlushHbrSpec, true⟩
  , ⟨"full_probe_assume_pair", [i64, i32], [i64], Full.fullProbeAssumePairSpec, true⟩
  , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], FullM6VivBackbone.fullVivInstM6Spec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], FullM6VivBackbone.fullVivClauseM6Spec, true⟩
  , ⟨"full_vivify_m6", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64],
      FullM6OrchAdapters.m6aVivifyTierSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool], Full.fullSubstElimVarsSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩
  , ⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.m7LuckyLateSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ ]

/-- Flat `469`-row base specification table (`fidStep1ReplRows ++ fidBaseSpecTable`) for Step 1. -/
private abbrev fidStep1EnvTable : List SpecEntry :=
  fidStep1Bundle.frontTable ++ fidStep1Bundle.baseTable

/-- Step-2 `PatchBundle` composing `fidStep1Module` + Option-A `fidBcpHotPushRepls`. -/
def fidStep2Bundle : PatchBundle where
  baseMod := fidStep1Module
  baseTable := fidStep1EnvTable
  baseOk := fidStep1_moduleOk
  repls := fidBcpHotPushRepls
  replRows := fidStep2ReplRows
  befores := fidBcpHotPushBefores
  beforeRows := fidStep2BeforeRows
  rewiredRows := fidStep2RewiredRows

/-- Closed `Env` for `fidStep2Module` (`471` fns). -/
def fidStep2Env : Env := patchEnv fidStep2Bundle

theorem fidStep2_externs_empty : fidStep2Module.externs = [] :=
  fidStep1_externs_empty

theorem fidStep2Fns_length : fidStep2Fns.length = 471 := by
  t_kernel_rfl

private def fidStep2ReplNames : List Sym :=
  [ "full_watch_push_m6", "full_heap_down", "full_heap_pop"
  , "full_propagate_ignore_hot", "full_propagate_ignore"
  , "full_deduce_1uip_m6", "full_deduce_1uip_m6_hdr"
  , "full_next_dec_var", "m6_hdr_decide_fid" ]

private def fidStep2FrontNames : List Sym :=
  [ "full_bcp_hot", "full_propagate", "full_parse_body_m6", "full_flush_trail"
  , "full_reduce", "full_reduce_m6", "full_warmup_m7", "full_warmup"
  , "full_lucky_scan", "full_lucky", "full_probe_flush_hbr", "full_probe_assume_pair"
  , "full_viv_inst_m6", "full_viv_clause_m6", "full_vivify_m6", "full_vivify_tier_m6_hdr"
  , "full_backbone_m6", "full_transitive_m6", "full_subst_elim_vars", "full_substitute"
  , "full_enter_dense", "full_rebuild_watches", "full_bce_m4", "full_lucky_late_m7"
  , "full_preprocess_m6", "full_search_m6"
  , "full_watch_push_m6", "full_heap_down", "full_heap_pop"
  , "full_propagate_ignore_hot", "full_propagate_ignore"
  , "full_deduce_1uip_m6", "full_deduce_1uip_m6_hdr"
  , "full_next_dec_var", "m6_hdr_decide_fid"
  , "full_watch_push_slow_m6", "full_prop_flush_del_fid" ]

private def fidStep2Bad : List Sym :=
  ["full_propagate_ignore_hot", "full_propagate_ignore", "full_bcp_hot", "full_propagate"]

private theorem fidStep2_replNames_eq : fidBcpHotPushRepls.map Fn.name = fidStep2ReplNames :=
  rfl

private theorem fidStep2_frontNames_eq :
    fidStep2Bundle.frontTable.map SpecEntry.name = fidStep2FrontNames :=
  rfl

private theorem fidStep2_front_nodup :
    (fidStep2Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep2_frontNames_eq]
  decide

private theorem fidStep2_replSigs_batch :
    [16, 20, 22, 83, 85, 139, 142, 155, 463].map (fun i => fidStep1Fns[i]?.map Fn.sig) =
      [ some ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool])
      , some ("full_heap_down", [i64, i32], [])
      , some ("full_heap_pop", [i64], [i64])
      , some ("full_propagate_ignore_hot", [i64, i64], [i64])
      , some ("full_propagate_ignore", [i64, i64], [i64])
      , some ("full_deduce_1uip_m6", [i64], [i64])
      , some ("full_deduce_1uip_m6_hdr", [i64], [i64])
      , some ("full_next_dec_var", [i64], [i64])
      , some ("m6_hdr_decide_fid", [i64], [i64]) ] := by
  t_kernel_rfl

private theorem fidStep2_slot {i : Nat} {s : SigEntry}
    (hi : fidStep1Fns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep1Fns, g.sig = s := by
  cases h : fidStep1Fns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidStep2Module_replSigs_ok :
    ∀ r ∈ fidBcpHotPushRepls, ∀ g ∈ fidStep1Module.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidStep1Fns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidStep1Fns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fidStep2_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have hnd : (fidStep1Fns.map Fn.name).Nodup :=
      (List.nodup_append.mp fidStep1Module_names_nodup).1
    have heq := nodup_name_eq Fn.name hnd hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [fidBcpHotPushRepls, FullM7HotWatchPush.m7HotWatchPushRepl, fidBcpRepls,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (slotSig_at fidStep2_replSigs_batch 0 16 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 1 20 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 2 22 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 3 83 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 4 85 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 5 139 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 6 142 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 7 155 _) rfl hnm
  · exact hslot (slotSig_at fidStep2_replSigs_batch 8 463 _) rfl hnm

theorem fidStep2Module_names_nodup : fidStep2Module.namesNodup :=
  LeanQbe.T.Module.namesNodup_of_checkNamesNodup (by t_kernel_rfl)

private theorem fidStep2Module_patchCallsOk :
    checkPatchCallsOk fidStep1Module fidBcpHotPushRepls fidBcpHotPushBefores = true := by
  t_kernel_rfl

private theorem fidStep2_isSome_find_of_name_mem {tbl : List SpecEntry} {nm : Sym}
    (h : nm ∈ tbl.map SpecEntry.name) : (tbl.find? (·.name == nm)).isSome = true := by
  obtain ⟨e, he, hnm⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hnm⟩

private theorem fidStep2_front_covered :
    ∀ fn, (fn ∈ fidBcpHotPushRepls ∨ fn ∈ fidBcpHotPushBefores.flatMap Prod.snd) →
      (fidStep2Bundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  refine fidStep2_isSome_find_of_name_mem ?_
  rw [fidStep2_frontNames_eq]
  rcases hfn with hr | hb
  · simp only [fidBcpHotPushRepls, FullM7HotWatchPush.m7HotWatchPushRepl, fidBcpRepls,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [fidBcpHotPushBefores, FullM7HotWatchPush.m7HotWatchPushBefore, fidBcpBefores,
      List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide

private theorem fidStep2_noCallBad_filter :
    (fidStep1Fns.filter fun fn =>
      !fidStep2ReplNames.contains fn.name && !fidStep2FrontNames.contains fn.name).all
      (noCallInFn fidStep2Bad) = true := by
  t_kernel_rfl

private theorem fidStep2_none_not_contains {tbl : List Sym} {nm : Sym}
    (hnone : ∀ x ∈ tbl, x ≠ nm) : tbl.contains nm = false := by
  induction tbl with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨(hnone hd List.mem_cons_self).symm, ih fun y hy => hnone y (List.mem_cons_of_mem _ hy)⟩

private theorem fidStep2_noCallBad :
    ∀ fn ∈ fidStep1Module.fns,
      fidBcpHotPushRepls.find? (·.name == fn.name) = none →
      fidStep2Bundle.frontTable.find? (·.name == fn.name) = none →
      noCallInFn fidStep2Bad fn = true := by
  intro fn hmem hr hf
  have hnr : fidStep2ReplNames.contains fn.name = false := by
    refine fidStep2_none_not_contains fun nm hnm => ?_
    rw [← fidStep2_replNames_eq] at hnm
    obtain ⟨r, hr_mem, rfl⟩ := List.mem_map.mp hnm
    intro heq
    have h1 := List.find?_eq_none.mp hr r hr_mem
    simp [heq] at h1
  have hnf : fidStep2FrontNames.contains fn.name = false := by
    refine fidStep2_none_not_contains fun nm hnm => ?_
    rw [← fidStep2_frontNames_eq] at hnm
    obtain ⟨e, he_mem, rfl⟩ := List.mem_map.mp hnm
    intro heq
    have h1 := List.find?_eq_none.mp hf e he_mem
    simp [heq] at h1
  exact List.all_eq_true.mp fidStep2_noCallBad_filter fn
    (List.mem_filter.mpr ⟨hmem, by rw [hnr, hnf]; rfl⟩)

/-! ## 2. Fast Table Lookup, Elimination, & Spec Agree Helpers -/

private abbrev Fid2EnvSpec (nm : Sym) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ a m Q X, sp a m Q X → fidStep2Env nm as bs a m Q X

private theorem fidStep2_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep2Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid2EnvSpec nm sp := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep2Bundle fidStep2_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

private theorem fidStep2_baseEnv_of_fidBase {f : Sym} {as bs : List Ty}
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv f as bs xs m Q X) :
    Env.ofTable fidStep1EnvTable f as bs xs m Q X := by
  change patchEnv fidStep1Bundle f as bs xs m Q X
  have hf : fidStep1Bundle.frontTable.find? (·.name == f) = none := by
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
  rw [patchEnv_base_eq fidStep1Bundle hf]
  exact h

private theorem fidStep2_of_fidBase {f : Sym} {as bs : List Ty}
    (hf2 : !(fidStep2FrontNames.contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv f as bs xs m Q X) :
    fidStep2Env f as bs xs m Q X := by
  have hf : fidStep2Bundle.frontTable.find? (·.name == f) = none := by
    apply List.find?_eq_none.mpr
    intro e he hbeq
    have hnm : e.name = f := beq_iff_eq.mp hbeq
    have hm : fidStep2FrontNames.contains f = true :=
      List.contains_iff_mem.mpr (fidStep2_frontNames_eq ▸ (hnm ▸ List.mem_map_of_mem he))
    cases hc : fidStep2FrontNames.contains f <;> simp_all
  change patchEnv fidStep2Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep2Bundle hf]
  exact fidStep2_baseEnv_of_fidBase hf1 h

private theorem fidStep2_m7BaseRow {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hf2 : !(fidStep2FrontNames.contains f) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains f = true := by decide)
    (hnmf : f ∉ mfExclNames := by decide)
    (hncp : f ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid2EnvSpec f sp := fun a m Q X hs =>
  fidStep2_of_fidBase hf2 hf1
    (fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hmem hno a m Q X hs)))

private theorem fidStep2_m7Row_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : m7FidBaseTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf2 : !(fidStep2FrontNames.contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hnmf : nm ∉ mfExclNames := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid2EnvSpec nm sp :=
  fidStep2_m7BaseRow (List.mem_of_getElem? hi) hf2 hf1 hnmf hncp hno

private theorem fidStep2_extraRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : mfExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hf2 : !(fidStep2FrontNames.contains nm) = true := by decide)
    (hf1 : !(fidStep1ReplRows.map SpecEntry.name).contains nm = true := by decide)
    (hncp : nm ∉ m8CpExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    Fid2EnvSpec nm sp := fun a m Q X hs =>
  fidStep2_of_fidBase hf2 hf1 (fid_extraRow i nm as bs sp hi hno hncp a m Q X hs)

private theorem fidStep2_extPush2Row :
    Fid2EnvSpec "full_extend_push2" Full.fullExtendPush2Spec := by
  rintro ⟨hp, blk, ot, ⟨⟩⟩ m Q X ⟨c, s, R, hel, hlen, hm, hQ⟩
  refine fidStep2_of_fidBase (by decide) (by decide) ?_
  refine fidBaseEnv_of_m8Sw (by decide) (.extPush2 ⟨c, s, R, hel, hlen, hm, ?_⟩)
  intro r s' m' hc hlen' ⟨h1, h2, h3, _⟩ hm'
  exact hQ r s' m' hc hlen' ⟨h1, h2, h3⟩ hm'

private theorem fidStep2_bceVarM4_mem :
    (⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.fullBceVarM4Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 21 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))

private theorem fidStep2_bceM4_mem :
    (⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 21 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 3) rfl))

private theorem fidStep2_luckyPolarM7_mem :
    (⟨"full_lucky_polar_m7", [i64], [i64], Full.fullLuckyPolarSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 25 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 7) rfl))

private theorem fidStep2_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep1EnvTable nm as bs xs m Q X)
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
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle hf1] at h
  exact fidBaseEnv_elim_m7Base hmem h hneEx hneSw hne1 hne2 hne3 hne4 hne5 hne6 hne7

private theorem fidStep2_elim_m7OrExtra {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hex : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ mfExtraRows)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep1EnvTable nm as bs xs m Q X)
    (hf1 : fidStep1ReplRows.find? (·.name == nm) = none := by decide)
    (hneSw : !(m8SwNamesLit.contains nm) = true := by decide)
    (hne1 : nm ∉ m8CpExclNames := by decide)
    (hne2 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (hne3 : nm ∉ fidBveHelperRows.map SpecEntry.name := by decide)
    (hne4 : nm ≠ "full_extend_push2" := by decide)
    (hne5 : nm ≠ "full_cong_enq_var" := by decide)
    (hne6 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne7 : nm ≠ "full_cong_worklist" := by decide) :
    sp xs m Q (fun _ _ _ _ => False) := by
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle hf1] at h
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat hne1 hne2 hne3 h)
  have hm7 := m8cp_sw_to_m7_of_ne hne4 (not_in_swRows nm hneSw) hne5 hne6 hne7 hsw
  cases hm7 with
  | base _ hb0 => exact m7FidBase_elim_of_mem hmem hb0
  | extra he => exact mf_extra_elim hex he

private theorem fidStep2_elim_extraOnly {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hex : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ mfExtraRows)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidStep1EnvTable nm as bs xs m Q X)
    (hexcl : nm ∈ mfExclNames := by decide)
    (hf1 : fidStep1ReplRows.find? (·.name == nm) = none := by decide)
    (hneSw : !(m8SwNamesLit.contains nm) = true := by decide)
    (hne1 : nm ∉ m8CpExclNames := by decide)
    (hne2 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (hne3 : nm ∉ fidBveHelperRows.map SpecEntry.name := by decide)
    (hne4 : nm ≠ "full_extend_push2" := by decide)
    (hne5 : nm ≠ "full_cong_enq_var" := by decide)
    (hne6 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne7 : nm ≠ "full_cong_worklist" := by decide) :
    sp xs m Q (fun _ _ _ _ => False) := by
  change patchEnv fidStep1Bundle nm as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep1Bundle hf1] at h
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat hne1 hne2 hne3 h)
  have hm7 := m8cp_sw_to_m7_of_ne hne4 (not_in_swRows nm hneSw) hne5 hne6 hne7 hsw
  cases hm7 with
  | base hne _ => exact absurd hexcl hne
  | extra he => exact mf_extra_elim hex he

private theorem fidStep2_before_not_in_step1 :
    (fidStep1Fns.map Fn.name).contains "full_watch_push_slow_m6" = false ∧
    (fidStep1Fns.map Fn.name).contains "full_prop_flush_del_fid" = false :=
  ⟨by t_kernel_rfl, by t_kernel_rfl⟩

private theorem fidStep2_agree :
    ∀ s ∈ fidStep1Module.sigs, s.1 ∉ fidStep2Bad →
      ∀ xs m P E, Env.ofTable fidStep1EnvTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidStep2Bundle s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs hnb xs m P E hBase
  cases hf : fidStep2Bundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidStep2Bundle hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hsig_in : e.name ∈ fidStep1Fns.map Fn.name := by
        have hm := hs
        rw [LeanQbe.T.Module.sigs, fidStep1_externs_empty, List.map_nil, List.append_nil] at hm
        obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
        exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
      have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
      have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
      have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
      have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
      have hPush :
          ∀ hmem : e ∈ fidStep2Bundle.frontTable, e.eff xs m P E →
            patchEnv fidStep2Bundle e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidStep2Bundle fidStep2_front_nodup hmem hs'
      have he0 := he
      simp only [fidStep2Bundle, PatchBundle.frontTable, fidStep2RewiredRows, fidStep2ReplRows,
        fidStep2BeforeRows, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (by decide : "full_bcp_hot" ∈ fidStep2Bad) hnb
      · exact absurd (by decide : "full_propagate" ∈ fidStep2Bad) hnb
      · exact hPush he0 (fidStep2_elim_m7Base hc1p.parseBodyM6 hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 106) (by rfl : m7FidBaseTable[106]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 110) (by rfl : m7FidBaseTable[110]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reduceM6) hBase)
      · exact hPush he0 (fidStep2_elim_m7OrExtra
          (List.mem_of_getElem? (i := 165) (by rfl : m7FidBaseTable[165]? = some _))
          (List.mem_of_getElem? (i := 24) (by rfl : mfExtraRows[24]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 167) (by rfl : m7FidBaseTable[167]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2.luckyScan hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2p.lucky hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 188) (by rfl : m7FidBaseTable[188]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 189) (by rfl : m7FidBaseTable[189]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7OrExtra
          (List.mem_of_getElem? (i := 203) (by rfl : m7FidBaseTable[203]? = some _))
          (List.mem_of_getElem? (i := 38) (by rfl : mfExtraRows[38]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7OrExtra
          (List.mem_of_getElem? (i := 209) (by rfl : m7FidBaseTable[209]? = some _))
          (List.mem_of_getElem? (i := 44) (by rfl : mfExtraRows[44]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 216) (by rfl : m7FidBaseTable[216]? = some _)) hBase)
      · have hmv : m6aVivifyTierSpec xs m P E :=
          m6aVivifyTierSpec_monoX (fidStep2_elim_extraOnly
            (List.mem_of_getElem? (i := 51) (by rfl : mfExtraRows[51]? = some _)) hBase)
        exact hPush he0 hmv
      · exact hPush he0 (fidStep2_elim_m7Base hc2p.backboneM6 hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2p.transitiveM6 hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 232) (by rfl : m7FidBaseTable[232]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2p.substitute hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2.enterDense hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2.rebuildWatches hBase)
      · exact hPush he0 (fidStep2_elim_m7Base fidStep2_bceM4_mem hBase)
      · have hmv : FullM7Search.m7LuckyLateSpec xs m P E :=
          FullM7Search.m7LuckyLateSpec_monoX (fidStep2_elim_m7Base hc3.luckyLateM7 hBase)
        exact hPush he0 hmv
      · exact hPush he0 (fidStep2_elim_m7Base
          (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.preprocessM6) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base m7FidBase_searchM6_mem hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc1p.watchPushM6 hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 20) (by rfl : m7FidBaseTable[20]? = some _)) hBase)
      · exact hPush he0 (fidStep2_elim_m7Base
          (List.mem_of_getElem? (i := 22) (by rfl : m7FidBaseTable[22]? = some _)) hBase)
      · exact absurd (by decide : "full_propagate_ignore_hot" ∈ fidStep2Bad) hnb
      · exact absurd (by decide : "full_propagate_ignore" ∈ fidStep2Bad) hnb
      · exact hPush he0 (fidStep2_elim_m7Base hc2p.deduce1uipM6 hBase)
      · exact hPush he0 (fidStep2_elim_m7Base m7FidBase_deduce1uipM6Hdr_mem hBase)
      · exact hPush he0 (fidStep2_elim_m7Base hc2.nextDecVar hBase)
      · exact hPush he0 (fidStep2_elim_extraOnly
          (List.mem_of_getElem? (i := 59) (by rfl : mfExtraRows[59]? = some _)) hBase)
      · have hno : (fidStep1Fns.map Fn.name).contains "full_watch_push_slow_m6" = false :=
          fidStep2_before_not_in_step1.1
        have hm : (fidStep1Fns.map Fn.name).contains "full_watch_push_slow_m6" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm
        cases hm
      · have hno : (fidStep1Fns.map Fn.name).contains "full_prop_flush_del_fid" = false :=
          fidStep2_before_not_in_step1.2
        have hm : (fidStep1Fns.map Fn.name).contains "full_prop_flush_del_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm
        cases hm
    · have hne : ∀ e' ∈ fidStep2Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep2_front_nodup he' he (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep2Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift fidStep2Bundle.frontTable hne

/-! ## 3. Front-Table Implementation Helpers & `fidStep2_moduleOk` (`471/471`) -/

private theorem fidStep2_fn_eq_before {fn b : Fn}
    (hfn : fn ∈ fidStep2Module.fns) (hb : b ∈ fidBcpHotPushBefores.flatMap Prod.snd)
    (htgt : ∃ tgt g0, (tgt, [b]) ∈ fidBcpHotPushBefores ∧ g0 ∈ fidStep1Fns ∧ g0.name = tgt)
    (hnm : b.name = fn.name) : fn = b := by
  have hModNd : (fidStep2Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep2Module_names_nodup).1
  obtain ⟨tgt, g0, hpair, hg0, hgn⟩ := htgt
  have hbm : b ∈ fidStep2Module.fns := by
    change b ∈ patchFns fidBcpHotPushRepls fidBcpHotPushBefores fidStep1Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    simp only [patchInsAt, fidBcpHotPushBefores, FullM7HotWatchPush.m7HotWatchPushBefore,
      fidBcpBefores] at hpair ⊢
    rcases List.mem_cons.mp hpair with h0 | h1
    · obtain ⟨ht0, hb0⟩ := Prod.mk.inj h0
      rw [← hb0, hgn, ← ht0]; simp
    · obtain ⟨ht1, hb1⟩ := Prod.mk.inj (List.mem_singleton.mp h1)
      have hb1' : b = fidPropFlushDelFn := List.singleton_inj.mp hb1
      subst ht1; subst hb1'
      simp [hgn]
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fidStep2_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidStep2Module.fns) (hr : r ∈ fidBcpHotPushRepls)
    {idx : Nat} {s : SigEntry} (hslot : fidStep1Fns[idx]?.map Fn.sig = some s)
    (hrn : r.name = s.1) (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidStep2Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep2Module_names_nodup).1
  obtain ⟨g, hg, hgs⟩ := fidStep2_slot hslot
  have hrm : r ∈ fidStep2Module.fns :=
    mem_patchFns_of_repl (by decide) hr hg (hrn.trans (congrArg Prod.fst hgs).symm)
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fidStep2_fn_eq_base {fn g : Fn}
    (hfn : fn ∈ fidStep2Module.fns) (idx : Nat)
    (hi : fidStep1Fns[idx]? = some g)
    (hne : fidBcpHotPushRepls.find? (·.name == g.name) = none := by rfl)
    (hnm : g.name = fn.name) : fn = g := by
  have hModNd : (fidStep2Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep2Module_names_nodup).1
  have hg : g ∈ fidStep1Fns := List.mem_of_getElem? hi
  have hgm : g ∈ fidStep2Module.fns := by
    change g ∈ patchFns fidBcpHotPushRepls fidBcpHotPushBefores fidStep1Fns
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨g, hg, Or.inr (by simp [hne])⟩
  exact nodup_name_eq Fn.name hModNd hfn hgm hnm.symm

private theorem fidStep2_front_impl :
    ∀ fn e, fn ∈ fidStep2Bundle.patchedMod.fns →
      fidStep2Bundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidStep2Env fn e := by
  intro fn e hfn hf
  change fn ∈ fidStep2Module.fns at hfn
  have he : e ∈ fidStep2Bundle.frontTable := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
  have hBv := m7Part2BvaGuRows_of_sub m7FidBase_part2_mem
  have rProp := fidStep2_frontRow 1 "full_propagate" FullM6BcpS15.fullBcpS15Spec
  have rBt := fidStep2_m7BaseRow hc1.backtrack
  have rAsg := fidStep2_m7BaseRow hc1.assign
  have rArSwp := fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.arenaSweep)
  have rNext := fidStep2_m7BaseRow hc1.arenaNext
  have rAu := fidStep2_m7BaseRow hc2.addUnit
  have rAddBinM6 := fidStep2_m7BaseRow hc2.addBin
  have rWp := fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.watchPush)
  have rNextDec := fidStep2_frontRow 33 "full_next_dec_var" Full.fullNextDecVarSpec
  simp only [fidStep2Bundle, PatchBundle.frontTable, fidStep2RewiredRows, fidStep2ReplRows,
    fidStep2BeforeRows, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hfeq := fidStep2_fn_eq_base hfn 84
      (by t_kernel_rfl : fidStep1Fns[84]? = some
        ⟨"full_bcp_hot", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩) rfl hnm
    subst hfeq
    exact .of (full_bcp_hot_s15_wp fidStep2Env
      (fidStep2_frontRow 29 "full_propagate_ignore_hot" FullM6BcpS15.fullPropagateIgnoreS15Spec))
  · have hfeq := fidStep2_fn_eq_base hfn 86
      (by t_kernel_rfl : fidStep1Fns[86]? = some
        ⟨"full_propagate", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩) rfl hnm
    subst hfeq
    exact .of (full_bcp_hot_s15_wp fidStep2Env
      (fidStep2_frontRow 29 "full_propagate_ignore_hot" FullM6BcpS15.fullPropagateIgnoreS15Spec))
  · have hfeq := fidStep2_fn_eq_base hfn 87
      (by t_kernel_rfl : fidStep1Fns[87]? = some
        ⟨"full_parse_body_m6", [i64, i64], [i64], FullM6WalkParse.full_parse_body_m6_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM6WalkParse.full_parse_body_m6_del_wp fidStep2Env
      (fidStep2_m7Row_at 76 "full_skip_cl" Full.fullSkipClSpec)
      (fidStep2_m7Row_at 77 "full_ingest_cl" Full.fullIngestClSpec)
      (s15_to_propagateDel rProp)
      (fidStep2_m7Row_at 2 "kissat_skip_ws_comments" kissatSkipWsCommentsSpec))
  · have hfeq := fidStep2_fn_eq_base hfn 106
      (by t_kernel_rfl : fidStep1Fns[106]? = some
        ⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.full_flush_trail_body⟩) rfl hnm
    subst hfeq
    exact .of (FullM6CompactFlush.full_flush_trail_del_wp fidStep2Env rBt
      (s15_to_propagateDel rProp))
  · have hfeq := fidStep2_fn_eq_base hfn 110
      (by t_kernel_rfl : fidStep1Fns[110]? = some
        ⟨"full_reduce", [i64, .bool], [i64], Full.full_reduce_body⟩) rfl hnm
    subst hfeq
    have rIsqrt := fidStep2_m7BaseRow hc1.isqrt
    have rIlog := fidStep2_m7BaseRow hc1.ilog10
    have rRec := fidStep2_m7Row_at 89 "full_recompute_tiers" Full.fullRecomputeTiersSpec
    have rMrk := fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.markReasons)
    have rSort := fidStep2_m7BaseRow hc1p.sortReds
    have hwp := Full.full_reduce_wp fidStep2Env
      (fun ⟨x, ⟨⟩⟩ m Q X hQ => rIsqrt (x, ()) m Q X fun r hsq _ _ =>
        hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq))
      rIlog rNext
      (by
        rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
        exact rRec (c.hdr, ()) m Q X ⟨c, s, R, rfl, hlen, hm, fun _ s' m' hc hlen' hp hm' => by
          rcases s' with ⟨c', sc'⟩; change c' = s.core at hc; subst hc
          exact hQ sc' m' hlen'.scratch_ok hp.1.1 hp.1.2 hp.2.2.1 hm'⟩)
      (by
        rintro ⟨h, sf, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hm, hQ⟩
        exact rMrk (c.hdr, sf, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hm,
          fun ar' m' hl' hr' hp' hrm' hw' hm' =>
            hQ ar' m' hl' hr' hp' (fun hsf idx hidx => hrm' hsf idx hidx) hw' hm'⟩)
      (by
        rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, hQ⟩
        exact rSort (c.hdr, n, ()) m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, fun rr' m' hrr hm' =>
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
        exact rBt (c.hdr, tgt, ()) m Q X ⟨c, s, R, rfl, hlen, hcl_bd, htg_bd, hw.trail_lits_lt,
          hm, fun va lv rs tr tp te pr cl un sc m' hl' _ _ hcl' hps _ _ _ hwt _ hm' => by
            have hmin : cl = tgt.toNat := hcl'.trans (Nat.min_eq_right hle)
            subst hmin
            exact hQ va lv rs tr tp te pr un sc m' hl' (hwt F0 Fc hw hle)
              hps.1.1 hps.1.2 hps.2.2.1 hm'⟩)
      (s15_to_dwPropagate rProp)
      (by
        rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm, hQ⟩
        exact rArSwp (c.hdr, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm,
          fun r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm' =>
            hQ r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'⟩)
    refine .of (by
      rintro ⟨h, force, ⟨⟩⟩ m Q X hs
      rcases hs with ⟨c, F0, Fc, s, R, rfl, ⟨hlen, hw, hlm, hnd0, hext, hdm⟩, hm, hQ⟩
      exact hwp (c.hdr, force, ()) m Q X
        ⟨c, F0, Fc, s, R, rfl, hlen, hw, hlm, hnd0, hext, hdm, hm,
          fun r s' m' hdw hw' hr hu hoom hcl hfu hcv htmp htl _ _ _ _ _ _ hws2 hpos hm' =>
            hQ r s' m' ⟨hdw.1.lengths, hw', hdw.2.1, hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2⟩
              hr hcl hfu hcv htmp htl hws2 hu hoom (fun _ => hpos) hm'⟩)
  · have hfeq := fidStep2_fn_eq_base hfn 111
      (by t_kernel_rfl : fidStep1Fns[111]? = some
        ⟨"full_reduce_m6", [i64, .bool], [i64], FullM7FidelitySchedFix.full_reduce_fid2_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM7FidelitySchedFix.full_reduce_fid2_wp fidStep2Env
      (fidStep2_m7BaseRow hc1.isqrt)
      (fidStep2_m7BaseRow hc1.log10Q16M7 (by decide) (by decide) (by decide) (by decide)
        (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h))
      rNext
      (fidStep2_m7BaseRow hc1p.recomputeTiers (by decide) (by decide) (by decide) (by decide)
        (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
      (fidStep2_m7BaseRow hc1.hdrSetWm (by decide) (by decide) (by decide) (by decide)
        (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
      (fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.markReasons))
      (fidStep2_m7BaseRow hc1p.sortReds) rBt rProp rArSwp)
  · have hfeq := fidStep2_fn_eq_base hfn 168
      (by t_kernel_rfl : fidStep1Fns[168]? = some
        ⟨"full_warmup_m7", [i64], [], FullM7Walk.full_warmup_m7_body⟩) rfl hnm
    subst hfeq
    exact .of (full_warmup_m7_s15_wp fidStep2Env rNextDec rAsg rProp rBt)
  · have hfeq := fidStep2_fn_eq_base hfn 170
      (by t_kernel_rfl : fidStep1Fns[170]? = some
        ⟨"full_warmup", [i64], [], FullM7Walk.full_warmup_m7_body⟩) rfl hnm
    subst hfeq
    exact .of (full_warmup_m7_s15_wp fidStep2Env rNextDec rAsg rProp rBt)
  · have hfeq := fidStep2_fn_eq_base hfn 185
      (by t_kernel_rfl : fidStep1Fns[185]? = some
        ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.full_lucky_scan_body⟩) rfl hnm
    subst hfeq
    exact .of (FullM6LuckyS15.full_lucky_scan_s15_wp fidStep2Env rAsg rBt rProp
      (fidStep2_m7Row_at 149 "full_analyze" Full.fullAnalyzeSpec))
  · have hfeq := fidStep2_fn_eq_base hfn 187
      (by t_kernel_rfl : fidStep1Fns[187]? = some
        ⟨"full_lucky", [i64], [i64], Full.full_lucky_body⟩) rfl hnm
    subst hfeq
    exact .of (FullM6LuckyS15.full_lucky_s15_wp fidStep2Env
      (fidStep2_m7Row_at 183 "full_lucky_polar" Full.fullLuckyPolarSpec)
      (fidStep2_frontRow 8 "full_lucky_scan" Full.fullLuckyScanSpec) rAsg rBt rProp)
  · have hfeq := fidStep2_fn_eq_base hfn 191
      (by t_kernel_rfl : fidStep1Fns[191]? = some
        ⟨"full_probe_flush_hbr", [i64, i64], [i64], Full.full_probe_flush_hbr_body⟩) rfl hnm
    subst hfeq
    exact .of (full_probe_flush_hbr_s15_wp fidStep2Env
      (m6_add_bin_m6_to_canon rAddBinM6) rProp)
  · have hfeq := fidStep2_fn_eq_base hfn 192
      (by t_kernel_rfl : fidStep1Fns[192]? = some
        ⟨"full_probe_assume_pair", [i64, i32], [i64],
          FullM6VivBackbone.full_probe_assume_pair_m6_body⟩) rfl hnm
    subst hfeq
    exact .of (full_probe_assume_pair_m6_s15_wp fidStep2Env rAsg
      (fidStep2_m7Row_at 187 "full_probe_prop" Full.fullProbePropSpec) rBt
      (m6_analyze_to_20 (fidStep2_m7Row_at 149 "full_analyze" Full.fullAnalyzeSpec))
      rProp (fidStep2_frontRow 10 "full_probe_flush_hbr" Full.fullProbeFlushHbrSpec) rAu)
  · have hfeq := fidStep2_fn_eq_base hfn 206
      (by t_kernel_rfl : fidStep1Fns[206]? = some
        ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], FullM6VivBackbone.full_viv_inst_m6_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM6VivBackbone.full_viv_inst_m6_del_wp fidStep2Env rBt rAsg
      (s15_to_propagateIgnoreDel
        (fidStep2_frontRow 30 "full_propagate_ignore" FullM6BcpS15.fullPropagateIgnoreS15Spec))
      (fidStep2_extraRow 34 "full_viv_deduce_m6" FullM6VivBackbone.fullVivDeduceM6Spec)
      (fidStep2_extraRow 37 "full_viv_inst_check_m6" FullM6VivBackbone.fullVivInstCheckM6Spec)
      (fidStep2_extraRow 30 "full_viv_commit_m6" FullM6VivBackbone.fullVivCommitM6Spec))
  · have hfeq := fidStep2_fn_eq_base hfn 212
      (by t_kernel_rfl : fidStep1Fns[212]? = some
        ⟨"full_viv_clause_m6", [i64, i32], [i64], FullM6VivBackbone.full_viv_clause_m6_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM6VivBackbone.full_viv_clause_m6_del_wp fidStep2Env
      (fidStep2_extraRow 42 "full_viv_l0_simp_m6" FullM6VivBackbone.fullVivL0SimpM6Spec)
      (fidStep2_extraRow 40 "full_viv_sort_counts_m6" FullM6VivBackbone.fullVivSortCountsM6Spec)
      (fidStep2_extraRow 43 "full_viv_reuse_prefix_m6" FullM6VivBackbone.fullVivReusePrefixM6Spec)
      (fidStep2_extraRow 35 "full_viv_best_implied_m6" FullM6VivBackbone.fullVivBestImpliedM6Spec)
      rAsg
      (s15_to_propagateIgnoreDel
        (fidStep2_frontRow 30 "full_propagate_ignore" FullM6BcpS15.fullPropagateIgnoreS15Spec))
      rBt (fidStep2_extraRow 39 "full_viv_finish_m6" FullM6VivBackbone.fullVivFinishM6Spec))
  · have hfeq := fidStep2_fn_eq_base hfn 219
      (by t_kernel_rfl : fidStep1Fns[219]? = some
        ⟨"full_vivify_m6", [i64, i64, i64], [i64], FullM6VivBackbone.full_vivify_m6_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM6VivBackbone.full_vivify_m6_del_wp fidStep2Env rBt
      (fidStep2_extraRow 46 "full_viv_collect_m6" FullM6VivBackbone.fullVivCollectM6Spec)
      (fidStep2_extraRow 47 "full_viv_count_m6" FullM6VivBackbone.fullVivCountM6Spec)
      (fidStep2_extraRow 48 "full_viv_keys_m6" FullM6VivBackbone.fullVivKeysM6Spec)
      (fidStep2_extraRow 49 "full_viv_sort_sched_m6" FullM6VivBackbone.fullVivSortSchedM6Spec)
      (fidStep2_frontRow 13 "full_viv_clause_m6" FullM6VivBackbone.fullVivClauseM6Spec)
      (s15_to_propagateDel rProp)
      (fidStep2_extraRow 50 "full_viv_clear_tier_m6" FullM6VivBackbone.fullVivClearTierM6Spec))
  · have hfeq := fidStep2_fn_eq_base hfn 220
      (by t_kernel_rfl : fidStep1Fns[220]? = some
        ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64],
          FullFidelityBase.full_vivify_tier_m6_hdr_fid_body⟩) rfl hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (full_vivify_tier_m6_hdr_fid_wp fidStep2Env rBt
        (fidStep2_extraRow 46 "full_viv_collect_m6" FullM6VivBackbone.fullVivCollectM6Spec)
        (fidStep2_extraRow 47 "full_viv_count_m6" FullM6VivBackbone.fullVivCountM6Spec)
        (fidStep2_extraRow 48 "full_viv_keys_m6" FullM6VivBackbone.fullVivKeysM6Spec)
        (fidStep2_extraRow 49 "full_viv_sort_sched_m6" FullM6VivBackbone.fullVivSortSchedM6Spec)
        (fidStep2_frontRow 13 "full_viv_clause_m6" FullM6VivBackbone.fullVivClauseM6Spec)
        rProp
        (fidStep2_extraRow 50 "full_viv_clear_tier_m6" FullM6VivBackbone.fullVivClearTierM6Spec)
        xs m Q _ hs)
  · have hfeq := fidStep2_fn_eq_base hfn 229
      (by t_kernel_rfl : fidStep1Fns[229]? = some
        ⟨"full_backbone_m6", [i64, i64], [i64], FullM6VivBackbone.full_backbone_m6_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM6VivBackbone.full_backbone_m6_del_wp fidStep2Env rBt
      (s15_to_propagateDel rProp) rAu
      (fidStep2_m7Row_at 219 "full_prioritize_binaries_m6"
        FullM6VivBackbone.fullPrioritizeBinariesM6Spec)
      (fidStep2_m7Row_at 220 "full_backbone_sched_m6" FullM6VivBackbone.fullBackboneSchedM6Spec)
      (fidStep2_m7Row_at 225 "full_backbone_round_m6" FullM6VivBackbone.fullBackboneRoundM6Spec)
      (fidStep2_m7Row_at 221 "full_backbone_keep_m6" FullM6VivBackbone.fullBackboneKeepM6Spec))
  · have hfeq := fidStep2_fn_eq_base hfn 232
      (by t_kernel_rfl : fidStep1Fns[232]? = some
        ⟨"full_transitive_m6", [i64, i64], [i64], FullM6VivBackbone.full_transitive_m6_body⟩)
      rfl hnm
    subst hfeq
    exact .of (FullM6VivBackbone.full_transitive_m6_del_wp fidStep2Env rBt
      (fidStep2_m7Row_at 219 "full_prioritize_binaries_m6"
        FullM6VivBackbone.fullPrioritizeBinariesM6Spec)
      (fidStep2_m7Row_at 228 "full_trans_sort_m6" FullM6VivBackbone.fullTransSortM6Spec)
      (fidStep2_m7Row_at 227 "full_trans_lit_m6" FullM6VivBackbone.fullTransLitM6Spec)
      (s15_to_propagateDel rProp)
      (fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)))
  · have hfeq := fidStep2_fn_eq_base hfn 235
      (by t_kernel_rfl : fidStep1Fns[235]? = some
        ⟨"full_subst_elim_vars", [i64, i64], [.bool], Full.full_subst_elim_vars_body⟩)
      rfl hnm
    subst hfeq
    exact .of (full_subst_elim_vars_s15_wp fidStep2Env rAu rProp fidStep2_extPush2Row
      (fidStep2_m7BaseRow hc2.setInactive))
  · have hfeq := fidStep2_fn_eq_base hfn 238
      (by t_kernel_rfl : fidStep1Fns[238]? = some
        ⟨"full_substitute", [i64], [i64], FullM6CongSubst.full_substitute_body⟩) rfl hnm
    subst hfeq
    exact .of (FullM6CongSubst.full_substitute_del_wp fidStep2Env rBt
      (fidStep2_m7Row_at 231 "full_tarjan_scc" Full.fullTarjanSccSpec)
      (fidStep2_frontRow 18 "full_subst_elim_vars" Full.fullSubstElimVarsSpec)
      (fidStep2_m7Row_at 233 "full_subst_rewrite_bins" Full.fullSubstRewriteBinsSpec)
      (fidStep2_m7Row_at 234 "full_subst_rewrite_ar" Full.fullSubstRewriteArSpec)
      rArSwp (s15_to_propagateDel rProp))
  · have hfeq := fidStep2_fn_eq_base hfn 239
      (by t_kernel_rfl : fidStep1Fns[239]? = some
        ⟨"full_enter_dense", [i64], [.bool], FullM8FidV12.m8_enter_dense_body⟩) rfl hnm
    subst hfeq
    exact .of (m8_enter_dense_s15_wp fidStep2Env rBt
      (fidStep2_frontRow 3 "full_flush_trail" FullM6CompactFlush.fullFlushTrailSpec) rProp
      (fidStep2_m7Row_at 96 "full_sweep_bins" Full.fullSweepBinsSpec)
      rWp rArSwp rNext)
  · have hfeq := fidStep2_fn_eq_base hfn 240
      (by t_kernel_rfl : fidStep1Fns[240]? = some
        ⟨"full_rebuild_watches", [i64], [i64], Full.full_rebuild_watches_body⟩) rfl hnm
    subst hfeq
    have hwp := Full.full_rebuild_watches_wp fidStep2Env
      (by
        rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm, hQ⟩
        exact rArSwp (c.hdr, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm,
          fun r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm' =>
            hQ r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'⟩)
      (s15_to_dwPropagate rProp)
    refine .of (by
      rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdn, hm, hQ⟩
      rcases hdn with ⟨⟨hlen, Fc, hw⟩, hlm, hnd0, hext, hcl0, _⟩
      exact hwp (c.hdr, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hlm, hnd0, hext, hcl0, hm,
        fun r s' m' hsp' _ hcl0' hr hu hfl _ _ _ _ _ hm' =>
          hQ r s' m' hsp' hcl0' hfl hr hu hm'⟩)
  · have hfeq := fidStep2_fn_eq_base hfn 431
      (by t_kernel_rfl : fidStep1Fns[431]? = some
        ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.full_bce_m4_body⟩) rfl hnm
    subst hfeq
    exact .of (FullM6Proof.m6_bce_m4_s15_wp fidStep2Env
      (fidStep2_frontRow 20 "full_enter_dense" FullFastSched.schedEnterDenseSpec)
      (fidStep2_m7BaseRow fidStep2_bceVarM4_mem)
      (fidStep2_frontRow 21 "full_rebuild_watches" Full.fullRebuildWatchesSpec) rProp)
  · have hfeq := fidStep2_fn_eq_base hfn 452
      (by t_kernel_rfl : fidStep1Fns[452]? = some
        ⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.full_lucky_late_m7_body⟩) rfl hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (full_lucky_late_m7_s15_wp fidStep2Env
        (fidStep2_m7BaseRow fidStep2_luckyPolarM7_mem)
        (fidStep2_frontRow 8 "full_lucky_scan" Full.fullLuckyScanSpec)
        rAsg rBt rProp xs m Q _ hs)
  · have hfeq := fidStep2_fn_eq_base hfn 461
      (by t_kernel_rfl : fidStep1Fns[461]? = some
        ⟨"full_preprocess_m6", [i64], [i64], FullM8FidV12.m8_preprocess_m6_body⟩) rfl hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (FullM8FidV12.m8_preprocess_m6_wp fidStep2Env rProp rArSwp
        (fidStep2_frontRow 9 "full_lucky" Full.fullLuckySpec)
        (fidStep2_extraRow 52 "full_compact_needed" FullM4Compact.fullCompactNeededSpec)
        (fidStep2_m7BaseRow (m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem).compact)
        (fidStep2_m7BaseRow hc1.scaleDeltaM5)
        (fidStep2_m7BaseRow m7FidBase_probeM6_mem (by decide) (by decide) (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h))
        xs m Q _ hs)
  · have hfeq := fidStep2_fn_eq_base hfn 464
      (by t_kernel_rfl : fidStep1Fns[464]? = some
        ⟨"full_search_m6", [i64], [i64], FullM8CoreParity.full_search_m6_body⟩) rfl hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (FullM8CoreParity.full_search_m6_m8_wp fidStep2Env
        (fidStep2_frontRow 23 "full_lucky_late_m7" FullM7Search.m7LuckyLateSpec
          (by rfl) (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h))
        rProp
        (fidStep2_m7BaseRow hc2.analyzeM6 (by decide) (by decide) (by decide) (by decide)
          (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
        (fidStep2_frontRow 5 "full_reduce_m6" FullM6Orch.m6ReduceSpec
          (by rfl) (fun _ _ _ _ h => m6ReduceSpec_monoX h))
        (fidStep2_m7BaseRow hc3.switchModeM7 (by decide) (by decide) (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h))
        (fidStep2_m7BaseRow hc2.restartDue)
        (fidStep2_m7BaseRow hc2.restart)
        (fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reorderM6))
        (fidStep2_m7BaseRow hc2.rephase (by decide) (by decide) (by decide) (by decide)
          (fun _ _ _ _ h => m7RephaseSpec_monoX h))
        (fidStep2_m7BaseRow (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.simplifyM6)
          (by decide) (by decide) (by decide) (by decide)
          (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
        (fidStep2_frontRow 34 "m6_hdr_decide_fid" FullM6Hdr.m6HdrDecideSpec
          (by rfl) (fun _ _ _ _ h => m6HdrDecideSpec_monoX h))
        xs m Q _ hs)
  · have hfeq := fidStep2_fn_eq_repl hfn (r := FullM7HotWatchPush.m7WatchPushFastFn)
      (by simp [fidBcpHotPushRepls, FullM7HotWatchPush.m7HotWatchPushRepl])
      (slotSig_at fidStep2_replSigs_batch 0 16
        (some ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool]))) rfl hnm
    subst hfeq
    exact .of (FullM7HotWatchPush.m7WatchPushFastFn_wp fidStep2Env
      (fidStep2_frontRow 35 "full_watch_push_slow_m6" Full.fullWatchPushSpec))
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidHeapDownFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 1 20 (some ("full_heap_down", [i64, i32], [])))
      rfl hnm
    subst hfeq
    exact .of (full_heap_down_fid_wp fidStep2Env)
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidHeapPopFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 2 22 (some ("full_heap_pop", [i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_heap_pop_fid_wp fidStep2Env
      (fidStep2_frontRow 27 "full_heap_down" Full.fullHeapDownSpec))
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidPropagateIgnoreHotFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 3 83
        (some ("full_propagate_ignore_hot", [i64, i64], [i64]))) rfl hnm
    subst hfeq
    exact .of (full_propagate_ignore_fid_wp fidStep2Env
      (fidStep2_extraRow 2 "full_prop_lit_ovf_hot" FullM7BcpHot.fullPropLitOvfHotSpec)
      (fidStep2_extraRow 3 "full_prop_chrono_hot" FullM7BcpHot.fullPropChronoHotSpec)
      (fidStep2_frontRow 36 "full_prop_flush_del_fid" fidPropFlushDelSpec
        (by rfl) (fun _ _ _ _ h => fidPropFlushDelSpec_monoX h)))
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidPropagateIgnoreFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 4 85 (some ("full_propagate_ignore", [i64, i64], [i64])))
      rfl hnm
    subst hfeq
    exact .of (full_propagate_ignore_fid_wp fidStep2Env
      (fidStep2_extraRow 2 "full_prop_lit_ovf_hot" FullM7BcpHot.fullPropLitOvfHotSpec)
      (fidStep2_extraRow 3 "full_prop_chrono_hot" FullM7BcpHot.fullPropChronoHotSpec)
      (fidStep2_frontRow 36 "full_prop_flush_del_fid" fidPropFlushDelSpec
        (by rfl) (fun _ _ _ _ h => fidPropFlushDelSpec_monoX h)))
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidDeduce1uipM6Fn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 5 139 (some ("full_deduce_1uip_m6", [i64], [i64])))
      rfl hnm
    subst hfeq
    exact .of (full_deduce_1uip_fid_wp fidStep2Env
      (fidStep2_m7BaseRow hBv.1)
      (fidStep2_m7BaseRow hBv.2)
      (fidStep2_m7BaseRow hc2p.clearAna)
      (fidStep2_m7BaseRow hc2p.otfsLarge)
      (fidStep2_m7BaseRow hc2p.otfsBin)
      (fidStep2_m7BaseRow hc2p.otfsSubsume))
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidDeduce1uipM6HdrFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 6 142 (some ("full_deduce_1uip_m6_hdr", [i64], [i64])))
      rfl hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
    exact full_deduce_1uip_hdr_fid_wp fidStep2Env
      (fidStep2_m7BaseRow hBv.1)
      (fidStep2_m7Row_at 114 "full_analyze_rsn_m6_hdr" FullM6Orch.m6AnalyzeRsnHdrSpec)
      (fidStep2_m7BaseRow hc2p.clearAna)
      (fidStep2_m7BaseRow hc2p.otfsLarge)
      (fidStep2_m7BaseRow hc2p.otfsBin)
      (fidStep2_m7BaseRow hc2p.otfsSubsume)
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidNextDecVarFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 7 155 (some ("full_next_dec_var", [i64], [i64])))
      rfl hnm
    subst hfeq
    exact .of (full_next_dec_var_fid_wp fidStep2Env
      (fidStep2_frontRow 28 "full_heap_pop" Full.fullHeapPopSpec))
  · have hfeq := fidStep2_fn_eq_repl hfn (r := fidHdrDecideFn)
      (by simp [fidBcpHotPushRepls, fidBcpRepls])
      (slotSig_at fidStep2_replSigs_batch 8 463 (some ("m6_hdr_decide_fid", [i64], [i64])))
      rfl hnm
    subst hfeq
    exact .of (m6_hdr_decide_fid_fast_wp fidStep2Env
      (fidStep2_m7BaseRow hc3.decideM7 (by decide) (by decide) (by decide) (by decide)
        (fun _ _ _ _ h => FullM7Search.m7DecideSpec_monoX h))
      (fidStep2_m7BaseRow hc1.hdrDrInit (by decide) (by decide) (by decide) (by decide)
        (fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)))
  · have hfeq := fidStep2_fn_eq_before hfn (b := FullM7HotWatchPush.m7WatchPushSlowFn)
      (by simp [fidBcpHotPushBefores, FullM7HotWatchPush.m7HotWatchPushBefore, fidBcpBefores])
      ?_ hnm
    · subst hfeq
      exact .of (FullM7HotWatchPush.m7WatchPushSlowFn_wp fidStep2Env
        (fidStep2_m7BaseRow hc1p.wstackDefragM6))
    · obtain ⟨g0, hg0, hsg0⟩ := fidStep2_slot (slotSig_at fidStep2_replSigs_batch 0 16
        (some ("full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool])))
      exact ⟨"full_watch_push_m6", g0, List.mem_cons_self, hg0, congrArg Prod.fst hsg0⟩
  · have hfeq := fidStep2_fn_eq_before hfn (b := fidPropFlushDelFn)
      (by simp [fidBcpHotPushBefores, FullM7HotWatchPush.m7HotWatchPushBefore, fidBcpBefores])
      ?_ hnm
    · subst hfeq
      exact .of (full_prop_flush_del_fid_wp fidStep2Env rWp)
    · obtain ⟨g0, hg0, hsg0⟩ := fidStep2_slot (slotSig_at fidStep2_replSigs_batch 3 83
        (some ("full_propagate_ignore_hot", [i64, i64], [i64])))
      exact ⟨"full_propagate_ignore_hot", g0,
        (by simp [fidBcpHotPushBefores, FullM7HotWatchPush.m7HotWatchPushBefore, fidBcpBefores]),
        hg0, congrArg Prod.fst hsg0⟩

/-- Closed `471/471` `ModuleOk` for `FullFidelityAssemblyStep2.fidStep2Module` under
`fidStep2Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep2_moduleOk : ModuleOk fidStep2Env fidStep2Module := by
  change ModuleOk (patchEnv fidStep2Bundle) fidStep2Bundle.patchedMod
  refine patchBundle_moduleOk fidStep2Bundle fidStep2Module_names_nodup
    fidStep2Module_replSigs_ok ?_ fidStep2Module_patchCallsOk fidStep2_front_covered
    fidStep2_front_impl fidStep2Bad fidStep2_noCallBad fidStep2_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact fidBcpHotPushRepls_wf fn hr
  · exact fidBcpHotPushBefores_wf fn hb

/-! ## 4. Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

theorem fidStep2Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep2Env f as bs xs m Q X → fidStep2Env f as bs xs m Q X' := by
  refine patchEnv_noExit_of fidStep2Bundle ?_ ?_
  · change (fidStep2RewiredRows ++ fidStep2ReplRows ++ fidStep2BeforeRows).all
      SpecEntry.noExit = true
    decide
  · change (fidStep1ReplRows ++ fidBaseSpecTable).all SpecEntry.noExit = true
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨by decide, fidBaseSpecTable_noExit⟩

private theorem fidStep2_front_noSolveBytes :
    fidStep2Bundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = "kissat_solve_bytes" := beq_iff_eq.mp hbeq
  have hm : "kissat_solve_bytes" ∈ fidStep2FrontNames :=
    fidStep2_frontNames_eq ▸ (hnm ▸ List.mem_map_of_mem he)
  exact absurd hm (by decide)

theorem fidStep2Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep2Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidStep2Bundle fidStep2_front_noSolveBytes
    (fun _ _ _ _ hs => fidStep1Env_solve_bytes_of hs) a m Q X

theorem fidStep2_solveBytes_mem : m6oSolveBytesFn ∈ fidStep2Module.fns :=
  patchBundle_solveBytes_mem fidStep2Bundle fidStep1_solveBytes_mem fun r hr => by
    change r ∈ fidBcpHotPushRepls at hr
    simp only [fidBcpHotPushRepls, FullM7HotWatchPush.m7HotWatchPushRepl, fidBcpRepls,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep2Module` (`471` fns, `XPost := False`). -/
theorem fidStep2_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep2Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep2_moduleOk fidStep2_solveBytes_mem
    (fun _ _ _ _ hs => fidStep2Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep2Module`. -/
theorem fidStep2_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep2Module`. -/
theorem fidStep2_unsat_nv :
    Func.wp fidStep2Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep2_moduleOk fidStep2_solveBytes_mem
    (fun _ _ _ _ hs => fidStep2Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep2_moduleOk`. -/
theorem fidStep2Module_acyclic : fidStep2Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep2_moduleOk

/-- Canonical `KissatUnsatPkg` for Step-2 (`fidStep2Module`, `fidInlPolicy`). -/
def fidStep2UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep2Module fidInlPolicy fidStep2_solveBytes_mem
    fidStep2Env fidStep2_moduleOk fidStep2Env_noExit
    (fun _ _ _ _ hs => fidStep2Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2

end

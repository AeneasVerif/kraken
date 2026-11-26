/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityBcp
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva4
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofProbe0
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullM3CongBva
public import LeanQbe.T.Examples.Kissat.FullM4Compact
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofCompact0
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofCompact1
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofProbe1
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofProbe
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva0
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva3
import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva
import LeanQbe.T.Examples.Kissat.FullM6Hdr
import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
import LeanQbe.T.Examples.Kissat.FullM3Backbone
import LeanQbe.T.Examples.Kissat.FullFastSched
import LeanQbe.T.Examples.Kissat.FullDefSweep
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 9 (`FullFidelityAssemblyStep9Proof`)

Certifies `FullFidelityAssemblyStep9.fidStep9Module` (`504` fns, `0` externs, `0` exits,
`0` `import all`, `0` `@[expose]` on theorems/lemmas) via `PatchModule` +
`FullFidelityAssemblyUtil`:
1. `fidStep9Bundle : PatchBundle` layering `FullFidelityStep9.fidStep9Repls` (`11` repls,
   including the `7 -> 6`-arg signature change on `full_bva_upd_lit_fid`) and
   `FullFidelityStep9.fidStep9Befores` (`+3` inserted helpers) onto `fidStep8Module`
   (`501 -> 504` fns).
2. Closed `504/504` `fidStep9_moduleOk : ModuleOk fidStep9Env fidStep9Module`,
   `fidStep9Env_noExit`, `fidStep9_solve_bytes_sound`, `fidStep9_solve_bytes_host_sound`,
   `fidStep9_unsat_nv` (`XPost := False`, `std3`), `fidStep9Module_acyclic`, and
   `fidStep9UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7MemShrink
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep9
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle`, `length`, `namesNodup`, & Slot Plan (`504/504`) -/

/-- The `11` replacement specification rows matching `FullFidelityStep9.fidStep9Repls`
(`full_bva_upd_lit_fid` uses `6`-arg `step9BvaUpdLitSpec`). -/
def fidStep9ReplRows : List SpecEntry :=
  [ ⟨"full_prop_flush_del_fid", [i64, i64], [.bool],
      FullFidelityBcp.fidPropFlushDelSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64],
      FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool],
      FullFidelityStep7.step7BvaCommitSpec, true⟩
  , ⟨"full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32],
      step9BvaUpdLitSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool],
      FullM4Compact.fullCompactNeededSpec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ ]

/-- The `3` inserted helper specification rows matching `FullFidelityStep9.fidStep9Befores`. -/
def fidStep9BeforeRows : List SpecEntry :=
  [ ⟨"full_fill_u64_m7", [i64, i64, i64], [], FullM7MemShrink.m7FillU64Spec, true⟩
  , ⟨"full_prop_flush_slow_fid", [i64, i64, i64], [.bool], fidPropFlushSlowSpec, true⟩
  , ⟨"full_rebuild_watches_nosort_fid", [i64], [i64],
      Full.fullRebuildWatchesSpec, true⟩ ]

/-- Step-9 `PatchBundle` composing `fidStep8Module` + `FullFidelityStep9` (`504` fns). -/
def fidStep9Bundle : PatchBundle where
  baseMod := fidStep8Module
  baseTable := fidStep8BaseSpecTable
  baseOk := fidStep8Base_moduleOk
  repls := FullFidelityStep9.fidStep9Repls
  replRows := fidStep9ReplRows
  befores := FullFidelityStep9.fidStep9Befores
  beforeRows := fidStep9BeforeRows

/-- Closed `Env` for `fidStep9Module` (`504` fns). -/
def fidStep9Env : Env :=
  patchEnv fidStep9Bundle

theorem fidStep9_externs_empty : fidStep9Module.externs = [] :=
  fidStep8_externs_empty

private def patchStrNames (nm : Sym) : List Sym :=
  if nm == "full_zero_tables1" then ["full_fill_u64_m7", nm]
  else if nm == "full_prop_flush_del_fid" then ["full_prop_flush_slow_fid", nm]
  else if nm == "full_rebuild_watches" then ["full_rebuild_watches_nosort_fid", nm]
  else [nm]

private theorem fidStep9Befores_map_name (f : Fn) :
    (patchInsAt FullFidelityStep9.fidStep9Befores f).map Fn.name ++ [f.name] =
      patchStrNames f.name := by
  unfold patchInsAt FullFidelityStep9.fidStep9Befores patchStrNames
  simp only [List.find?]
  by_cases h1 : f.name = "full_zero_tables1"
  · simp [h1, fidStep9FillU64Fn]
  · have h1a : ("full_zero_tables1" == f.name) = false := beq_false_of_ne (Ne.symm h1)
    have h1b : (f.name == "full_zero_tables1") = false := beq_false_of_ne h1
    by_cases h2 : f.name = "full_prop_flush_del_fid"
    · simp [h2, fidStep9PropFlushSlowFn]
    · have h2a : ("full_prop_flush_del_fid" == f.name) = false := beq_false_of_ne (Ne.symm h2)
      have h2b : (f.name == "full_prop_flush_del_fid") = false := beq_false_of_ne h2
      by_cases h3 : f.name = "full_rebuild_watches"
      · simp [h3, fidStep9RebuildWatchesNosortFn]
      · have h3a : ("full_rebuild_watches" == f.name) = false := beq_false_of_ne (Ne.symm h3)
        have h3b : (f.name == "full_rebuild_watches") = false := beq_false_of_ne h3
        simp [h1a, h1b, h2a, h2b, h3a, h3b]

private theorem mem_patchStrNames {x y : Sym} (hx : x ∈ patchStrNames y) :
    x = y ∨
    (x = "full_fill_u64_m7" ∧ y = "full_zero_tables1") ∨
    (x = "full_prop_flush_slow_fid" ∧ y = "full_prop_flush_del_fid") ∨
    (x = "full_rebuild_watches_nosort_fid" ∧ y = "full_rebuild_watches") := by
  unfold patchStrNames at hx
  split at hx
  · rename_i h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, beq_iff_eq.mp h⟩)
    · exact Or.inl rfl
  · split at hx
    · rename_i _ h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, beq_iff_eq.mp h⟩))
      · exact Or.inl rfl
    · split at hx
      · rename_i _ _ h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, beq_iff_eq.mp h⟩))
        · exact Or.inl rfl
      · simp only [List.mem_singleton] at hx; exact Or.inl hx

private theorem mem_flatMap_patchStrNames {x : Sym} {nms : List Sym}
    (hx : x ∈ nms.flatMap patchStrNames) :
    x ∈ nms ∨
    (x = "full_fill_u64_m7" ∧ "full_zero_tables1" ∈ nms) ∨
    (x = "full_prop_flush_slow_fid" ∧ "full_prop_flush_del_fid" ∈ nms) ∨
    (x = "full_rebuild_watches_nosort_fid" ∧ "full_rebuild_watches" ∈ nms) := by
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  rcases mem_patchStrNames hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hy
  · exact Or.inr (Or.inl ⟨rfl, hy⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, hy⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, hy⟩))

private theorem nodup_patchStrNames (nm : Sym) : (patchStrNames nm).Nodup := by
  unfold patchStrNames
  split
  · rename_i h; rw [beq_iff_eq.mp h]; decide
  · split
    · rename_i _ h; rw [beq_iff_eq.mp h]; decide
    · split
      · rename_i _ _ h; rw [beq_iff_eq.mp h]; decide
      · simp

private theorem nodup_flatMap_patchStrNames :
    ∀ {nms : List Sym}, nms.Nodup →
      "full_fill_u64_m7" ∉ nms → "full_prop_flush_slow_fid" ∉ nms →
      "full_rebuild_watches_nosort_fid" ∉ nms →
      (nms.flatMap patchStrNames).Nodup
  | [], _, _, _, _ => List.nodup_nil
  | nm :: nms, hnd, h1, h2, h3 => by
    have ⟨hnm, hnd'⟩ := List.nodup_cons.mp hnd
    have h1' : "full_fill_u64_m7" ∉ nms := fun hm => h1 (List.mem_cons_of_mem _ hm)
    have h2' : "full_prop_flush_slow_fid" ∉ nms := fun hm => h2 (List.mem_cons_of_mem _ hm)
    have h3' : "full_rebuild_watches_nosort_fid" ∉ nms :=
      fun hm => h3 (List.mem_cons_of_mem _ hm)
    have hhead1 : nm ≠ "full_fill_u64_m7" := fun heq => h1 (heq ▸ List.mem_cons_self)
    have hhead2 : nm ≠ "full_prop_flush_slow_fid" := fun heq => h2 (heq ▸ List.mem_cons_self)
    have hhead3 : nm ≠ "full_rebuild_watches_nosort_fid" :=
      fun heq => h3 (heq ▸ List.mem_cons_self)
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_patchStrNames nm, nodup_flatMap_patchStrNames hnd' h1' h2' h3',
      fun x hx y hy heq => ?_⟩
    subst heq
    rcases mem_patchStrNames hx with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases mem_flatMap_patchStrNames hy with hyn | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hnm hyn
      · exact hhead1 rfl
      · exact hhead2 rfl
      · exact hhead3 rfl
    · rcases mem_flatMap_patchStrNames hy with hyn | ⟨_, hyk⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
      · exact h1' hyn
      · exact hnm hyk
      · exact absurd hf (by decide)
      · exact absurd hf (by decide)
    · rcases mem_flatMap_patchStrNames hy with hyn | ⟨hf, _⟩ | ⟨_, hyk⟩ | ⟨hf, _⟩
      · exact h2' hyn
      · exact absurd hf (by decide)
      · exact hnm hyk
      · exact absurd hf (by decide)
    · rcases mem_flatMap_patchStrNames hy with hyn | ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, hyk⟩
      · exact h3' hyn
      · exact absurd hf (by decide)
      · exact absurd hf (by decide)
      · exact hnm hyk

private theorem patchFns_map_name (repls : List Fn) :
    ∀ (fs : List Fn),
      (patchFns repls FullFidelityStep9.fidStep9Befores fs).map Fn.name =
        (fs.map Fn.name).flatMap patchStrNames
  | [] => rfl
  | f :: fs => by
    have hnm : ((repls.find? (·.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (·.name == f.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)
    have hl : patchFns repls FullFidelityStep9.fidStep9Befores (f :: fs) =
        patchInsAt FullFidelityStep9.fidStep9Befores f ++
          [(repls.find? (·.name == f.name)).getD f] ++
          patchFns repls FullFidelityStep9.fidStep9Befores fs := rfl
    rw [List.map_cons, List.flatMap_cons, hl, List.map_append, List.map_append,
      List.map_singleton, hnm, fidStep9Befores_map_name f, patchFns_map_name repls fs]

private theorem fidStep9_map_name :
    fidStep9Fns.map Fn.name = fidStep7FnNames.flatMap patchStrNames := by
  rw [fidStep9Fns, patchFns_map_name, ← fidStep8Fns_eq, fidStep8Module_map_name]

private theorem fidStep9_len_rfl :
    (fidStep7FnNames.flatMap patchStrNames).length = 504 := by
  t_kernel_rfl

private theorem fidStep9_not_in1 :
    fidStep7FnNames.contains "full_fill_u64_m7" = false := by
  t_kernel_rfl

private theorem fidStep9_not_in2 :
    fidStep7FnNames.contains "full_prop_flush_slow_fid" = false := by
  t_kernel_rfl

private theorem fidStep9_not_in3 :
    fidStep7FnNames.contains "full_rebuild_watches_nosort_fid" = false := by
  t_kernel_rfl

theorem fidStep9Fns_length : fidStep9Fns.length = 504 := by
  rw [← List.length_map Fn.name, fidStep9_map_name]
  exact fidStep9_len_rfl

theorem fidStep9Module_names_nodup : fidStep9Module.namesNodup := by
  have hnd7 : fidStep7FnNames.Nodup := by
    rw [← fidStep7Module_map_name]
    exact module_fns_namesNodup fidStep7Module_names_nodup
  have h1 : "full_fill_u64_m7" ∉ fidStep7FnNames := fun hm => by
    have hc := List.contains_iff_mem.mpr hm
    rw [fidStep9_not_in1] at hc
    cases hc
  have h2 : "full_prop_flush_slow_fid" ∉ fidStep7FnNames := fun hm => by
    have hc := List.contains_iff_mem.mpr hm
    rw [fidStep9_not_in2] at hc
    cases hc
  have h3 : "full_rebuild_watches_nosort_fid" ∉ fidStep7FnNames := fun hm => by
    have hc := List.contains_iff_mem.mpr hm
    rw [fidStep9_not_in3] at hc
    cases hc
  change (fidStep9Module.fns.map Fn.name ++ fidStep9Module.externs.map Extern.name).Nodup
  rw [fidStep9_externs_empty, List.map_nil, List.append_nil, fidStep9Fns_eq, fidStep9_map_name]
  exact nodup_flatMap_patchStrNames hnd7 h1 h2 h3

private def fidStep9FrontNames : List Sym :=
  [ "full_prop_flush_del_fid", "full_arena_sweep_m6", "full_reduce_m6"
  , "full_congruence_dense", "full_rebuild_watches", "full_bva_commit"
  , "full_bva_upd_lit_fid", "full_factor", "full_compact_needed"
  , "full_compact_flush", "full_probe_m6"
  , "full_fill_u64_m7", "full_prop_flush_slow_fid", "full_rebuild_watches_nosort_fid" ]

private theorem fidStep9_frontNames_eq :
    fidStep9Bundle.frontTable.map SpecEntry.name = fidStep9FrontNames :=
  rfl

private theorem fidStep9_front_nodup :
    (fidStep9Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep9_frontNames_eq]
  decide

private theorem fidStep9_before_not_in_step8 :
    (fidStep8Module.fns.map Fn.name).contains "full_fill_u64_m7" = false ∧
    (fidStep8Module.fns.map Fn.name).contains "full_prop_flush_slow_fid" = false ∧
    (fidStep8Module.fns.map Fn.name).contains "full_rebuild_watches_nosort_fid" = false := by
  rw [fidStep8Module_map_name]
  exact ⟨fidStep9_not_in1, fidStep9_not_in2, fidStep9_not_in3⟩

private theorem fidStep9_slot8 {i : Nat} {s : SigEntry}
    (hs : (i, s) ∈ fidStep7_step9_sigPairs) :
    ∃ g ∈ fidStep8Module.fns, fidStep8Module.fns[i]? = some g ∧ g.sig = s := by
  have hi := fidStep8_step9_sig_at hs
  cases h : fidStep8Module.fns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, rfl, hi⟩

theorem fidStep9Module_replSigs_except_updLit :
    ∀ r ∈ FullFidelityStep9.fidStep9Repls, r.name ≠ "full_bva_upd_lit_fid" →
      ∀ g ∈ fidStep8Module.fns, r.name = g.name → r.sig = g.sig := by
  have hnd := module_fns_namesNodup fidStep8Module_names_nodup
  intro r hr hne g hg hnm
  have hslot : ∀ {i : Nat} {s : SigEntry}, (i, s) ∈ fidStep7_step9_sigPairs →
      r.sig = s → r.sig = g.sig := by
    intro i s hs hrs
    obtain ⟨g0, hg0, _, hsg⟩ := fidStep9_slot8 hs
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg.symm)
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans hgnm), hsg, hrs]
  simp only [FullFidelityStep9.fidStep9Repls, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hslot (i := 84) (s := ("full_prop_flush_del_fid", [i64, i64], [.bool]))
      (by decide) rfl
  · exact hslot (i := 104) (s := ("full_arena_sweep_m6", [i64], [i64]))
      (by decide) rfl
  · exact hslot (i := 113) (s := ("full_reduce_m6", [i64, .bool], [i64]))
      (by decide) rfl
  · exact hslot (i := 288) (s := ("full_congruence_dense", [i64, i64], [i64]))
      (by decide) rfl
  · exact hslot (i := 247) (s := ("full_rebuild_watches", [i64], [i64]))
      (by decide) rfl
  · exact hslot (i := 436) (s := ("full_bva_commit", [i64, i32], [.bool]))
      (by decide) rfl
  · exact absurd rfl hne
  · exact hslot (i := 441) (s := ("full_factor", [i64, i64], [i64]))
      (by decide) rfl
  · exact hslot (i := 442) (s := ("full_compact_needed", [i64], [.bool]))
      (by decide) rfl
  · exact hslot (i := 443) (s := ("full_compact_flush", [i64], [i64]))
      (by decide) rfl
  · exact hslot (i := 492) (s := ("full_probe_m6", [i64, .bool], [i64]))
      (by decide) rfl

/-! ## 2. Single-Function `checkCallsOk` Checks & Signature Preservation Helpers -/

private theorem fillU64_callsOk :
    fidStep9FillU64Fn.checkCallsOk [] [] = true := by t_kernel_rfl

private theorem propFlushSlow_callsOk :
    fidStep9PropFlushSlowFn.checkCallsOk
      [("full_watch_push", [i64, i32, i32, i32, i32], [.bool])] [] = true := by
  t_kernel_rfl

private theorem propFlushDel_callsOk :
    fidStep9PropFlushDelFn.checkCallsOk
      [("full_prop_flush_slow_fid", [i64, i64, i64], [.bool])] [] = true := by
  t_kernel_rfl

private theorem arenaSweepM6_callsOk :
    fidStep9ArenaSweepM6Fn.checkCallsOk
      [ ("full_sweep_bins_range_m6", [i64, i64], [])
      , ("full_rewatch_range_m6", [i64, i64, i64], [.bool])
      , ("full_arena_next", [i64, i32], [i32])
      , ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64])
      , ("full_move_red_end_m6", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem reduceM6_callsOk :
    fidStep9ReduceM6Fn.checkCallsOk
      [ ("full_isqrt", [i64], [i64])
      , ("full_log10_q16_m7", [i64], [i64])
      , ("full_arena_next", [i64, i32], [i32])
      , ("m6_hdr_recompute_tiers", [i64], [])
      , ("m6_hdr_set_watermark", [i64, i64, i64], [])
      , ("full_mark_reasons", [i64, .bool], [])
      , ("full_sort_reds", [i64, i64], [])
      , ("full_backtrack", [i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem congruenceDense_callsOk :
    fidStep9CongruenceDenseFn.checkCallsOk
      [ ("full_cong_extract_binaries", [i64, i64], [i64])
      , ("full_cong_find_units_equivs", [i64], [i64])
      , ("full_cong_extract", [i64, i64, i64], [i64])
      , ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32])
      , ("full_cong_worklist", [i64, i64, i64, i64], [i64])
      , ("full_cong_fwd_subsume", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem rebuildWatchesNosort_callsOk :
    fidStep9RebuildWatchesNosortFn.checkCallsOk
      [ ("full_arena_sweep", [i64], [i64])
      , ("full_propagate", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem rebuildWatches_callsOk :
    fidStep9RebuildWatchesFn.checkCallsOk
      [ ("full_rebuild_watches_nosort_fid", [i64], [i64])
      , ("full_sort_bin_watches_fid", [i64], []) ] [] = true := by
  t_kernel_rfl

private theorem bvaCommit_callsOk :
    fidStep9BvaCommitFn.checkCallsOk
      [ ("full_bva_steps_cap_fid", [i64], [i32])
      , ("full_fill_u64_m7", [i64, i64, i64], [])
      , ("full_wstack_defrag", [i64], [])
      , ("full_init_fresh_var", [i64, i32], [])
      , ("full_add_bin", [i64, i32, i32], [i64])
      , ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_delete_binary", [i64, i32, i32], [])
      , ("full_unwatch_large", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

private theorem bvaUpdLit_callsOk :
    fidStep9BvaUpdLitFn.checkCallsOk
      [ ("full_bva_count_lit_deg_fid", [i64, i32], [i32])
      , ("full_fheap_up_fid", [i64, i64, i64, i32], [])
      , ("full_fheap_down_fid", [i64, i64, i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

private theorem factor_callsOk :
    fidStep9FactorFn.checkCallsOk
      [ ("full_bva_steps_cap_fid", [i64], [i32])
      , ("full_bva_connect_clauses_fid", [i64], [])
      , ("full_fheap_up_fid", [i64, i64, i64, i32], [])
      , ("full_fheap_down_fid", [i64, i64, i64, i32, i32], [])
      , ("full_bva_try_lit", [i64, i32, i64], [.bool])
      , ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i64, i64], [i32]) ] [] = true := by
  t_kernel_rfl

private theorem compactNeeded_callsOk :
    fidStep9CompactNeededFn.checkCallsOk [] [] = true := by t_kernel_rfl

private theorem compactFlush_callsOk :
    fidStep9CompactFlushFn.checkCallsOk
      [("full_flush_trail", [i64], [i64])] [] = true := by
  t_kernel_rfl

private theorem probeM6_callsOk :
    fidStep9ProbeM6Fn.checkCallsOk
      [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
      , ("full_log10_q16_m7", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64])
      , ("full_vivify_m6_hdr", [i64], [i64])
      , ("full_enter_dense", [i64], [.bool])
      , ("m6_hdr_delaying", [i64, i64], [.bool])
      , ("full_congruence_dense", [i64, i64], [i64])
      , ("full_rebuild_watches_nosort_fid", [i64], [i64])
      , ("m6_hdr_get_watermark", [i64, i64], [i64])
      , ("m6_hdr_set_watermark", [i64, i64, i64], [])
      , ("m6_hdr_reduce_delay", [i64, i64], [])
      , ("m6_hdr_bump_delay", [i64, i64], [])
      , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
      , ("full_substitute", [i64], [i64])
      , ("full_backbone_m6", [i64, i64], [i64])
      , ("full_transitive_m6", [i64, i64], [i64])
      , ("full_factor", [i64, i64], [i64])
      , ("full_sort_bin_watches_fid", [i64], []) ] [] = true := by
  t_kernel_rfl

private theorem fidStep9_front_none_of_names {nm : Sym}
    (hf9 : !(fidStep9FrontNames.contains nm) = true) :
    fidStep9Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : nm ∈ fidStep9FrontNames :=
    fidStep9_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
  simp [hm] at hf9

private theorem fid9_of_step8 {f : Sym} {as bs : List Ty}
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep8Env f as bs xs m Q X) :
    fidStep9Env f as bs xs m Q X := by
  change patchEnv fidStep9Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep9Bundle (fidStep9_front_none_of_names hf9)]
  dsimp only [fidStep9Bundle]
  rwa [fidStep8Base_eq_env]

private theorem fid9_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep9Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidStep9Env nm as bs a m Q X := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep9Bundle fidStep9_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

/-! ## 3. Patch-Split Infrastructure & `fidStep9_agree` -/

private theorem drop_eq_cons_9 {α : Type _} {xs : List α} {i : Nat} {x : α}
    (hx : xs[i]? = some x) : xs.drop i = x :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    cases i with
    | zero => simp at hx; simp [hx]
    | succ i => simp at hx ⊢; exact ih hx

private theorem split_append_cons_9 {α : Type _} {xs : List α} {x y : α} {zs pre post : List α}
    (h : xs ++ y :: zs = pre ++ x :: post) :
    (∃ iPre iPost, xs = iPre ++ x :: iPost ∧ pre = iPre) ∨
    (x = y ∧ pre = xs) ∨
    (∃ tPre, zs = tPre ++ x :: post ∧ pre = xs ++ y :: tPre) := by
  by_cases hlt : pre.length < xs.length
  · have hpre_eq : pre = xs.take pre.length := by
      have ht := congrArg (List.take pre.length) h
      simpa [List.take_left', List.take_append_of_le_length (Nat.le_of_lt hlt)] using ht.symm
    have hget : xs[pre.length]? = some x := by
      have hg := congrArg (·[pre.length]?) h
      simpa [List.getElem?_append_left hlt] using hg
    have hx_split : xs = xs.take pre.length ++ x :: xs.drop (pre.length + 1) := by
      have hd := List.take_append_drop pre.length xs
      have hdrop : xs.drop pre.length = x :: xs.drop (pre.length + 1) := drop_eq_cons_9 hget
      simpa [hdrop] using hd.symm
    exact Or.inl ⟨xs.take pre.length, xs.drop (pre.length + 1), hx_split, hpre_eq⟩
  · have hge : xs.length ≤ pre.length := Nat.not_lt.mp hlt
    by_cases heq : pre.length = xs.length
    · have hpre_eq : pre = xs := by
        have ht := congrArg (List.take pre.length) h
        simpa [List.take_left', heq] using ht.symm
      have hget : x = y := by
        have hg := congrArg (·[xs.length]?) h
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero] at hg
        have hg2 : (pre ++ x :: post)[pre.length]? = some x := by simp
        rw [← heq, hg2] at hg
        exact (Option.some.inj hg).symm
      exact Or.inr (Or.inl ⟨hget, hpre_eq⟩)
    · have hgt : xs.length < pre.length := by omega
      have htake_pre : pre.take (xs.length + 1) = xs ++ [y] := by
        have ht := congrArg (List.take (xs.length + 1)) h
        have hL : (xs ++ y :: zs).take (xs.length + 1) = xs ++ [y] := by
          have : xs ++ y :: zs = (xs ++ [y]) ++ zs := by simp [List.append_assoc]
          rw [this, List.take_left' (by simp)]
        have hR : (pre ++ x :: post).take (xs.length + 1) = pre.take (xs.length + 1) := by
          rw [List.take_append_of_le_length hgt]
        exact hR.symm.trans (ht.symm.trans hL)
      have hpre_eq : pre = xs ++ y :: pre.drop (xs.length + 1) := by
        have hd := List.take_append_drop (xs.length + 1) pre
        rw [htake_pre, List.append_assoc, List.singleton_append] at hd
        exact hd.symm
      rw [hpre_eq, List.append_assoc, List.cons_append] at h
      have h1 := List.append_cancel_left h
      have h2 := (List.cons.inj h1).2
      exact Or.inr (Or.inr ⟨pre.drop (xs.length + 1), h2, hpre_eq⟩)

private theorem patchFns_split_9 {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs pre post : List Fn} {fn : Fn}
    (hsplit : patchFns repls befores fs = pre ++ fn :: post) :
    ∃ bPre f0 bPost, fs = bPre ++ f0 :: bPost ∧
      ((∃ iPre iPost, patchInsAt befores f0 = iPre ++ fn :: iPost ∧
          ∀ s, s ∈ (patchFns repls befores bPre ++ iPre).map Fn.sig → s ∈ pre.map Fn.sig) ∨
       (fn = (repls.find? (·.name == f0.name)).getD f0 ∧
          ∀ s, s ∈ (patchFns repls befores bPre ++ patchInsAt befores f0).map Fn.sig →
            s ∈ pre.map Fn.sig)) := by
  induction fs generalizing pre with
  | nil => simp [patchFns] at hsplit
  | cons f fs ih =>
    have hcons : patchFns repls befores (f :: fs) =
        patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f] ++
          patchFns repls befores fs := by
      simp [patchFns]
    rw [hcons, List.append_assoc, List.singleton_append] at hsplit
    rcases split_append_cons_9 hsplit with
      ⟨iPre, iPost, hi, hpreEq⟩ | ⟨hr, rfl⟩ | ⟨preRest, htail, rfl⟩
    · subst hpreEq
      refine ⟨[], f, fs, rfl, Or.inl ⟨pre, iPost, hi, fun s hs => ?_⟩⟩
      simpa [patchFns] using hs
    · refine ⟨[], f, fs, rfl, Or.inr ⟨hr, fun s hs => ?_⟩⟩
      simpa [patchFns] using hs
    · obtain ⟨bPre', f0, bPost, hfs_eq, hcase⟩ := ih htail
      refine ⟨f :: bPre', f0, bPost, by rw [hfs_eq, List.cons_append], ?_⟩
      have hcons' : patchFns repls befores (f :: bPre') =
          patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f] ++
            patchFns repls befores bPre' := by
        simp [patchFns]
      rcases hcase with ⟨iPre, iPost, hi, hpreM⟩ | ⟨hr', hpreM⟩
      · refine Or.inl ⟨iPre, iPost, hi, fun s hs => ?_⟩
        rw [List.map_append, List.mem_append, hcons'] at hs
        rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        rcases hs with hA | h3
        · simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton] at hA
          rcases hA with (h1 | hcur) | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inl hcur)
          · exact Or.inr (Or.inr (hpreM s (by
              rw [List.map_append, List.mem_append]; exact Or.inl h2)))
        · exact Or.inr (Or.inr (hpreM s (by
            rw [List.map_append, List.mem_append]; exact Or.inr h3)))
      · refine Or.inr ⟨hr', fun s hs => ?_⟩
        rw [List.map_append, List.mem_append, hcons'] at hs
        rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        rcases hs with hA | h3
        · simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton] at hA
          rcases hA with (h1 | hcur) | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inl hcur)
          · exact Or.inr (Or.inr (hpreM s (by
              rw [List.map_append, List.mem_append]; exact Or.inl h2)))
        · exact Or.inr (Or.inr (hpreM s (by
            rw [List.map_append, List.mem_append]; exact Or.inr h3)))

private theorem patchFns_sig_except_updLit {bPre : List Fn}
    (hsub : ∀ f ∈ bPre, f ∈ fidStep8Module.fns) {f : Fn} (hf : f ∈ bPre)
    (hne : f.name ≠ "full_bva_upd_lit_fid") :
    f.sig ∈ (patchFns FullFidelityStep9.fidStep9Repls
      FullFidelityStep9.fidStep9Befores bPre).map Fn.sig := by
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem hf
  have hmem : (FullFidelityStep9.fidStep9Repls.find? (·.name == f.name)).getD f ∈
      patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores bPre := by
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨f, hf, Or.inr rfl⟩
  have hsig : ((FullFidelityStep9.fidStep9Repls.find? (·.name == f.name)).getD f).sig =
      f.sig := by
    cases hr : FullFidelityStep9.fidStep9Repls.find? (·.name == f.name) with
    | none => rfl
    | some r =>
      have hr_mem := List.mem_of_find?_eq_some hr
      have hrnm : r.name = f.name :=
        beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hr)
      exact fidStep9Module_replSigs_except_updLit r hr_mem (hrnm ▸ hne) f (hsub f hf) hrnm
  exact hsig ▸ List.mem_map_of_mem hmem

private theorem patchFns_before_in_bPre {bPre : List Fn}
    {anc ins : Fn} (ha : anc ∈ bPre) (hi : ins ∈ patchInsAt FullFidelityStep9.fidStep9Befores anc) :
    ins.sig ∈ (patchFns FullFidelityStep9.fidStep9Repls
      FullFidelityStep9.fidStep9Befores bPre).map Fn.sig := by
  have hmem : ins ∈ patchFns FullFidelityStep9.fidStep9Repls
      FullFidelityStep9.fidStep9Befores bPre := by
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨anc, ha, Or.inl hi⟩
  exact List.mem_map_of_mem hmem

private theorem nodup_list_getElem?_inj {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : xs[j]? = some a) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    have ⟨hnmem, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj
        subst hi
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨j, hj⟩))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj
        subst hj
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      | succ j =>
        simp at hi hj
        exact congrArg Nat.succ (ih hnd' hi hj)

private theorem fidStep9_slot_eq_len {bPre bPost : List Fn} {f0 : Fn} {slot : Nat} {sf0 : SigEntry}
    (hfs : fidStep8Module.fns = bPre ++ f0 :: bPost)
    (hs : (slot, sf0) ∈ fidStep7_step9_sigPairs) (hf0 : f0.name = sf0.1) :
    bPre.length = slot := by
  obtain ⟨g0, _, hg0, hsg0⟩ := fidStep9_slot8 hs
  have h1 : (fidStep8Module.fns.map Fn.name)[bPre.length]? = some sf0.1 := by
    rw [hfs]; simp [hf0]
  have h2 : (fidStep8Module.fns.map Fn.name)[slot]? = some sf0.1 := by
    simp [List.getElem?_map, hg0, ← hsg0, Fn.sig]
  exact nodup_list_getElem?_inj (module_fns_namesNodup fidStep8Module_names_nodup) h1 h2

private theorem fidStep9_base_sig_in_patch {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep8Module.fns = bPre ++ f0 :: bPost)
    {i : Nat} {s : SigEntry} (hs : (i, s) ∈ fidStep7_step9_sigPairs)
    (hne : s.1 ≠ "full_bva_upd_lit_fid") (hlt : i < bPre.length) :
    s ∈ (patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores bPre).map
      Fn.sig := by
  obtain ⟨g, _, hgi, hsg⟩ := fidStep9_slot8 hs
  have hgb : bPre[i]? = some g := by
    rwa [hfs, List.getElem?_append_left hlt] at hgi
  have hgmem : g ∈ bPre := List.mem_of_getElem? hgb
  have hsub : ∀ f ∈ bPre, f ∈ fidStep8Module.fns := fun f hf => hfs ▸ List.mem_append_left _ hf
  have hgnm : g.name ≠ "full_bva_upd_lit_fid" := by
    intro heq; apply hne; rw [← hsg, Fn.sig]; exact heq
  exact hsg ▸ patchFns_sig_except_updLit hsub hgmem hgnm

private theorem fidStep9_before_sig_in_patch {bPre bPost : List Fn} {f0 ins : Fn}
    (hfs : fidStep8Module.fns = bPre ++ f0 :: bPost)
    {slot : Nat} {sa : SigEntry} (hs : (slot, sa) ∈ fidStep7_step9_sigPairs)
    (hlt : slot < bPre.length)
    (hi : ∀ anc : Fn, anc.name = sa.1 →
      ins ∈ patchInsAt FullFidelityStep9.fidStep9Befores anc) :
    ins.sig ∈ (patchFns FullFidelityStep9.fidStep9Repls
      FullFidelityStep9.fidStep9Befores bPre).map Fn.sig := by
  obtain ⟨g, _, hgi, hsg⟩ := fidStep9_slot8 hs
  have hgb : bPre[slot]? = some g := by
    rwa [hfs, List.getElem?_append_left hlt] at hgi
  exact patchFns_before_in_bPre (List.mem_of_getElem? hgb)
    (hi g (congrArg Prod.fst hsg))

private theorem fidStep9_updLit_sig_in_patch {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep8Module.fns = bPre ++ f0 :: bPost) (hlt : 440 < bPre.length) :
    fidStep9BvaUpdLitFn.sig ∈ (patchFns FullFidelityStep9.fidStep9Repls
      FullFidelityStep9.fidStep9Befores bPre).map Fn.sig := by
  obtain ⟨g, _, hgi, hsg⟩ := fidStep9_slot8
    (i := 440) (s := ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32]))
    (by decide)
  have hgb : bPre[440]? = some g := by
    rwa [hfs, List.getElem?_append_left hlt] at hgi
  have hgmem : g ∈ bPre := List.mem_of_getElem? hgb
  have hgnm : g.name = "full_bva_upd_lit_fid" := congrArg Prod.fst hsg
  have hfind : FullFidelityStep9.fidStep9Repls.find? (·.name == g.name) =
      some fidStep9BvaUpdLitFn := by
    rw [hgnm]; rfl
  have hmem : fidStep9BvaUpdLitFn ∈ patchFns FullFidelityStep9.fidStep9Repls
      FullFidelityStep9.fidStep9Befores bPre := by
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨g, hgmem, Or.inr (by simp [hfind])⟩
  exact List.mem_map_of_mem hmem

private theorem fidStep9_agree :
    ∀ s ∈ fidStep8Module.sigs, s.1 ≠ "full_bva_upd_lit_fid" →
      ∀ xs m P E, Env.ofTable fidStep8BaseSpecTable s.1 s.2.1 s.2.2 xs m P E →
        fidStep9Env s.1 s.2.1 s.2.2 xs m P E := by
  rintro ⟨nm, as, bs⟩ hs hne xs m P E hBase
  rw [fidStep8Base_eq_env] at hBase
  cases hf : fidStep9Bundle.frontTable.find? (·.name == nm) with
  | none =>
    change patchEnv fidStep9Bundle nm as bs xs m P E
    rw [patchEnv_base_eq fidStep9Bundle hf]
    dsimp only [fidStep9Bundle]
    rwa [fidStep8Base_eq_env]
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    have hsig_in : e.name ∈ (fidStep8Module.fns.map Fn.name) := by
      have hm := hs
      rw [LeanQbe.T.Module.sigs, fidStep8_externs_empty, List.map_nil, List.append_nil] at hm
      obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hm
      exact hnm ▸ List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
    by_cases hsig : e.as = as ∧ e.rs = bs
    · obtain ⟨has, hrs⟩ := hsig
      subst hnm; subst has; subst hrs
      have hPush : ∀ (hmem : e ∈ fidStep9Bundle.frontTable), e.eff xs m P E →
          fidStep9Env e.name e.as e.rs xs m P E := fun hmem hs' =>
        patchEnv_of_front_mem fidStep9Bundle fidStep9_front_nodup hmem hs'
      have he0 := he
      simp only [fidStep9Bundle, PatchBundle.frontTable, fidStep9ReplRows, fidStep9BeforeRows,
        List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        dsimp only [SpecEntry.eff, SpecEntry.name, SpecEntry.as, SpecEntry.rs, ite_true] at hBase ⊢
      · exact hPush he0 (FullFidelityBcp.fidPropFlushDelSpec_monoX
          (X' := fun _ _ _ _ => False) (fidStep8Env_elim_propFlushDel hBase))
      · exact hPush he0 (fidStep8Env_elim_arenaSweepM6 hBase)
      · exact hPush he0 (m6ReduceSpec_monoX
          (X' := fun _ _ _ _ => False) (fidStep8Env_elim_reduceM6 hBase))
      · exact hPush he0 (fidStep8Env_elim_congruenceDense hBase)
      · exact hPush he0 (fidStep8Env_elim_rebuildWatches hBase)
      · exact hPush he0 (FullFidelityStep7.step7BvaCommitSpec_monoX
          (X' := fun _ _ _ _ => False) (fidStep8Env_elim_bvaCommit hBase))
      · exact absurd rfl hne
      · exact hPush he0 (fidStep8Env_elim_factor hBase)
      · exact hPush he0 (fidStep8Env_elim_compactNeeded hBase)
      · exact hPush he0 (fidStep8Env_elim_compactFlush hBase)
      · exact hPush he0 (m6ProbeSpec_monoX
          (X' := fun _ _ _ _ => False) (fidStep8Env_elim_probeM6 hBase))
      · have hno := fidStep9_before_not_in_step8.1
        have hm : (fidStep8Module.fns.map Fn.name).contains "full_fill_u64_m7" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno := fidStep9_before_not_in_step8.2.1
        have hm : (fidStep8Module.fns.map Fn.name).contains "full_prop_flush_slow_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
      · have hno := fidStep9_before_not_in_step8.2.2
        have hm : (fidStep8Module.fns.map Fn.name).contains
            "full_rebuild_watches_nosort_fid" = true :=
          List.contains_iff_mem.mpr hsig_in
        rw [hno] at hm; cases hm
    · have hneq : ∀ e' ∈ fidStep9Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep9_front_nodup he' he
          (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep9Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil =>
          dsimp only [fidStep9Bundle]
          rwa [List.nil_append, fidStep8Base_eq_env]
        | cons x xs ih =>
          rw [List.cons_append]
          exact Or.inr ⟨hpfx x List.mem_cons_self,
            ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)⟩
      exact hLift fidStep9Bundle.frontTable hneq

/-! ## 4. Closed `504/504` `fidStep9_moduleOk` & Soundness Packaging -/

private theorem fidStep9_fn_eq_before {fn b : Fn} {tgt : Sym} {ins : List Fn}
    (hfn : fn ∈ fidStep9Module.fns)
    (hpair : (tgt, ins) ∈ FullFidelityStep9.fidStep9Befores)
    (hb : b ∈ ins) {slot : Nat} {stgt : SigEntry}
    (hs : (slot, stgt) ∈ fidStep7_step9_sigPairs) (htn : tgt = stgt.1)
    (hnm : b.name = fn.name) : fn = b := by
  have hModNd := module_fns_namesNodup fidStep9Module_names_nodup
  obtain ⟨g0, hg0, _, hsg⟩ := fidStep9_slot8 hs
  have hgn : g0.name = tgt := (congrArg Prod.fst hsg).trans htn.symm
  have hbm : b ∈ fidStep9Module.fns := by
    change b ∈ patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
      fidStep8Module.fns
    simp only [patchFns, List.mem_flatMap, List.mem_append]
    refine ⟨g0, hg0, Or.inl ?_⟩
    unfold patchInsAt
    simp only [FullFidelityStep9.fidStep9Befores, List.mem_cons, List.not_mem_nil,
      or_false] at hpair ⊢
    rcases hpair with h0 | h1 | h2
    · obtain ⟨ht, hi⟩ := Prod.mk.inj h0
      subst ht; subst hi; simp only [hgn]; exact hb
    · obtain ⟨ht, hi⟩ := Prod.mk.inj h1
      subst ht; subst hi; simp only [hgn]; exact hb
    · obtain ⟨ht, hi⟩ := Prod.mk.inj h2
      subst ht; subst hi; simp only [hgn]; exact hb
  exact nodup_name_eq Fn.name hModNd hfn hbm hnm.symm

private theorem fidStep9_callsOk_of {fn : Fn} {deps pre : List SigEntry}
    (hchk : fn.checkCallsOk deps [] = true)
    (hsub : ∀ d ∈ deps, d ∈ pre) :
    fn.callsOk (pre ++ fidStep9Module.externs.map Extern.sig) fidStep9Module.exits := by
  rw [fidStep9_noExit, fidStep9_externs_empty, List.map_nil, List.append_nil]
  exact fn_callsOk_mono hsub (Fn.callsOk_of_checkCallsOk hchk)

private theorem patchInsAt_fidStep9_cases {f0 fn : Fn} {iPre iPost : List Fn}
    (hi : patchInsAt FullFidelityStep9.fidStep9Befores f0 = iPre ++ fn :: iPost) :
    (f0.name = "full_zero_tables1" ∧ fn = fidStep9FillU64Fn) ∨
    (f0.name = "full_prop_flush_del_fid" ∧ fn = fidStep9PropFlushSlowFn) ∨
    (f0.name = "full_rebuild_watches" ∧ fn = fidStep9RebuildWatchesNosortFn) := by
  unfold patchInsAt FullFidelityStep9.fidStep9Befores at hi
  simp only [List.find?] at hi
  by_cases h1 : ("full_zero_tables1" == f0.name) = true
  · simp only [h1] at hi
    cases iPre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hi
      exact Or.inl ⟨(beq_iff_eq.mp h1).symm, hi.1.symm⟩
    | cons _ tl => simp at hi
  · simp only [h1] at hi
    by_cases h2 : ("full_prop_flush_del_fid" == f0.name) = true
    · simp only [h2] at hi
      cases iPre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hi
        exact Or.inr (Or.inl ⟨(beq_iff_eq.mp h2).symm, hi.1.symm⟩)
      | cons _ tl => simp at hi
    · simp only [h2] at hi
      by_cases h3 : ("full_rebuild_watches" == f0.name) = true
      · simp only [h3] at hi
        cases iPre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hi
          exact Or.inr (Or.inr ⟨(beq_iff_eq.mp h3).symm, hi.1.symm⟩)
        | cons _ tl => simp at hi
      · simp only [h3] at hi; cases iPre <;> simp at hi

private theorem fidStep9_repl_find?_none_ne {nm : Sym}
    (hnone : FullFidelityStep9.fidStep9Repls.find? (·.name == nm) = none)
    {r : Fn} (hr : r ∈ FullFidelityStep9.fidStep9Repls) : nm ≠ r.name := by
  intro heq
  have h := List.find?_eq_none.mp hnone r hr
  simp [heq] at h

private theorem fidStep9_front_none_of_repl_none {nm : Sym}
    (hnone : FullFidelityStep9.fidStep9Repls.find? (·.name == nm) = none)
    (hnb1 : nm ≠ "full_fill_u64_m7") (hnb2 : nm ≠ "full_prop_flush_slow_fid")
    (hnb3 : nm ≠ "full_rebuild_watches_nosort_fid") :
    fidStep9Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = nm := beq_iff_eq.mp hbeq
  simp only [fidStep9Bundle, PatchBundle.frontTable, fidStep9ReplRows, fidStep9BeforeRows,
    List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 0) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 1) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 2) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 3) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 4) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 5) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 6) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 7) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 8) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 9) rfl) hnm.symm
  · exact fidStep9_repl_find?_none_ne hnone (List.mem_of_getElem? (i := 10) rfl) hnm.symm
  · exact hnb1 hnm.symm
  · exact hnb2 hnm.symm
  · exact hnb3 hnm.symm

/-- Closed `504/504` `ModuleOk` for `FullFidelityAssemblyStep9.fidStep9Module` under
`fidStep9Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep9_moduleOk : ModuleOk fidStep9Env fidStep9Module := by
  refine ⟨fidStep9Module_names_nodup, fun pre fn post hsplit => ?_⟩
  change patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
    fidStep8Module.fns = pre ++ fn :: post at hsplit
  obtain ⟨bPre, f0, bPost, hfs, hcase⟩ := patchFns_split_9 hsplit
  have hf0_ok := fidStep8Base_moduleOk.fnsOk bPre f0 bPost hfs
  have hsub8 : ∀ f ∈ bPre, f ∈ fidStep8Module.fns :=
    fun f hf => hfs ▸ List.mem_append_left _ hf
  have hliftBase : ∀ {i : Nat} {s : SigEntry}, (i, s) ∈ fidStep7_step9_sigPairs →
      s.1 ≠ "full_bva_upd_lit_fid" → i < bPre.length →
      s ∈ (patchFns FullFidelityStep9.fidStep9Repls
        FullFidelityStep9.fidStep9Befores bPre).map Fn.sig := fun hs hne hlt =>
    fidStep9_base_sig_in_patch hfs hs hne hlt
  rcases hcase with ⟨iPre, iPost, hi, hpreM⟩ | ⟨hfn_eq, hpreM⟩
  · have hprePatch : ∀ s, s ∈ (patchFns FullFidelityStep9.fidStep9Repls
        FullFidelityStep9.fidStep9Befores bPre).map Fn.sig → s ∈ pre.map Fn.sig := fun s hs =>
      hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inl hs)
    rcases patchInsAt_fidStep9_cases hi with
      ⟨hf0_nm, rfl⟩ | ⟨hf0_nm, rfl⟩ | ⟨hf0_nm, rfl⟩
    · refine ⟨full_fill_u64_m7_step9_wf,
        fidStep9_callsOk_of fillU64_callsOk (fun _ hd => nomatch hd), fun xs m Q X hlk => ?_⟩
      have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9FillU64Fn.name) =
          some fidStep9BeforeRows[0] := rfl
      exact (SpecEntry.Impl.of (full_fill_u64_m7_step9_wp fidStep9Env)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · have hlen84 : bPre.length = 84 :=
        fidStep9_slot_eq_len hfs (slot := 84)
          (sf0 := ("full_prop_flush_del_fid", [i64, i64], [.bool])) (by decide) hf0_nm
      refine ⟨full_prop_flush_slow_step9_wf, fidStep9_callsOk_of propFlushSlow_callsOk ?_,
        fun xs m Q X hlk => ?_⟩
      · intro d hd
        simp only [List.mem_singleton] at hd; subst hd
        exact hprePatch _ (hliftBase (i := 19) (by decide) (by decide) (by omega))
      · have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9PropFlushSlowFn.name) =
            some fidStep9BeforeRows[1] := rfl
        exact (SpecEntry.Impl.of (full_prop_flush_slow_fid_step9_wp fidStep9Env
          (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_watchPush _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · have hlen247 : bPre.length = 247 :=
        fidStep9_slot_eq_len hfs (slot := 247)
          (sf0 := ("full_rebuild_watches", [i64], [i64])) (by decide) hf0_nm
      refine ⟨full_rebuild_watches_nosort_step9_wf,
        fidStep9_callsOk_of rebuildWatchesNosort_callsOk ?_, fun xs m Q X hlk => ?_⟩
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact hprePatch _ (hliftBase (i := 106) (by decide) (by decide) (by omega))
        · exact hprePatch _ (hliftBase (i := 88) (by decide) (by decide) (by omega))
      · have hfind : fidStep9Bundle.frontTable.find?
            (·.name == fidStep9RebuildWatchesNosortFn.name) = some fidStep9BeforeRows[2] := rfl
        exact (SpecEntry.Impl.of (full_rebuild_watches_nosort_fid_step9_wp fidStep9Env
          (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_arenaSweep _ _ _ _ hs))
          (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_propagate _ _ _ _ hs)))).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · have hprePatch : ∀ s, s ∈ (patchFns FullFidelityStep9.fidStep9Repls
        FullFidelityStep9.fidStep9Befores bPre).map Fn.sig → s ∈ pre.map Fn.sig := fun s hs =>
      hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inl hs)
    have hpreIns : ∀ s, s ∈ (patchInsAt FullFidelityStep9.fidStep9Befores f0).map Fn.sig →
        s ∈ pre.map Fn.sig := fun s hs =>
      hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inr hs)
    cases hrepl : FullFidelityStep9.fidStep9Repls.find? (·.name == f0.name) with
    | none =>
      simp only [hrepl, Option.getD_none] at hfn_eq
      subst hfn_eq
      have hf0_mem : fn ∈ fidStep8Module.fns := hfs ▸ by simp
      have hne_fac : fn.name ≠ "full_factor" :=
        fidStep9_repl_find?_none_ne hrepl (List.mem_of_getElem? (i := 7) rfl)
      have hno := fidStep8_noCallBvaUpdLit_ok fn hf0_mem hne_fac
      have hcalls8 : fn.callsOk (bPre.map Fn.sig) [] := by
        simpa only [fidStep8_noExit, fidStep8_externs_empty, List.map_nil, List.append_nil] using
          hf0_ok.2.1
      have hcalls_filt := expr_callsOk_filter_noCallIn _ hcalls8 hno
      have hcalls9 : fn.callsOk (pre.map Fn.sig) [] := by
        refine fn_callsOk_mono (fun s hs => ?_) hcalls_filt
        obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hs1
        have hgne : g.name ≠ "full_bva_upd_lit_fid" := by
          intro heq; simp [Fn.sig, heq] at hs2
        exact hprePatch _ (patchFns_sig_except_updLit hsub8 hg hgne)
      have hnb1 : fn.name ≠ "full_fill_u64_m7" := fun heq => by
        have h1 := fidStep9_before_not_in_step8.1
        have hm := List.contains_iff_mem.mpr (List.mem_map.mpr ⟨fn, hf0_mem, heq⟩)
        rw [h1] at hm; cases hm
      have hnb2 : fn.name ≠ "full_prop_flush_slow_fid" := fun heq => by
        have h1 := fidStep9_before_not_in_step8.2.1
        have hm := List.contains_iff_mem.mpr (List.mem_map.mpr ⟨fn, hf0_mem, heq⟩)
        rw [h1] at hm; cases hm
      have hnb3 : fn.name ≠ "full_rebuild_watches_nosort_fid" := fun heq => by
        have h1 := fidStep9_before_not_in_step8.2.2
        have hm := List.contains_iff_mem.mpr (List.mem_map.mpr ⟨fn, hf0_mem, heq⟩)
        rw [h1] at hm; cases hm
      have hfrontNone := fidStep9_front_none_of_repl_none hrepl hnb1 hnb2 hnb3
      refine ⟨hf0_ok.1, ?_, fun xs m Q X hlk => ?_⟩
      · simpa only [fidStep9_noExit, fidStep9_externs_empty, List.map_nil, List.append_nil] using
          hcalls9
      · change fidStep9Env fn.name fn.as fn.rs xs m Q X at hlk
        dsimp only [fidStep9Env] at hlk
        rw [patchEnv_base_eq fidStep9Bundle hfrontNone] at hlk
        have hwp_base := hf0_ok.2.2 xs m Q X hlk
        refine fn_wp_env_agree_of_noCallIn hf0_ok.1 hf0_ok.2.1 hno (fun f as bs hs hb => ?_)
          hwp_base
        simp only [List.mem_singleton] at hb
        refine fidStep9_agree (f, as, bs) ?_ hb
        simp only [Module.sigs, List.mem_append, List.mem_map] at hs ⊢
        rcases hs with ⟨g, hg, hgsig⟩ | ⟨ex, hex, hexsig⟩
        · left; exact ⟨g, hfs ▸ List.mem_append_left _ hg, hgsig⟩
        · right; exact ⟨ex, hex, hexsig⟩
    | some r =>
      have hr_mem : r ∈ FullFidelityStep9.fidStep9Repls := List.mem_of_find?_eq_some hrepl
      have hf0_nm : f0.name = r.name :=
        (beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f0.name) hrepl)).symm
      simp only [hrepl, Option.getD_some] at hfn_eq
      subst hfn_eq
      simp only [FullFidelityStep9.fidStep9Repls, List.mem_cons, List.not_mem_nil,
        or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have hlen84 : bPre.length = 84 := fidStep9_slot_eq_len hfs (slot := 84)
          (sf0 := ("full_prop_flush_del_fid", [i64, i64], [.bool])) (by decide) hf0_nm
        refine ⟨full_prop_flush_del_step9_wf, fidStep9_callsOk_of propFlushDel_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_singleton] at hd; subst hd
          refine hpreIns _ (List.mem_map_of_mem (a := fidStep9PropFlushSlowFn) ?_)
          simp only [patchInsAt, FullFidelityStep9.fidStep9Befores, List.find?, hf0_nm]
          change fidStep9PropFlushSlowFn ∈ [fidStep9PropFlushSlowFn]
          exact List.mem_cons_self
        · have hfind : fidStep9Bundle.frontTable.find?
              (·.name == fidStep9PropFlushDelFn.name) = some fidStep9ReplRows[0] := rfl
          exact (SpecEntry.Impl.of (full_prop_flush_del_fid_step9_wp fidStep9Env
            (fid9_frontRow 12 "full_prop_flush_slow_fid" fidPropFlushSlowSpec rfl
              fidPropFlushSlowSpec_noExit))).2 xs m Q X
            (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen104 : bPre.length = 104 := fidStep9_slot_eq_len hfs (slot := 104)
          (sf0 := ("full_arena_sweep_m6", [i64], [i64])) (by decide) hf0_nm
        refine ⟨full_arena_sweep_m6_step9_wf, fidStep9_callsOk_of arenaSweepM6_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 93) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 94) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 11) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 99) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 103) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find?
              (·.name == fidStep9ArenaSweepM6Fn.name) = some fidStep9ReplRows[1] := rfl
          exact (SpecEntry.Impl.of (full_arena_sweep_m6_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_sweepBinsRangeM6 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_arenaNext _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_sweepCopy _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_moveRedEndM6 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_rewatchRangeM6 _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen113 : bPre.length = 113 := fidStep9_slot_eq_len hfs (slot := 113)
          (sf0 := ("full_reduce_m6", [i64, .bool], [i64])) (by decide) hf0_nm
        refine ⟨full_reduce_m6_step9_wf, fidStep9_callsOk_of reduceM6_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 8) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 32) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 11) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 62) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 72) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 107) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 111) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 40) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 88) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 106) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find?
              (·.name == fidStep9ReduceM6Fn.name) = some fidStep9ReplRows[2] := rfl
          exact (SpecEntry.Impl.of (full_reduce_m6_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_isqrt _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_log10Q16M7 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_arenaNext _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_hdrRecomputeTiers _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_hdrSetWatermark _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_markReasons _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_sortReds _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_backtrack _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_propagate _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_arenaSweep _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen288 : bPre.length = 288 := fidStep9_slot_eq_len hfs (slot := 288)
          (sf0 := ("full_congruence_dense", [i64, i64], [i64])) (by decide) hf0_nm
        refine ⟨full_congruence_dense_step9_wf, fidStep9_callsOk_of congruenceDense_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 263) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 264) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 265) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 287) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 271) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 274) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find?
              (·.name == fidStep9CongruenceDenseFn.name) = some fidStep9ReplRows[3] := rfl
          exact (SpecEntry.Impl.of (full_congruence_dense_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_congExtractBinaries _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_congFindUnitsEquivs _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_congExtract _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_congExtractIteAll _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_congWorklist _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_congFwdSubsume _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen247 : bPre.length = 247 := fidStep9_slot_eq_len hfs (slot := 247)
          (sf0 := ("full_rebuild_watches", [i64], [i64])) (by decide) hf0_nm
        refine ⟨full_rebuild_watches_step9_wf, fidStep9_callsOk_of rebuildWatches_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · refine hpreIns _ (List.mem_map_of_mem (a := fidStep9RebuildWatchesNosortFn) ?_)
            simp only [patchInsAt, FullFidelityStep9.fidStep9Befores, List.find?, hf0_nm]
            change fidStep9RebuildWatchesNosortFn ∈ [fidStep9RebuildWatchesNosortFn]
            exact List.mem_cons_self
          · exact hprePatch _ (hliftBase (i := 246) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find?
              (·.name == fidStep9RebuildWatchesFn.name) = some fidStep9ReplRows[4] := rfl
          exact (SpecEntry.Impl.of (full_rebuild_watches_step9_wp fidStep9Env
            (fid9_frontRow 13 "full_rebuild_watches_nosort_fid" Full.fullRebuildWatchesSpec)
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_sortBinWatches _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen436 : bPre.length = 436 := fidStep9_slot_eq_len hfs (slot := 436)
          (sf0 := ("full_bva_commit", [i64, i32], [.bool])) (by decide) hf0_nm
        refine ⟨full_bva_commit_step9_wf, fidStep9_callsOk_of bvaCommit_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 425) (by decide) (by decide) (by omega))
          · exact hprePatch _ (fidStep9_before_sig_in_patch hfs
              (ins := fidStep9FillU64Fn) (slot := 42)
              (sa := ("full_zero_tables1", [i64], [])) (by decide) (by omega)
              fun anc hnm => by
                simp [patchInsAt, FullFidelityStep9.fidStep9Befores, hnm])
          · exact hprePatch _ (hliftBase (i := 18) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 420) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 183) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 12) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 19) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 184) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 81) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9BvaCommitFn.name) =
              some fidStep9ReplRows[5] := rfl
          exact (SpecEntry.Impl.of (full_bva_commit_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_bvaStepsCap _ _ _ _ hs))
            (fid9_frontRow 11 "full_fill_u64_m7" FullM7MemShrink.m7FillU64Spec rfl
              (fun _ _ _ _ h => by rw [m7FillU64Spec_eq] at h ⊢; exact h))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_wstackDefrag _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_initFreshVar _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_addBin _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_allocCl _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_watchPush _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_deleteBinary _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_unwatchLarge _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen440 : bPre.length = 440 := fidStep9_slot_eq_len hfs (slot := 440)
          (sf0 := ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32]))
          (by decide) hf0_nm
        refine ⟨full_bva_upd_lit_step9_wf, fidStep9_callsOk_of bvaUpdLit_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 429) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 427) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 428) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9BvaUpdLitFn.name) =
              some fidStep9ReplRows[6] := rfl
          exact (SpecEntry.Impl.of (full_bva_upd_lit_fid_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_bvaCountLitDeg _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_fheapUp _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_fheapDown _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen441 : bPre.length = 441 := fidStep9_slot_eq_len hfs (slot := 441)
          (sf0 := ("full_factor", [i64, i64], [i64])) (by decide) hf0_nm
        refine ⟨full_factor_step9_wf, fidStep9_callsOk_of factor_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 425) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 430) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 427) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 428) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 437) (by decide) (by decide) (by omega))
          · exact hprePatch _ (fidStep9_updLit_sig_in_patch hfs (by omega))
        · have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9FactorFn.name) =
              some fidStep9ReplRows[7] := rfl
          exact (SpecEntry.Impl.of (full_factor_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_bvaStepsCap _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_bvaConnectClauses _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_fheapUp _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_fheapDown _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_bvaTryLit _ _ _ _ hs))
            (fid9_frontRow 6 "full_bva_upd_lit_fid" step9BvaUpdLitSpec rfl
              step9BvaUpdLitSpec_noExit))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · refine ⟨full_compact_needed_step9_wf,
          fidStep9_callsOk_of compactNeeded_callsOk (fun _ hd => nomatch hd),
          fun xs m Q X hlk => ?_⟩
        have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9CompactNeededFn.name) =
            some fidStep9ReplRows[8] := rfl
        exact (SpecEntry.Impl.of (full_compact_needed_step9_wp fidStep9Env)).2 xs m Q X
          (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen443 : bPre.length = 443 := fidStep9_slot_eq_len hfs (slot := 443)
          (sf0 := ("full_compact_flush", [i64], [i64])) (by decide) hf0_nm
        refine ⟨full_compact_flush_step9_wf, fidStep9_callsOk_of compactFlush_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_singleton] at hd; subst hd
          exact hprePatch _ (hliftBase (i := 108) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9CompactFlushFn.name) =
              some fidStep9ReplRows[9] := rfl
          exact (SpecEntry.Impl.of (full_compact_flush_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_flushTrail _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen492 : bPre.length = 492 := fidStep9_slot_eq_len hfs (slot := 492)
          (sf0 := ("full_probe_m6", [i64, .bool], [i64])) (by decide) hf0_nm
        refine ⟨full_probe_m6_step9_wf, fidStep9_callsOk_of probeM6_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch _ (hliftBase (i := 490) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 32) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 33) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 227) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 245) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 67) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 288) (by decide) (by decide) (by omega))
          · exact hprePatch _ (fidStep9_before_sig_in_patch hfs
              (ins := fidStep9RebuildWatchesNosortFn) (slot := 247)
              (sa := ("full_rebuild_watches", [i64], [i64])) (by decide) (by omega)
              fun anc hnm => by
                simp [patchInsAt, FullFidelityStep9.fidStep9Befores, hnm])
          · exact hprePatch _ (hliftBase (i := 71) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 72) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 69) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 68) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 348) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 244) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 235) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 238) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 441) (by decide) (by decide) (by omega))
          · exact hprePatch _ (hliftBase (i := 246) (by decide) (by decide) (by omega))
        · have hfind : fidStep9Bundle.frontTable.find? (·.name == fidStep9ProbeM6Fn.name) =
              some fidStep9ReplRows[10] := rfl
          exact (SpecEntry.Impl.of (full_probe_m6_step9_wp fidStep9Env
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_probeDticksM6Hdr _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_log10Q16M7 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_scaleDeltaM5 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_vivifyM6Hdr _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_enterDense _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_hdrDelaying _ _ _ _ hs))
            (fid9_frontRow 3 "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
            (fid9_frontRow 13 "full_rebuild_watches_nosort_fid" Full.fullRebuildWatchesSpec)
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_hdrGetWatermark _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_hdrSetWatermark _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_hdrReduceDelay _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_hdrBumpDelay _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_sweepDenseM6 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_substitute _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_backboneM6 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid9_of_step8 (by decide) (fidStep8Env_transitiveM6 _ _ _ _ hs))
            (fid9_frontRow 7 "full_factor" FullBvaHeap.fullFactorHeapSpec)
            (fun _ _ _ _ hs => fid9_of_step8 (by decide)
              (fidStep8Env_sortBinWatches _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem fidStep9Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep9Env f as bs xs m Q X → fidStep9Env f as bs xs m Q X' :=
  patchEnv_noExit_of fidStep9Bundle (by decide) fidStep8BaseSpecTable_noExit

theorem fidStep9Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep9Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun hs => fid9_of_step8 (by decide) (fidStep8Env_solve_bytes_of hs)

theorem fidStep9_solveBytes_mem : m6oSolveBytesFn ∈ fidStep9Module.fns :=
  patchBundle_solveBytes_mem fidStep9Bundle fidStep8_solveBytes_mem fun r hr => by
    change r ∈ FullFidelityStep9.fidStep9Repls at hr
    simp only [FullFidelityStep9.fidStep9Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep9Module` (`504` fns, `XPost := False`). -/
theorem fidStep9_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep9Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep9_moduleOk fidStep9_solveBytes_mem
    (fun _ _ _ _ hs => fidStep9Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep9Module`. -/
theorem fidStep9_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep9Module`. -/
theorem fidStep9_unsat_nv :
    Func.wp fidStep9Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep9_moduleOk fidStep9_solveBytes_mem
    (fun _ _ _ _ hs => fidStep9Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep9_moduleOk`. -/
theorem fidStep9Module_acyclic : fidStep9Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep9_moduleOk

/-- Canonical Gate-1 Step-9 `KissatUnsatPkg` (`fidStep9Module`, `fidInlPolicy`). -/
def fidStep9UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep9Module fidInlPolicy fidStep9_solveBytes_mem
    fidStep9Env fidStep9_moduleOk fidStep9Env_noExit
    (fun _ _ _ _ hs => fidStep9Env_solve_bytes_of hs)

/-! ## 5. Additive Thin Spec Interface for `fidStep9Env` (`0` `import all` Needed Down-Stream) -/

def fidStep9BaseSpecTable : List SpecEntry :=
  fidStep9Bundle.frontTable ++ fidStep9Bundle.baseTable

theorem fidStep9Base_eq_env : Env.ofTable fidStep9BaseSpecTable = fidStep9Env := by
  unfold fidStep9BaseSpecTable fidStep9Env patchEnv
  rfl

theorem fidStep9Base_moduleOk :
    ModuleOk (Env.ofTable fidStep9BaseSpecTable) fidStep9Module :=
  fidStep9_moduleOk

theorem fidStep9Base_noExit :
    ∀ f as bs xs m Q X X',
      Env.ofTable fidStep9BaseSpecTable f as bs xs m Q X →
      Env.ofTable fidStep9BaseSpecTable f as bs xs m Q X' :=
  fidStep9Env_noExit

theorem fidStep9BaseSpecTable_noExit :
    fidStep9BaseSpecTable.all SpecEntry.noExit = true := by
  unfold fidStep9BaseSpecTable
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨by decide, fidStep8BaseSpecTable_noExit⟩

theorem fidStep9Base_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      Env.ofTable fidStep9BaseSpecTable "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fidStep9Env_solve_bytes_of

@[expose] def fidStep9PatchStrNames (nm : Sym) : List Sym :=
  if nm == "full_zero_tables1" then ["full_fill_u64_m7", nm]
  else if nm == "full_prop_flush_del_fid" then ["full_prop_flush_slow_fid", nm]
  else if nm == "full_rebuild_watches" then ["full_rebuild_watches_nosort_fid", nm]
  else [nm]

@[expose] def fidStep9FnNames : List Sym :=
  fidStep7FnNames.flatMap fidStep9PatchStrNames

theorem fidStep9Module_map_name :
    fidStep9Module.fns.map Fn.name = fidStep9FnNames := by
  rw [fidStep9Fns_eq]
  exact fidStep9_map_name

theorem fidStep9Env_wstackDefrag :
    ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      fidStep9Env "full_wstack_defrag" [i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_wstackDefrag a m Q X hs)

theorem fidStep9Env_tickRel :
    ∀ a m Q X, Full.fullTickRelSpec a m Q X → fidStep9Env "full_tick_rel" [i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_tickRel a m Q X hs)

theorem fidStep9Env_emaUpdate :
    ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      fidStep9Env "full_ema_update" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_emaUpdate a m Q X hs)

theorem fidStep9Env_assignLvl :
    ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      fidStep9Env "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_assignLvl a m Q X hs)

theorem fidStep9Env_backtrack :
    ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      fidStep9Env "full_backtrack" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_backtrack a m Q X hs)

theorem fidStep9Env_addClause :
    ∀ a m Q X, Full.fullAddClauseSpec a m Q X →
      fidStep9Env "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_addClause a m Q X hs)

theorem fidStep9Env_propagate :
    ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      fidStep9Env "full_propagate" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_propagate a m Q X hs)

theorem fidStep9Env_arenaSweep :
    ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      fidStep9Env "full_arena_sweep" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_arenaSweep a m Q X hs)

theorem fidStep9Env_reduceM6 :
    ∀ a m Q X, m6ReduceSpec a m Q X →
      fidStep9Env "full_reduce_m6" [i64, .bool] [i64] a m Q X :=
  fid9_frontRow 2 "full_reduce_m6" m6ReduceSpec rfl (fun _ _ _ _ h => m6ReduceSpec_monoX h)

theorem fidStep9Env_restoreBumpAnaM6Hdr :
    ∀ a m Q X, m6aRestoreBumpAnaSpecP M6ExtW2bPres a m Q X →
      fidStep9Env "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_restoreBumpAnaM6Hdr a m Q X hs)

theorem fidStep9Env_anaFailedLitM6Hdr :
    ∀ a m Q X, m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      fidStep9Env "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_anaFailedLitM6Hdr a m Q X hs)

theorem fidStep9Env_minShrinkM6 :
    ∀ a m Q X, FullM8CoreParity.m8MinShrinkSpec a m Q X →
      fidStep9Env "full_min_shrink_m6" [i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_minShrinkM6 a m Q X hs)

theorem fidStep9Env_deduce1uipM6Hdr :
    ∀ a m Q X, FullM7Proof.m7Deduce1uipHdrSpec a m Q X →
      fidStep9Env "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_deduce1uipM6Hdr a m Q X hs)

theorem fidStep9Env_detNewLevel :
    ∀ a m Q X, Full.fullDetNewLevelSpec a m Q X →
      fidStep9Env "full_det_new_level" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_detNewLevel a m Q X hs)

theorem fidStep9Env_oneLitConfl :
    ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      fidStep9Env "full_one_lit_confl" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_oneLitConfl a m Q X hs)

theorem fidStep9Env_eagerSubsume :
    ∀ a m Q X, Full.fullEagerSubsumeSpec a m Q X →
      fidStep9Env "full_eager_subsume" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_eagerSubsume a m Q X hs)

theorem fidStep9Env_vivClauseM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      fidStep9Env "full_viv_clause_m6" [i64, i32] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_vivClauseM6 a m Q X hs)

theorem fidStep9Env_vivClearTierM6 :
    ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      fidStep9Env "full_viv_clear_tier_m6" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_vivClearTierM6 a m Q X hs)

theorem fidStep9Env_vivCollectFid :
    ∀ a m Q X, FullFidelityVivK6.fullVivCollectFidSpec a m Q X →
      fidStep9Env "full_viv_collect_fid" [i64, i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_vivCollectFid a m Q X hs)

theorem fidStep9Env_vivCountFid :
    ∀ a m Q X, FullFidelityVivK6.fullVivCountFidSpec a m Q X →
      fidStep9Env "full_viv_count_fid" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_vivCountFid a m Q X hs)

theorem fidStep9Env_vivSortFid :
    ∀ a m Q X, FullFidelityVivK6.fullVivSortFidSpec a m Q X →
      fidStep9Env "full_viv_sort_fid" [i64, i64] [] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_vivSortFid a m Q X hs)

theorem fidStep9Env_bveK6MvFid :
    ∀ a m Q X, FullFidelityBve.fidBveK6MvSpec a m Q X →
      fidStep9Env "full_bve_k6_mv_fid" [i64] [i64] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_bveK6MvFid a m Q X hs)

theorem fidStep9Env_k6ExtractSolveFid :
    ∀ a m Q X, FullFidelityBve.fidK6ExtractSolveSpec a m Q X →
      fidStep9Env "full_k6_extract_and_solve_fid"
        [i64, i32, i32, i32, .bool, i32] [.bool] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_k6ExtractSolveFid a m Q X hs)

theorem fidStep9Env_bveCertifyUnitFid :
    ∀ a m Q X, FullFidelityBve.fidBveCertifyUnitSpec a m Q X →
      fidStep9Env "full_bve_certify_unit_fid" [i64, i32, i32, i32, i32, i32] [.bool] a m Q X :=
  fun a m Q X hs => fid9_of_step8 (by decide) (fidStep8Env_bveCertifyUnitFid a m Q X hs)

private theorem fidStep9_peel_from_base {f : Sym} {as bs : List Ty}
    (hf9 : !(fidStep9FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep9Env f as bs xs m Q X) :
    fidStep8Env f as bs xs m Q X := by
  change patchEnv fidStep9Bundle f as bs xs m Q X at h
  rw [patchEnv_base_eq fidStep9Bundle (fidStep9_front_none_of_names hf9)] at h
  dsimp only [fidStep9Bundle] at h
  rwa [fidStep8Base_eq_env] at h

theorem fidStep9Env_elim_analyzeCoreM6 {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep9Env "full_analyze_core_m6" [i64] [i64] xs m Q X) :
    m6HdrAnalyzeSpec xs m Q X :=
  fidStep8Env_elim_analyzeCoreM6 (fidStep9_peel_from_base (by decide) h)

theorem fidStep9Env_elim_vivifyTierM6Hdr {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep9Env "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] xs m Q X) :
    m6aVivifyTierSpec xs m Q X :=
  fidStep8Env_elim_vivifyTierM6Hdr (fidStep9_peel_from_base (by decide) h)

theorem fidStep9Env_elim_rebuildWatchesNosort {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : fidStep9Env "full_rebuild_watches_nosort_fid" [i64] [i64] xs m Q X) :
    Full.fullRebuildWatchesSpec xs m Q X := by
  have hfind : fidStep9Bundle.frontTable.find? (·.name == "full_rebuild_watches_nosort_fid") =
      some fidStep9BeforeRows[2] := rfl
  exact env_ofTable_find?_of_append hfind rfl rfl h

theorem fidStep9Env_elim_congHasClauseK {xs : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (h : fidStep9Env "full_cong_has_clause_k" [i64, i32] [.bool] xs m Q X) :
    FullM6CongSubst.m6CongHasClauseKSpec xs m Q X :=
  fidStep8Env_elim_congHasClauseK (fidStep9_peel_from_base (by decide) h)

theorem fidStep9Env_elim_bveDefK6Fid {xs : Tup Val [i64, i32, i32, i32]} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (h : fidStep9Env "full_bve_def_k6_fid" [i64, i32, i32, i32] [] xs m Q X) :
    FullM8CoreParity.m8BveGatesSpec xs m Q (fun _ _ _ _ => False) :=
  fidStep8Env_elim_bveDefK6Fid (fidStep9_peel_from_base (by decide) h)

private theorem fidStep9_shift_check :
    (List.range 502).all (fun i =>
      ((fidStep7FnNames.take i).flatMap patchStrNames).length ==
        i + (if i ≤ 42 then 0 else if i ≤ 84 then 1 else if i ≤ 247 then 2 else 3)) = true := by
  t_kernel_rfl

private theorem fidStep9_shift_len {i : Nat} (hi : i ≤ 501) :
    ((fidStep7FnNames.take i).flatMap patchStrNames).length =
      i + (if i ≤ 42 then 0 else if i ≤ 84 then 1 else if i ≤ 247 then 2 else 3) := by
  have h := List.all_eq_true.mp fidStep9_shift_check i (List.mem_range.mpr (by omega))
  exact beq_iff_eq.mp h

private theorem fidStep9_patchFns_append (xs ys : List Fn) :
    patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores (xs ++ ys) =
      patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores xs ++
      patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores ys := by
  unfold patchFns; exact List.flatMap_append

theorem fidStep9_slot_of_step8 {i j : Nat} {s : SigEntry}
    (h8 : fidStep8Module.fns[i]?.map Fn.sig = some s)
    (hne : s.1 ≠ "full_bva_upd_lit_fid")
    (hni : s.1 ≠ "full_zero_tables1" ∧ s.1 ≠ "full_prop_flush_del_fid" ∧
      s.1 ≠ "full_rebuild_watches")
    (hj : j = i + (if i ≤ 42 then 0 else if i ≤ 84 then 1 else if i ≤ 247 then 2 else 3)) :
    fidStep9Module.fns[j]?.map Fn.sig = some s := by
  cases hg : fidStep8Module.fns[i]? with
  | none => simp [hg] at h8
  | some g =>
    simp only [hg, Option.map_some, Option.some.injEq] at h8
    have hi_lt : i < fidStep8Module.fns.length :=
      Nat.lt_of_not_le fun hge => by rw [List.getElem?_eq_none hge] at hg; cases hg
    have hlen8 : fidStep8Module.fns.length = 501 := by rw [fidStep8Fns_eq]; exact fidStep8Fns_length
    have hsplit : fidStep8Module.fns =
        fidStep8Module.fns.take i ++ g :: fidStep8Module.fns.drop (i + 1) := by
      have hd := List.take_append_drop i fidStep8Module.fns
      rw [drop_eq_cons_9 hg] at hd; exact hd.symm
    have hgnm : g.name = s.1 := congrArg Prod.fst h8
    have hins : patchInsAt FullFidelityStep9.fidStep9Befores g = [] := by
      unfold patchInsAt FullFidelityStep9.fidStep9Befores
      have h1 : ("full_zero_tables1" == g.name) = false :=
        beq_false_of_ne (Ne.symm (hgnm ▸ hni.1))
      have h2 : ("full_prop_flush_del_fid" == g.name) = false :=
        beq_false_of_ne (Ne.symm (hgnm ▸ hni.2.1))
      have h3 : ("full_rebuild_watches" == g.name) = false :=
        beq_false_of_ne (Ne.symm (hgnm ▸ hni.2.2))
      simp [List.find?, h1, h2, h3]
    have hpf : fidStep9Module.fns =
        patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
          (fidStep8Module.fns.take i) ++
        ((FullFidelityStep9.fidStep9Repls.find? (·.name == g.name)).getD g) ::
        patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
          (fidStep8Module.fns.drop (i + 1)) := by
      have h1 : fidStep9Module.fns =
          patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
            (fidStep8Module.fns.take i ++ g :: fidStep8Module.fns.drop (i + 1)) :=
        congrArg (patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores) hsplit
      rw [h1, fidStep9_patchFns_append]
      simp [patchFns, hins]
    have hpre_len : (patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
        (fidStep8Module.fns.take i)).length = j := by
      rw [← List.length_map Fn.name, patchFns_map_name, List.map_take, fidStep8Module_map_name,
        fidStep9_shift_len (by omega), hj]
    have hget9 : fidStep9Module.fns[j]? =
        some ((FullFidelityStep9.fidStep9Repls.find? (·.name == g.name)).getD g) := by
      rw [hpf, ← hpre_len, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
    rw [hget9, Option.map_some]
    cases hr : FullFidelityStep9.fidStep9Repls.find? (·.name == g.name) with
    | none => simp [h8]
    | some r =>
      have hrnm : r.name = g.name :=
        beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == g.name) hr)
      have hsig := fidStep9Module_replSigs_except_updLit r (List.mem_of_find?_eq_some hr)
        (hrnm.trans hgnm ▸ hne) g (List.mem_of_getElem? hg) hrnm
      simp [hsig, h8]

theorem fidStep9_slot_rebuildWatchesNosort :
    fidStep9Module.fns[249]?.map Fn.sig =
      some ("full_rebuild_watches_nosort_fid", [i64], [i64]) := by
  obtain ⟨g, _, hg, hsg⟩ := fidStep9_slot8
    (i := 247) (s := ("full_rebuild_watches", [i64], [i64])) (by decide)
  have hgnm : g.name = "full_rebuild_watches" := congrArg Prod.fst hsg
  have hsplit : fidStep8Module.fns =
      fidStep8Module.fns.take 247 ++ g :: fidStep8Module.fns.drop 248 := by
    have hd := List.take_append_drop 247 fidStep8Module.fns
    rw [drop_eq_cons_9 hg] at hd; exact hd.symm
  have hins : patchInsAt FullFidelityStep9.fidStep9Befores g =
      [fidStep9RebuildWatchesNosortFn] := by
    unfold patchInsAt FullFidelityStep9.fidStep9Befores
    simp [List.find?, hgnm]
  have hpf : fidStep9Module.fns =
      patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
        (fidStep8Module.fns.take 247) ++
      fidStep9RebuildWatchesNosortFn ::
      (((FullFidelityStep9.fidStep9Repls.find? (·.name == g.name)).getD g) ::
        patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
          (fidStep8Module.fns.drop 248)) := by
    have h1 : fidStep9Module.fns =
        patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
          (fidStep8Module.fns.take 247 ++ g :: fidStep8Module.fns.drop 248) :=
      congrArg (patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores) hsplit
    rw [h1, fidStep9_patchFns_append]
    simp [patchFns, hins]
  have hpre_len : (patchFns FullFidelityStep9.fidStep9Repls FullFidelityStep9.fidStep9Befores
      (fidStep8Module.fns.take 247)).length = 249 := by
    rw [← List.length_map Fn.name, patchFns_map_name, List.map_take, fidStep8Module_map_name,
      fidStep9_shift_len (by decide)]
    decide
  rw [hpf, ← hpre_len, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]
  rfl

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9

end

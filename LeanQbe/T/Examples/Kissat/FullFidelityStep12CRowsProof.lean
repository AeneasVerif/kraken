/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CProof
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Logic.C0Step

/-!
# Kissat Step-12 Bundle C Specification Rows & `Impl` Barrel (`FullFidelityStep12CRowsProof`)

Plain `public section` (`0` `@[expose]` on theorems/lemmas, `0` new `import all`, `std3`,
`XPost`-polymorphic) barrel exporting the `4` replacement rows (`fidStep12CReplRows`),
`3` inserted helper rows (`fidStep12CBeforeRows`), spliced `508`-fn `fidStep12CModule` shape /
acyclicity / `checkPatchCallsOk` witnesses, `7/7` `Fn.checkCallsOk` certificates, and `7/7`
parametric `(Γ : Env)` `SpecEntry.Impl` theorems ready for final Step-11/12 assembly wire-up:
- **`P1-4a` (`3 + 2` fns):** `full_watch_pop_c0`, `full_add_clause`, `full_sweep_copy`,
  `full_reduce_purge_c0`, `full_learn_clause_m6` (`step10LearnClauseM6Spec` verbatim;
  `renameFuncCalls pr3BtAcMap`-ready for PR3).
- **`P1-9b` (`1 + 1` fns):** `full_viv_sift_counts_m6`, `full_viv_sort_counts_m6`
  (`fullVivSortCountsM6Spec` verbatim, $O(K \log K)$ heapsort).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12C

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7V2Robust
open LeanQbe.T.Examples.Kissat.FullFidelityStep10
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. `fidStep12CReplRows`, `fidStep12CBeforeRows`, Signatures & Spliced Module Checks -/

/-- The `4` Step-12C replacement `SpecEntry` rows matching `fidStep12CRepls`. -/
@[expose] def fidStep12CReplRows : List SpecEntry :=
  [ ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  , ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  , ⟨"full_learn_clause_m6", [i64, i64], [i64], step10LearnClauseM6Spec, true⟩
  , ⟨"full_viv_sort_counts_m6", [i64, i32], [], fullVivSortCountsM6Spec, true⟩ ]

/-- The `3` Step-12C inserted helper `SpecEntry` rows matching `fidStep12CBefores`. -/
@[expose] def fidStep12CBeforeRows : List SpecEntry :=
  [ ⟨"full_watch_pop_c0", [i64, i32, i32], [], fullWatchPopC0Spec, true⟩
  , ⟨"full_reduce_purge_c0", [i64], [i64], fullReducePurgeC0Spec, true⟩
  , ⟨"full_viv_sift_counts_m6", [i64, i64, i64], [], fullVivSiftCountsM6Spec, true⟩ ]

/-- Combined `7` Step-12C `SpecEntry` rows (`4` repls + `3` inserted helpers). -/
@[expose] def fidStep12CRows : List SpecEntry :=
  fidStep12CReplRows ++ fidStep12CBeforeRows

/-- Names of all `7` Step-12C rows (`frontNames` helper). -/
@[expose] def fidStep12CNames : List Sym :=
  [ "full_add_clause", "full_sweep_copy", "full_learn_clause_m6", "full_viv_sort_counts_m6"
  , "full_watch_pop_c0", "full_reduce_purge_c0", "full_viv_sift_counts_m6" ]

theorem fidStep12CRows_map_name : fidStep12CRows.map SpecEntry.name = fidStep12CNames :=
  rfl

theorem fidStep12CRows_nodup : (fidStep12CRows.map SpecEntry.name).Nodup := by
  rw [fidStep12CRows_map_name]
  decide

theorem fidStep12CRows_noExit : ∀ e ∈ fidStep12CRows, e.noExit = true := by
  intro e he
  have hall : fidStep12CRows.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem fidStep12CReplRows_sigs :
    fidStep12CReplRows.map (fun e => (e.name, e.as, e.rs)) =
      fidStep12CRepls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep12CBeforeRows_sigs :
    fidStep12CBeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep12CBefores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep12C_externs_empty : fidStep12CModule.externs = [] :=
  fidStep10_externs_empty

private def patchStr10_12c (nm : Sym) : List Sym :=
  if nm == "full_analyze_core_m6" then ["full_learn_clause_m6", nm] else [nm]

private theorem patchFns_map_name_10_12c (repls : List Fn) :
    ∀ (fs : List Fn),
      (PatchModule.patchFns repls FullFidelityStep10.fidStep10Befores fs).map Fn.name =
        (fs.map Fn.name).flatMap patchStr10_12c
  | [] => rfl
  | f :: fs => by
    have hnm : ((repls.find? (·.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (·.name == f.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)
    have hl : PatchModule.patchFns repls FullFidelityStep10.fidStep10Befores (f :: fs) =
        PatchModule.patchInsAt FullFidelityStep10.fidStep10Befores f ++
          [(repls.find? (·.name == f.name)).getD f] ++
          PatchModule.patchFns repls FullFidelityStep10.fidStep10Befores fs := rfl
    have hbef :
        (PatchModule.patchInsAt FullFidelityStep10.fidStep10Befores f).map Fn.name ++ [f.name] =
          patchStr10_12c f.name := by
      unfold PatchModule.patchInsAt FullFidelityStep10.fidStep10Befores patchStr10_12c
      simp only [List.find?]
      by_cases h1 : f.name = "full_analyze_core_m6"
      · simp [h1, fidStep10LearnClauseM6Fn]
      · simp [beq_false_of_ne (Ne.symm h1), beq_false_of_ne h1]
    rw [List.map_cons, List.flatMap_cons, hl, List.map_append, List.map_append,
      List.map_singleton, hnm, hbef, patchFns_map_name_10_12c repls fs]

private def patchStr12c (nm : Sym) : List Sym :=
  if nm == "full_add_clause" then ["full_watch_pop_c0", nm]
  else if nm == "full_learn_clause_m6" then ["full_reduce_purge_c0", nm]
  else if nm == "full_viv_sort_counts_m6" then ["full_viv_sift_counts_m6", nm]
  else [nm]

private theorem mem_patchStr12c {x y : Sym} (hx : x ∈ patchStr12c y) :
    x = y ∨
    (x = "full_watch_pop_c0" ∧ y = "full_add_clause") ∨
    (x = "full_reduce_purge_c0" ∧ y = "full_learn_clause_m6") ∨
    (x = "full_viv_sift_counts_m6" ∧ y = "full_viv_sort_counts_m6") := by
  unfold patchStr12c at hx
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

private theorem mem_flatMap_patchStr12c {x : Sym} {nms : List Sym}
    (hx : x ∈ nms.flatMap patchStr12c) :
    x ∈ nms ∨
    (x = "full_watch_pop_c0" ∧ "full_add_clause" ∈ nms) ∨
    (x = "full_reduce_purge_c0" ∧ "full_learn_clause_m6" ∈ nms) ∨
    (x = "full_viv_sift_counts_m6" ∧ "full_viv_sort_counts_m6" ∈ nms) := by
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  rcases mem_patchStr12c hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hy
  · exact Or.inr (Or.inl ⟨rfl, hy⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, hy⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, hy⟩))

private theorem nodup_patchStr12c (nm : Sym) : (patchStr12c nm).Nodup := by
  unfold patchStr12c
  split
  · rename_i h; rw [beq_iff_eq.mp h]; decide
  · split
    · rename_i _ h; rw [beq_iff_eq.mp h]; decide
    · split
      · rename_i _ _ h; rw [beq_iff_eq.mp h]; decide
      · simp

private theorem nodup_flatMap_patchStr12c :
    ∀ {nms : List Sym}, nms.Nodup →
      "full_watch_pop_c0" ∉ nms → "full_reduce_purge_c0" ∉ nms →
      "full_viv_sift_counts_m6" ∉ nms →
      (nms.flatMap patchStr12c).Nodup
  | [], _, _, _, _ => List.nodup_nil
  | nm :: nms, hnd, h1, h2, h3 => by
    have ⟨hnm, hnd'⟩ := List.nodup_cons.mp hnd
    have h1' : "full_watch_pop_c0" ∉ nms := fun hm => h1 (List.mem_cons_of_mem _ hm)
    have h2' : "full_reduce_purge_c0" ∉ nms := fun hm => h2 (List.mem_cons_of_mem _ hm)
    have h3' : "full_viv_sift_counts_m6" ∉ nms := fun hm => h3 (List.mem_cons_of_mem _ hm)
    have hhead1 : nm ≠ "full_watch_pop_c0" := fun heq => h1 (heq ▸ List.mem_cons_self)
    have hhead2 : nm ≠ "full_reduce_purge_c0" := fun heq => h2 (heq ▸ List.mem_cons_self)
    have hhead3 : nm ≠ "full_viv_sift_counts_m6" := fun heq => h3 (heq ▸ List.mem_cons_self)
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_patchStr12c nm, nodup_flatMap_patchStr12c hnd' h1' h2' h3',
      fun x hx y hy heq => ?_⟩
    subst heq
    rcases mem_patchStr12c hx with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases mem_flatMap_patchStr12c hy with hyn | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hnm hyn
      · exact hhead1 rfl
      · exact hhead2 rfl
      · exact hhead3 rfl
    · rcases mem_flatMap_patchStr12c hy with hyn | ⟨_, hyk⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
      · exact h1' hyn
      · exact hnm hyk
      · exact absurd hf (by decide)
      · exact absurd hf (by decide)
    · rcases mem_flatMap_patchStr12c hy with hyn | ⟨hf, _⟩ | ⟨_, hyk⟩ | ⟨hf, _⟩
      · exact h2' hyn
      · exact absurd hf (by decide)
      · exact hnm hyk
      · exact absurd hf (by decide)
    · rcases mem_flatMap_patchStr12c hy with hyn | ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, hyk⟩
      · exact h3' hyn
      · exact absurd hf (by decide)
      · exact absurd hf (by decide)
      · exact hnm hyk

private theorem patchFns_map_name_12c (repls : List Fn) :
    ∀ (fs : List Fn),
      (PatchModule.patchFns repls fidStep12CBefores fs).map Fn.name =
        (fs.map Fn.name).flatMap patchStr12c
  | [] => rfl
  | f :: fs => by
    have hnm : ((repls.find? (·.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (·.name == f.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)
    have hl : PatchModule.patchFns repls fidStep12CBefores (f :: fs) =
        PatchModule.patchInsAt fidStep12CBefores f ++ [(repls.find? (·.name == f.name)).getD f] ++
          PatchModule.patchFns repls fidStep12CBefores fs := rfl
    have hbef : (PatchModule.patchInsAt fidStep12CBefores f).map Fn.name ++ [f.name] =
        patchStr12c f.name := by
      unfold PatchModule.patchInsAt fidStep12CBefores patchStr12c
      simp only [List.find?]
      by_cases h1 : f.name = "full_add_clause"
      · simp [h1, fidStep12CWatchPopFn, v2rWatchPopFn]
      · by_cases h2 : f.name = "full_learn_clause_m6"
        · simp [h2, fidStep12CReducePurgeFn, v2rReducePurgeFn]
        · by_cases h3 : f.name = "full_viv_sort_counts_m6"
          · simp [h3, fidStep12CVivSiftCountsM6Fn]
          · simp [beq_false_of_ne (Ne.symm h1), beq_false_of_ne h1,
              beq_false_of_ne (Ne.symm h2), beq_false_of_ne h2,
              beq_false_of_ne (Ne.symm h3), beq_false_of_ne h3]
    rw [List.map_cons, List.flatMap_cons, hl, List.map_append, List.map_append,
      List.map_singleton, hnm, hbef, patchFns_map_name_12c repls fs]

private def fidStep10FnNames12c : List Sym :=
  fidStep9FnNames.flatMap patchStr10_12c

private theorem fidStep10_map_name_12c :
    fidStep10Fns.map Fn.name = fidStep10FnNames12c := by
  rw [fidStep10Fns, patchFns_map_name_10_12c, ← fidStep9Fns_eq, fidStep9Module_map_name]
  rfl

private theorem fidStep12C_map_name :
    fidStep12CModuleFns.map Fn.name = fidStep10FnNames12c.flatMap patchStr12c := by
  rw [fidStep12CModuleFns, patchFns_map_name_12c, fidStep10_map_name_12c]

theorem fidStep12CFns_length : fidStep12CModuleFns.length = 508 := by
  rw [← List.length_map Fn.name, fidStep12C_map_name]
  t_kernel_rfl

theorem fidStep12CModule_names_nodup : fidStep12CModule.namesNodup := by
  have hnd10 : fidStep10FnNames12c.Nodup := by
    rw [← fidStep10_map_name_12c, ← fidStep10Fns_eq]
    exact module_fns_namesNodup fidStep10Module_names_nodup
  have hnot1 : fidStep10FnNames12c.contains "full_watch_pop_c0" = false := by t_kernel_rfl
  have hnot2 : fidStep10FnNames12c.contains "full_reduce_purge_c0" = false := by t_kernel_rfl
  have hnot3 : fidStep10FnNames12c.contains "full_viv_sift_counts_m6" = false := by t_kernel_rfl
  have h1 : "full_watch_pop_c0" ∉ fidStep10FnNames12c := fun hm => by
    have hc := List.contains_iff_mem.mpr hm; rw [hnot1] at hc; cases hc
  have h2 : "full_reduce_purge_c0" ∉ fidStep10FnNames12c := fun hm => by
    have hc := List.contains_iff_mem.mpr hm; rw [hnot2] at hc; cases hc
  have h3 : "full_viv_sift_counts_m6" ∉ fidStep10FnNames12c := fun hm => by
    have hc := List.contains_iff_mem.mpr hm; rw [hnot3] at hc; cases hc
  change (fidStep12CModule.fns.map Fn.name ++ fidStep12CModule.externs.map Extern.name).Nodup
  rw [fidStep12C_externs_empty, List.map_nil, List.append_nil]
  change (fidStep12CModuleFns.map Fn.name).Nodup
  rw [fidStep12C_map_name]
  exact nodup_flatMap_patchStr12c hnd10 h1 h2 h3

/-! ## 2. Static `checkCallsOk` Witnesses (`7/7`) -/

theorem fid12c_watchPop_callsOk :
    fidStep12CWatchPopFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fid12c_addClause_callsOk :
    fidStep12CAddClauseFn.checkCallsOk
      [ ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
      , ("full_watch_pop_c0", [i64, i32, i32], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem fid12c_sweepCopy_callsOk :
    fidStep12CSweepCopyFn.checkCallsOk
      [ ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_watch_pop_c0", [i64, i32, i32], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem fid12c_reducePurge_callsOk :
    fidStep12CReducePurgeFn.checkCallsOk
      [ ("full_arena_next", [i64, i32], [i32])
      , ("full_backtrack", [i64, i64], [])
      , ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_mark_reasons", [i64, .bool], []) ] [] = true := by
  t_kernel_rfl

theorem fid12c_learnClauseM6_callsOk :
    fidStep12CLearnClauseM6Fn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_wstack_defrag", [i64], [])
      , ("full_reduce_m6", [i64, .bool], [i64])
      , ("full_reduce_purge_c0", [i64], [i64])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64])
      , ("full_eager_subsume", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem fid12c_vivSiftCountsM6_callsOk :
    fidStep12CVivSiftCountsM6Fn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fid12c_vivSortCountsM6_callsOk :
    fidStep12CVivSortCountsM6Fn.checkCallsOk
      [ ("full_viv_sift_counts_m6", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Theorems (`7/7`, `XPost`-Polymorphic) -/

theorem fid12c_add_clause_impl (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hPop : ∀ a m Q X, fullWatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12CAddClauseFn fidStep12CReplRows[0] :=
  SpecEntry.Impl.of (full_add_clause_wp Γ hAlloc hPush hPop)

theorem fid12c_sweep_copy_impl (Γ : Env)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hPop : ∀ a m Q X, fullWatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12CSweepCopyFn fidStep12CReplRows[1] :=
  SpecEntry.Impl.of (full_sweep_copy_wp Γ hAssign hPush hPop)

theorem fid12c_learn_clause_m6_impl (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ a m Q X, fullReducePurgeC0Spec a m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12CLearnClauseM6Fn fidStep12CReplRows[2] :=
  SpecEntry.Impl.of
    (full_learn_clause_m6_step12c_wp Γ hBt hAsgn hDnl hDefrag hRedM6 hRedPurge hAddCl hEsub)

theorem fid12c_viv_sort_counts_m6_impl (Γ : Env)
    (hSift : ∀ a m Q X, fullVivSiftCountsM6Spec a m Q X →
      Γ "full_viv_sift_counts_m6" [i64, i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep12CVivSortCountsM6Fn fidStep12CReplRows[3] :=
  SpecEntry.Impl.of (full_viv_sort_counts_m6_step12c_wp Γ hSift)

theorem fid12c_watch_pop_c0_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep12CWatchPopFn fidStep12CBeforeRows[0] :=
  SpecEntry.Impl.of (full_watch_pop_c0_wp Γ)

theorem fid12c_reduce_purge_c0_impl (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    SpecEntry.Impl Γ fidStep12CReducePurgeFn fidStep12CBeforeRows[1] :=
  SpecEntry.Impl.of (full_reduce_purge_c0_wp Γ hBt hProp hMarkRsn hArenaNext hSweep)

theorem fid12c_viv_sift_counts_m6_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep12CVivSiftCountsM6Fn fidStep12CBeforeRows[2] :=
  SpecEntry.Impl.of (full_viv_sift_counts_m6_wp Γ)

end LeanQbe.T.Examples.Kissat.FullFidelityStep12C

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofMisc
import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofCong
import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofAnalyze
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 10 (`FullFidelityAssemblyStep10Proof`)

Certifies `FullFidelityAssemblyStep10.fidStep10Module` (`505` fns, `0` externs, `0` exits,
`0` `import all`, `0` `@[expose]` on theorems/lemmas) via `PatchModule` +
`FullFidelityAssemblyUtil`:
1. `fidStep10Bundle : PatchBundle` layering `FullFidelityStep10.fidStep10Repls` (`5` sig-preserving
   repls) and `FullFidelityStep10.fidStep10Befores` (`+1` inserted helper `full_learn_clause_m6`
   before `full_analyze_core_m6`) onto `fidStep9Module` (`504 -> 505` fns).
2. Closed `505/505` `fidStep10_moduleOk : ModuleOk fidStep10Env fidStep10Module`,
   `fidStep10Env_noExit`, `fidStep10_solve_bytes_sound`, `fidStep10_solve_bytes_host_sound`,
   `fidStep10_unsat_nv` (`XPost := False`, `r = 20#64`, `std3`), `fidStep10Module_acyclic`, and
   `fidStep10UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityStep10
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle`, `length`, `namesNodup`, & Slot Plan (`505/505`) -/

/-- The `5` sig-preserving replacement specification rows matching `fidStep10Repls`. -/
def fidStep10ReplRows : List SpecEntry :=
  [ ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_rebuild_watches_nosort_fid", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"full_cong_has_clause_k", [i64, i32], [.bool],
      FullM6CongSubst.m6CongHasClauseKSpec, true⟩
  , ⟨"full_bve_def_k6_fid", [i64, i32, i32, i32], [],
      FullM8CoreParity.m8BveGatesSpec, true⟩ ]

/-- The `1` inserted helper specification row matching `fidStep10Befores`. -/
def fidStep10BeforeRows : List SpecEntry :=
  [ ⟨"full_learn_clause_m6", [i64, i64], [i64], step10LearnClauseM6Spec, true⟩ ]

/-- Step-10 `PatchBundle` composing `fidStep9Module` + `FullFidelityStep10` (`505` fns). -/
def fidStep10Bundle : PatchBundle where
  baseMod := fidStep9Module
  baseTable := fidStep9BaseSpecTable
  baseOk := fidStep9Base_moduleOk
  repls := FullFidelityStep10.fidStep10Repls
  replRows := fidStep10ReplRows
  befores := FullFidelityStep10.fidStep10Befores
  beforeRows := fidStep10BeforeRows

/-- Closed `Env` for `fidStep10Module` (`505` fns). -/
def fidStep10Env : Env :=
  patchEnv fidStep10Bundle

theorem fidStep10_externs_empty : fidStep10Module.externs = [] :=
  fidStep9_externs_empty

private def patchStrNames10 (nm : Sym) : List Sym :=
  if nm == "full_analyze_core_m6" then ["full_learn_clause_m6", nm] else [nm]

private theorem fidStep10Befores_map_name (f : Fn) :
    (patchInsAt FullFidelityStep10.fidStep10Befores f).map Fn.name ++ [f.name] =
      patchStrNames10 f.name := by
  unfold patchInsAt FullFidelityStep10.fidStep10Befores patchStrNames10
  simp only [List.find?]
  by_cases h1 : f.name = "full_analyze_core_m6"
  · simp [h1, fidStep10LearnClauseM6Fn]
  · have h1a : ("full_analyze_core_m6" == f.name) = false := beq_false_of_ne (Ne.symm h1)
    have h1b : (f.name == "full_analyze_core_m6") = false := beq_false_of_ne h1
    simp [h1a, h1b]

private theorem mem_patchStrNames10 {x y : Sym} (hx : x ∈ patchStrNames10 y) :
    x = y ∨ (x = "full_learn_clause_m6" ∧ y = "full_analyze_core_m6") := by
  unfold patchStrNames10 at hx
  split at hx
  · rename_i h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr ⟨rfl, beq_iff_eq.mp h⟩
    · exact Or.inl rfl
  · simp only [List.mem_singleton] at hx; exact Or.inl hx

private theorem mem_flatMap_patchStrNames10 {x : Sym} {nms : List Sym}
    (hx : x ∈ nms.flatMap patchStrNames10) :
    x ∈ nms ∨ (x = "full_learn_clause_m6" ∧ "full_analyze_core_m6" ∈ nms) := by
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  rcases mem_patchStrNames10 hxy with rfl | ⟨rfl, rfl⟩
  · exact Or.inl hy
  · exact Or.inr ⟨rfl, hy⟩

private theorem nodup_patchStrNames10 (nm : Sym) : (patchStrNames10 nm).Nodup := by
  unfold patchStrNames10
  split
  · rename_i h; rw [beq_iff_eq.mp h]; decide
  · simp

private theorem nodup_flatMap_patchStrNames10 :
    ∀ {nms : List Sym}, nms.Nodup → "full_learn_clause_m6" ∉ nms →
      (nms.flatMap patchStrNames10).Nodup
  | [], _, _ => List.nodup_nil
  | nm :: nms, hnd, h1 => by
    have ⟨hnm, hnd'⟩ := List.nodup_cons.mp hnd
    have h1' : "full_learn_clause_m6" ∉ nms := fun hm => h1 (List.mem_cons_of_mem _ hm)
    have hhead1 : nm ≠ "full_learn_clause_m6" := fun heq => h1 (heq ▸ List.mem_cons_self)
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_patchStrNames10 nm, nodup_flatMap_patchStrNames10 hnd' h1',
      fun x hx y hy heq => ?_⟩
    subst heq
    rcases mem_patchStrNames10 hx with rfl | ⟨rfl, rfl⟩
    · rcases mem_flatMap_patchStrNames10 hy with hyn | ⟨rfl, _⟩
      · exact hnm hyn
      · exact hhead1 rfl
    · rcases mem_flatMap_patchStrNames10 hy with hyn | ⟨_, hyk⟩
      · exact h1' hyn
      · exact hnm hyk

private theorem patchFns_map_name10 (repls : List Fn) :
    ∀ (fs : List Fn),
      (patchFns repls FullFidelityStep10.fidStep10Befores fs).map Fn.name =
        (fs.map Fn.name).flatMap patchStrNames10
  | [] => rfl
  | f :: fs => by
    have hnm : ((repls.find? (·.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (·.name == f.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) h)
    have hl : patchFns repls FullFidelityStep10.fidStep10Befores (f :: fs) =
        patchInsAt FullFidelityStep10.fidStep10Befores f ++
          [(repls.find? (·.name == f.name)).getD f] ++
          patchFns repls FullFidelityStep10.fidStep10Befores fs := rfl
    rw [List.map_cons, List.flatMap_cons, hl, List.map_append, List.map_append,
      List.map_singleton, hnm, fidStep10Befores_map_name f, patchFns_map_name10 repls fs]

private theorem fidStep10_map_name :
    fidStep10Fns.map Fn.name = fidStep9FnNames.flatMap patchStrNames10 := by
  rw [fidStep10Fns, patchFns_map_name10, ← fidStep9Fns_eq, fidStep9Module_map_name]

private theorem fidStep10_len_rfl :
    (fidStep9FnNames.flatMap patchStrNames10).length = 505 := by
  t_kernel_rfl

private theorem fidStep10_not_in1 :
    fidStep9FnNames.contains "full_learn_clause_m6" = false := by
  t_kernel_rfl

theorem fidStep10Fns_length : fidStep10Fns.length = 505 := by
  rw [← List.length_map Fn.name, fidStep10_map_name]
  exact fidStep10_len_rfl

theorem fidStep10Module_names_nodup : fidStep10Module.namesNodup := by
  have hnd9 : fidStep9FnNames.Nodup := by
    rw [← fidStep9Module_map_name]
    exact module_fns_namesNodup fidStep9Module_names_nodup
  have h1 : "full_learn_clause_m6" ∉ fidStep9FnNames := fun hm => by
    have hc := List.contains_iff_mem.mpr hm
    rw [fidStep10_not_in1] at hc
    cases hc
  change (fidStep10Module.fns.map Fn.name ++ fidStep10Module.externs.map Extern.name).Nodup
  rw [fidStep10_externs_empty, List.map_nil, List.append_nil, fidStep10Fns_eq, fidStep10_map_name]
  exact nodup_flatMap_patchStrNames10 hnd9 h1

private def fidStep10FrontNames : List Sym :=
  [ "full_analyze_core_m6", "full_vivify_tier_m6_hdr", "full_rebuild_watches_nosort_fid"
  , "full_cong_has_clause_k", "full_bve_def_k6_fid", "full_learn_clause_m6" ]

private theorem fidStep10_frontNames_eq :
    fidStep10Bundle.frontTable.map SpecEntry.name = fidStep10FrontNames :=
  rfl

private theorem fidStep10_front_nodup :
    (fidStep10Bundle.frontTable.map SpecEntry.name).Nodup := by
  rw [fidStep10_frontNames_eq]
  decide

private theorem fidStep10_slot9_of_at {j : Nat} {s : SigEntry}
    (h9 : fidStep9Module.fns[j]?.map Fn.sig = some s) :
    ∃ g ∈ fidStep9Module.fns, fidStep9Module.fns[j]? = some g ∧ g.sig = s := by
  cases h : fidStep9Module.fns[j]? with
  | none => simp [h] at h9
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at h9
    exact ⟨g, List.mem_of_getElem? h, rfl, h9⟩

theorem fidStep10Module_replSigs_ok :
    ∀ r ∈ FullFidelityStep10.fidStep10Repls, ∀ g ∈ fidStep9Module.fns,
      r.name = g.name → r.sig = g.sig := by
  have hnd := module_fns_namesNodup fidStep9Module_names_nodup
  intro r hr g hg hnm
  have hslot : ∀ {j : Nat} {s : SigEntry}, fidStep9Module.fns[j]?.map Fn.sig = some s →
      r.sig = s → r.sig = g.sig := by
    intro j s hs hrs
    obtain ⟨g0, hg0, _, hsg⟩ := fidStep10_slot9_of_at hs
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg.symm)
    rw [nodup_name_eq Fn.name hnd hg hg0 (hnm.symm.trans hgnm), hsg, hrs]
  simp only [FullFidelityStep10.fidStep10Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hslot (fidStep9_slot_of_step8 (fidStep8_step10_sig_at (p := (155, _)) (by decide))
      (by decide) (by decide) rfl) rfl
  · exact hslot (fidStep9_slot_of_step8 (fidStep8_step10_sig_at (p := (226, _)) (by decide))
      (by decide) (by decide) rfl) rfl
  · exact hslot fidStep9_slot_rebuildWatchesNosort rfl
  · exact hslot (fidStep9_slot_of_step8 (fidStep8_step10_sig_at (p := (257, _)) (by decide))
      (by decide) (by decide) rfl) rfl
  · exact hslot (fidStep9_slot_of_step8 (fidStep8_step10_sig_at (p := (416, _)) (by decide))
      (by decide) (by decide) rfl) rfl

/-! ## 2. Per-Function `checkCallsOk` & `fidStep10Env` Lifts -/

private theorem learnClauseM6_callsOk :
    fidStep10LearnClauseM6Fn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_wstack_defrag", [i64], [])
      , ("full_reduce_m6", [i64, .bool], [i64])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64])
      , ("full_eager_subsume", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem analyzeCoreM6_callsOk :
    fidStep10AnalyzeCoreM6Fn.checkCallsOk
      [ ("full_one_lit_confl", [i64], [i64])
      , ("full_ana_failed_lit_m6_hdr", [i64], [i64])
      , ("full_deduce_1uip_m6_hdr", [i64], [i64])
      , ("full_restore_bump_ana_m6_hdr", [i64], [])
      , ("full_min_shrink_m6", [i64], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], [])
      , ("full_learn_clause_m6", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem vivifyTierM6Hdr_callsOk :
    fidStep10VivifyTierM6HdrFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_viv_collect_fid", [i64, i64], [i64])
      , ("full_viv_count_fid", [i64, i64], [])
      , ("full_viv_sort_fid", [i64, i64], [])
      , ("full_viv_clause_m6", [i64, i32], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_viv_clear_tier_m6", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem rebuildWatchesNosort10_callsOk :
    fidStep10RebuildWatchesNosortFn.checkCallsOk
      [ ("full_arena_sweep", [i64], [i64])
      , ("full_propagate", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem congHasClauseK10_callsOk :
    fidStep10CongHasClauseKFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

private theorem bveDefK6Fid10_callsOk :
    fidStep10BveDefK6Fn.checkCallsOk
      [ ("full_bve_k6_mv_fid", [i64], [i64])
      , ("full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool])
      , ("full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

private theorem fidStep10_front_none_of_names {nm : Sym}
    (hf10 : !(fidStep10FrontNames.contains nm) = true) :
    fidStep10Bundle.frontTable.find? (·.name == nm) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hm : nm ∈ fidStep10FrontNames :=
    fidStep10_frontNames_eq ▸ (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
  simp [hm] at hf10

private theorem fid10_of_step9 {f : Sym} {as bs : List Ty}
    (hf10 : !(fidStep10FrontNames.contains f) = true := by decide)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidStep9Env f as bs xs m Q X) :
    fidStep10Env f as bs xs m Q X := by
  change patchEnv fidStep10Bundle f as bs xs m Q X
  rw [patchEnv_base_eq fidStep10Bundle (fidStep10_front_none_of_names hf10)]
  dsimp only [fidStep10Bundle]
  rwa [fidStep9Base_eq_env]

private theorem fid10_frontRow (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep10Bundle.frontTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidStep10Env nm as bs a m Q X := fun a m Q X hs =>
  patchEnv_of_front_mem fidStep10Bundle fidStep10_front_nodup (List.mem_of_getElem? hi)
    (hno a m Q X hs)

/-! ## 3. Patch-Split Infrastructure & `fidStep10_agree` -/

private theorem drop_eq_cons_10 {α : Type _} {xs : List α} {i : Nat} {x : α}
    (hx : xs[i]? = some x) : xs.drop i = x :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    cases i with
    | zero => simp at hx; simp [hx]
    | succ i => simp at hx ⊢; exact ih hx

private theorem split_append_cons_10 {α : Type _} {xs : List α} {x y : α} {zs pre post : List α}
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
      have hdrop : xs.drop pre.length = x :: xs.drop (pre.length + 1) := drop_eq_cons_10 hget
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

private theorem patchFns_split_10 {repls : List Fn} {befores : List (Sym × List Fn)}
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
    rcases split_append_cons_10 hsplit with
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

private theorem patchFns_sig_preserved10 {bPre : List Fn}
    (hsub : ∀ f ∈ bPre, f ∈ fidStep9Module.fns) {f : Fn} (hf : f ∈ bPre) :
    f.sig ∈ (patchFns FullFidelityStep10.fidStep10Repls
      FullFidelityStep10.fidStep10Befores bPre).map Fn.sig := by
  have hmem : (FullFidelityStep10.fidStep10Repls.find? (·.name == f.name)).getD f ∈
      patchFns FullFidelityStep10.fidStep10Repls FullFidelityStep10.fidStep10Befores bPre := by
    simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨f, hf, Or.inr rfl⟩
  have hsig : ((FullFidelityStep10.fidStep10Repls.find? (·.name == f.name)).getD f).sig =
      f.sig := by
    cases hr : FullFidelityStep10.fidStep10Repls.find? (·.name == f.name) with
    | none => rfl
    | some r =>
      have hrnm : r.name = f.name :=
        beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hr)
      exact fidStep10Module_replSigs_ok r (List.mem_of_find?_eq_some hr) f (hsub f hf) hrnm
  exact hsig ▸ List.mem_map_of_mem hmem

private theorem nodup_list_getElem?_inj10 {α : Type _} {xs : List α} (hnd : xs.Nodup)
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
        simp at hi hj; subst hi
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨j, hj⟩))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj; subst hj
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      | succ j =>
        simp at hi hj
        exact congrArg Nat.succ (ih hnd' hi hj)

private theorem fidStep10_slot_eq_len {bPre bPost : List Fn} {f0 : Fn} {slot : Nat}
    {sf0 : SigEntry} (hfs : fidStep9Module.fns = bPre ++ f0 :: bPost)
    (hs : fidStep9Module.fns[slot]?.map Fn.sig = some sf0) (hf0 : f0.name = sf0.1) :
    bPre.length = slot := by
  obtain ⟨g0, _, hg0, hsg0⟩ := fidStep10_slot9_of_at hs
  have h1 : (fidStep9Module.fns.map Fn.name)[bPre.length]? = some sf0.1 := by
    rw [hfs]; simp [hf0]
  have h2 : (fidStep9Module.fns.map Fn.name)[slot]? = some sf0.1 := by
    simp [List.getElem?_map, hg0, ← hsg0, Fn.sig]
  exact nodup_list_getElem?_inj10 (module_fns_namesNodup fidStep9Module_names_nodup) h1 h2

private theorem fidStep10_base_sig_in_patch {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep9Module.fns = bPre ++ f0 :: bPost)
    {j : Nat} {s : SigEntry} (hs : fidStep9Module.fns[j]?.map Fn.sig = some s)
    (hlt : j < bPre.length) :
    s ∈ (patchFns FullFidelityStep10.fidStep10Repls FullFidelityStep10.fidStep10Befores bPre).map
      Fn.sig := by
  obtain ⟨g, _, hgi, hsg⟩ := fidStep10_slot9_of_at hs
  have hgb : bPre[j]? = some g := by rwa [hfs, List.getElem?_append_left hlt] at hgi
  have hsub : ∀ f ∈ bPre, f ∈ fidStep9Module.fns := fun f hf => hfs ▸ List.mem_append_left _ hf
  exact hsg ▸ patchFns_sig_preserved10 hsub (List.mem_of_getElem? hgb)

private theorem fidStep10_callsOk_of {fn : Fn} {deps : List SigEntry} {pre : List Fn}
    (hchk : fn.checkCallsOk deps [] = true) (hsub : ∀ d ∈ deps, d ∈ pre.map Fn.sig) :
    fn.callsOk (pre.map Fn.sig ++ fidStep10Module.externs.map Extern.sig)
      fidStep10Module.exits := by
  rw [fidStep10_noExit, fidStep10_externs_empty, List.map_nil, List.append_nil]
  exact fn_callsOk_mono hsub (Fn.callsOk_of_checkCallsOk hchk)

private theorem fidStep10_front_none_of_repl_none {f0 : Fn} (hf0 : f0 ∈ fidStep9Module.fns)
    (h : FullFidelityStep10.fidStep10Repls.find? (·.name == f0.name) = none) :
    fidStep10Bundle.frontTable.find? (·.name == f0.name) = none := by
  rw [List.find?_eq_none]
  intro e he hbeq
  have hnm : e.name = f0.name := beq_iff_eq.mp hbeq
  have hmem : e.name ∈ fidStep10FrontNames := fidStep10_frontNames_eq ▸ List.mem_map_of_mem he
  simp only [fidStep10FrontNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hnotRepl : ∀ r ∈ FullFidelityStep10.fidStep10Repls, r.name ≠ f0.name := fun r hr heq => by
    have := List.find?_eq_none.mp h r hr
    simp [heq] at this
  have hf0_in9 : f0.name ∈ fidStep9FnNames := by
    rw [← fidStep9Module_map_name]; exact List.mem_map_of_mem hf0
  rcases hmem with h0 | h0 | h0 | h0 | h0 | h0
  · exact hnotRepl fidStep10AnalyzeCoreM6Fn (by simp [FullFidelityStep10.fidStep10Repls])
      (h0.symm.trans hnm)
  · exact hnotRepl fidStep10VivifyTierM6HdrFn (by simp [FullFidelityStep10.fidStep10Repls])
      (h0.symm.trans hnm)
  · exact hnotRepl fidStep10RebuildWatchesNosortFn (by simp [FullFidelityStep10.fidStep10Repls])
      (h0.symm.trans hnm)
  · exact hnotRepl fidStep10CongHasClauseKFn (by simp [FullFidelityStep10.fidStep10Repls])
      (h0.symm.trans hnm)
  · exact hnotRepl fidStep10BveDefK6Fn (by simp [FullFidelityStep10.fidStep10Repls])
      (h0.symm.trans hnm)
  · have hc := List.contains_iff_mem.mpr ((hnm.symm.trans h0) ▸ hf0_in9)
    rw [fidStep10_not_in1] at hc; cases hc

private theorem fidStep10_agree :
    ∀ s ∈ fidStep9Module.sigs,
      ∀ xs m P E, Env.ofTable fidStep9BaseSpecTable s.1 s.2.1 s.2.2 xs m P E →
        fidStep10Env s.1 s.2.1 s.2.2 xs m P E := by
  intro ⟨nm, as, bs⟩ hs xs m P E hBase
  change patchEnv fidStep10Bundle nm as bs xs m P E
  cases hf : fidStep10Bundle.frontTable.find? (·.name == nm) with
  | none =>
    rw [patchEnv_base_eq fidStep10Bundle hf]
    exact hBase
  | some e =>
    have he : e ∈ fidStep10Bundle.frontTable := List.mem_of_find?_eq_some hf
    have hnm : e.name = nm :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
    by_cases hsig : e.as = as ∧ e.rs = bs
    · rcases hsig with ⟨has, hrs⟩
      subst hnm has hrs
      have hBase9 : fidStep9Env e.name e.as e.rs xs m P E := fidStep9Base_eq_env ▸ hBase
      refine patchEnv_of_front_mem fidStep10Bundle fidStep10_front_nodup he ?_
      simp only [fidStep10Bundle, PatchBundle.frontTable, fidStep10ReplRows, fidStep10BeforeRows,
        List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact m6HdrAnalyzeSpec_monoX (fidStep9Env_elim_analyzeCoreM6 hBase9)
      · exact m6aVivifyTierSpec_monoX (fidStep9Env_elim_vivifyTierM6Hdr hBase9)
      · exact fidStep9Env_elim_rebuildWatchesNosort hBase9
      · exact fidStep9Env_elim_congHasClauseK hBase9
      · exact fidStep9Env_elim_bveDefK6Fid hBase9
      · exfalso
        simp only [Module.sigs, fidStep9_externs_empty, List.map_nil, List.append_nil,
          List.mem_map] at hs
        obtain ⟨g, hg, hgs⟩ := hs
        have hgn : g.name = "full_learn_clause_m6" := congrArg Prod.fst hgs
        have hc : fidStep9FnNames.contains "full_learn_clause_m6" = true :=
          List.contains_iff_mem.mpr (by
            rw [← fidStep9Module_map_name, ← hgn]; exact List.mem_map_of_mem hg)
        rw [fidStep10_not_in1] at hc; cases hc
    · have hne : ∀ e' ∈ fidStep10Bundle.frontTable,
          ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq := nodup_name_eq SpecEntry.name fidStep10_front_nodup he' he
          (hnm'.trans hnm.symm)
        subst heq; exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = nm ∧ e'.as = as ∧ e'.rs = bs)) →
          Env.ofTable (pfx ++ fidStep10Bundle.baseTable) nm as bs xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          exact Or.inr ⟨hpfx x List.mem_cons_self,
            ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)⟩
      exact hLift fidStep10Bundle.frontTable hne

/-! ## 4. Closed `505/505` `fidStep10_moduleOk`, UNSAT Soundness, `Mem 64` NV & `KissatUnsatPkg` -/

/-- Closed `505/505` `ModuleOk` for `FullFidelityAssemblyStep10.fidStep10Module` under
`fidStep10Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep10_moduleOk : ModuleOk fidStep10Env fidStep10Module := by
  refine ⟨fidStep10Module_names_nodup, fun pre fn post hsplit => ?_⟩
  have hsplit' : patchFns FullFidelityStep10.fidStep10Repls
      FullFidelityStep10.fidStep10Befores fidStep9Module.fns = pre ++ fn :: post := hsplit
  obtain ⟨bPre, f0, bPost, hfs, hcase⟩ := patchFns_split_10 hsplit'
  have hf0_mem : f0 ∈ fidStep9Module.fns := hfs ▸ List.mem_append_right _ List.mem_cons_self
  have hf0_ok := fidStep9Base_moduleOk.fnsOk bPre f0 bPost hfs
  have hsubPre : ∀ g ∈ bPre, g ∈ fidStep9Module.fns := fun g hg => hfs ▸ List.mem_append_left _ hg
  have hlift9 : ∀ {i j : Nat} {s : SigEntry},
      fidStep8Module.fns[i]?.map Fn.sig = some s →
      s.1 ≠ "full_bva_upd_lit_fid" →
      (s.1 ≠ "full_zero_tables1" ∧ s.1 ≠ "full_prop_flush_del_fid" ∧
        s.1 ≠ "full_rebuild_watches") →
      j = i + (if i ≤ 42 then 0 else if i ≤ 84 then 1 else if i ≤ 247 then 2 else 3) →
      j < bPre.length →
      s ∈ (patchFns FullFidelityStep10.fidStep10Repls FullFidelityStep10.fidStep10Befores
        bPre).map Fn.sig :=
    fun h8 hne hni hj hlt =>
      fidStep10_base_sig_in_patch hfs (fidStep9_slot_of_step8 h8 hne hni hj) hlt
  rcases hcase with ⟨iPre, iPost, hi, hpreIns⟩ | ⟨hfn_eq, hprePatch⟩
  · -- Inserted `before` helper (`full_learn_clause_m6` before `full_analyze_core_m6` at slot 157)
    have hprePatch0 : ∀ s, s ∈ (patchFns FullFidelityStep10.fidStep10Repls
        FullFidelityStep10.fidStep10Befores bPre).map Fn.sig → s ∈ pre.map Fn.sig := fun s hs =>
      hpreIns s (by rw [List.map_append, List.mem_append]; exact Or.inl hs)
    unfold patchInsAt FullFidelityStep10.fidStep10Befores at hi
    simp only [List.find?] at hi
    by_cases hf0_1 : f0.name = "full_analyze_core_m6"
    · simp only [hf0_1, beq_self_eq_true] at hi
      have hfn_rfl : fn = fidStep10LearnClauseM6Fn := by
        cases iPre with
        | nil => simpa using (List.cons.inj hi).1.symm
        | cons _ _ => simp at hi
      subst hfn_rfl
      have hlen157 : bPre.length = 157 := fidStep10_slot_eq_len hfs
        (fidStep9_slot_of_step8
          (fidStep8_step10_sig_at (p := (155, ("full_analyze_core_m6", [i64], [i64]))) (by decide))
          (by decide) (by decide) rfl) hf0_1
      refine ⟨full_learn_clause_m6_step10_wf, fidStep10_callsOk_of learnClauseM6_callsOk ?_,
        fun xs m Q X hlk => ?_⟩
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (40, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
        · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (36, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
        · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (145, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
        · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (18, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
        · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (113, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
        · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (41, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
        · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (147, _)) (by decide))
            (by decide) (by decide) rfl (by rw [hlen157]; decide))
      · have hfind : fidStep10Bundle.frontTable.find?
            (·.name == fidStep10LearnClauseM6Fn.name) = some fidStep10BeforeRows[0] := rfl
        have hcast := env_ofTable_find?_of_append hfind rfl rfl hlk
        exact (SpecEntry.Impl.of (full_learn_clause_m6_step10_wp fidStep10Env
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_backtrack _ _ _ _ hs))
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_assignLvl _ _ _ _ hs))
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_detNewLevel _ _ _ _ hs))
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_wstackDefrag _ _ _ _ hs))
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_reduceM6 _ _ _ _ hs))
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_addClause _ _ _ _ hs))
          (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_eagerSubsume _ _ _ _ hs)))).2
          xs m Q X hcast
    · have h1a : ("full_analyze_core_m6" == f0.name) = false := beq_false_of_ne (Ne.symm hf0_1)
      simp [h1a] at hi
  · -- Kept Step-9 function or one of the `5` Step-10 replacements
    have hprePatch0 : ∀ s, s ∈ (patchFns FullFidelityStep10.fidStep10Repls
        FullFidelityStep10.fidStep10Befores bPre).map Fn.sig → s ∈ pre.map Fn.sig := fun s hs =>
      hprePatch s (by rw [List.map_append, List.mem_append]; exact Or.inl hs)
    cases hrepl : FullFidelityStep10.fidStep10Repls.find? (·.name == f0.name) with
    | none =>
      simp only [hrepl, Option.getD_none] at hfn_eq
      subst hfn_eq
      have hfrontNone := fidStep10_front_none_of_repl_none hf0_mem hrepl
      have hcalls9 : fn.callsOk (bPre.map Fn.sig) [] := by
        simpa only [fidStep9_noExit, fidStep9_externs_empty, List.map_nil, List.append_nil] using
          hf0_ok.2.1
      refine ⟨hf0_ok.1, ?_, fun xs m Q X hlookup => ?_⟩
      · rw [fidStep10_noExit, fidStep10_externs_empty, List.map_nil, List.append_nil]
        refine fn_callsOk_mono (fun s hs => ?_) hcalls9
        obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hs
        exact hprePatch0 s (hgs ▸ patchFns_sig_preserved10 hsubPre hg)
      · change fidStep10Env fn.name fn.as fn.rs xs m Q X at hlookup
        dsimp only [fidStep10Env] at hlookup
        rw [patchEnv_base_eq fidStep10Bundle hfrontNone] at hlookup
        dsimp only [fidStep10Bundle] at hlookup
        have hwp_base := hf0_ok.2.2 xs m Q X hlookup
        refine wp_env_agree_of_callsOk (hf0_ok.1 _ _ _ _ _ _) hf0_ok.2.1 (fun f as bs hs => ?_)
          m hwp_base
        apply fidStep10_agree (f, as, bs)
        simp only [Module.sigs, List.mem_append, List.mem_map] at hs ⊢
        rcases hs with ⟨g, hg, hgsig⟩ | ⟨ex, hex, hexsig⟩
        · exact Or.inl ⟨g, hfs ▸ List.mem_append_left _ hg, hgsig⟩
        · exact Or.inr ⟨ex, hex, hexsig⟩
    | some r =>
      have hr_mem : r ∈ FullFidelityStep10.fidStep10Repls := List.mem_of_find?_eq_some hrepl
      have hf0_nm : f0.name = r.name :=
        (beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f0.name) hrepl)).symm
      simp only [hrepl, Option.getD_some] at hfn_eq
      subst hfn_eq
      simp only [FullFidelityStep10.fidStep10Repls, List.mem_cons, List.not_mem_nil,
        or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl
      · have hlen157 : bPre.length = 157 := fidStep10_slot_eq_len hfs
          (fidStep9_slot_of_step8
            (fidStep8_step10_sig_at (p := (155, ("full_analyze_core_m6", [i64], [i64])))
              (by decide))
            (by decide) (by decide) rfl) hf0_nm
        refine ⟨full_analyze_core_m6_step10_wf, fidStep10_callsOk_of analyzeCoreM6_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (146, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (122, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (144, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (121, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (140, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (30, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (34, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen157]; decide))
          · exact hprePatch _ (by
              rw [List.map_append, List.mem_append]; right
              unfold patchInsAt FullFidelityStep10.fidStep10Befores
              simp [List.find?, hf0_nm, fidStep10AnalyzeCoreM6Fn, fidStep10LearnClauseM6Fn, Fn.sig])
        · have hfind : fidStep10Bundle.frontTable.find?
              (·.name == fidStep10AnalyzeCoreM6Fn.name) = some fidStep10ReplRows[0] := rfl
          exact (SpecEntry.Impl.of (full_analyze_core_m6_step10_wp fidStep10Env
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_oneLitConfl _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide)
              (fidStep9Env_anaFailedLitM6Hdr _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide)
              (fidStep9Env_deduce1uipM6Hdr _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide)
              (fidStep9Env_restoreBumpAnaM6Hdr _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_minShrinkM6 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_tickRel _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_emaUpdate _ _ _ _ hs))
            (fid10_frontRow 5 "full_learn_clause_m6" step10LearnClauseM6Spec rfl
              (fun _ _ _ _ h => step10LearnClauseM6Spec_monoX h)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen228 : bPre.length = 228 := fidStep10_slot_eq_len hfs
          (fidStep9_slot_of_step8
            (fidStep8_step10_sig_at
              (p := (226, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))) (by decide))
            (by decide) (by decide) rfl) hf0_nm
        refine ⟨full_vivify_tier_m6_hdr_step10_wf, fidStep10_callsOk_of vivifyTierM6Hdr_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (40, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (222, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (223, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (225, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (214, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (88, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (220, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen228]; decide))
        · have hfind : fidStep10Bundle.frontTable.find?
              (·.name == fidStep10VivifyTierM6HdrFn.name) = some fidStep10ReplRows[1] := rfl
          exact (SpecEntry.Impl.of (full_vivify_tier_m6_hdr_step10_wp fidStep10Env
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_backtrack _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_vivCollectFid _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_vivCountFid _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_vivSortFid _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_vivClauseM6 _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_propagate _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide)
              (fidStep9Env_vivClearTierM6 _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen249 : bPre.length = 249 := fidStep10_slot_eq_len hfs
          fidStep9_slot_rebuildWatchesNosort hf0_nm
        refine ⟨full_rebuild_watches_nosort_step10_wf,
          fidStep10_callsOk_of rebuildWatchesNosort10_callsOk ?_, fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (106, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen249]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step9_sig_at (p := (88, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen249]; decide))
        · have hfind : fidStep10Bundle.frontTable.find?
              (·.name == fidStep10RebuildWatchesNosortFn.name) = some fidStep10ReplRows[2] := rfl
          exact (SpecEntry.Impl.of (full_rebuild_watches_nosort_fid_step10_wp fidStep10Env
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_arenaSweep _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_propagate _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · refine ⟨full_cong_has_clause_k_step10_wf,
          fidStep10_callsOk_of congHasClauseK10_callsOk (fun _ hd => nomatch hd),
          fun xs m Q X hlk => ?_⟩
        have hfind : fidStep10Bundle.frontTable.find?
            (·.name == fidStep10CongHasClauseKFn.name) = some fidStep10ReplRows[3] := rfl
        exact (SpecEntry.Impl.of (full_cong_has_clause_k_step10_wp fidStep10Env)).2
          xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
      · have hlen419 : bPre.length = 419 := fidStep10_slot_eq_len hfs
          (fidStep9_slot_of_step8
            (fidStep8_step10_sig_at
              (p := (416, ("full_bve_def_k6_fid", [i64, i32, i32, i32], []))) (by decide))
            (by decide) (by decide) rfl) hf0_nm
        refine ⟨full_bve_def_k6_fid_step10_wf, fidStep10_callsOk_of bveDefK6Fid10_callsOk ?_,
          fun xs m Q X hlk => ?_⟩
        · intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (403, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen419]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (414, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen419]; decide))
          · exact hprePatch0 _ (hlift9 (fidStep8_step10_sig_at (p := (415, _)) (by decide))
              (by decide) (by decide) rfl (by rw [hlen419]; decide))
        · have hfind : fidStep10Bundle.frontTable.find?
              (·.name == fidStep10BveDefK6Fn.name) = some fidStep10ReplRows[4] := rfl
          exact (SpecEntry.Impl.of (full_bve_def_k6_fid_step10_wp fidStep10Env
            (fun _ _ _ _ hs => fid10_of_step9 (by decide) (fidStep9Env_bveK6MvFid _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide)
              (fidStep9Env_k6ExtractSolveFid _ _ _ _ hs))
            (fun _ _ _ _ hs => fid10_of_step9 (by decide)
              (fidStep9Env_bveCertifyUnitFid _ _ _ _ hs)))).2
            xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem fidStep10Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep10Env f as bs xs m Q X → fidStep10Env f as bs xs m Q X' :=
  patchEnv_noExit_of fidStep10Bundle (by decide) fidStep9BaseSpecTable_noExit

theorem fidStep10Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep10Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun hs => fid10_of_step9 (by decide) (fidStep9Env_solve_bytes_of hs)

theorem fidStep10_solveBytes_mem : m6oSolveBytesFn ∈ fidStep10Module.fns :=
  patchBundle_solveBytes_mem fidStep10Bundle fidStep9_solveBytes_mem fun r hr => by
    change r ∈ FullFidelityStep10.fidStep10Repls at hr
    simp only [FullFidelityStep10.fidStep10Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep10Module` (`505` fns, `XPost := False`). -/
theorem fidStep10_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep10Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep10_moduleOk fidStep10_solveBytes_mem
    (fun _ _ _ _ hs => fidStep10Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep10Module`. -/
theorem fidStep10_solve_bytes_host_sound
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

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep10Module`. -/
theorem fidStep10_unsat_nv :
    Func.wp fidStep10Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep10_moduleOk fidStep10_solveBytes_mem
    (fun _ _ _ _ hs => fidStep10Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep10_moduleOk`. -/
theorem fidStep10Module_acyclic : fidStep10Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep10_moduleOk

/-- Canonical Gate-1 Step-10 `KissatUnsatPkg` (`fidStep10Module`, `fidInlPolicy`). -/
def fidStep10UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep10Module fidInlPolicy fidStep10_solveBytes_mem
    fidStep10Env fidStep10_moduleOk fidStep10Env_noExit
    (fun _ _ _ _ hs => fidStep10Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10

end

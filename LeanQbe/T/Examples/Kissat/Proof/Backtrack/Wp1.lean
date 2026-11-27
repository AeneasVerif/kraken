/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
import LeanQbe.T.Examples.Kissat.Proof.Backtrack.WitnessLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Backtrack WP Proofs — Part 1 (`Proof.Backtrack.Wp1`)

Parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`) for `full_backtrack_raw_m5` (`fullBacktrackRawSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backtrack

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
open LeanQbe.T.Examples.Kissat.Src.Backtrack
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local elab "bt_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

local elab "bt_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local macro "bt_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Pure BitVec & Trail-Backtrack Witness Helpers -/

theorem bt_post_noop_raw {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {Q : Post []}
    {target_lvl : Val i64} {m : Mem 64}
    (hlen : FullState.LengthsOk c s)
    (hle : s.core.cur_level ≤ target_lvl.toNat)
    (htrl_bd : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hPost : ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { core := { s.core with
            unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
            cur_level := cl' },
          scratch := sc' }
      FullState.LengthsOk c s' → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat →
      FullProbeScratchPres s s' →
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss',
        sc' = { (s.scratch) with
          target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb',
          heap := hp', pos := ps', heap_len := hl',
          q_search_idx := qsi', q_search_stamp := qss' }) →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ v < s.core.cur_vars, (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat →
        lvl'[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
            then s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end,
          let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 =
            if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat
            then s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m') : Q () m := by
  refine hPost s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.propagated s.core.cur_level s.core.unassigned s.scratch m
    hlen (Nat.le_refl _) hlen.core_ok.propagated_le (Nat.min_eq_left hle).symm
    (bt_fullProbeScratchPres_refl s)
    ⟨s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
      s.scratch.phases_best, s.scratch.heap, s.scratch.pos, s.scratch.heap_len,
      s.scratch.q_search_idx, s.scratch.q_search_stamp, rfl⟩
    htrl_bd (fun _ _ _ => rfl) ?_ ?_ (fun _ _ _ hlt => by omega) hm
  · rintro ⟨F0, F_cur, hw | hw⟩
    · refine ⟨fun l hl => ?_, fun i hi => ?_⟩
      · by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
        · simp only [hlv, ite_true]
        · simp only [hlv, ite_false]
          exact bt_witness_nochange_vals_zero hw hle hl (Nat.lt_of_not_le hlv)
      · have hlv : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl.toNat := Nat.le_trans (hw.lvl_le i hi) hle
        simp only [hlv, ite_true]
    · refine ⟨fun l hl => ?_, fun i hi => ?_⟩
      · by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
        · simp only [hlv, ite_true]
        · simp only [hlv, ite_false]
          exact bt_nochange_vals_zero hw hle hl (Nat.lt_of_not_le hlv)
      · have hlv : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl.toNat := Nat.le_trans (hw.lvl_le i hi) hle
        simp only [hlv, ite_true]
  · intro _ _ hw _; exact hw

private theorem bt_fullWitness_to_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  { ext_sound := hw.ext_sound
    inconsistent_sound := hw.inconsistent_sound
    arena := hw.arena
    watches := hw.watches
    cur_level_le := hw.cur_level_le
    trail_lits_lt := hw.trail_lits_lt
    trail_vars_nodup := hw.trail_vars_nodup
    vals_domain := hw.vals_domain
    vals_true_iff := hw.vals_true_iff
    vals_false_iff := hw.vals_false_iff
    lvl_le := hw.lvl_le
    dec_earliest := hw.dec_earliest
    levels_inhabited := hw.levels_inhabited
    level0_sound := hw.level0_sound
    trail_pos_inv := hw.trail_pos_inv
    level0_rsn_none := hw.level0_rsn_none
    frame_trail_lt := hw.frame_trail_lt
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := hw.frame_trail_before_lt
    frame_dec_lt := hw.frame_dec_lt
    reason_inv_below := fun i hi _ => hw.reason_inv i hi
    reason_lit_mem_below := fun i hi _ => hw.reason_lit_mem i hi }

private theorem bt_nat_xor1_lt {l n : Nat} (hl : l < 2 * n) : l ^^^ 1 < 2 * n := by
  rw [nat_xor1_eq]; split <;> omega

private theorem bt_nat_xor1_ne (l : Nat) : l ^^^ 1 ≠ l := by
  rw [nat_xor1_eq]; split <;> omega

private theorem bt_vals_clear_pair (vals : List (BitVec 8)) {l k : Nat}
    (hl : l < vals.length) (hl1 : (l ^^^ 1) < vals.length) :
    (((vals.set l 0#8).set (l ^^^ 1) 0#8)[k]?.getD 0#8) =
      if k / 2 = l / 2 then 0#8 else vals[k]?.getD 0#8 := by
  have hlen1 : (vals.set l 0#8).length = vals.length := List.length_set
  have hk_or : k = l ∨ k = (l ^^^ 1) ∨ (k ≠ l ∧ k ≠ (l ^^^ 1)) := by
    by_cases h1 : k = l
    · exact Or.inl h1
    · by_cases h2 : k = (l ^^^ 1)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  rcases hk_or with rfl | rfl | ⟨h1, h2⟩
  · simp only [ite_true]
    rw [List.getElem?_set_ne (bt_nat_xor1_ne k),
      List.getElem?_set_self hl, Option.getD_some]
  · have hdiv : (l ^^^ 1) / 2 = l / 2 := bt_nat_xor1_div2 l
    simp only [hdiv, ite_true]
    rw [List.getElem?_set_self (by omega), Option.getD_some]
  · have hne : ¬ k / 2 = l / 2 := by
      rw [nat_xor1_eq] at h2; split at h2 <;> omega
    simp only [hne, ite_false]
    rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]

private theorem bt_lengthsOk_loop_core {c : FullCfg} {k : FullCoreState}
    {unass' : BitVec 64} {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    (hk : FullCoreState.LengthsOk c k)
    (h1 : vals'.length = k.vals.length) (h2 : lvl'.length = k.lvl.length)
    (h3 : rsns'.length = k.rsns.length) (h4 : trl'.length = k.trl.length)
    (h5 : tp'.length = k.trail_pos.length) :
    FullCoreState.LengthsOk c
      { k with
        unassigned := unass', vals := vals', lvl := lvl',
        rsns := rsns', trl := trl', trail_pos := tp' } := by
  cases hk
  constructor <;> simp only [h1, h2, h3, h4, h5] <;> assumption

private theorem bt_lengthsOk_qsearch {c : FullCfg} {sc : FullScratch}
    (qsi' qss' : BitVec 64) (hsc : FullScratch.LengthsOk c sc) :
    FullScratch.LengthsOk c { sc with q_search_idx := qsi', q_search_stamp := qss' } := by
  cases hsc; constructor <;> assumption

private def btKeptList (k : FullCoreState) (target_lvl q_start i : Nat) : List (BitVec 32) :=
  List.take q_start k.trl ++
    (List.drop q_start (List.take i k.trl)).filter
      (fun lit => decide ((k.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl))

private theorem btKeptList_base (k : FullCoreState) (target_lvl q_start : Nat) :
    btKeptList k target_lvl q_start q_start = List.take q_start k.trl := by
  unfold btKeptList
  have hnil : List.drop q_start (List.take q_start k.trl) = [] :=
    List.drop_eq_nil_of_le (Nat.le_trans (List.length_take_le _ _) (Nat.le_refl _))
  simp [hnil]

private theorem btKeptList_succ (k : FullCoreState) (target_lvl q_start i : Nat)
    (hqi : q_start ≤ i) (hi : i < k.trl.length) :
    btKeptList k target_lvl q_start (i + 1) =
      if (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl then
        btKeptList k target_lvl q_start i ++ [k.trl[i]]
      else btKeptList k target_lvl q_start i := by
  unfold btKeptList
  have htake : List.take (i + 1) k.trl = List.take i k.trl ++ [k.trl[i]] :=
    List.take_succ_eq_append_getElem hi
  have hlen_take : q_start ≤ (List.take i k.trl).length := by
    rw [List.length_take_of_le (Nat.le_of_lt hi)]; exact hqi
  have hdrop : List.drop q_start (List.take (i + 1) k.trl) =
      List.drop q_start (List.take i k.trl) ++ [k.trl[i]] := by
    rw [htake, List.drop_append_of_le_length hlen_take]
  rw [hdrop, List.filter_append, List.filter_cons, List.filter_nil]
  have hget : k.trl[i]?.getD 0#32 = k.trl[i] := by
    rw [List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hget]
  by_cases hp : (k.lvl[(k.trl[i]).toNat / 2]?.getD 0#32).toNat ≤ target_lvl
  · simp [hp, List.append_assoc]
  · simp [hp]

private theorem btKeptList_mem_take (k : FullCoreState) (target_lvl q_start i : Nat)
    (hqi : q_start ≤ i) :
    ∀ x ∈ btKeptList k target_lvl q_start i, ∃ j < i, k.trl[j]?.getD 0#32 = x := by
  intro x hx
  unfold btKeptList at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    have hj_len : j < q_start ∧ j < k.trl.length := by
      simpa only [List.length_take, Nat.lt_min] using hj
    refine ⟨j, Nat.lt_of_lt_of_le hj_len.1 hqi, ?_⟩
    rw [List.getElem?_eq_getElem hj_len.2, Option.getD_some, List.getElem_take]
  · have hx' : x ∈ List.drop q_start (List.take i k.trl) := (List.mem_filter.mp hx).1
    rw [List.mem_iff_getElem] at hx'
    rcases hx' with ⟨j, hj, rfl⟩
    rw [List.length_drop, List.length_take] at hj
    have hj_lt : q_start + j < i ∧ q_start + j < k.trl.length := by omega
    refine ⟨q_start + j, hj_lt.1, ?_⟩
    rw [List.getElem_drop, List.getElem_take, List.getElem?_eq_getElem hj_lt.2, Option.getD_some]

private theorem bt_bv32_ushr1 (x : BitVec 32) : (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]
  change x.toNat >>> 1 = x.toNat / 2
  rw [Nat.shiftRight_eq_div_pow]

private theorem bt_bv32_ushr_one (x : BitVec 32) {y : Nat} (hy : y = 1) :
    (x >>> y).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, hy]
  change x.toNat >>> 1 = x.toNat / 2
  rw [Nat.shiftRight_eq_div_pow]

private theorem bt_bv32_xor1 (x : BitVec 32) : (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by
  rw [BitVec.toNat_xor]; rfl

private structure BtLoopInv (c : FullCfg) (s1 : FullState) (R : Mem 64 → Prop)
    (target_lvl q_start : Nat) (keep_bv i_bv : BitVec 64)
    (st : FullState) (mem : Mem 64) : Prop where
  mem_ok : (FullMem c st ⋆ R) mem
  len_ok : FullState.LengthsOk c st
  keep_le_i : keep_bv.toNat ≤ i_bv.toNat
  qs_le_keep : q_start ≤ keep_bv.toNat
  i_le_te : i_bv.toNat ≤ s1.core.trail_end
  core_eq : ∃ unass' vals' lvl' rsns' trl' tp',
    st.core = { s1.core with
      unassigned := unass', vals := vals', lvl := lvl',
      rsns := rsns', trl := trl', trail_pos := tp' }
  scratch_eq : ∃ hp' ps' hl' qsi' qss',
    st.scratch = { s1.scratch with
      heap := hp', pos := ps', heap_len := hl',
      q_search_idx := qsi', q_search_stamp := qss' }
  pres_ok : FullProbeScratchPres s1 st
  trl_prefix_bd : ∀ k < keep_bv.toNat, (st.core.trl[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars
  trl_suffix : ∀ k, i_bv.toNat ≤ k → k < s1.core.trail_end →
    st.core.trl[k]?.getD 0#32 = s1.core.trl[k]?.getD 0#32
  lvl_keep_eq : ∀ v < s1.core.cur_vars,
    (s1.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl →
    st.core.lvl[v]?.getD 0#32 = s1.core.lvl[v]?.getD 0#32
  wit_inv :
    (∃ F0 F_cur, FullWitnessInv c F0 F_cur s1.core ∨ FullOtfsWitnessInv c F0 F_cur s1.core) →
    keep_bv.toNat = (btKeptList s1.core target_lvl q_start i_bv.toNat).length ∧
    (∀ k < keep_bv.toNat,
      (st.core.trl[k]?.getD 0#32).toNat =
        ((btKeptList s1.core target_lvl q_start i_bv.toNat)[k]?.getD 0#32).toNat) ∧
    (∀ l < 2 * s1.core.cur_vars,
      st.core.vals[l]?.getD 0#8 =
        if (∃ j < i_bv.toNat, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ∧
            target_lvl < (s1.core.lvl[l / 2]?.getD 0#32).toNat
        then 0#8 else s1.core.vals[l]?.getD 0#8) ∧
    (∀ j < i_bv.toNat,
      let v := (s1.core.trl[j]?.getD 0#32).toNat / 2
      st.core.lvl[v]?.getD 0#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl
        then s1.core.lvl[v]?.getD 0#32 else 0#32) ∧
    (∀ j < i_bv.toNat,
      let v := (s1.core.trl[j]?.getD 0#32).toNat / 2
      st.core.rsns[v]?.getD 4294967295#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl
        then s1.core.rsns[v]?.getD 4294967295#32 else 4294967295#32) ∧
    (∀ u < s1.core.cur_vars,
      (∀ j < i_bv.toNat, (s1.core.trl[j]?.getD 0#32).toNat / 2 ≠ u) →
      st.core.lvl[u]?.getD 0#32 = s1.core.lvl[u]?.getD 0#32 ∧
        st.core.rsns[u]?.getD 4294967295#32 = s1.core.rsns[u]?.getD 4294967295#32) ∧
    (∀ k < keep_bv.toNat,
      (st.core.trail_pos[(st.core.trl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k)

private theorem bt_inv_base {c : FullCfg} {s1 : FullState} {R : Mem 64 → Prop}
    {target_lvl : Nat} {q_bv : BitVec 64} {m1 : Mem 64}
    (hlen1 : FullState.LengthsOk c s1)
    (htrl_bd : ∀ k < s1.core.trail_end, (s1.core.trl[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars)
    (htv_lt : target_lvl < s1.core.cur_level)
    (hm1 : (FullMem c s1 ⋆ R) m1)
    (q_start : Nat)
    (hqs_def : q_start =
      min (s1.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s1.core.trail_end)
    (hq_eq : q_bv.toNat = q_start) :
    BtLoopInv c s1 R target_lvl q_start q_bv q_bv s1 m1 := by
  have hqs_le_te : q_start ≤ s1.core.trail_end := by rw [hqs_def]; exact Nat.min_le_right _ _
  have hqs_le_ft : q_start ≤ (s1.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat := by
    rw [hqs_def]; exact Nat.min_le_left _ _
  have hqs_le_trl : q_start ≤ s1.core.trl.length :=
    Nat.le_trans hqs_le_te (Nat.le_trans hlen1.core_ok.trail_end_le
      (Nat.le_trans hlen1.core_ok.cur_vars_le (Nat.le_of_eq hlen1.core_ok.trl_len.symm)))
  refine
    { mem_ok := hm1
      len_ok := hlen1
      keep_le_i := Nat.le_refl _
      qs_le_keep := by rw [hq_eq]; exact Nat.le_refl _
      i_le_te := by rw [hq_eq]; exact hqs_le_te
      core_eq := ⟨s1.core.unassigned, s1.core.vals, s1.core.lvl, s1.core.rsns,
        s1.core.trl, s1.core.trail_pos, rfl⟩
      scratch_eq := ⟨s1.scratch.heap, s1.scratch.pos, s1.scratch.heap_len,
        s1.scratch.q_search_idx, s1.scratch.q_search_stamp, rfl⟩
      pres_ok := bt_fullProbeScratchPres_refl s1
      trl_prefix_bd := fun k hk => htrl_bd k (by omega)
      trl_suffix := fun _ _ _ => rfl
      lvl_keep_eq := fun _ _ _ => rfl
      wit_inv := fun ⟨F0, F_cur, hw⟩ => by
        have hw' : FullOtfsWitnessInv c F0 F_cur s1.core :=
          hw.elim bt_fullWitness_to_otfs id
        have hbef : ∀ j < q_bv.toNat,
            (s1.core.lvl[(s1.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl := by
          intro j hj
          have hj_ft : j < (s1.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat := by omega
          have h := hw'.frame_trail_before_lt (target_lvl + 1) (by omega) htv_lt j hj_ft
          omega
        refine ⟨?_, ?_, ?_, ?_, ?_, fun _ _ _ => ⟨rfl, rfl⟩, ?_⟩
        · rw [hq_eq, btKeptList_base, List.length_take_of_le hqs_le_trl]
        · intro k hk
          rw [hq_eq, btKeptList_base, List.getElem?_take_of_lt (by omega)]
        · intro l _
          by_cases hcond : (∃ j < q_bv.toNat, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ∧
              target_lvl < (s1.core.lvl[l / 2]?.getD 0#32).toNat
          · rcases hcond with ⟨⟨j, hj, hj_eq⟩, hgt⟩
            have := hbef j hj
            rw [hj_eq] at this
            omega
          · simp only [hcond, ite_false]
        · intro j hj
          simp only [hbef j hj, ite_true]
        · intro j hj
          simp only [hbef j hj, ite_true]
        · intro k hk
          exact hw'.trail_pos_inv k (by omega) }

private theorem bt_inv_step_keep {c : FullCfg} {s1 st : FullState} {R : Mem 64 → Prop}
    {target_lvl q_start : Nat} {keep_bv i_bv : BitVec 64} {mem mem' : Mem 64}
    (hinv : BtLoopInv c s1 R target_lvl q_start keep_bv i_bv st mem)
    (hlen1 : FullState.LengthsOk c s1)
    (hi : i_bv.toNat < s1.core.trail_end)
    (htrl_bd : ∀ k < s1.core.trail_end, (s1.core.trl[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars)
    (hle : (st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      target_lvl)
    (hm' : (FullMem c { st with core := { st.core with
      trl := st.core.trl.set keep_bv.toNat (st.core.trl[i_bv.toNat]?.getD 0#32),
      trail_pos := st.core.trail_pos.set
        ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2) (keep_bv.setWidth 32) } } ⋆ R) mem') :
    BtLoopInv c s1 R target_lvl q_start (keep_bv + 1#64) (i_bv + 1#64)
      { st with core := { st.core with
        trl := st.core.trl.set keep_bv.toNat (st.core.trl[i_bv.toNat]?.getD 0#32),
        trail_pos := st.core.trail_pos.set
          ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2) (keep_bv.setWidth 32) } } mem' := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨unass', vals', lvl', rsns', trl', tp', hcore⟩ := hinv.core_eq
  have hs1_te : st.core.trail_end = s1.core.trail_end := by rw [hcore]
  have hs1_cv : st.core.cur_vars = s1.core.cur_vars := by rw [hcore]
  have hkeep_add1 : (keep_bv + 1#64).toNat = keep_bv.toNat + 1 := by
    have := hinv.keep_le_i; have := hinv.i_le_te
    have := hinv.len_ok.core_ok.trail_end_le; have := hinv.len_ok.core_ok.cur_vars_le
    exact bv64_add1_toNat' (by omega)
  have hi_add1 : (i_bv + 1#64).toNat = i_bv.toNat + 1 := by
    have := hinv.i_le_te; have := hinv.len_ok.core_ok.trail_end_le
    have := hinv.len_ok.core_ok.cur_vars_le
    exact bv64_add1_toNat' (by omega)
  have htrl_i : st.core.trl[i_bv.toNat]?.getD 0#32 = s1.core.trl[i_bv.toNat]?.getD 0#32 :=
    hinv.trl_suffix i_bv.toNat (Nat.le_refl _) hi
  have hkeep_lt_trl : keep_bv.toNat < st.core.trl.length := by
    have := hinv.keep_le_i
    have := hinv.len_ok.core_ok.trail_end_le
    have := hinv.len_ok.core_ok.cur_vars_le
    have := hinv.len_ok.core_ok.trl_len
    omega
  have hi_lt_s1_trl : i_bv.toNat < s1.core.trl.length := by
    have := hlen1.core_ok.trail_end_le
    have := hlen1.core_ok.cur_vars_le
    have := hlen1.core_ok.trl_len
    omega
  have hlit_lt : (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat < 2 * s1.core.cur_vars := htrl_bd _ hi
  have hv_lt_tp : (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 < st.core.trail_pos.length := by
    rw [hinv.len_ok.core_ok.trail_pos_len]
    have := hinv.len_ok.core_ok.cur_vars_le; rw [← hs1_cv] at hlit_lt; omega
  have hkeep32 : (keep_bv.setWidth 32).toNat = keep_bv.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    have := hinv.keep_le_i; have := hinv.len_ok.core_ok.trail_end_le
    have := hinv.len_ok.core_ok.cur_vars_le; omega
  refine
    { mem_ok := hm'
      len_ok := ⟨bt_lengthsOk_loop_core hinv.len_ok.core_ok
        rfl rfl rfl List.length_set List.length_set, hinv.len_ok.scratch_ok⟩
      keep_le_i := by rw [hkeep_add1, hi_add1]; exact Nat.add_le_add_right hinv.keep_le_i 1
      qs_le_keep := by rw [hkeep_add1]; exact Nat.le_trans hinv.qs_le_keep (Nat.le_succ _)
      i_le_te := by rw [hi_add1]; exact hi
      core_eq := ⟨unass', vals', lvl', rsns',
        st.core.trl.set keep_bv.toNat (st.core.trl[i_bv.toNat]?.getD 0#32),
        st.core.trail_pos.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2)
          (keep_bv.setWidth 32), by rw [hcore]⟩
      scratch_eq := hinv.scratch_eq
      pres_ok := hinv.pres_ok
      trl_prefix_bd := fun k hk => by
        rw [hkeep_add1] at hk
        dsimp only
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk_lt | rfl
        · rw [List.getElem?_set_ne (Nat.ne_of_lt hk_lt).symm]
          exact hinv.trl_prefix_bd k hk_lt
        · rw [List.getElem?_set_self hkeep_lt_trl, Option.getD_some, htrl_i]
          exact hlit_lt
      trl_suffix := fun k hki hkte => by
        rw [hi_add1] at hki
        have hne : keep_bv.toNat ≠ k := by have := hinv.keep_le_i; omega
        rw [List.getElem?_set_ne hne]
        exact hinv.trl_suffix k (by omega) hkte
      lvl_keep_eq := fun v hv hlv => by dsimp only; rw [hinv.lvl_keep_eq v hv hlv]
      wit_inv := fun ⟨F0, F_cur, hw⟩ => by
        have hw' : FullOtfsWitnessInv c F0 F_cur s1.core :=
          hw.elim bt_fullWitness_to_otfs id
        obtain ⟨hk_len, hk_trl, hvals_ih, hlvl_ih, hrsns_ih, hunt_ih, htp_ih⟩ :=
          hinv.wit_inv ⟨F0, F_cur, hw⟩
        have hnodup_i : ∀ j < i_bv.toNat,
            (s1.core.trl[j]?.getD 0#32).toNat / 2 ≠
              (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := by
          intro j hj heq
          have := hw'.trail_vars_nodup j i_bv.toNat (by omega) hi heq
          omega
        have hv_eq_i : st.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 =
            s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 :=
          (hunt_ih _ (by omega) hnodup_i).1
        have hle_s1 : (s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat ≤ target_lvl := by
          simpa only [htrl_i, hv_eq_i] using hle
        have hqi : q_start ≤ i_bv.toNat := Nat.le_trans hinv.qs_le_keep hinv.keep_le_i
        have hkl_succ : btKeptList s1.core target_lvl q_start (i_bv.toNat + 1) =
            btKeptList s1.core target_lvl q_start i_bv.toNat ++
              [s1.core.trl[i_bv.toNat]'hi_lt_s1_trl] := by
          rw [btKeptList_succ s1.core target_lvl q_start i_bv.toNat hqi hi_lt_s1_trl]
          simp only [hle_s1, ite_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hkeep_add1, hi_add1, hkl_succ, List.length_append, List.length_singleton, hk_len]
        · intro k hk
          rw [hkeep_add1] at hk
          rw [hi_add1, hkl_succ]
          dsimp only
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk_lt | rfl
          · rw [List.getElem?_set_ne (Nat.ne_of_lt hk_lt).symm]
            rw [List.getElem?_append_left (by omega)]
            exact hk_trl k hk_lt
          · rw [List.getElem?_set_self hkeep_lt_trl, Option.getD_some, htrl_i]
            rw [List.getElem?_append_right (by omega), ← hk_len, Nat.sub_self]
            simp only [List.getElem?_cons_zero, Option.getD_some]
            rw [List.getElem?_eq_getElem hi_lt_s1_trl, Option.getD_some]
        · intro l hl
          rw [hi_add1]
          rw [hvals_ih l hl]
          by_cases he : (∃ j < i_bv.toNat + 1, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ∧
              target_lvl < (s1.core.lvl[l / 2]?.getD 0#32).toNat
          · have he0 : (∃ j < i_bv.toNat, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ∧
                target_lvl < (s1.core.lvl[l / 2]?.getD 0#32).toNat := by
              rcases he with ⟨⟨j, hj, hj_eq⟩, hgt⟩
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
              · exact ⟨⟨j, hj_lt, hj_eq⟩, hgt⟩
              · rw [← hj_eq] at hgt; omega
            simp only [he, he0]
          · have he0 : ¬ ((∃ j < i_bv.toNat, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ∧
                target_lvl < (s1.core.lvl[l / 2]?.getD 0#32).toNat) := by
              rintro ⟨⟨j, hj, hj_eq⟩, hgt⟩
              exact he ⟨⟨j, Nat.lt_succ_of_lt hj, hj_eq⟩, hgt⟩
            simp only [he, he0, ite_false]
        · intro j hj
          rw [hi_add1] at hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
          · exact hlvl_ih j hj_lt
          · simp only [hle_s1, ite_true]; exact hv_eq_i
        · intro j hj
          rw [hi_add1] at hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
          · exact hrsns_ih j hj_lt
          · simp only [hle_s1, ite_true]
            exact (hunt_ih _ (by omega) hnodup_i).2
        · intro u hu hnu
          rw [hi_add1] at hnu
          exact hunt_ih u hu (fun j hj => hnu j (Nat.lt_succ_of_lt hj))
        · intro k hk
          rw [hkeep_add1] at hk
          dsimp only
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk_lt | rfl
          · have h_trk :
                (st.core.trl.set keep_bv.toNat (st.core.trl[i_bv.toNat]?.getD 0#32))[k]?.getD
                  0#32 = st.core.trl[k]?.getD 0#32 := by
              rw [List.getElem?_set_ne (Nat.ne_of_lt hk_lt).symm]
            have hk_kl := hk_trl k hk_lt
            have hmem_k : ((btKeptList s1.core target_lvl q_start i_bv.toNat)[k]?.getD 0#32) ∈
                btKeptList s1.core target_lvl q_start i_bv.toNat := by
              have hk_lt_kl : k < (btKeptList s1.core target_lvl q_start i_bv.toNat).length := by
                omega
              rw [List.getElem?_eq_getElem hk_lt_kl, Option.getD_some]
              exact List.getElem_mem _
            obtain ⟨j0, hj0_lt, hj0_eq⟩ := btKeptList_mem_take s1.core target_lvl q_start i_bv.toNat
              hqi _ hmem_k
            have hne_v : (st.core.trl[k]?.getD 0#32).toNat / 2 ≠
                (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := by
              rw [htrl_i]
              intro heq
              apply hnodup_i j0 hj0_lt
              rw [hj0_eq, ← hk_kl, heq]
            rw [h_trk, List.getElem?_set_ne hne_v.symm]
            exact htp_ih k hk_lt
          · rw [List.getElem?_set_self hkeep_lt_trl, Option.getD_some, htrl_i,
              List.getElem?_set_self hv_lt_tp, Option.getD_some, hkeep32] }

private theorem bt_inv_step_unassign {c : FullCfg} {s1 st st_sc : FullState}
    {R : Mem 64 → Prop} {target_lvl q_start : Nat} {keep_bv i_bv : BitVec 64}
    {mem mem' : Mem 64} {unass' : BitVec 64}
    (hinv : BtLoopInv c s1 R target_lvl q_start keep_bv i_bv st mem)
    (hlen1 : FullState.LengthsOk c s1)
    (hi : i_bv.toNat < s1.core.trail_end)
    (htrl_bd : ∀ k < s1.core.trail_end, (s1.core.trl[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars)
    (hgt : ¬ (st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      target_lvl)
    (_hst_sc_core : st_sc.core = st.core)
    (hst_sc_len : FullState.LengthsOk c st_sc)
    (hst_sc_pres : FullProbeScratchPres st st_sc)
    (hst_sc_eq : ∃ hp' ps' hl' qsi' qss', st_sc.scratch =
      { st.scratch with
        heap := hp', pos := ps', heap_len := hl',
        q_search_idx := qsi', q_search_stamp := qss' })
    (hm' : (FullMem c { st_sc with core := { st.core with
      unassigned := unass',
      vals := (st.core.vals.set (st.core.trl[i_bv.toNat]?.getD 0#32).toNat 0#8).set
        ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat ^^^ 1) 0#8,
      lvl := st.core.lvl.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2) 0#32,
      rsns := st.core.rsns.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2)
        4294967295#32 } } ⋆ R) mem') :
    BtLoopInv c s1 R target_lvl q_start keep_bv (i_bv + 1#64)
      { st_sc with core := { st.core with
        unassigned := unass',
        vals := (st.core.vals.set (st.core.trl[i_bv.toNat]?.getD 0#32).toNat 0#8).set
          ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat ^^^ 1) 0#8,
        lvl := st.core.lvl.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2) 0#32,
        rsns := st.core.rsns.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2)
          4294967295#32 } } mem' := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨unass0, vals0, lvl0, rsns0, trl0, tp0, hcore⟩ := hinv.core_eq
  have hs1_te : st.core.trail_end = s1.core.trail_end := by rw [hcore]
  have hs1_cv : st.core.cur_vars = s1.core.cur_vars := by rw [hcore]
  have hi_add1 : (i_bv + 1#64).toNat = i_bv.toNat + 1 := by
    have := hinv.i_le_te; have := hinv.len_ok.core_ok.trail_end_le
    have := hinv.len_ok.core_ok.cur_vars_le
    exact bv64_add1_toNat' (by omega)
  have htrl_i : st.core.trl[i_bv.toNat]?.getD 0#32 = s1.core.trl[i_bv.toNat]?.getD 0#32 :=
    hinv.trl_suffix i_bv.toNat (Nat.le_refl _) hi
  have hlit_lt : (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat < 2 * s1.core.cur_vars := htrl_bd _ hi
  have hvals_len0 : (st.core.trl[i_bv.toNat]?.getD 0#32).toNat < st.core.vals.length := by
    rw [hinv.len_ok.core_ok.vals_len, htrl_i]
    have := hlen1.core_ok.cur_vars_le; omega
  have hvals_len1 : ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat ^^^ 1) < st.core.vals.length := by
    rw [hinv.len_ok.core_ok.vals_len, htrl_i]
    have := hlen1.core_ok.cur_vars_le
    exact Nat.lt_of_lt_of_le (bt_nat_xor1_lt hlit_lt) (Nat.mul_le_mul_left 2 this)
  have hlvl_len : (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 < st.core.lvl.length := by
    rw [hinv.len_ok.core_ok.lvl_len, htrl_i]
    have := hinv.len_ok.core_ok.cur_vars_le; omega
  have hrsns_len : (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 < st.core.rsns.length := by
    rw [hinv.len_ok.core_ok.rsns_len, htrl_i]
    have := hinv.len_ok.core_ok.cur_vars_le; omega
  have hpres_trans : FullProbeScratchPres s1 st_sc := by
    have p1 := hinv.pres_ok; have p2 := hst_sc_pres
    exact ⟨⟨p2.1.1.trans p1.1.1, p2.1.2.trans p1.1.2⟩,
      p2.2.1.trans p1.2.1, p2.2.2.1.trans p1.2.2.1,
      p2.2.2.2.1.trans p1.2.2.2.1, p2.2.2.2.2.1.trans p1.2.2.2.2.1,
      p2.2.2.2.2.2.1.trans p1.2.2.2.2.2.1,
      p2.2.2.2.2.2.2.1.trans p1.2.2.2.2.2.2.1,
      p2.2.2.2.2.2.2.2.trans p1.2.2.2.2.2.2.2⟩
  obtain ⟨hp0, ps0, hl0, qsi0, qss0, hsc0⟩ := hinv.scratch_eq
  obtain ⟨hp1, ps1, hl1, qsi1, qss1, hsc1⟩ := hst_sc_eq
  refine
    { mem_ok := hm'
      len_ok := ⟨bt_lengthsOk_loop_core hinv.len_ok.core_ok
        (List.length_set.trans List.length_set) List.length_set List.length_set rfl rfl,
        hst_sc_len.scratch_ok⟩
      keep_le_i := by rw [hi_add1]; exact Nat.le_trans hinv.keep_le_i (Nat.le_succ _)
      qs_le_keep := hinv.qs_le_keep
      i_le_te := by rw [hi_add1]; exact hi
      core_eq := ⟨unass', _, _, _, trl0, tp0, by rw [hcore]⟩
      scratch_eq := ⟨hp1, ps1, hl1, qsi1, qss1, by rw [hsc1, hsc0]⟩
      pres_ok := hpres_trans
      trl_prefix_bd := hinv.trl_prefix_bd
      trl_suffix := fun k hki hkte => by
        rw [hi_add1] at hki
        exact hinv.trl_suffix k (by omega) hkte
      lvl_keep_eq := fun u hu hlu => by
        dsimp only
        have hne : u ≠ (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := by
          intro heq
          apply hgt
          rw [← heq, hinv.lvl_keep_eq u hu hlu]
          exact hlu
        rw [List.getElem?_set_ne hne.symm]
        exact hinv.lvl_keep_eq u hu hlu
      wit_inv := fun ⟨F0, F_cur, hw⟩ => by
        have hw' : FullOtfsWitnessInv c F0 F_cur s1.core :=
          hw.elim bt_fullWitness_to_otfs id
        obtain ⟨hk_len, hk_trl, hvals_ih, hlvl_ih, hrsns_ih, hunt_ih, htp_ih⟩ :=
          hinv.wit_inv ⟨F0, F_cur, hw⟩
        have hnodup_i : ∀ j < i_bv.toNat,
            (s1.core.trl[j]?.getD 0#32).toNat / 2 ≠
              (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := by
          intro j hj heq
          have := hw'.trail_vars_nodup j i_bv.toNat (by omega) hi heq
          omega
        have hv_eq_i : st.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 =
            s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 :=
          (hunt_ih _ (by omega) hnodup_i).1
        have hgt_s1 : target_lvl <
            (s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          have : ¬ (s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
              0#32).toNat ≤ target_lvl := by
            simpa only [htrl_i, hv_eq_i] using hgt
          omega
        have hqi : q_start ≤ i_bv.toNat := Nat.le_trans hinv.qs_le_keep hinv.keep_le_i
        have hi_lt_s1_trl : i_bv.toNat < s1.core.trl.length := by
          have := hlen1.core_ok.trail_end_le
          have := hlen1.core_ok.cur_vars_le
          have := hlen1.core_ok.trl_len
          omega
        have hkl_succ : btKeptList s1.core target_lvl q_start (i_bv.toNat + 1) =
            btKeptList s1.core target_lvl q_start i_bv.toNat := by
          rw [btKeptList_succ s1.core target_lvl q_start i_bv.toNat hqi hi_lt_s1_trl]
          have hle_f : ¬ (s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
              0#32).toNat ≤ target_lvl := by omega
          simp only [hle_f, ite_false]
        rw [htrl_i] at hlvl_len hrsns_len
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, htp_ih⟩
        · rw [hi_add1, hkl_succ]; exact hk_len
        · intro k hk; rw [hi_add1, hkl_succ]; exact hk_trl k hk
        · intro l hl
          dsimp only
          rw [bt_vals_clear_pair st.core.vals hvals_len0 hvals_len1, hvals_ih l hl, htrl_i, hi_add1]
          by_cases hlv_eq : l / 2 = (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2
          · have hcond : (∃ j < i_bv.toNat + 1, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ∧
                target_lvl < (s1.core.lvl[l / 2]?.getD 0#32).toNat :=
              ⟨⟨i_bv.toNat, Nat.lt_succ_self _, hlv_eq.symm⟩, by rwa [hlv_eq]⟩
            split
            · first | rfl | (split <;> first | rfl | contradiction)
            · contradiction
          · simp only [hlv_eq, ite_false]
            have hiff : (∃ j < i_bv.toNat + 1, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) ↔
                (∃ j < i_bv.toNat, (s1.core.trl[j]?.getD 0#32).toNat / 2 = l / 2) := by
              constructor
              · rintro ⟨j, hj, hj_eq⟩
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
                · exact ⟨j, hj_lt, hj_eq⟩
                · exact absurd hj_eq.symm hlv_eq
              · rintro ⟨j, hj, hj_eq⟩; exact ⟨j, Nat.lt_succ_of_lt hj, hj_eq⟩
            simp only [hiff]
        · intro j hj
          rw [hi_add1] at hj
          dsimp only
          rw [htrl_i]
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
          · have hne : (s1.core.trl[j]?.getD 0#32).toNat / 2 ≠
                (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := hnodup_i j hj_lt
            rw [List.getElem?_set_ne hne.symm]
            exact hlvl_ih j hj_lt
          · rw [List.getElem?_set_self hlvl_len, Option.getD_some]
            have hle_f : ¬ (s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ target_lvl := by omega
            simp only [hle_f, ite_false]
        · intro j hj
          rw [hi_add1] at hj
          dsimp only
          rw [htrl_i]
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
          · have hne : (s1.core.trl[j]?.getD 0#32).toNat / 2 ≠
                (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := hnodup_i j hj_lt
            rw [List.getElem?_set_ne hne.symm]
            exact hrsns_ih j hj_lt
          · rw [List.getElem?_set_self hrsns_len, Option.getD_some]
            have hle_f : ¬ (s1.core.lvl[(s1.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ target_lvl := by omega
            simp only [hle_f, ite_false]
        · intro u hu hnu
          rw [hi_add1] at hnu
          dsimp only
          have hne_i : (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 ≠ u := by
            rw [htrl_i]; exact hnu i_bv.toNat (Nat.lt_succ_self _)
          rw [List.getElem?_set_ne hne_i, List.getElem?_set_ne hne_i]
          exact hunt_ih u hu (fun j hj => hnu j (Nat.lt_succ_of_lt hj)) }

private theorem bt_inv_finish {c : FullCfg} {s s1 st : FullState} {R : Mem 64 → Prop}
    {Q : Post []} {target_lvl : Val i64} {q_start : Nat} {keep_bv : BitVec 64}
    {m_loop m' : Mem 64} {prop_fin : Nat}
    (hcore1 : s1.core = s.core)
    (hpres1 : FullProbeScratchPres s s1)
    (hsc1 : ∃ ta1 ba1 pt1 pb1, s1.scratch =
      { s.scratch with
        target_assigned := ta1, best_assigned := ba1,
        phases_target := pt1, phases_best := pb1 })
    (hcl_lt : target_lvl.toNat < s.core.cur_level)
    (hlen_s : FullState.LengthsOk c s)
    (hqs_def : q_start =
      min (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat s.core.trail_end)
    (hinv : BtLoopInv c s1 R target_lvl.toNat q_start keep_bv (BitVec.ofNat 64 s1.core.trail_end)
      st m_loop)
    (hprop_le : prop_fin ≤ keep_bv.toNat)
    (hm_fin : (FullMem c { st with core := { st.core with
      trail_end := keep_bv.toNat, propagated := prop_fin, cur_level := target_lvl.toNat } } ⋆ R)
      m')
    (hPost : ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { core := { s.core with
            unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
            cur_level := cl' },
          scratch := sc' }
      FullState.LengthsOk c s' → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat →
      FullProbeScratchPres s s' →
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss',
        sc' = { s.scratch with
          target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb',
          heap := hp', pos := ps', heap_len := hl',
          q_search_idx := qsi', q_search_stamp := qss' }) →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ v < s.core.cur_vars, (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat →
        lvl'[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
            then s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end,
          let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 =
            if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat
            then s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    Q () m' := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨unass', vals', lvl', rsns', trl', tp', hcore⟩ := hinv.core_eq
  have hs1_te : st.core.trail_end = s1.core.trail_end := by rw [hcore]
  have hte_lt64 : s1.core.trail_end < 2 ^ 64 := by
    have := hinv.len_ok.core_ok.trail_end_le
    have := hinv.len_ok.core_ok.cur_vars_le; omega
  have hi_eq : (BitVec.ofNat 64 s1.core.trail_end).toNat = s1.core.trail_end :=
    bv64_ofNat_toNat' hte_lt64
  obtain ⟨ta1, ba1, pt1, pb1, hsc1_eq⟩ := hsc1
  obtain ⟨hp', ps', hl', qsi', qss', hsc_eq⟩ := hinv.scratch_eq
  have hcore_fin : { st.core with
      trail_end := keep_bv.toNat, propagated := prop_fin, cur_level := target_lvl.toNat } =
      { s.core with
        unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
        trl := trl', trail_pos := tp', trail_end := keep_bv.toNat,
        propagated := prop_fin, cur_level := target_lvl.toNat } := by
    rw [hcore, hcore1]
  have hsc_fin : st.scratch = { s.scratch with
      target_assigned := ta1, best_assigned := ba1,
      phases_target := pt1, phases_best := pb1,
      heap := hp', pos := ps', heap_len := hl',
      q_search_idx := qsi', q_search_stamp := qss' } := by
    rw [hsc_eq, hsc1_eq]
  have hpres_fin : FullProbeScratchPres s st := by
    have p1 := hpres1; have p2 := hinv.pres_ok
    exact ⟨⟨p2.1.1.trans p1.1.1, p2.1.2.trans p1.1.2⟩,
      p2.2.1.trans p1.2.1, p2.2.2.1.trans p1.2.2.1,
      p2.2.2.2.1.trans p1.2.2.2.1, p2.2.2.2.2.1.trans p1.2.2.2.2.1,
      p2.2.2.2.2.2.1.trans p1.2.2.2.2.2.1,
      p2.2.2.2.2.2.2.1.trans p1.2.2.2.2.2.2.1,
      p2.2.2.2.2.2.2.2.trans p1.2.2.2.2.2.2.2⟩
  have hkeep_te : keep_bv.toNat ≤ s.core.trail_end := by
    rw [← hcore1]; exact Nat.le_trans hinv.keep_le_i (Nat.le_of_eq hi_eq)
  have hkeep_te_st : keep_bv.toNat ≤ st.core.trail_end := by rwa [hs1_te, hcore1]
  have hlen_fin : FullState.LengthsOk c ⟨{ s.core with
      unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
      trl := trl', trail_pos := tp', trail_end := keep_bv.toNat,
      propagated := prop_fin, cur_level := target_lvl.toNat }, st.scratch⟩ := by
    have hok := hinv.len_ok
    rw [← hcore_fin]
    refine ⟨?_, hok.scratch_ok⟩
    cases hok.core_ok
    constructor <;> dsimp only <;>
      first | assumption | exact Nat.le_trans hkeep_te_st (by assumption)
  have hinv_fin :
      (∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
      (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
        then s.core.vals[l]?.getD 0#8 else 0#8) ∧
      (∀ i < s.core.trail_end,
        let v := (s.core.trl[i]?.getD 0#32).toNat / 2
        lvl'[v]?.getD 0#32 =
          if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat
          then s.core.lvl[v]?.getD 0#32 else 0#32) := by
    rintro ⟨F0, F_cur, hw⟩
    have hw_otfs : FullOtfsWitnessInv c F0 F_cur s.core :=
      hw.elim bt_fullWitness_to_otfs id
    obtain ⟨_, _, hvals_ih, hlvl_ih, _, _, _⟩ :=
      hinv.wit_inv ⟨F0, F_cur, by rw [hcore1]; exact hw⟩
    rw [hi_eq, hcore1] at hvals_ih hlvl_ih
    have hvals' : ∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
        then s.core.vals[l]?.getD 0#8 else 0#8 := by
      intro l hl
      have hv_eq := hvals_ih l hl
      have hv_core : st.core.vals[l]?.getD 0#8 = vals'[l]?.getD 0#8 := by rw [hcore]
      rw [hv_core] at hv_eq
      rw [hv_eq]
      by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
      · have hngt : ¬ target_lvl.toNat < (s.core.lvl[l / 2]?.getD 0#32).toNat := by omega
        simp only [hlv, hngt, ite_true, ite_false, and_false]
      · have hgt : target_lvl.toNat < (s.core.lvl[l / 2]?.getD 0#32).toNat := by omega
        simp only [hlv, ite_false]
        by_cases hex : ∃ j < s.core.trail_end, (s.core.trl[j]?.getD 0#32).toNat / 2 = l / 2
        · simp only [hex, hgt, and_self, ite_true]
        · simp only [hex, hgt, false_and, ite_false]
          rcases hw_otfs.vals_domain l hl with h0 | h1 | h255
          · exact h0
          · obtain ⟨j, hj, hj_eq⟩ := (hw_otfs.vals_true_iff l hl).mp h1
            exact absurd ⟨j, hj, by rw [hj_eq]⟩ hex
          · obtain ⟨j, hj, hj_eq⟩ := (hw_otfs.vals_false_iff l hl).mp h255
            exact absurd ⟨j, hj, by rw [hj_eq, bt_nat_xor1_div2]⟩ hex
    have hlvl' : ∀ i < s.core.trail_end,
        lvl'[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
          if (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl.toNat
          then s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 else 0#32 := by
      intro i hi
      have hl_eq := hlvl_ih i hi
      dsimp only at hl_eq
      have : st.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
          lvl'[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 := by rw [hcore]
      rwa [this] at hl_eq
    exact ⟨hvals', hlvl'⟩
  have hotfs_pres : ∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
      FullWitnessInv c F0 F_cur { s.core with
        unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
        trl := trl', trail_pos := tp', trail_end := keep_bv.toNat,
        propagated := prop_fin, cur_level := target_lvl.toNat } := by
    intro F0 F_cur hw
    obtain ⟨hk_len, hk_trl, _, _, hrsns_ih, _, htp_ih⟩ :=
      hinv.wit_inv ⟨F0, F_cur, Or.inr (by rw [hcore1]; exact hw)⟩
    rw [hi_eq, hcore1] at hk_len hk_trl hrsns_ih
    have ⟨hvals', hlvl'⟩ := hinv_fin ⟨F0, F_cur, Or.inr hw⟩
    refine bt_otfs_preserves_fullWitness (s := s)
      (s' := ⟨{ s.core with
        unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
        trl := trl', trail_pos := tp', trail_end := keep_bv.toNat,
        propagated := prop_fin, cur_level := target_lvl.toNat }, st.scratch⟩)
      hw hcl_lt rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hlen_s hlen_fin
      ?_ ?_ hvals' hlvl' ?_ ?_
    · intro i hi
      have h_tr := hk_trl i hi
      simpa only [hcore, btKeptList, hqs_def] using h_tr
    · simpa only [btKeptList, hqs_def] using hk_len
    · intro i hi
      have h_rs := hrsns_ih i hi
      simpa only [hcore] using h_rs
    · intro i hi
      have h_tp := htp_ih i hi
      simpa only [hcore] using h_tp
  refine hPost vals' lvl' rsns' trl' tp' keep_bv.toNat prop_fin target_lvl.toNat
    unass' st.scratch m'
    hlen_fin hkeep_te hprop_le (Nat.min_eq_right (Nat.le_of_lt hcl_lt)).symm
    hpres_fin ⟨ta1, ba1, pt1, pb1, hp', ps', hl', qsi', qss', hsc_fin⟩
    (fun k hk => by
      have h_bd := hinv.trl_prefix_bd k hk
      simpa only [hcore, hcore1] using h_bd)
    (fun v hv hlv => by
      have h_ke := hinv.lvl_keep_eq v (by rw [hcore1]; exact hv)
        (by rw [← hcore1] at hlv; exact hlv)
      simpa only [hcore, hcore1] using h_ke)
    hinv_fin
    (fun F0 F_cur hw _ => hotfs_pres F0 F_cur (bt_fullWitness_to_otfs hw))
    (fun F0 F_cur hw _ => hotfs_pres F0 F_cur hw)
    (by simpa only [← hcore_fin] using hm_fin)

theorem full_backtrack_raw_m5_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Func.wp Γ full_backtrack_raw_m5_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htv_max, htrl_bd, hm, hPost⟩
  unfold Func.wp full_backtrack_raw_m5_body
  bt_steps_nogrp
  refine wp_jnz_of (fun hc => ?_) (fun hnc => ?_)
  · bt_steps_nogrp
    have hle : s.core.cur_level ≤ target_lvl.toNat := by
      have h1 := bv64_ule_true_le' hc
      rwa [bv64_ofNat_toNat' hcl64] at h1
    exact bt_post_noop_raw hlen hle htrl_bd hm hPost
  · bt_steps_nogrp
    bt_call hSave
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    intro _ s1 m1 hcore1 hlen1 ⟨hpres1, ta1, ba1, pt1, pb1, hsc1⟩ hm1
    dsimp only [fullSafetySlice] at hlen1 hm1
    have hcore1_eq : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
    have hcl_lt : target_lvl.toNat < s.core.cur_level := by
      have h1 := bv64_ule_false_lt' hnc
      rwa [bv64_ofNat_toNat' hcl64] at h1
    have htv_mv : target_lvl.toNat < c.max_vars := htv_max hcl_lt
    have htv_add1 : (target_lvl + 1#64).toNat = target_lvl.toNat + 1 := by
      have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
      exact bv64_add1_toNat' (by omega)
    have hft_idx : (target_lvl + 1#64).toNat < s1.core.frame_trail.length := by
      rw [htv_add1, hcore1_eq, hlen.core_ok.frame_trail_len]; omega
    bt_steps_nogrp
    refine wp_unroll_group (fun Jqs hJqs => ?_)
    let q_start := min (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat s.core.trail_end
    have hqs_def : q_start =
        min (s1.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat s1.core.trail_end := by
      rw [hcore1_eq]
    have hLoopEntry : ∀ (q_bv : BitVec 64) (m_e : Mem 64),
        q_bv.toNat = q_start → (FullMem c s1 ⋆ R) m_e →
        Jqs (q_bv, ()) m_e := by
      intro q_bv m_e hq_eq hm_e
      refine hJqs (q_bv, ()) m_e ?_
      let LoopInv : Tup Val [i64, i64] → Mem 64 → Prop :=
        fun p mem => ∃ st, BtLoopInv c s1 R target_lvl.toNat q_start p.fst p.snd.fst st mem
      refine wp_loop_inv LoopInv (fun p _ => s1.core.trail_end - p.snd.fst.toNat)
        (fun J hJ => ?_) (fun J ⟨keep_bv, i_bv, ⟨⟩⟩ mem ⟨st, hinv⟩ hrec => ?_)
      · bt_steps_nogrp
        exact hJ (q_bv, q_bv, ()) m_e ⟨s1, bt_inv_base hlen1
          (by simpa only [hcore1_eq] using htrl_bd)
          (by simpa only [hcore1_eq] using hcl_lt) hm_e q_start hqs_def hq_eq⟩
      · have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
        dsimp only at hinv
        have hm_st := hinv.mem_ok
        obtain ⟨unass_l, vals_l, lvl_l, rsns_l, trl_l, tp_l, hst_core⟩ := hinv.core_eq
        have hte_eq : st.core.trail_end = s1.core.trail_end := by rw [hst_core]
        have hcv_eq : st.core.cur_vars = s1.core.cur_vars := by rw [hst_core]
        have hte_64 : st.core.trail_end < 2 ^ 64 := by
          have := hinv.len_ok.core_ok.trail_end_le
          have := hinv.len_ok.core_ok.cur_vars_le; omega
        bt_steps_nogrp
        refine wp_jnz_of (fun hi_lt => ?_) (fun hi_nlt => ?_)
        · have hi_nat : i_bv.toNat < s1.core.trail_end := by
            have h1 := bv64_ult_true_lt' hi_lt
            rwa [bv64_ofNat_toNat' hte_64, hte_eq] at h1
          have hi_st_trl : i_bv.toNat < st.core.trl.length := by
            have := hinv.len_ok.core_ok.trail_end_le
            have := hinv.len_ok.core_ok.cur_vars_le
            have := hinv.len_ok.core_ok.trl_len; omega
          have htrl_i : st.core.trl[i_bv.toNat]?.getD 0#32 =
              s1.core.trl[i_bv.toNat]?.getD 0#32 := hinv.trl_suffix _ (Nat.le_refl _) hi_nat
          have htrl_get : st.core.trl[i_bv.toNat]?.getD 0#32 = st.core.trl[i_bv.toNat] := by
            rw [List.getElem?_eq_getElem hi_st_trl, Option.getD_some]
          have htrl_val : st.core.trl[i_bv.toNat] = s1.core.trl[i_bv.toNat]?.getD 0#32 :=
            htrl_get.symm.trans htrl_i
          have hcv64 : s1.core.cur_vars < 2 ^ 64 := by
            have := hlen1.core_ok.cur_vars_le; omega
          have hlit_lt : (s1.core.trl[i_bv.toNat]?.getD 0#32).toNat < 2 * s1.core.cur_vars := by
            simpa only [hcore1_eq] using htrl_bd _ (by rw [← hcore1_eq]; exact hi_nat)
          have hv_nat : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat < st.core.cur_vars := by
            rw [bt_bv32_ushr1, htrl_val, hcv_eq]; omega
          have hv_zext : (BitVec.setWidth 64
              (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32))).toNat =
              (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := by
            rw [bv64_zext32_toNat', bt_bv32_ushr1, htrl_get]
          bt_steps_nogrp
          refine wp_unroll_group (fun Jnext hJnext => ?_)
          have hNextOk : ∀ (keep_next : BitVec 64) (st_next : FullState) (m_next : Mem 64),
              BtLoopInv c s1 R target_lvl.toNat q_start keep_next (i_bv + 1#64) st_next m_next →
              Jnext (keep_next, ()) m_next := by
            intro keep_next st_next m_next hinv_n
            refine hJnext (keep_next, ()) m_next ?_
            bt_steps_nogrp
            have hi_add1 : (i_bv + 1#64).toNat = i_bv.toNat + 1 := by
              have := hinv.len_ok.core_ok.trail_end_le
              have := hinv.len_ok.core_ok.cur_vars_le
              exact bv64_add1_toNat' (by omega)
            exact hrec (keep_next, i_bv + 1#64, ()) m_next (by dsimp only; rw [hi_add1]; omega)
              ⟨st_next, hinv_n⟩
          clear hJnext
          refine wp_unroll_group (fun Junass hJunass => ?_)
          have hUnassOk :
              ¬ (st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                target_lvl.toNat →
              Junass () mem := by
            intro hgt_lvl
            refine hJunass () mem ?_
            refine wp_unroll_group (fun JafterU hJafterU => ?_)
            have hAfterUOk : ∀ (unass_u : BitVec 64) (st_sc : FullState) (m_u : Mem 64),
                st_sc.core = st.core →
                FullState.LengthsOk c st_sc →
                FullProbeScratchPres st st_sc →
                (∃ hp' ps' hl' qsi' qss', st_sc.scratch =
                  { st.scratch with
                    heap := hp', pos := ps', heap_len := hl',
                    q_search_idx := qsi', q_search_stamp := qss' }) →
                (FullMem c { st_sc with core := { st.core with
                  unassigned := unass_u,
                  vals := (st.core.vals.set (st.core.trl[i_bv.toNat]?.getD 0#32).toNat 0#8).set
                    ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat ^^^ 1) 0#8,
                  lvl := st.core.lvl.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2) 0#32,
                  rsns := st.core.rsns.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2)
                    4294967295#32 } } ⋆ R) m_u →
                JafterU () m_u := by
              intro unass_u st_sc m_u hsc_c hsc_l hsc_p hsc_e hm_u
              refine hJafterU () m_u ?_
              bt_steps_nogrp
              exact hNextOk keep_bv _ m_u (bt_inv_step_unassign hinv hlen1 hi_nat
                (by simpa only [hcore1_eq] using htrl_bd) hgt_lvl hsc_c hsc_l hsc_p hsc_e hm_u)
            clear hJafterU
            bt_steps_nogrp
            refine wp_jnz_of (fun _ => ?_) (fun hnv => ?_)
            · have hxor_bd : (st.core.trl[i_bv.toNat] ^^^ (1 : BitVec 32)).toNat <
                  st.core.vals.length := by
                rw [bt_bv32_xor1, htrl_val, hinv.len_ok.core_ok.vals_len]
                have := hlen1.core_ok.cur_vars_le
                exact Nat.lt_of_lt_of_le (bt_nat_xor1_lt hlit_lt) (Nat.mul_le_mul_left 2 this)
              have hlit_vlen : st.core.trl[i_bv.toNat].toNat < st.core.vals.length := by
                rw [htrl_val, hinv.len_ok.core_ok.vals_len]
                have := hlen1.core_ok.cur_vars_le; omega
              have hv_llen : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat <
                  st.core.lvl.length := by
                rw [bt_bv32_ushr1, htrl_val, hinv.len_ok.core_ok.lvl_len]
                have := hlen1.core_ok.cur_vars_le; omega
              have hv_rlen : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat <
                  st.core.rsns.length := by
                rw [bt_bv32_ushr1, htrl_val, hinv.len_ok.core_ok.rsns_len]
                have := hlen1.core_ok.cur_vars_le; omega
              bt_steps_nogrp
              let st_u : FullState := { st with core := { st.core with
                vals := (st.core.vals.set (st.core.trl[i_bv.toNat]?.getD 0#32).toNat 0#8).set
                  ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat ^^^ 1) 0#8,
                lvl := st.core.lvl.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2) 0#32,
                rsns := st.core.rsns.set ((st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2)
                  4294967295#32 } }
              have hlen_u : FullState.LengthsOk c st_u :=
                ⟨bt_lengthsOk_loop_core hinv.len_ok.core_ok
                  (List.length_set.trans List.length_set) List.length_set List.length_set rfl rfl,
                  hinv.len_ok.scratch_ok⟩
              refine wp_unroll_group (fun Jflags hJflags => ?_)
              have hFlagsOk : ∀ (unass_u : BitVec 64) (m_f : Mem 64),
                  (FullMem c { st_u with core := { st_u.core with unassigned := unass_u } } ⋆ R)
                    m_f →
                  Jflags () m_f := by
                intro unass_u m_f hm_f
                let st_uf : FullState :=
                  { st_u with core := { st_u.core with unassigned := unass_u } }
                have huf_core : st_uf.core = { st.core with
                    unassigned := unass_u,
                    vals := st_u.core.vals, lvl := st_u.core.lvl, rsns := st_u.core.rsns } := rfl
                have hlen_uf : FullState.LengthsOk c st_uf :=
                  ⟨bt_lengthsOk_loop_core hlen_u.core_ok rfl rfl rfl rfl rfl, hlen_u.scratch_ok⟩
                refine hJflags () m_f ?_
                refine wp_unroll_group (fun Jpush hJpush => ?_)
                have hPostPushOk : ∀ (st_p : FullState) (m_p : Mem 64),
                    st_p.core = st_uf.core →
                    FullState.LengthsOk c st_p →
                    FullProbeScratchPres st st_p →
                    (∃ hp' ps' hl' qsi' qss', st_p.scratch =
                      { st.scratch with
                        heap := hp', pos := ps', heap_len := hl',
                        q_search_idx := qsi', q_search_stamp := qss' }) →
                    (FullMem c st_p ⋆ R) m_p →
                    Jpush () m_p := by
                  intro st_p m_p hsp_core hsp_len hsp_pres ⟨hp', ps', hl', qsi', qss', hsp_sc⟩ hm_p
                  refine hJpush () m_p ?_
                  bt_steps_nogrp
                  have hsp_rec :
                      { { st_p with core := st.core } with core := st_uf.core } = st_p := by
                    cases st_p; simp only [← hsp_core]
                  exact hAfterUOk unass_u { st_p with core := st.core } m_p rfl
                    ⟨hinv.len_ok.core_ok, hsp_len.scratch_ok⟩
                    hsp_pres
                    ⟨hp', ps', hl', qsi', qss', hsp_sc⟩
                    (by dsimp only [st_uf, st_u] at hsp_rec ⊢; rwa [hsp_rec])
                clear hJpush
                bt_steps_nogrp
                refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
                · bt_steps_nogrp
                  bt_call hPush
                  refine ⟨c, st_uf, R, rfl, hlen_uf, (by dsimp only [st_uf]; exact hm_f), ?_⟩
                  intro _ st_p m_p hcore_p hlen_p
                    ⟨h_ext, h_w1, h_w2, h_tm, h_sb, h_ant, h_res, h_sim, hp', ps', hl', hsc_p⟩ hm_p
                  dsimp only [fullSafetySlice] at hlen_p hm_p
                  have hcore_p_eq : st_p.core = st_uf.core :=
                    fullCoreState_agrees_with_scratch hcore_p
                  have hpres_p : FullProbeScratchPres st st_p :=
                    ⟨h_ext, h_w1, h_w2, h_tm, h_sb, h_ant, h_res, h_sim⟩
                  bt_steps_nogrp
                  exact hPostPushOk st_p m_p hcore_p_eq hlen_p hpres_p
                    ⟨hp', ps', hl', st.scratch.q_search_idx, st.scratch.q_search_stamp, hsc_p⟩ hm_p
                · refine wp_unroll_group (fun Jq hJq => ?_)
                  have hJqOk : ∀ (qsi' qss' : BitVec 64) (m_q : Mem 64),
                      (FullMem c { st_uf with scratch :=
                        { st.scratch with q_search_idx := qsi', q_search_stamp := qss' } } ⋆ R)
                        m_q →
                      Jq () m_q := by
                    intro qsi' qss' m_q hm_q
                    refine hJq () m_q ?_
                    bt_steps_nogrp
                    exact hPostPushOk { st_uf with scratch :=
                        { st.scratch with q_search_idx := qsi', q_search_stamp := qss' } }
                      m_q rfl
                      ⟨hlen_uf.core_ok, bt_lengthsOk_qsearch qsi' qss' hlen_uf.scratch_ok⟩
                      ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                      ⟨st.scratch.heap, st.scratch.pos, st.scratch.heap_len, qsi', qss', rfl⟩
                      hm_q
                  clear hJq
                  have hqlen : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat <
                      st_uf.scratch.q_stamp.length := by
                    rw [bt_bv32_ushr1, htrl_val, hlen_uf.scratch_ok.q_stamp_len]
                    have := hlen1.core_ok.cur_vars_le; omega
                  bt_steps_nogrp
                  refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
                  · bt_steps_nogrp
                    exact hJqOk _ _ _ (by dsimp only; assumption)
                  · exact hJqOk _ _ _ (by dsimp only; assumption)
              clear hJflags
              have hflen : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat <
                  st_u.core.flags.length := by
                rw [bt_bv32_ushr1, htrl_val, hlen_u.core_ok.flags_len]
                have := hlen1.core_ok.cur_vars_le; omega
              bt_steps_nogrp
              refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
              · bt_steps_nogrp
                exact hFlagsOk (st.core.unassigned + 1#64) _
                  (by dsimp only [st_u]
                      simpa only [htrl_get, bt_bv32_ushr1, bt_bv32_xor1, bv64_zext32_toNat'] using
                        (by assumption))
              · exact hFlagsOk st.core.unassigned _
                  (by dsimp only [st_u]
                      simpa only [htrl_get, bt_bv32_ushr1, bt_bv32_xor1, bv64_zext32_toNat'] using
                        (by assumption))
            · have h1 := bv64_ult_false_le' hnv
              rw [bv64_ofNat_toNat' hcv64, bv64_zext32_toNat', bt_bv32_ushr_one, htrl_val] at h1
              · exfalso; omega
              · rfl
          clear hJunass
          bt_steps_nogrp
          refine wp_jnz_of (fun _ => ?_) (fun hnv => ?_)
          · have hv_llen : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat <
                st.core.lvl.length := by
              rw [bt_bv32_ushr1, htrl_val, hinv.len_ok.core_ok.lvl_len]
              have := hlen1.core_ok.cur_vars_le; omega
            have h_lvl_eq : ∀ {y : Nat} (_ : y = 1) (hp : (BitVec.setWidth 64
                (st.core.trl[i_bv.toNat] >>> y)).toNat < st.core.lvl.length),
                st.core.lvl[(BitVec.setWidth 64 (st.core.trl[i_bv.toNat] >>> y)).toNat]'hp =
                  st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 := by
              intro y hy hp
              have hid : (BitVec.setWidth 64 (st.core.trl[i_bv.toNat] >>> y)).toNat =
                  (st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2 := by
                rw [bv64_zext32_toNat', bt_bv32_ushr_one _ hy, htrl_get]
              have hopt : st.core.lvl[(BitVec.setWidth 64 (st.core.trl[i_bv.toNat] >>> y)).toNat]? =
                  st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]? := by rw [hid]
              rw [← hopt, List.getElem?_eq_getElem hp, Option.getD_some]
            bt_steps_nogrp
            refine wp_jnz_of (fun hle_bv => ?_) (fun hnle_bv => ?_)
            · have hle_n : (st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
                  0#32).toNat ≤ target_lvl.toNat := by
                have h1 := bv64_ule_true_le' hle_bv
                rw [h_lvl_eq] at h1
                · exact h1
                · rfl
              have hkeep_lt_trl : keep_bv.toNat < st.core.trl.length := by
                have := hinv.keep_le_i; have := hte_eq
                have := hinv.len_ok.core_ok.trail_end_le
                have := hinv.len_ok.core_ok.cur_vars_le
                have := hinv.len_ok.core_ok.trl_len; omega
              have hv_tplen : (st.core.trl[i_bv.toNat] >>> (1 : BitVec 32)).toNat <
                  st.core.trail_pos.length := by
                rw [bt_bv32_ushr1, htrl_val, hinv.len_ok.core_ok.trail_pos_len]
                have := hlen1.core_ok.cur_vars_le; omega
              bt_steps_nogrp
              exact hNextOk (keep_bv + 1#64) _ _ (bt_inv_step_keep hinv hlen1 hi_nat
                (by simpa only [hcore1_eq] using htrl_bd) hle_n
                (by dsimp only
                    simpa only [htrl_get, bt_bv32_ushr1, bv64_zext32_toNat'] using
                      (by assumption)))
            · have hgt_n : ¬ (st.core.lvl[(st.core.trl[i_bv.toNat]?.getD 0#32).toNat / 2]?.getD
                  0#32).toNat ≤ target_lvl.toNat := by
                have h1 := bv64_ule_false_lt' hnle_bv
                rw [h_lvl_eq, bv64_zext32_toNat'] at h1
                · omega
                · rfl
              bt_steps_nogrp
              exact hUnassOk hgt_n
          · have h1 := bv64_ult_false_le' hnv
            rw [bv64_ofNat_toNat' hcv64, bv64_zext32_toNat', bt_bv32_ushr_one, htrl_val] at h1
            · exfalso; omega
            · rfl
        · have hi_ge : s1.core.trail_end ≤ i_bv.toNat := by
            have h1 := bv64_ult_false_le' hi_nlt
            rwa [bv64_ofNat_toNat' hte_64, hte_eq] at h1
          have hte_s1_64 : s1.core.trail_end < 2 ^ 64 := hte_eq ▸ hte_64
          have hi_eq : i_bv = BitVec.ofNat 64 s1.core.trail_end := by
            apply BitVec.eq_of_toNat_eq
            rw [bv64_ofNat_toNat' hte_s1_64]
            have := hinv.i_le_te; omega
          subst hi_eq
          have hkeep_lt64 : keep_bv.toNat < 2 ^ 64 := by
            have := hinv.keep_le_i; have := hinv.i_le_te
            rw [bv64_ofNat_toNat' hte_s1_64] at this; omega
          have hprop64 : st.core.propagated < 2 ^ 64 := by
            have := hinv.len_ok.core_ok.propagated_le
            have := hinv.len_ok.core_ok.trail_end_le
            have := hinv.len_ok.core_ok.cur_vars_le; omega
          bt_steps_nogrp
          refine wp_unroll_group (fun JpropQ hJpropQ => ?_)
          have hPropQOk : ∀ (prop_mid : Nat) (m_mid : Mem 64),
              prop_mid ≤ keep_bv.toNat →
              (FullMem c { st with core := { st.core with
                trail_end := keep_bv.toNat, propagated := prop_mid } } ⋆ R) m_mid →
              JpropQ () m_mid := by
            intro prop_mid m_mid hpm_le hm_mid
            refine hJpropQ () m_mid ?_
            refine wp_unroll_group (fun Jprop hJprop => ?_)
            have hPropOk : ∀ (prop_fin : Nat) (m_fin : Mem 64),
                prop_fin ≤ keep_bv.toNat →
                (FullMem c { st with core := { st.core with
                  trail_end := keep_bv.toNat, propagated := prop_fin } } ⋆ R) m_fin →
                Jprop () m_fin := by
              intro prop_fin m_fin hpf_le hm_fin
              refine hJprop () m_fin ?_
              bt_steps_nogrp
              exact bt_inv_finish (q_start := q_start) (st := st) hcore1_eq hpres1
                ⟨ta1, ba1, pt1, pb1, hsc1⟩ hcl_lt hlen rfl hinv hpf_le
                (by dsimp only; assumption) hPost
            clear hJprop
            bt_steps_nogrp
            refine wp_jnz_of (fun _ => ?_) (fun hnugt => ?_)
            · bt_steps_nogrp
              exact hPropOk keep_bv.toNat _ (Nat.le_refl _) (by dsimp only; assumption)
            · have hpm64 : prop_mid < 2 ^ 64 := by omega
              have h1 := bv64_ult_false_le' hnugt
              rw [bv64_ofNat_toNat' hpm64] at h1
              exact hPropOk prop_mid _ hpm_le (by dsimp only; assumption)
          clear hJpropQ
          bt_steps_nogrp
          refine wp_jnz_of (fun _ => ?_) (fun hnugt => ?_)
          · bt_steps_nogrp
            exact hPropQOk q_bv.toNat _ (by rw [hq_eq]; exact hinv.qs_le_keep)
              (by dsimp only; assumption)
          · have h1 := bv64_ult_false_le' hnugt
            rw [bv64_ofNat_toNat' hprop64, hq_eq] at h1
            exact hPropQOk st.core.propagated _ (Nat.le_trans h1 hinv.qs_le_keep)
              (by dsimp only; assumption)
    clear hJqs
    bt_steps_nogrp
    refine wp_jnz_of (fun hgt => ?_) (fun hngt => ?_)
    · bt_steps_nogrp
      have h1 := bv64_ult_true_lt' hgt
      have hte_s1_64 : s1.core.trail_end < 2 ^ 64 := by
        have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
        have := hlen.core_ok.trail_end_le; have := hlen.core_ok.cur_vars_le; rw [hcore1_eq]; omega
      have h_idx : (target_lvl + (1 : BitVec 64)).toNat = target_lvl.toNat + 1 := htv_add1
      have hft_idx' : (target_lvl + (1 : BitVec 64)).toNat < s1.core.frame_trail.length := hft_idx
      have hget_opt : s1.core.frame_trail[target_lvl.toNat + 1]? =
          s1.core.frame_trail[(target_lvl + (1 : BitVec 64)).toNat]? := by rw [h_idx]
      have hget : s1.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32 =
          s1.core.frame_trail[(target_lvl + (1 : BitVec 64)).toNat]'hft_idx' := by
        rw [hget_opt, List.getElem?_eq_getElem hft_idx', Option.getD_some]
      rw [bv64_ofNat_toNat' hte_s1_64, bv64_zext32_toNat', ← hget, hcore1_eq] at h1
      have hqs_eq : (BitVec.ofNat 64 s1.core.trail_end).toNat = q_start := by
        rw [bv64_ofNat_toNat' hte_s1_64, hcore1_eq]
        exact (Nat.min_eq_right (Nat.le_of_lt h1)).symm
      exact hLoopEntry _ _ hqs_eq hm1
    · bt_steps_nogrp
      have h1 := bv64_ult_false_le' hngt
      have hte_s1_64 : s1.core.trail_end < 2 ^ 64 := by
        have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
        have := hlen.core_ok.trail_end_le; have := hlen.core_ok.cur_vars_le; rw [hcore1_eq]; omega
      have h_idx : (target_lvl + (1 : BitVec 64)).toNat = target_lvl.toNat + 1 := htv_add1
      have hft_idx' : (target_lvl + (1 : BitVec 64)).toNat < s1.core.frame_trail.length := hft_idx
      have hget_opt : s1.core.frame_trail[target_lvl.toNat + 1]? =
          s1.core.frame_trail[(target_lvl + (1 : BitVec 64)).toNat]? := by rw [h_idx]
      have hget : s1.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32 =
          s1.core.frame_trail[(target_lvl + (1 : BitVec 64)).toNat]'hft_idx' := by
        rw [hget_opt, List.getElem?_eq_getElem hft_idx', Option.getD_some]
      rw [bv64_ofNat_toNat' hte_s1_64, bv64_zext32_toNat', ← hget, hcore1_eq] at h1
      have hqs_eq : ((s1.core.frame_trail[(target_lvl + (1 : BitVec 64)).toNat]'hft_idx').setWidth
          64).toNat = q_start := by
        rw [bv64_zext32_toNat', ← hget, hcore1_eq]
        exact (Nat.min_eq_left h1).symm
      exact hLoopEntry _ _ hqs_eq hm1

end LeanQbe.T.Examples.Kissat.Proof.Backtrack

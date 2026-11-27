/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Backtrack Witness Lemmas (`Proof.Backtrack.WitnessLemmas`)

Shared pure BitVec and `FullWitnessInv` / `FullOtfsWitnessInv` preservation lemmas
for `LeanQbe.T.Examples.Kissat.Proof.Backtrack`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backtrack

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. Pure BitVec & Trail-Backtrack Witness Helpers -/

theorem bv64_ofNat_toNat' {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv64_add1_toNat' {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

theorem bv64_ule_true_le' {a b : BitVec 64} (h : a.ule b = true) :
    a.toNat ≤ b.toNat := by
  rw [BitVec.ule_iff_le] at h
  exact h

theorem bv64_ult_true_lt' {a b : BitVec 64} (h : a.ult b = true) :
    a.toNat < b.toNat := by
  rw [BitVec.ult_iff_lt] at h
  exact h

theorem bv64_ule_false_lt' {a b : BitVec 64} (h : a.ule b = false) :
    b.toNat < a.toNat := by
  have h1 : ¬ (a.ule b = true) := by simp [h]
  rw [BitVec.ule_iff_le] at h1
  have h2 : ¬ a.toNat ≤ b.toNat := fun hle => h1 hle
  omega

theorem bv64_ult_false_le' {a b : BitVec 64} (h : a.ult b = false) :
    b.toNat ≤ a.toNat := by
  have h1 : ¬ (a.ult b = true) := by simp [h]
  rw [BitVec.ult_iff_lt] at h1
  have h2 : ¬ a.toNat < b.toNat := fun hlt => h1 hlt
  omega

theorem bv32_xor1_toNat' (x : BitVec 32) :
    (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_lshr_nat1' (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_zext32_toNat' (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem bt_nat_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  rw [nat_xor1_eq]; split <;> omega

private theorem bt_nat_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := by
  simp only [nat_xor1_eq]
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm
  · have hm1 : (l + 1) % 2 = 1 := by omega
    simp [hm, hm1]
  · have hm1 : (l - 1) % 2 = 0 := by omega
    simp [hm, hm1]; omega

private theorem bt_pairwise_lt_range (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    exact ⟨ih, List.pairwise_singleton _ _, fun a ha _ hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact List.mem_range.mp ha⟩

private theorem bt_pairwise_lt_map_succ_nodup :
    ∀ {l : List Nat}, l.Pairwise (· < ·) → (l.map (· + 1)).Nodup
  | [], _ => List.nodup_nil
  | _ :: xs, h => by
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, bt_pairwise_lt_map_succ_nodup h.2⟩
    rw [List.mem_map] at hmem
    rcases hmem with ⟨y, hy, hy_eq⟩
    have := h.1 y hy
    omega

private theorem bt_nodup_subset_len :
    ∀ (l1 l2 : List Nat), l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l2, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ l2 := hsub x List.mem_cons_self
    have hxs : ∀ y ∈ xs, y ∈ l2.erase x := fun y hy =>
      (List.mem_erase_of_ne (fun he => by subst he; exact hnd.1 hy)).mpr
        (hsub y (List.mem_cons_of_mem _ hy))
    have hle := bt_nodup_subset_len xs (l2.erase x) hnd.2 hxs
    have hlen : (l2.erase x).length = l2.length - 1 := List.length_erase_of_mem hx
    have hpos : 0 < l2.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

private theorem bt_nodup_card_le {n m : Nat} (g : Nat → Nat)
    (hg : ∀ L, 1 ≤ L → L ≤ n → ∃ i < m, g i = L) : n ≤ m := by
  suffices h : ∀ (ks : List Nat), ks.Nodup → (∀ k ∈ ks, 1 ≤ k ∧ k ≤ n) →
      ∃ is : List Nat, is.Nodup ∧ is.length = ks.length ∧
        (∀ i ∈ is, i < m ∧ g i ∈ ks) by
    obtain ⟨is, hnd, hlen, hlt⟩ :=
      h ((List.range n).map (· + 1))
        (bt_pairwise_lt_map_succ_nodup (bt_pairwise_lt_range n))
        (fun k hk => by
          simp only [List.mem_map, List.mem_range] at hk
          rcases hk with ⟨j, hj, rfl⟩; omega)
    have hsub : ∀ i ∈ is, i ∈ List.range m := fun i hi => List.mem_range.mpr (hlt i hi).1
    have hle := bt_nodup_subset_len is (List.range m) hnd hsub
    simp only [List.length_range, List.length_map] at hle hlen
    omega
  intro ks hnd hmem
  induction ks with
  | nil => exact ⟨[], List.nodup_nil, rfl, fun _ h => by cases h⟩
  | cons k ks ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨is, hnd_is, hlen_is, hlt_is⟩ :=
      ih hnd.2 (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    obtain ⟨i0, hi0_lt, hi0_eq⟩ :=
      hg k (hmem k List.mem_cons_self).1 (hmem k List.mem_cons_self).2
    have hi0_not : i0 ∉ is := fun hin => hnd.1 (hi0_eq ▸ (hlt_is i0 hin).2)
    refine ⟨i0 :: is, List.nodup_cons.mpr ⟨hi0_not, hnd_is⟩, by simp [hlen_is], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hi0_lt, List.mem_cons.mpr (Or.inl hi0_eq)⟩
    · exact ⟨(hlt_is x hx).1, List.mem_cons_of_mem _ (hlt_is x hx).2⟩

private theorem bt_list_take_eq_map_range {α : Type} [Inhabited α] (xs : List α) {n : Nat}
    (hn : n ≤ xs.length) :
    xs.take n = (List.range n).map (fun i => xs[i]?.getD default) := by
  apply List.ext_getElem
  · simp [List.length_take, hn]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem bt_drop_map {α β : Type} (f : α → β) :
    ∀ (k : Nat) (xs : List α), List.drop k (xs.map f) = (List.drop k xs).map f
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: xs => bt_drop_map f k xs

private theorem bt_range_split {n q : Nat} (hq : q ≤ n) :
    List.range n = List.range q ++ (List.range n).drop q := by
  exact (List.take_append_drop q (List.range n)).symm |>.trans (by
    congr 1
    apply List.ext_getElem
    · simp [List.length_range, hq]
    · intro i h1 h2; simp [List.getElem_range])

private theorem bt_filter_map {α β : Type} (xs : List α) (f : α → β) (p : β → Bool) :
    (xs.map f).filter p = (xs.filter (fun x => p (f x))).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    split <;> simp [ih]

private theorem bt_pairwise_filter_lt {xs : List Nat} (hp : xs.Pairwise (· < ·)) (p : Nat → Bool) :
    (xs.filter p).Pairwise (· < ·) :=
  hp.sublist (List.filter_sublist)

private theorem bt_pairwise_lt_getElem {xs : List Nat} (hp : xs.Pairwise (· < ·)) :
    ∀ a b (ha : a < xs.length) (hb : b < xs.length), a < b → xs[a] < xs[b] := by
  induction xs with
  | nil => intro a b ha; simp at ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at hp
    intro a b ha hb hab
    cases a with
    | zero =>
      cases b with
      | zero => omega
      | succ b => exact hp.1 _ (List.getElem_mem _)
    | succ a =>
      cases b with
      | zero => omega
      | succ b => exact ih hp.2 a b (by simp at ha; omega) (by simp at hb; omega) (by omega)

theorem bt_nochange_vals_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {target_lvl l : Nat}
    (hw : FullOtfsWitnessInv c F0 F_cur k) (hcle : k.cur_level ≤ target_lvl)
    (hl : l < 2 * k.cur_vars) (hgt : target_lvl < (k.lvl[l / 2]?.getD 0#32).toNat) :
    k.vals[l]?.getD 0#8 = 0#8 := by
  rcases hw.vals_domain l hl with h0 | h1 | h255
  · exact h0
  · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
    have hlv := hw.lvl_le i hi
    rw [heq] at hlv; omega
  · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h255
    have hlv := hw.lvl_le i hi
    rw [heq, bt_nat_xor1_div2] at hlv; omega

theorem bt_fullProbeScratchPres_refl (s : FullState) :
    FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bt_lengthsOk_with_probing {c : FullCfg} {s : FullState} (p : BitVec 64)
    (h : FullState.LengthsOk c s) :
    FullState.LengthsOk c ⟨{ s.core with probing := p }, s.scratch⟩ :=
  ⟨by cases h.core_ok; constructor <;> assumption, h.scratch_ok⟩

theorem bt_witness_nochange_vals_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {target_lvl l : Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hcle : k.cur_level ≤ target_lvl)
    (hl : l < 2 * k.cur_vars) (hgt : target_lvl < (k.lvl[l / 2]?.getD 0#32).toNat) :
    k.vals[l]?.getD 0#8 = 0#8 := by
  rcases hw.vals_domain l hl with h0 | h1 | h255
  · exact h0
  · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
    have hlv := hw.lvl_le i hi
    rw [heq] at hlv; omega
  · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h255
    have hlv := hw.lvl_le i hi
    rw [heq, bt_nat_xor1_div2] at hlv; omega

theorem bt_fullProbeScratchPres_trans {s1 s2 s3 : FullState}
    (h12 : FullProbeScratchPres s1 s2) (h23 : FullProbeScratchPres s2 s3) :
    FullProbeScratchPres s1 s3 :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩,
   h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

theorem bt_otfsWitness_with_probing {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (p : BitVec 64)
    (hw : FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur { k with probing := p } :=
  { ext_sound := hw.ext_sound
    inconsistent_sound := hw.inconsistent_sound
    arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
      hw.arena.lits_lt, hw.arena.entails⟩
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
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
    reason_inv_below := hw.reason_inv_below
    reason_lit_mem_below := hw.reason_lit_mem_below }

theorem bt_witness_with_probing {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (p : BitVec 64)
    (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with probing := p } :=
  { ext_sound := hw.ext_sound
    inconsistent_sound := hw.inconsistent_sound
    arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
      hw.arena.lits_lt, hw.arena.entails⟩
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
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
    reason_inv := hw.reason_inv
    reason_lit_mem := hw.reason_lit_mem }

theorem bt_otfs_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {target_lvl : Nat}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core) (hlt : target_lvl < s.core.cur_level)
    (hs' : s'.core.cur_vars = s.core.cur_vars)
    (hinc : s'.core.inconsistent = s.core.inconsistent)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hwv : s'.core.wvec = s.core.wvec) (hws : s'.core.wstk = s.core.wstk)
    (hwl : s'.core.wlen = s.core.wlen)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hftr : s'.core.frame_trail = s.core.frame_trail) (hfdec : s'.core.frame_dec = s.core.frame_dec)
    (hcle : s'.core.cur_level = target_lvl)
    (hlen_s : s.LengthsOk c) (_hlen' : s'.LengthsOk c)
    (htrl_eq : ∀ i < s'.core.trail_end, (s'.core.trl[i]?.getD 0#32).toNat =
      (have q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
      have keptTail := List.filter
        (fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl))
        (List.drop q_start (List.take s.core.trail_end s.core.trl))
      ((List.take q_start s.core.trl ++ keptTail)[i]?.getD 0#32).toNat))
    (hte_eq : s'.core.trail_end =
      (have q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
      have keptTail := List.filter
        (fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl))
        (List.drop q_start (List.take s.core.trail_end s.core.trl))
      (List.take q_start s.core.trl ++ keptTail).length))
    (hvals_eq : ∀ l < 2 * s.core.cur_vars, s'.core.vals[l]?.getD 0#8 =
      if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl then s.core.vals[l]?.getD 0#8 else 0#8)
    (hlvl_eq : ∀ i < s.core.trail_end,
      let v := (s.core.trl[i]?.getD 0#32).toNat / 2
      s'.core.lvl[v]?.getD 0#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then s.core.lvl[v]?.getD 0#32 else 0#32)
    (hrsns_eq : ∀ i < s.core.trail_end,
      let v := (s.core.trl[i]?.getD 0#32).toNat / 2
      s'.core.rsns[v]?.getD 4294967295#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then
          s.core.rsns[v]?.getD 4294967295#32
        else 4294967295#32)
    (htp_inv : ∀ i < s'.core.trail_end,
      (s'.core.trail_pos[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i) :
    FullWitnessInv c F0 F_cur s'.core := by
  have hcl := hlen_s.core_ok
  have hte_le_trl : s.core.trail_end ≤ s.core.trl.length :=
    Nat.le_trans hcl.trail_end_le (Nat.le_trans hcl.cur_vars_le (Nat.le_of_eq hcl.trl_len.symm))
  have hqs_le : min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end ≤
      s.core.trail_end := Nat.min_le_right _ _
  have hqs_eq : min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end =
      (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat :=
    Nat.min_eq_left (hw.frame_trail_lt (target_lvl + 1) (by omega))
  let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
  let keptPred : BitVec 32 → Bool :=
    fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
  let keptList := List.take q_start s.core.trl ++
    List.filter keptPred (List.drop q_start (List.take s.core.trail_end s.core.trl))
  let f_idxs : List Nat := List.range q_start ++
    ((List.range s.core.trail_end).drop q_start).filter
      (fun idx => keptPred (s.core.trl[idx]?.getD 0#32))
  have htake_eq : List.take s.core.trail_end s.core.trl =
      (List.range s.core.trail_end).map (fun i => s.core.trl[i]?.getD 0#32) :=
    bt_list_take_eq_map_range s.core.trl hte_le_trl
  have hq_take : List.take q_start s.core.trl =
      (List.range q_start).map (fun i => s.core.trl[i]?.getD 0#32) :=
    bt_list_take_eq_map_range s.core.trl (Nat.le_trans hqs_le hte_le_trl)
  have hdrop_take : List.drop q_start (List.take s.core.trail_end s.core.trl) =
      ((List.range s.core.trail_end).drop q_start).map (fun i => s.core.trl[i]?.getD 0#32) := by
    rw [htake_eq, bt_drop_map]
  have hkept_map : keptList = f_idxs.map (fun i => s.core.trl[i]?.getD 0#32) := by
    dsimp only [keptList, f_idxs]
    rw [hq_take, hdrop_take, bt_filter_map, List.map_append]
  have hf_len : f_idxs.length = s'.core.trail_end := by
    have h_eq : s'.core.trail_end = keptList.length := hte_eq
    rw [hkept_map, List.length_map] at h_eq
    exact h_eq.symm
  have hf_pw : f_idxs.Pairwise (· < ·) := by
    have h1 : (List.range q_start ++ ((List.range s.core.trail_end).drop q_start)).Pairwise
        (· < ·) := by
      rw [← bt_range_split hqs_le]; exact bt_pairwise_lt_range _
    rw [List.pairwise_append] at h1 ⊢
    refine ⟨h1.1, bt_pairwise_filter_lt h1.2.1 _,
      fun a ha b hb => h1.2.2 a ha b (List.mem_filter.mp hb).1⟩
  have hf_mono : ∀ a b (ha : a < s'.core.trail_end) (hb : b < s'.core.trail_end),
      a < b → f_idxs[a]'(by omega) < f_idxs[b]'(by omega) := fun a b ha hb hab =>
    bt_pairwise_lt_getElem hf_pw a b (by omega) (by omega) hab
  have hf_mem_iff : ∀ idx, idx ∈ f_idxs ↔ idx < s.core.trail_end ∧
      (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl := by
    intro idx
    dsimp only [f_idxs]
    rw [List.mem_append, List.mem_filter, List.mem_range]
    constructor
    · rintro (hq | ⟨hd, hk⟩)
      · refine ⟨by omega, ?_⟩
        have hb := hw.frame_trail_before_lt (target_lvl + 1) (by omega) (by omega) idx
          (by rw [← hqs_eq]; exact hq)
        omega
      · have hr : idx ∈ List.range s.core.trail_end := List.mem_of_mem_drop hd
        rw [List.mem_range] at hr
        simp only [keptPred, decide_eq_true_eq] at hk
        exact ⟨hr, hk⟩
    · rintro ⟨hlt_idx, hlv_le⟩
      by_cases hq : idx < q_start
      · exact Or.inl hq
      · right
        refine ⟨?_, by simp [keptPred, hlv_le]⟩
        rw [List.mem_iff_getElem]
        refine ⟨idx - q_start, by simp [List.length_drop, List.length_range]; omega, ?_⟩
        simp [List.getElem_drop, List.getElem_range]; omega
  have hf_elem : ∀ i (hi : i < s'.core.trail_end),
      (s'.core.trl[i]?.getD 0#32).toNat =
        (s.core.trl[f_idxs[i]'(by omega)]?.getD 0#32).toNat := fun i hi => by
    have ht := htrl_eq i hi
    dsimp only at ht
    have heq : keptList[i]?.getD 0#32 = s.core.trl[f_idxs[i]'(by omega)]?.getD 0#32 := by
      rw [hkept_map, List.getElem?_eq_getElem (by rw [List.length_map]; omega),
        Option.getD_some, List.getElem_map]
    exact ht.trans (congrArg BitVec.toNat heq)
  have hf_get_spec : ∀ i (hi : i < s'.core.trail_end),
      f_idxs[i]'(by omega) < s.core.trail_end ∧
        (s.core.lvl[(s.core.trl[f_idxs[i]'(by omega)]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          target_lvl :=
    fun i hi => (hf_mem_iff _).mp (List.getElem_mem _)
  have hf_lvl_eq : ∀ i (hi : i < s'.core.trail_end),
      s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
        s.core.lvl[(s.core.trl[f_idxs[i]'(by omega)]?.getD 0#32).toNat / 2]?.getD 0#32 := by
    intro i hi
    have hs := hf_get_spec i hi
    rw [hf_elem i hi, hlvl_eq _ hs.1]
    simp only [hs.2, ite_true]
  have hf_rsns_eq : ∀ i (hi : i < s'.core.trail_end),
      s'.core.rsns[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 4294967295#32 =
        s.core.rsns[(s.core.trl[f_idxs[i]'(by omega)]?.getD 0#32).toNat / 2]?.getD
          4294967295#32 := by
    intro i hi
    have hs := hf_get_spec i hi
    rw [hf_elem i hi, hrsns_eq _ hs.1]
    simp only [hs.2, ite_true]
  have hf_find : ∀ idx, idx < s.core.trail_end →
      (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl →
      ∃ i, ∃ (hi : i < s'.core.trail_end), f_idxs[i]'(by omega) = idx := by
    intro idx hidx hlv
    have hm : idx ∈ f_idxs := (hf_mem_iff idx).mpr ⟨hidx, hlv⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hm
    exact ⟨i, by omega, heq⟩
  have harena' : FullArenaClausesInv c F_cur s'.core :=
    ⟨hal ▸ hw.arena.len_ok,
     fun r hr => by
       have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
         unfold fullArenaClauseRefsCore at hr ⊢; rwa [har, hal] at hr
       simpa only [fullArenaClauseSizeCore, fullArenaNextOff, har, hal] using
         hw.arena.refs_wf r hr0,
     fun r hr hsh => by
       have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
         unfold fullArenaClauseRefsCore at hr ⊢; rwa [har, hal] at hr
       have hsh0 : fullArenaHdrCore s.core r &&& 8388608#32 ≠ 0#32 := by
         unfold fullArenaHdrCore at hsh ⊢; rwa [har] at hsh
       simpa only [fullArenaClauseSizeCore, har, hal] using hw.arena.shrk_term r hr0 hsh0,
     fun r hr hng l hl => by
       have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
         unfold fullArenaClauseRefsCore at hr ⊢; rwa [har, hal] at hr
       have hng0 : fullArenaClauseGarbCore s.core r = false := by
         unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; rwa [har] at hng
       have hl0 : l ∈ fullArenaClauseLitsCore s.core r := by
         unfold fullArenaClauseLitsCore fullArenaClauseSizeCore at hl ⊢; rwa [har] at hl
       rw [hs']; exact hw.arena.lits_lt r hr0 hng0 l hl0,
     fun r hr hng => by
       have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
         unfold fullArenaClauseRefsCore at hr ⊢; rwa [har, hal] at hr
       have hng0 : fullArenaClauseGarbCore s.core r = false := by
         unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; rwa [har] at hng
       have he := hw.arena.entails r hr0 hng0
       simpa only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using he⟩
  have hwat' : ModeWatchesInv F_cur s'.core :=
    hw.watches.with_wstk hdm hs' hwv hws hwl fun r hr => by
      unfold fullArenaClauseRefsCore at hr ⊢; rwa [har, hal]
  have hlevels' : ∀ L, 1 ≤ L → L ≤ s'.core.cur_level →
      ∃ i < s'.core.trail_end,
        (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := by
    intro L hL1 hL2
    rw [hcle] at hL2
    obtain ⟨idx, hidx, hlv⟩ := hw.levels_inhabited L hL1 (by omega)
    obtain ⟨i, hi, rfl⟩ := hf_find idx hidx (by omega)
    exact ⟨i, hi, by rw [hf_lvl_eq i hi]; exact hlv⟩
  exact
    { ext_sound := hs' ▸ hw.ext_sound
      inconsistent_sound := hinc ▸ hw.inconsistent_sound
      arena := harena'
      watches := hwat'
      cur_level_le := by
        rw [hcle]
        exact bt_nodup_card_le
          (fun i => (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
          (fun L h1 h2 => hlevels' L h1 (by rw [hcle]; exact h2))
      trail_lits_lt := fun i hi => by
        rw [hs', hf_elem i hi]; exact hw.trail_lits_lt _ (hf_get_spec i hi).1
      trail_vars_nodup := fun i j hi hj heq => by
        rw [hf_elem i hi, hf_elem j hj] at heq
        have hij := hw.trail_vars_nodup _ _ (hf_get_spec i hi).1 (hf_get_spec j hj).1 heq
        refine Classical.byContradiction (fun hne => ?_)
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := hf_mono i j hi hj h; omega
        · have := hf_mono j i hj hi h; omega
      vals_domain := fun l hl => by
        rw [hs'] at hl; rw [hvals_eq l hl]
        split
        · exact hw.vals_domain l hl
        · exact Or.inl rfl
      vals_true_iff := fun l hl => by
        rw [hs'] at hl; rw [hvals_eq l hl]
        constructor
        · intro h1
          split at h1
          · rename_i hlv
            obtain ⟨idx, hidx, heq⟩ := (hw.vals_true_iff l hl).mp h1
            obtain ⟨i, hi, rfl⟩ := hf_find idx hidx (by rwa [heq])
            exact ⟨i, hi, (hf_elem i hi).trans heq⟩
          · cases h1
        · rintro ⟨i, hi, heq⟩
          have hs := hf_get_spec i hi
          rw [hf_elem i hi] at heq
          have hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl := by
            rw [← heq]; exact hs.2
          simp only [hlv, ite_true]
          exact (hw.vals_true_iff l hl).mpr ⟨_, hs.1, heq⟩
      vals_false_iff := fun l hl => by
        rw [hs'] at hl; rw [hvals_eq l hl]
        constructor
        · intro h1
          split at h1
          · rename_i hlv
            obtain ⟨idx, hidx, heq⟩ := (hw.vals_false_iff l hl).mp h1
            have heq' : (s.core.trl[idx]?.getD 0#32).toNat / 2 = l / 2 := by
              rw [heq, bt_nat_xor1_div2]
            obtain ⟨i, hi, rfl⟩ := hf_find idx hidx (by rwa [heq'])
            exact ⟨i, hi, (hf_elem i hi).trans heq⟩
          · cases h1
        · rintro ⟨i, hi, heq⟩
          have hs := hf_get_spec i hi
          rw [hf_elem i hi] at heq
          have hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl := by
            rw [← bt_nat_xor1_div2 l, ← heq]; exact hs.2
          simp only [hlv, ite_true]
          exact (hw.vals_false_iff l hl).mpr ⟨_, hs.1, heq⟩
      lvl_le := fun i hi => by
        rw [hcle, hf_lvl_eq i hi]; exact (hf_get_spec i hi).2
      dec_earliest := fun i j hi hj hlv_eq ⟨hpos, hrsn⟩ => by
        rw [hf_lvl_eq i hi, hf_lvl_eq j hj] at hlv_eq
        rw [hf_lvl_eq j hj] at hpos
        rw [hf_rsns_eq j hj] at hrsn
        have hij := hw.dec_earliest _ _ (hf_get_spec i hi).1 (hf_get_spec j hj).1
          hlv_eq ⟨hpos, hrsn⟩
        refine Classical.byContradiction (fun hlt_ji => ?_)
        have h1 : i < j := by omega
        have := hf_mono i j hi hj h1
        omega
      levels_inhabited := hlevels'
      level0_sound := fun i hi hlv0 => by
        rw [hf_lvl_eq i hi] at hlv0
        rw [hf_elem i hi]
        exact hw.level0_sound _ (hf_get_spec i hi).1 hlv0
      trail_pos_inv := htp_inv
      level0_rsn_none := fun idx hidx hlv0 => by
        rw [hf_lvl_eq idx hidx] at hlv0
        rw [hf_rsns_eq idx hidx]
        exact hw.level0_rsn_none _ (hf_get_spec idx hidx).1 hlv0
      frame_trail_lt := fun L hL => by
        rw [hftr]
        rw [hcle] at hL
        have hm := hw.frame_trail_mono L (target_lvl + 1) (by omega) (by omega)
        have hlen_c : keptList.length = s'.core.trail_end := by rw [hte_eq]
        have hqs_trl : q_start ≤ s.core.trl.length := Nat.le_trans hqs_le hte_le_trl
        have hlen_k : q_start ≤ keptList.length := by simp [keptList, List.length_take, hqs_trl]
        omega
      frame_trail_mono := fun L1 L2 h12 h2 => by
        rw [hftr]; rw [hcle] at h2; exact hw.frame_trail_mono L1 L2 h12 (by omega)
      frame_trail_before_lt := fun L h1 h2 i hi => by
        rw [hftr] at hi
        rw [hcle] at h2
        have hm := hw.frame_trail_mono L (target_lvl + 1) (by omega) (by omega)
        have hlen_c : keptList.length = s'.core.trail_end := by rw [hte_eq]
        have hqs_trl : q_start ≤ s.core.trl.length := Nat.le_trans hqs_le hte_le_trl
        have hlen_k : q_start ≤ keptList.length := by simp [keptList, List.length_take, hqs_trl]
        have hi_qs : i < q_start := by omega
        have hf_i : f_idxs[i]'(by omega) = i := by
          dsimp only [f_idxs]
          rw [List.getElem_append_left (by simp [hi_qs])]
          simp
        rw [hf_lvl_eq i (by omega), hf_i]
        exact hw.frame_trail_before_lt L h1 (by omega) i hi
      frame_dec_lt := fun L h1 h2 => by
        rw [hfdec, hs']; rw [hcle] at h2; exact hw.frame_dec_lt L h1 (by omega)
      reason_inv := fun idx hidx hne => by
        have hspec := hf_get_spec idx hidx
        rw [hf_rsns_eq idx hidx] at hne
        have hlt_cur : (s.core.lvl[(s.core.trl[f_idxs[idx]'(by omega)]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat < s.core.cur_level := by omega
        have hr := hw.reason_inv_below _ hspec.1 hlt_cur hne
        dsimp only at hr ⊢
        rw [hf_rsns_eq idx hidx, hf_elem idx hidx]
        split at hr <;> split
        · rename_i hmask _
          refine ⟨hs' ▸ hr.1, ?_, ?_⟩
          · have : (s'.core.arena = s.core.arena) := har; exact hr.2.1
          · obtain ⟨m0, hm0_lt, hm0_eq, hm0_lv⟩ := hr.2.2
            have hm0_le : (s.core.lvl[(s.core.trl[m0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                target_lvl := by
              rw [hm0_eq, bt_nat_xor1_div2]; omega
            obtain ⟨m, hm, hm_eq⟩ := hf_find m0 (by omega) hm0_le
            refine ⟨m, ?_, (hf_elem m hm).trans (hm_eq ▸ hm0_eq), ?_⟩
            · refine Classical.byContradiction (fun hge => ?_)
              rcases Nat.eq_or_lt_of_le (Nat.not_lt.mp hge) with rfl | hlt_m
              · omega
              · have := hf_mono idx m hidx hm hlt_m; omega
            · have hrlv : (s.core.rsns[(s.core.trl[f_idxs[idx]]?.getD 0#32).toNat / 2]?.getD
                    4294967295#32 &&& 2147483647#32).toNat / 2 =
                    (s.core.trl[m0]?.getD 0#32).toNat / 2 := by
                rw [hm0_eq, bt_nat_xor1_div2]
              rw [hrlv, hlvl_eq m0 (by omega), hlvl_eq _ hspec.1]
              simp only [hm0_le, hspec.2, ite_true]
              rw [← hrlv]
              exact hm0_lv
        · contradiction
        · contradiction
        · refine ⟨?_, ?_, fun q hq => ?_⟩
          · simpa only [fullArenaClauseRefsCore, har, hal] using hr.1
          · simpa only [fullArenaClauseGarbCore, fullArenaHdrCore, har] using hr.2.1
          · have hq0 : q ∈ fullArenaClauseLitsCore s.core
                ((s.core.rsns[(s.core.trl[f_idxs[idx]'(by omega)]?.getD 0#32).toNat / 2]?.getD
                  4294967295#32).toNat) := by
              unfold fullArenaClauseLitsCore fullArenaClauseSizeCore at hq ⊢; rwa [har] at hq
            rcases hr.2.2 q hq0 with rfl | ⟨m0, hm0_lt, hm0_eq, hm0_lv⟩
            · exact Or.inl rfl
            · right
              have hm0_le : (s.core.lvl[(s.core.trl[m0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                  target_lvl := by
                rw [hm0_eq, bt_nat_xor1_div2]; omega
              obtain ⟨m, hm, hm_eq⟩ := hf_find m0 (by omega) hm0_le
              refine ⟨m, ?_, (hf_elem m hm).trans (hm_eq ▸ hm0_eq), ?_⟩
              · refine Classical.byContradiction (fun hge => ?_)
                rcases Nat.eq_or_lt_of_le (Nat.not_lt.mp hge) with rfl | hlt_m
                · omega
                · have := hf_mono idx m hidx hm hlt_m; omega
              · have hrlv : (s.core.trl[m0]?.getD 0#32).toNat / 2 = q / 2 := by
                  rw [hm0_eq, bt_nat_xor1_div2]
                rw [← hrlv, hlvl_eq m0 (by omega), hlvl_eq _ hspec.1]
                simp only [hm0_le, hspec.2, ite_true]
                rw [hrlv]
                exact hm0_lv
      reason_lit_mem := fun idx hidx hne hmask => by
        have hspec := hf_get_spec idx hidx
        rw [hf_rsns_eq idx hidx] at hne hmask
        rw [hf_rsns_eq idx hidx, hf_elem idx hidx]
        have hlt_cur : (s.core.lvl[(s.core.trl[f_idxs[idx]'(by omega)]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat < s.core.cur_level := by omega
        have hm := hw.reason_lit_mem_below _ hspec.1 hlt_cur hne hmask
        unfold fullArenaClauseLitsCore fullArenaClauseSizeCore at hm ⊢
        rwa [har] }


end LeanQbe.T.Examples.Kissat.Proof.Backtrack

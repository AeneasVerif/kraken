/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-! # Watch WP Proofs Part 0: Shared Helpers and `full_wsort_sift`

Self-contained `CanonicalEnv` WP proofs for `full_wsort_sift` and `full_wstack_radix_sort_m6`,
plus shared BitVec/List/`wsort`/`FullMem` lemmas reused across `Proof/Watch/Wp1..4`. -/

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Std.ExtHashMap
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. Shared Public Helpers -/

public section

@[expose] def WsCovers (ws : List (BitVec 32)) (n nlits : Nat) (sz : Nat → Nat) : Prop :=
  (∀ j < n, Spec.wsVal ws j < nlits ∧ 0 < sz (Spec.wsVal ws j)) ∧
  (∀ a < n, ∀ b < n, a ≠ b → Spec.wsVal ws a ≠ Spec.wsVal ws b) ∧
  (∀ l < nlits, 0 < sz l → ∃ j < n, Spec.wsVal ws j = l)

@[expose] def SplitLe (key : Nat → Nat) (ws : List (BitVec 32)) (lo n : Nat) : Prop :=
  ∀ i < lo, ∀ j, lo ≤ j → j < n → key (Spec.wsVal ws i) ≤ key (Spec.wsVal ws j)

@[expose] def swapIdx (xs : List (BitVec 32)) (i j : Nat) : List (BitVec 32) :=
  if h : i < xs.length ∧ j < xs.length then
    (xs.set i (xs[j]'h.2)).set j (xs[i]'h.1)
  else xs

@[expose] def FullRestNoWatch (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
  array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆
  array (t := i32) c.pRepr s.core.repr ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
  array (t := i32) c.pArena s.core.arena ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

theorem bv64_shl1_toNat {l : BitVec 32} (hl : l.toNat < 2 ^ 31) :
    (l.setWidth 64 <<< (1 : Nat)).toNat = 2 * l.toNat := by
  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
  simp [Nat.shiftLeft_eq]
  omega

theorem bv64_lit2 {lit : BitVec 32} :
    (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
  have hlt : lit.toNat < 2 ^ 32 := lit.isLt
  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
  simp [Nat.shiftLeft_eq]
  omega

theorem bv64_lit2p1 {lit : BitVec 32} :
    ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * lit.toNat + 1 := by
  have hlt : lit.toNat < 2 ^ 32 := lit.isLt
  rw [BitVec.toNat_add, bv64_lit2]
  simp
  omega

theorem bv32_trunc_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, Proof.Spec.bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt hn]

theorem bv32_trunc_add {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat :=
  bv32_add_small_eq h

theorem bv64_eq_zero_of_not_pos {x : BitVec 64} (h : ¬ (0 : BitVec 64) < x) :
    x.toNat = 0 := by
  by_cases hz : x.toNat = 0
  · exact hz
  · exact False.elim (h (BitVec.lt_def.mpr (Nat.zero_lt_of_ne_zero hz)))

theorem bv32_eq_nat {x : BitVec 32} (k : Nat) (hk : k < 2 ^ 32)
    (h : x = BitVec.ofNat 32 k) : x.toNat = k := by
  subst h; exact bv32_ofNat_toNat hk

theorem bv32_ne_nat {x : BitVec 32} (k : Nat) (hk : k < 2 ^ 32)
    (h : ¬ x = BitVec.ofNat 32 k) : x.toNat ≠ k :=
  fun heq => h (BitVec.eq_of_toNat_eq (by simpa [bv32_ofNat_toNat hk] using heq))

theorem bv64_eq_nat {x : BitVec 64} (k : Nat) (hk : k < 2 ^ 64)
    (h : x = BitVec.ofNat 64 k) : x.toNat = k := by
  subst h; exact Proof.Spec.bv64_ofNat_toNat hk

theorem bv64_ne_nat {x : BitVec 64} (k : Nat) (hk : k < 2 ^ 64)
    (h : ¬ x = BitVec.ofNat 64 k) : x.toNat ≠ k :=
  fun heq => h (BitVec.eq_of_toNat_eq (by simpa [Proof.Spec.bv64_ofNat_toNat hk] using heq))

theorem list_getElem_congr {α : Type _} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) :
    xs[i]'hi = xs[j]'(hij ▸ hi) := by
  subst hij; rfl

theorem wsVal_getElem {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    Spec.wsVal xs i = (xs[i]'hi).toNat := by
  unfold Spec.wsVal
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem list_perm_take_of_drop_eq {α : Type _} {xs ys : List α} {n : Nat}
    (hp : xs.Perm ys) (hd : xs.drop n = ys.drop n) :
    (xs.take n).Perm (ys.take n) := by
  have hcat : (xs.take n ++ xs.drop n).Perm (ys.take n ++ ys.drop n) := by
    simpa [List.take_append_drop] using hp
  rw [hd] at hcat
  exact (List.perm_append_right_iff _).mp hcat

theorem nodup_of_map_nodup {α β : Type _} (f : α → β) {xs : List α}
    (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 ⟨a, ha, rfl⟩, ih h.2⟩

theorem perm_of_nodup_subset_len {α : Type _} [DecidableEq α] {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) (hlen : xs.length = ys.length) :
    xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons _ _ => simp at hlen
  | cons a t ih =>
    have ha_nd := List.nodup_cons.mp hnd
    have ha_mem : a ∈ ys := hsub a List.mem_cons_self
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem ha_mem
    have hperm_step : t.Perm (l1 ++ l2) := by
      refine ih ha_nd.2 (fun x hx => ?_) (by simp at hlen ⊢; omega)
      have hxy := hsub x (List.mem_cons_of_mem a hx)
      simp only [List.mem_append, List.mem_cons] at hxy ⊢
      rcases hxy with h | rfl | h
      · exact Or.inl h
      · exact absurd hx ha_nd.1
      · exact Or.inr h
    exact (List.Perm.cons a hperm_step).trans List.perm_middle.symm

theorem swapIdx_length {xs : List (BitVec 32)} {i j : Nat} :
    (swapIdx xs i j).length = xs.length := by
  unfold swapIdx; split <;> simp [List.length_set]

theorem swapIdx_getElem_self {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapIdx xs i j)[i]'(by rw [swapIdx_length]; exact hi) = xs[j]'hj ∧
    (swapIdx xs i j)[j]'(by rw [swapIdx_length]; exact hj) = xs[i]'hi := by
  unfold swapIdx
  split
  case isFalse h => exact False.elim (h ⟨hi, hj⟩)
  case isTrue =>
    by_cases hij : i = j
    · subst hij; simp
    · constructor
      · rw [List.getElem_set_ne (fun h => hij h.symm), List.getElem_set_self]
      · rw [List.getElem_set_self]

theorem swapIdx_getElem_other {xs : List (BitVec 32)} {i j k : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (hk : k < xs.length)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (swapIdx xs i j)[k]'(by rw [swapIdx_length]; exact hk) = xs[k]'hk := by
  unfold swapIdx
  split
  case isFalse h => exact False.elim (h ⟨hi, hj⟩)
  case isTrue =>
    rw [List.getElem_set_ne (fun h => hkj h.symm),
      List.getElem_set_ne (fun h => hki h.symm)]

theorem swapIdx_perm {xs : List (BitVec 32)} {i j : Nat} :
    (swapIdx xs i j).Perm xs := by
  unfold swapIdx
  split
  case isFalse => exact List.Perm.refl xs
  case isTrue h =>
    by_cases hij : i = j
    · subst hij
      have h1 : xs.set i (xs[i]'h.1) = xs := List.set_getElem_self h.1
      rw [h1, h1]
    · rw [List.perm_iff_count]
      intro x
      rw [List.count_set (by rw [List.length_set]; exact h.2), List.count_set h.1,
        List.getElem_set_ne hij]
      by_cases hxi : xs[i]'h.1 = x <;> by_cases hxj : xs[j]'h.2 = x <;> simp [hxi, hxj]
      all_goals
        try
          first
          | (have hc : 0 < xs.count x := List.count_pos_iff.mpr (hxi ▸ List.getElem_mem h.1)
             omega)
          | (have hc : 0 < xs.count x := List.count_pos_iff.mpr (hxj ▸ List.getElem_mem h.2)
             omega)

theorem wsVal_swap {xs : List (BitVec 32)} {i j k : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    Spec.wsVal (swapIdx xs i j) k =
      if k = i then Spec.wsVal xs j
      else if k = j then Spec.wsVal xs i
      else Spec.wsVal xs k := by
  have heq : swapIdx xs i j = (xs.set i (xs[j]'hj)).set j (xs[i]'hi) := by
    simp [swapIdx, hi, hj]
  unfold Spec.wsVal
  rw [heq]
  by_cases hki : k = i
  · subst hki
    by_cases hkj : k = j
    · subst hkj
      simp only [↓reduceIte]
      rw [List.getElem?_eq_getElem (by rw [List.length_set, List.length_set]; exact hi),
        List.getElem?_eq_getElem hi, List.getElem_set_self]
    · simp only [↓reduceIte]
      rw [List.getElem?_eq_getElem (by rw [List.length_set, List.length_set]; exact hi),
        List.getElem?_eq_getElem hj, List.getElem_set_ne (fun h => hkj h.symm),
        List.getElem_set_self]
  · by_cases hkj : k = j
    · subst hkj
      simp only [hki, ↓reduceIte]
      rw [List.getElem?_eq_getElem (by rw [List.length_set, List.length_set]; exact hj),
        List.getElem?_eq_getElem hi, List.getElem_set_self]
    · simp only [hki, ↓reduceIte, hkj]
      rw [List.getElem?_set_ne (fun h => hkj h.symm), List.getElem?_set_ne (fun h => hki h.symm)]

theorem wsCovers_swap {ws : List (BitVec 32)} {n nlits : Nat} {sz : Nat → Nat}
    (hcov : WsCovers ws n nlits sz) {i j : Nat} (hi : i < n) (hj : j < n)
    (hil : i < ws.length) (hjl : j < ws.length) :
    WsCovers (swapIdx ws i j) n nlits sz := by
  let p : Nat → Nat := fun a => if a = i then j else if a = j then i else a
  have hp_lt : ∀ a < n, p a < n := fun a ha => by
    dsimp only [p]
    by_cases hai : a = i
    · simp [hai, hj]
    · by_cases haj : a = j
      · simp [haj]; by_cases hji : j = i <;> simp [hji, hi]
      · simp [hai, haj, ha]
  have hp_inv : ∀ a, p (p a) = a := fun a => by
    dsimp only [p]
    by_cases hij : i = j
    · subst hij; by_cases ha : a = i <;> simp [ha]
    · by_cases ha1 : a = i
      · simp [ha1]
      · by_cases ha2 : a = j
        · simp [ha2]
        · simp [ha1, ha2]
  have hp_inj : ∀ a b, p a = p b → a = b := fun a b hab => by
    rw [← hp_inv a, ← hp_inv b, hab]
  have h1 : ∀ a, Spec.wsVal (swapIdx ws i j) a = Spec.wsVal ws (p a) := fun a => by
    rw [wsVal_swap hil hjl]
    dsimp only [p]
    by_cases hij : i = j
    · subst hij; by_cases ha : a = i <;> simp [ha]
    · by_cases ha1 : a = i
      · simp [ha1]
      · by_cases ha2 : a = j
        · simp [ha2, show j ≠ i from fun h => hij h.symm]
        · simp [ha1, ha2]
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · rw [h1 a]; exact hcov.1 (p a) (hp_lt a ha)
  · rw [h1 a, h1 b]
    exact hcov.2.1 (p a) (hp_lt a ha) (p b) (hp_lt b hb) (fun h => hab (hp_inj a b h))
  · obtain ⟨k, hk, hkl⟩ := hcov.2.2 l hl hsz
    refine ⟨p k, hp_lt k hk, ?_⟩
    rw [h1 (p k), hp_inv k]; exact hkl

theorem wsCovers_of_perm_suffix {ws ws' : List (BitVec 32)} {n nlits : Nat} {sz : Nat → Nat}
    (hcov : WsCovers ws n nlits sz) (hperm : (ws'.take n).Perm (ws.take n))
    (hle : n ≤ ws.length) (hle' : n ≤ ws'.length) :
    WsCovers ws' n nlits sz := by
  have hmem1 : ∀ j < n, ∃ k < n, ws'[j]? = ws[k]? := by
    intro j hj
    have hin0 : (ws'.take n)[j]'(by rw [List.length_take]; omega) ∈ ws'.take n :=
      List.getElem_mem _
    have hin : ws'[j]'(by omega) ∈ ws'.take n := by
      simpa [List.getElem_take] using hin0
    have hin2 : ws'[j]'(by omega) ∈ ws.take n := hperm.mem_iff.mp hin
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hin2
    have hkn : k < n := by simp [hle] at hk; exact hk
    rw [List.getElem_take] at hkeq
    refine ⟨k, hkn, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), hkeq]
  have hmem2 : ∀ k < n, ∃ j < n, ws'[j]? = ws[k]? := by
    intro k hk
    have hin0 : (ws.take n)[k]'(by rw [List.length_take]; omega) ∈ ws.take n :=
      List.getElem_mem _
    have hin : ws[k]'(by omega) ∈ ws.take n := by
      simpa [List.getElem_take] using hin0
    have hin2 : ws[k]'(by omega) ∈ ws'.take n := hperm.symm.mem_iff.mp hin
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hin2
    have hjn : j < n := by simp [hle'] at hj; exact hj
    rw [List.getElem_take] at hjeq
    refine ⟨j, hjn, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), hjeq]
  have hnd : (ws.take n).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    have hin : i < n := by simp [hle] at hi; exact hi
    have hjn : j < n := by simp [hle] at hj; exact hj
    simp only [List.getElem_take] at heq
    have hval : Spec.wsVal ws i = Spec.wsVal ws j := by
      unfold Spec.wsVal
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), heq]
    exact hcov.2.1 i hin j hjn (by omega) hval
  have hnd' : (ws'.take n).Nodup := hperm.nodup_iff.mpr hnd
  refine ⟨fun j hj => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · obtain ⟨k, hk, hjk⟩ := hmem1 j hj
    have hveq : Spec.wsVal ws' j = Spec.wsVal ws k := by unfold Spec.wsVal; rw [hjk]
    rw [hveq]; exact hcov.1 k hk
  · obtain ⟨ka, hka, hja⟩ := hmem1 a ha
    obtain ⟨kb, hkb, hjb⟩ := hmem1 b hb
    have hne_val : ws'[a]'(by omega) ≠ ws'[b]'(by omega) := by
      intro heq
      have hpw := List.pairwise_iff_getElem.mp hnd'
      rcases Nat.lt_trichotomy a b with hlt | heq_ab | hgt
      · exact hpw a b (by simp; omega) (by simp; omega) hlt (by simpa [List.getElem_take] using heq)
      · exact hab heq_ab
      · exact hpw b a (by simp; omega) (by simp; omega) hgt
          (by simpa [List.getElem_take] using heq.symm)
    have hkab : ka ≠ kb := by
      intro heq; subst heq
      apply hne_val
      have h1 := hja.trans hjb.symm
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
    have hva : Spec.wsVal ws' a = Spec.wsVal ws ka := by unfold Spec.wsVal; rw [hja]
    have hvb : Spec.wsVal ws' b = Spec.wsVal ws kb := by unfold Spec.wsVal; rw [hjb]
    rw [hva, hvb]; exact hcov.2.1 ka hka kb hkb hkab
  · obtain ⟨k, hk, hkl⟩ := hcov.2.2 l hl hsz
    obtain ⟨j, hj, hjk⟩ := hmem2 k hk
    refine ⟨j, hj, ?_⟩
    unfold Spec.wsVal at hkl ⊢; rw [hjk]; exact hkl

theorem wsortMaxHeap_root_ge {wvec ws : List (BitVec 32)} {n : Nat}
    (hmh : FullWsortMaxHeap wvec ws 0 n) (_hn : 0 < n) :
    ∀ j < n, Spec.fullWvecOff wvec (Spec.wsVal ws j) ≤
      Spec.fullWvecOff wvec (Spec.wsVal ws 0) := by
  intro j hj
  refine Nat.strongRecOn (motive := fun k =>
      k < n → Spec.fullWvecOff wvec (Spec.wsVal ws k) ≤ Spec.fullWvecOff wvec (Spec.wsVal ws 0))
    j (fun k ih hk => ?_) hj
  rcases Nat.eq_zero_or_pos k with rfl | hkp
  · exact Nat.le_refl _
  · have hp : (k - 1) / 2 < k := by omega
    have hle_par := ih ((k - 1) / 2) hp (by omega)
    have hpar := hmh ((k - 1) / 2) (Nat.zero_le _) (by omega)
    dsimp only [Spec.fullWvecOff, Spec.wsVal] at hle_par hpar ⊢
    have hch : 2 * ((k - 1) / 2) + 1 = k ∨ 2 * ((k - 1) / 2) + 2 = k := by omega
    rcases hch with hc | hc
    · have h1 := hpar.1 (by omega); rw [hc] at h1; exact Nat.le_trans h1 hle_par
    · have h2 := hpar.2 (by omega); rw [hc] at h2; exact Nat.le_trans h2 hle_par

theorem fullMem_eq_wvec_wsort_wstk (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWstk s.core.wstk ⋆ FullRestNoWatch c s) := by
  unfold FullMem FullCoreArrays FullCoreU32B FullCoreDynArrs
    FullScratchArrays FullScrWksArrs FullRestNoWatch
  ac_rfl

theorem array_i32_split_at {a : BitVec 64} {xs : List (Val i32)} (k : Nat) :
    array a xs = array a (xs.take k) ⋆
      array (a + BitVec.ofNat 64 (4 * (xs.take k).length)) (xs.drop k) := by
  have h := congrArg (array a) (List.take_append_drop k xs).symm
  rw [array_append] at h
  exact h

theorem full_wvec_wsort_split3 {c : FullCfg} {s : FullState}
    {m : Mem 64} {R : Mem 64 → Prop} {n : Nat}
    (hm : (FullMem c s ⋆ R) m) (hws_len : 2 * c.max_vars = s.scratch.wsort.length)
    (hfit : 2 * n + 256 ≤ 2 * c.max_vars) :
    (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n))
        ((s.scratch.wsort.drop n).take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n)))
        (s.scratch.wsort.drop (2 * n)) ⋆
      (array (t := i32) c.pWstk s.core.wstk ⋆ FullRestNoWatch c s ⋆ R)) m := by
  have h1 : (s.scratch.wsort.take n).length = n := by simp; omega
  have h2 : ((s.scratch.wsort.drop n).take n).length = n := by simp; omega
  have hsplit : array (t := i32) c.pWsort s.scratch.wsort =
      array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n))
        ((s.scratch.wsort.drop n).take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n)))
        (s.scratch.wsort.drop (2 * n)) := by
    have ha := array_i32_split_at (a := c.pWsort) (xs := s.scratch.wsort) n
    rw [h1] at ha
    have hb := array_i32_split_at (a := c.pWsort + BitVec.ofNat 64 (4 * n))
      (xs := s.scratch.wsort.drop n) n
    rw [h2, List.drop_drop, show n + n = 2 * n by omega,
      BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * n + 4 * n = 4 * (2 * n) by omega] at hb
    rw [ha, hb, sep_assoc]
  rw [fullMem_eq_wvec_wsort_wstk, hsplit] at hm
  simpa only [sep_assoc] using hm

end

/-! ## 2. `full_wsort_sift_wp` -/

private def FullWsortHoleParent (wvec ws : List (BitVec 32)) (lo n root : Nat) : Prop :=
  lo ≤ root ∧ root < n ∧
  ∀ c, c = 2 * root + 1 ∨ c = 2 * root + 2 → c < n → root ≠ lo →
    (wvec[2 * Spec.wsVal ws c]?.getD 0#32).toNat ≤
    (wvec[2 * Spec.wsVal ws ((root - 1) / 2)]?.getD 0#32).toNat

private def FullWsortMaxHeapExcept (wvec ws : List (BitVec 32))
    (lo n root : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n → i ≠ root →
    have p := (wvec[2 * Spec.wsVal ws i]?.getD 0#32).toNat
    (2 * i + 1 < n → (wvec[2 * Spec.wsVal ws (2 * i + 1)]?.getD 0#32).toNat ≤ p) ∧
    (2 * i + 2 < n → (wvec[2 * Spec.wsVal ws (2 * i + 2)]?.getD 0#32).toNat ≤ p)

private theorem fullWsortMaxHeap_sift_done {wvec ws : List (BitVec 32)} {lo n root : Nat}
    (hmax : FullWsortMaxHeapExcept wvec ws lo n root)
    (h1 : 2 * root + 1 < n →
      (wvec[2 * Spec.wsVal ws (2 * root + 1)]?.getD 0#32).toNat ≤
      (wvec[2 * Spec.wsVal ws root]?.getD 0#32).toNat)
    (h2 : 2 * root + 2 < n →
      (wvec[2 * Spec.wsVal ws (2 * root + 2)]?.getD 0#32).toNat ≤
      (wvec[2 * Spec.wsVal ws root]?.getD 0#32).toNat) :
    FullWsortMaxHeap wvec ws lo n := by
  intro i hlo hi
  by_cases hir : i = root
  · subst hir; exact ⟨h1, h2⟩
  · exact hmax i hlo hi hir

private theorem fullWsort_sift_step {wvec ws : List (BitVec 32)}
    {lo n root ch : Nat}
    (hlo : lo ≤ root) (hch : ch < n)
    (hrel : ch = 2 * root + 1 ∨ ch = 2 * root + 2)
    (hil : root < ws.length) (hjl : ch < ws.length)
    (hmax : FullWsortMaxHeapExcept wvec ws lo n root)
    (hpar : FullWsortHoleParent wvec ws lo n root)
    (hlt : (wvec[2 * Spec.wsVal ws root]?.getD 0#32).toNat <
           (wvec[2 * Spec.wsVal ws ch]?.getD 0#32).toNat)
    (hmaxch : (2 * root + 1 < n →
        (wvec[2 * Spec.wsVal ws (2 * root + 1)]?.getD 0#32).toNat ≤
        (wvec[2 * Spec.wsVal ws ch]?.getD 0#32).toNat) ∧
      (2 * root + 2 < n →
        (wvec[2 * Spec.wsVal ws (2 * root + 2)]?.getD 0#32).toNat ≤
        (wvec[2 * Spec.wsVal ws ch]?.getD 0#32).toNat)) :
    FullWsortMaxHeapExcept wvec (swapIdx ws root ch) lo n ch ∧
    FullWsortHoleParent wvec (swapIdx ws root ch) lo n ch := by
  let ws' := swapIdx ws root ch
  let key : List (BitVec 32) → Nat → Nat :=
    fun xs k => (wvec[2 * Spec.wsVal xs k]?.getD 0#32).toNat
  have hk_root : key ws' root = key ws ch := by simp [key, ws', wsVal_swap hil hjl]
  have hk_ch : key ws' ch = key ws root := by
    have hrc : root < ch := by omega
    simp [key, ws', wsVal_swap hil hjl, show ch ≠ root by omega]
  have hk_other : ∀ k, k ≠ root → k ≠ ch → key ws' k = key ws k := fun k hkr hkc => by
    simp [key, ws', wsVal_swap hil hjl, hkr, hkc]
  have hrc : root < ch := by omega
  have hpar_ch : (ch - 1) / 2 = root := by omega
  dsimp only [key] at hk_root hk_ch hk_other
  refine ⟨fun i hloi hi hich => ?_, ⟨by omega, hch, fun c hc hc_lt _ => ?_⟩⟩
  · change (2 * i + 1 < n → key ws' (2 * i + 1) ≤ key ws' i) ∧
      (2 * i + 2 < n → key ws' (2 * i + 2) ≤ key ws' i)
    dsimp only [key]
    by_cases hir : i = root
    · subst hir
      rw [hk_root]
      refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
      · by_cases h1c : 2 * i + 1 = ch
        · rw [h1c, hk_ch]; omega
        · rw [hk_other _ (by omega) h1c]; exact hmaxch.1 hc1
      · by_cases h2c : 2 * i + 2 = ch
        · rw [h2c, hk_ch]; omega
        · rw [hk_other _ (by omega) h2c]; exact hmaxch.2 hc2
    · rw [hk_other i hir hich]
      have hold := hmax i hloi hi hir
      refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
      · by_cases h1c : 2 * i + 1 = ch
        · have hpold : (ch - 1) / 2 = i := by rw [← h1c]; omega
          rw [hpar_ch] at hpold; exact absurd hpold.symm hir
        · by_cases h1r : 2 * i + 1 = root
          · rw [h1r, hk_root]
            have hpr : (root - 1) / 2 = i := by rw [← h1r]; omega
            have hhp := hpar.2.2 ch hrel hch (by omega)
            rw [← hpr]; exact hhp
          · rw [hk_other _ h1r h1c]; exact hold.1 hc1
      · by_cases h2c : 2 * i + 2 = ch
        · have hpold : (ch - 1) / 2 = i := by rw [← h2c]; omega
          rw [hpar_ch] at hpold; exact absurd hpold.symm hir
        · by_cases h2r : 2 * i + 2 = root
          · rw [h2r, hk_root]
            have hpr : (root - 1) / 2 = i := by rw [← h2r]; omega
            have hhp := hpar.2.2 ch hrel hch (by omega)
            rw [← hpr]; exact hhp
          · rw [hk_other _ h2r h2c]; exact hold.2 hc2
  · change key ws' c ≤ key ws' ((ch - 1) / 2)
    dsimp only [key]
    rw [hpar_ch, hk_root, hk_other c (by omega) (by omega)]
    have hmch := hmax ch (by omega) hch (by omega)
    rcases hc with rfl | rfl
    · exact hmch.1 hc_lt
    · exact hmch.2 hc_lt

public theorem full_wsort_sift_wp (Γ : Env) :
    ∀ a m Q X, fullWsortSiftSpec a m Q X → Func.wp Γ full_wsort_sift_body a m Q X := by
  rintro ⟨wvec_ptr, ws_ptr, start, n, ⟨⟩⟩ m Q X
    ⟨nlits, wvec, ws, R, hnl, hst_lt, hn_bd, hn_len, hcov, hmax0, hm, hQ⟩
  dsimp only [Func.wp, full_wsort_sift_body]
  c0_hsteps_nogrp
  refine wp_join_group (fun _ m1 =>
    ∃ ws' : List (BitVec 32), ws'.length = ws.length ∧ ws'.Perm ws ∧
      (∀ i, i < start.toNat ∨ n.toNat ≤ i → ws'[i]? = ws[i]?) ∧
      FullWsortMaxHeap wvec ws' start.toNat n.toNat ∧
      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws' ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ws', hwsl, hperm, hpres, hmax, hm1⟩
    c0_hsteps_nogrp
    exact hQ ws' m1 hwsl hperm hpres hmax hm1
  · intro Js hJs
    refine wp_loop_inv
      (fun (root, ()) mS =>
        start.toNat ≤ root.toNat ∧ root.toNat < n.toNat ∧ ∃ wsS : List (BitVec 32),
          wsS.length = ws.length ∧ wsS.Perm ws ∧
          (∀ i, i < start.toNat ∨ n.toNat ≤ i → wsS[i]? = ws[i]?) ∧
          (∀ i < n.toNat, (wsS[i]?.getD 0#32).toNat < nlits) ∧
          FullWsortMaxHeapExcept wvec wsS start.toNat n.toNat root.toNat ∧
          FullWsortHoleParent wvec wsS start.toNat n.toNat root.toNat ∧
          (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆ R) mS)
      (fun (root, ()) _ => n.toNat - root.toNat)
      (fun Js_1 hLoopS => by
        c0_hsteps_nogrp
        refine hLoopS (start, ()) m ⟨Nat.le_refl _, hst_lt, ws, rfl, List.Perm.refl _,
          fun _ _ => rfl, hcov, fun i h1 h2 hne => hmax0 i (by omega) h2,
          ⟨Nat.le_refl _, hst_lt, fun _ _ _ hne => absurd rfl hne⟩, hm⟩)
      (fun Js_1 ⟨root, ⟨⟩⟩ mS
          ⟨hloS, hrt_lt, wsS, hwsS, hpermS, hpresS, hcovS, hmaxS, hparS, hmS⟩ hLoopS => ?_)
    have hch1_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by
        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
      rw [BitVec.toNat_add, hsh]; simp; omega
    have h1_bv : (1 : BitVec 64).toNat = 1 := rfl
    c0_hsplit
    · clear hc
      c0_hsplit
      · rw [h1_bv] at hc
        have hge : n.toNat ≤ 2 * root.toNat + 1 := by omega
        clear hc; c0_hsteps_nogrp
        exact hJs (root, ()) mS ⟨wsS, hwsS, hpermS, hpresS,
          fullWsortMaxHeap_sift_done hmaxS (fun h => by omega) (fun h => by omega), hmS⟩
      · rw [h1_bv] at hc
        have hch1_lt : 2 * root.toNat + 1 < n.toNat := by omega
        clear hc
        have hc1_nat : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 :=
          hch1_eq
        have hws_c1_bd : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wsS.length := by omega
        have hws_c1_val : wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd =
            wsS[2 * root.toNat + 1]'(by omega) := list_getElem_congr hws_c1_bd hc1_nat
        have hwc1_bd : (wsS[2 * root.toNat + 1]'(by omega)).toNat < nlits := by
          have h0 := hcovS _ hch1_lt
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0; exact h0
        have hwvc1 : (((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).setWidth
            64) <<< (1 : Nat)).toNat < wvec.length := by
          rw [bv64_lit2, hws_c1_val]; omega
        have hco1_eq :
            wvec[(((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).setWidth
              64) <<< (1 : Nat)).toNat]'hwvc1 =
            wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32 := by
          have hidx : (((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).setWidth
              64) <<< (1 : Nat)).toNat = 2 * Spec.wsVal wsS (2 * root.toNat + 1) := by
            rw [bv64_lit2, hws_c1_val, wsVal_getElem (by omega)]
          rw [List.getElem?_eq_getElem (by rw [← hidx]; exact hwvc1), Option.getD_some]
          exact list_getElem_congr hwvc1 hidx
        have hco1_mod_bd :
            2 * (wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).toNat % 2 ^ 64 <
              wvec.length := by
          rw [hws_c1_val, Nat.mod_eq_of_lt (by omega)]; omega
        have hco1_mod :
            wvec[2 * (wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).toNat %
              2 ^ 64]'hco1_mod_bd = wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32 := by
          have hidx :
              2 * (wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).toNat % 2 ^ 64 =
                2 * Spec.wsVal wsS (2 * root.toNat + 1) := by
            rw [hws_c1_val, wsVal_getElem (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [List.getElem?_eq_getElem (by rw [← hidx]; exact hco1_mod_bd), Option.getD_some]
          exact list_getElem_congr hco1_mod_bd hidx
        c0_hstraight
        refine wp_join_group (fun (ch, co, ()) mJ =>
          (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
          ch.toNat < n.toNat ∧
          co = wvec[2 * Spec.wsVal wsS ch.toNat]?.getD 0#32 ∧
          (2 * root.toNat + 1 < n.toNat →
            (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat ≤ co.toNat) ∧
          (2 * root.toNat + 2 < n.toNat →
            (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat ≤ co.toNat) ∧
          mS = mJ) ?_ ?_
        · rintro _ ⟨ch, co, ⟨⟩⟩ mJ ⟨hch_or, hch_lt, hco_eq, hmax_c1, hmax_c2, hmJ⟩
          subst hmJ
          have hwr : (wsS[root.toNat]'(by omega)).toNat < nlits := by
            have h0 := hcovS root.toNat hrt_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0; exact h0
          have hwvr : (((wsS[root.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat <
              wvec.length := by
            rw [bv64_lit2]; omega
          have hro_mod_bd : 2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64 < wvec.length := by
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          have hro_eq : wvec[2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64]'hro_mod_bd =
              wvec[2 * Spec.wsVal wsS root.toNat]?.getD 0#32 := by
            have hidx : 2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64 =
                2 * Spec.wsVal wsS root.toNat := by
              rw [wsVal_getElem (by omega), Nat.mod_eq_of_lt (by omega)]
            rw [List.getElem?_eq_getElem (by rw [← hidx]; exact hro_mod_bd), Option.getD_some]
            exact list_getElem_congr hro_mod_bd hidx
          c0_hstraight
          c0_hsplit
          · have hge : co.toNat ≤
                (wvec[2 * Spec.wsVal wsS root.toNat]?.getD 0#32).toNat := by
              rw [← hro_eq]; omega
            clear hc; c0_hstraight
            exact hJs (root, ()) mS ⟨wsS, hwsS, hpermS, hpresS,
              fullWsortMaxHeap_sift_done hmaxS (fun h => Nat.le_trans (hmax_c1 h) hge)
                (fun h => Nat.le_trans (hmax_c2 h) hge), hmS⟩
          · have hlt : (wvec[2 * Spec.wsVal wsS root.toNat]?.getD 0#32).toNat <
                (wvec[2 * Spec.wsVal wsS ch.toNat]?.getD 0#32).toNat := by
              rw [← hro_eq, ← hco_eq]; omega
            clear hc; c0_hstraight
            have hws'_eq : (wsS.set root.toNat (wsS[ch.toNat]'(by omega))).set ch.toNat
                (wsS[root.toNat]'(by omega)) = swapIdx wsS root.toNat ch.toNat := by
              simp [swapIdx, show root.toNat < wsS.length by omega,
                show ch.toNat < wsS.length by omega]
            have hstep := fullWsort_sift_step hloS hch_lt hch_or (by omega) (by omega)
              hmaxS hparS hlt ⟨fun h => by rw [← hco_eq]; exact hmax_c1 h,
                fun h => by rw [← hco_eq]; exact hmax_c2 h⟩
            refine hLoopS (ch, ()) _ (by dsimp only; omega)
              ⟨by omega, hch_lt, swapIdx wsS root.toNat ch.toNat,
                by rw [swapIdx_length, hwsS], swapIdx_perm.trans hpermS,
                fun i hi => ?_, fun i hi => ?_, hstep.1, hstep.2, ?_⟩
            · by_cases hil : i < wsS.length
              · rw [List.getElem?_eq_getElem (by rw [swapIdx_length]; exact hil),
                  swapIdx_getElem_other (by omega) (by omega) hil
                    (by rcases hi with h | h <;> omega) (by rcases hi with h | h <;> omega),
                  ← List.getElem?_eq_getElem hil]
                exact hpresS i hi
              · rw [List.getElem?_eq_none (by rw [swapIdx_length]; omega),
                  List.getElem?_eq_none (by omega)]
            · rw [List.getElem?_eq_getElem (by rw [swapIdx_length, hwsS]; omega), Option.getD_some]
              have hcov_fn : ∀ (k : Nat) (hk : k < n.toNat),
                  (wsS[k]'(Nat.lt_of_lt_of_le hk (hwsS ▸ hn_len))).toNat < nlits := by
                intro k hk
                have h0 := hcovS k hk
                rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hk (hwsS ▸ hn_len)),
                  Option.getD_some] at h0
                exact h0
              by_cases kir : i = root.toNat
              · subst kir
                rw [(swapIdx_getElem_self (by omega) (by omega)).1]; exact hcov_fn _ hch_lt
              · by_cases kic : i = ch.toNat
                · subst kic
                  rw [(swapIdx_getElem_self (by omega) (by omega)).2]; exact hcov_fn _ hrt_lt
                · rw [swapIdx_getElem_other (by omega) (by omega) (by omega) kir kic]
                  exact hcov_fn i hi
            · have hmem := hm
              rw [hws'_eq, sep_comm R emp, emp_sep, sep_comm_l, ← sep_assoc] at hmem
              exact hmem
        · intro J2 hJ2
          c0_hstraight
          c0_hsplit
          · rw [h1_bv] at hc
            have hc2_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                2 * root.toNat + 2 := by
              rw [BitVec.toNat_add, hc1_nat]; simp; omega
            have hch2_lt : 2 * root.toNat + 2 < n.toNat := by omega
            have hws_c2_bd :
                ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat < wsS.length := by
              omega
            have hws_c2_val :
                wsS[((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat]'hws_c2_bd =
                  wsS[2 * root.toNat + 2]'(by omega) := list_getElem_congr hws_c2_bd hc2_eq
            have hwc2_bd : (wsS[2 * root.toNat + 2]'(by omega)).toNat < nlits := by
              have h0 := hcovS _ hch2_lt
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0; exact h0
            have hwvc2 : (((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64) +
                (1 : BitVec 64)).toNat]'hws_c2_bd).setWidth 64) <<< (1 : Nat)).toNat <
                wvec.length := by
              rw [bv64_lit2, hws_c2_val]; omega
            have hco2_eq : wvec[(((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64) +
                (1 : BitVec 64)).toNat]'hws_c2_bd).setWidth 64) <<< (1 : Nat)).toNat]'hwvc2 =
                wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32 := by
              have hidx : (((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64) +
                  (1 : BitVec 64)).toNat]'hws_c2_bd).setWidth 64) <<< (1 : Nat)).toNat =
                  2 * Spec.wsVal wsS (2 * root.toNat + 2) := by
                rw [bv64_lit2, hws_c2_val, wsVal_getElem (by omega)]
              rw [List.getElem?_eq_getElem (by rw [← hidx]; exact hwvc2), Option.getD_some]
              exact list_getElem_congr hwvc2 hidx
            have hco1_raw_bd :
                2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                  rw [h1_bv, Nat.mod_eq_of_lt (by omega)]; omega)).toNat % 2 ^ 64 <
                  wvec.length := by
              have hi : (2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * root.toNat + 1 := by
                rw [h1_bv, Nat.mod_eq_of_lt (by omega)]
              have hv := list_getElem_congr (xs := wsS) (i := (2 * root.toNat +
                (1 : BitVec 64).toNat) % 2 ^ 64) (by rw [hi]; omega) hi
              rw [hv, Nat.mod_eq_of_lt (by omega)]; omega
            have hco1_raw :
                wvec[2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                  rw [h1_bv, Nat.mod_eq_of_lt (by omega)]; omega)).toNat % 2 ^ 64]'hco1_raw_bd =
                wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32 := by
              have hi : (2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * root.toNat + 1 := by
                rw [h1_bv, Nat.mod_eq_of_lt (by omega)]
              have hidx : 2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                  rw [hi]; omega)).toNat % 2 ^ 64 = 2 * Spec.wsVal wsS (2 * root.toNat + 1) := by
                have hv := list_getElem_congr (xs := wsS) (i := (2 * root.toNat +
                  (1 : BitVec 64).toNat) % 2 ^ 64) (by rw [hi]; omega) hi
                rw [hv, wsVal_getElem (by omega), Nat.mod_eq_of_lt (by omega)]
              rw [List.getElem?_eq_getElem (by rw [← hidx]; exact hco1_raw_bd), Option.getD_some]
              exact list_getElem_congr hco1_raw_bd hidx
            have hco2_raw_bd :
                2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) %
                  2 ^ 64]'(by rw [h1_bv, Nat.mod_eq_of_lt (by omega)]; omega)).toNat % 2 ^ 64 <
                  wvec.length := by
              have hi : (2 * root.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                  2 * root.toNat + 2 := by
                rw [h1_bv, Nat.mod_eq_of_lt (by omega)]
              have hv := list_getElem_congr (xs := wsS) (i := (2 * root.toNat +
                (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64) (by rw [hi]; omega) hi
              rw [hv, Nat.mod_eq_of_lt (by omega)]; omega
            have hco2_raw :
                wvec[2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) %
                  2 ^ 64]'(by rw [h1_bv, Nat.mod_eq_of_lt (by omega)]; omega)).toNat %
                  2 ^ 64]'hco2_raw_bd =
                wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32 := by
              have hi : (2 * root.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                  2 * root.toNat + 2 := by
                rw [h1_bv, Nat.mod_eq_of_lt (by omega)]
              have hidx : 2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat +
                  (1 : BitVec 64).toNat) % 2 ^ 64]'(by rw [hi]; omega)).toNat % 2 ^ 64 =
                  2 * Spec.wsVal wsS (2 * root.toNat + 2) := by
                have hv := list_getElem_congr (xs := wsS) (i := (2 * root.toNat +
                  (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64) (by rw [hi]; omega) hi
                rw [hv, wsVal_getElem (by omega), Nat.mod_eq_of_lt (by omega)]
              rw [List.getElem?_eq_getElem (by rw [← hidx]; exact hco2_raw_bd), Option.getD_some]
              exact list_getElem_congr hco2_raw_bd hidx
            clear hc
            c0_hstraight
            refine wp_join_group (fun (ch, co, ()) mJ =>
              mS = mJ ∧
              (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
              ch.toNat < n.toNat ∧
              co = wvec[2 * Spec.wsVal wsS ch.toNat]?.getD 0#32 ∧
              (2 * root.toNat + 1 < n.toNat →
                (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat ≤ co.toNat) ∧
              (2 * root.toNat + 2 < n.toNat →
                (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat ≤ co.toNat)) ?_ ?_
            · rintro _ ⟨ch, co, ⟨⟩⟩ mJ ⟨hmJ, h1, h2, h3, h4, h5⟩
              subst hmJ
              c0_hstraight
              exact hJ2 (ch, co, ()) mS ⟨h1, h2, h3, h4, h5, rfl⟩
            · intro J3 hJ3
              c0_hsplit
              · have hgt : (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat <
                    (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat := by
                  rw [← hco1_raw, ← hco2_raw]; omega
                clear hc
                c0_hstraight
                refine hJ3 _ mS ⟨rfl, Or.inr hc2_eq, by rw [hc2_eq]; exact hch2_lt,
                  by rw [hco2_eq, hc2_eq], fun _ => by rw [hco2_eq]; omega,
                  fun _ => by rw [hco2_eq]; exact Nat.le_refl _⟩
              · have hle : (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat ≤
                    (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat := by
                  rw [← hco1_raw, ← hco2_raw]; omega
                clear hc
                c0_hstraight
                refine hJ3 _ mS ⟨rfl, Or.inl hc1_nat, by rw [hc1_nat]; omega,
                  by rw [hco1_eq, hc1_nat], fun _ => by rw [hco1_eq]; exact Nat.le_refl _,
                  fun _ => by rw [hco1_eq]; omega⟩
          · rw [h1_bv] at hc
            have hc2_ge : n.toNat ≤ 2 * root.toNat + 2 := by
              have hc2_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                  2 * root.toNat + 2 := by
                rw [BitVec.toNat_add, hc1_nat]; simp; omega
              omega
            clear hc
            c0_hstraight
            exact hJ2 _ mS ⟨Or.inl hc1_nat, by rw [hc1_nat]; omega, by rw [hco1_eq, hc1_nat],
              fun _ => by rw [hco1_eq]; exact Nat.le_refl _, fun h => by omega, rfl⟩
    · cases hc

end LeanQbe.T.Examples.Kissat.Proof.Watch

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Watch
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1

import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.ProofKit

/-! # Watch WP Shared Helpers (`Proof.Watch.Helpers`)

Shared pure `BitVec` / `List` / `WsCovers` / `swapIdx` / `wvec` / `ModeWatchesInv` /
`FullMem` lemmas reused across `Proof/Watch/Wp0..Wp7a`. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Grind
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec

public section

/-! ## 1. Shared Predicates & `FullRestNoWatch` -/

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

/-! ## 2. BitVec & List Indexing / Arithmetic Bridges -/

theorem bv64_shl1_lit (lit : BitVec 32) :
    (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
  have := lit.isLt; c0_bv_omega

theorem bv64_shl1_add1_lit (lit : BitVec 32) :
    ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * lit.toNat + 1 := by
  have := lit.isLt; rw [BitVec.toNat_add, bv64_shl1_lit]; c0_bv_omega

theorem bv64_shl1_mod {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  c0_bv_omega

theorem bv64_shr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  c0_bv_omega

theorem bv64_ofNat_toNat_id {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  c0_bv_omega

theorem bv64_add1_nat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by
  c0_bv_omega

theorem bv64_ofNat_add1 {n : Nat} (hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + (1 : BitVec 64) = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq; c0_bv_omega

theorem bv64_sub1_nat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - (1 : BitVec 64)).toNat = x.toNat - 1 := by
  c0_bv_omega

theorem bv64_add_ofNat (a b : Nat) (h : a + b < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat = a + b := by
  c0_bv_omega

theorem bv64_add_setWidth (a : Nat) (b : BitVec 32) (h : a + b.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.setWidth 64 b).toNat = a + b.toNat := by
  have := b.isLt; c0_bv_omega

theorem bv32_trunc_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  c0_bv_omega

theorem bv32_ofNat_64 (a : Nat) :
    (BitVec.ofNat 64 a).setWidth 32 = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq; simp

theorem bv64_eq_zero_of_not_pos {x : BitVec 64} (h : ¬ (0 : BitVec 64) < x) :
    x.toNat = 0 := by
  c0_bv_omega

theorem bv64_eq_zero_of_not_pos_nat {x : BitVec 64} (h : ¬ 0 < x.toNat) : x = 0#64 :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)

theorem bv32_eq_nat {x : BitVec 32} (k : Nat) (hk : k < 2 ^ 32)
    (h : x = BitVec.ofNat 32 k) : x.toNat = k := by
  subst h; c0_bv_omega

theorem bv32_ne_nat {x : BitVec 32} (k : Nat) (hk : k < 2 ^ 32)
    (h : x ≠ BitVec.ofNat 32 k) : x.toNat ≠ k :=
  fun heq => h (BitVec.eq_of_toNat_eq (by simpa [bv32_ofNat_toNat hk] using heq))

theorem bv64_eq_nat {x : BitVec 64} (k : Nat) (hk : k < 2 ^ 64)
    (h : x = BitVec.ofNat 64 k) : x.toNat = k := by
  subst h; c0_bv_omega

theorem bv64_ne_nat {x : BitVec 64} (k : Nat) (hk : k < 2 ^ 64)
    (h : x ≠ BitVec.ofNat 64 k) : x.toNat ≠ k :=
  fun heq => h (BitVec.eq_of_toNat_eq (by simpa [Proof.Spec.bv64_ofNat_toNat hk] using heq))

theorem bv64_zext_eq_zero {x : BitVec 32} (h : x.setWidth 64 = 0#64) : x.toNat = 0 := by
  have := x.isLt; c0_bv_omega

theorem bv64_zext_pos {x : BitVec 32} (h : x.setWidth 64 ≠ 0#64) : 0 < x.toNat :=
  Nat.pos_of_ne_zero fun h0 => h (BitVec.eq_of_toNat_eq (by c0_bv_omega))

theorem list_getElem_congr {α : Type _} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) :
    xs[i]'hi = xs[j]'(hij ▸ hi) := by
  subst hij; rfl

theorem list_getElem_toNat_eq {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hji : j = i) :
    (xs[j]'(hji ▸ hi)).toNat = (xs[i]'hi).toNat := by
  subst hji; rfl

theorem list_getElem_getD_eq {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) :
    xs[i]'hi = xs[j]?.getD 0#32 := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem list_getElem_toNat_getD {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) :
    (xs[i]'hi).toNat = (xs[j]?.getD 0#32).toNat := by
  rw [list_getElem_getD_eq hi hij]

theorem list_zext64_eq_zero {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (heq : j = i)
    (h : (xs[j]'hj).setWidth 64 = 0#64) : (xs[i]?.getD 0#32).toNat = 0 := by
  subst heq; rw [List.getElem?_eq_getElem hi]; exact bv64_zext_eq_zero h

theorem list_zext64_pos {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (heq : j = i)
    (h : (xs[j]'hj).setWidth 64 ≠ 0#64) : 0 < (xs[i]?.getD 0#32).toNat := by
  subst heq; rw [List.getElem?_eq_getElem hi]; exact bv64_zext_pos h

theorem wsVal_getElem {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    Spec.wsVal xs i = (xs[i]'hi).toNat := by
  unfold Spec.wsVal; rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem wsVal_lt_2p32 (xs : List (BitVec 32)) (i : Nat) : Spec.wsVal xs i < 2 ^ 32 :=
  (xs[i]?.getD 0#32).isLt

/-! ## 3. Permutation, `swapIdx`, & `WsCovers` Helpers -/

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
  | nil => cases ys with | nil => exact .nil | cons _ _ => simp at hlen
  | cons a t ih =>
    have ha_nd := List.nodup_cons.mp hnd
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem (hsub a List.mem_cons_self)
    refine (List.Perm.cons a (ih ha_nd.2 (fun x hx => ?_) (by simp at hlen ⊢; omega))).trans
      List.perm_middle.symm
    have hxy := hsub x (List.mem_cons_of_mem a hx)
    simp only [List.mem_append, List.mem_cons] at hxy ⊢
    rcases hxy with h | rfl | h
    · exact Or.inl h
    · exact absurd hx ha_nd.1
    · exact Or.inr h

theorem swapIdx_length {xs : List (BitVec 32)} {i j : Nat} :
    (swapIdx xs i j).length = xs.length := by
  unfold swapIdx; split <;> simp [List.length_set]

theorem swapIdx_getElem_self {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapIdx xs i j)[i]'(by rw [swapIdx_length]; exact hi) = xs[j]'hj ∧
    (swapIdx xs i j)[j]'(by rw [swapIdx_length]; exact hj) = xs[i]'hi := by
  unfold swapIdx; split
  · by_cases hij : i = j
    · subst hij; simp
    · exact ⟨by rw [List.getElem_set_ne (Ne.symm hij), List.getElem_set_self],
        by rw [List.getElem_set_self]⟩
  · next h => exact absurd ⟨hi, hj⟩ h

theorem swapIdx_getElem_other {xs : List (BitVec 32)} {i j k : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (hk : k < xs.length)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (swapIdx xs i j)[k]'(by rw [swapIdx_length]; exact hk) = xs[k]'hk := by
  unfold swapIdx; split
  · rw [List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hki)]
  · next h => exact absurd ⟨hi, hj⟩ h

theorem swapIdx_perm {xs : List (BitVec 32)} {i j : Nat} :
    (swapIdx xs i j).Perm xs := by
  unfold swapIdx; split
  case isFalse => exact List.Perm.refl xs
  case isTrue h =>
    by_cases hij : i = j
    · subst hij; simp [List.set_getElem_self h.1]
    · rw [List.perm_iff_count]; intro x
      rw [List.count_set (by rw [List.length_set]; exact h.2), List.count_set h.1,
        List.getElem_set_ne hij]
      by_cases hxi : xs[i]'h.1 = x <;> by_cases hxj : xs[j]'h.2 = x <;> simp [hxi, hxj] <;>
        first
        | (have := List.count_pos_iff.mpr (hxi ▸ List.getElem_mem h.1); omega)
        | (have := List.count_pos_iff.mpr (hxj ▸ List.getElem_mem h.2); omega)

theorem wsVal_swap {xs : List (BitVec 32)} {i j k : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    Spec.wsVal (swapIdx xs i j) k =
      if k = i then Spec.wsVal xs j
      else if k = j then Spec.wsVal xs i
      else Spec.wsVal xs k := by
  have heq : swapIdx xs i j = (xs.set i (xs[j]'hj)).set j (xs[i]'hi) := by
    simp [swapIdx, hi, hj]
  unfold Spec.wsVal; rw [heq]
  by_cases hki : k = i
  · subst hki; by_cases hkj : k = j
    · subst hkj; simp [List.getElem?_eq_getElem hi]
    · simp only [↓reduceIte]
      rw [List.getElem?_eq_getElem (by simp [hi]), List.getElem?_eq_getElem hj,
        List.getElem_set_ne (Ne.symm hkj), List.getElem_set_self]
  · by_cases hkj : k = j
    · subst hkj; simp only [hki, ↓reduceIte]
      rw [List.getElem?_eq_getElem (by simp [hj]), List.getElem?_eq_getElem hi,
        List.getElem_set_self]
    · simp only [hki, ↓reduceIte, hkj]
      rw [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hki)]

theorem wsCovers_swap {ws : List (BitVec 32)} {n nlits : Nat} {sz : Nat → Nat}
    (hcov : WsCovers ws n nlits sz) {i j : Nat} (hi : i < n) (hj : j < n)
    (hil : i < ws.length) (hjl : j < ws.length) :
    WsCovers (swapIdx ws i j) n nlits sz := by
  let p : Nat → Nat := fun a => if a = i then j else if a = j then i else a
  have hp_lt : ∀ a < n, p a < n := fun a ha => by
    dsimp only [p]; split; exact hj; split; exact hi; exact ha
  have hp_inv : ∀ a, p (p a) = a := fun a => by dsimp only [p]; c0_grind
  have hp_inj : ∀ a b, p a = p b → a = b := fun a b hab => by rw [← hp_inv a, ← hp_inv b, hab]
  have h1 : ∀ a, Spec.wsVal (swapIdx ws i j) a = Spec.wsVal ws (p a) := fun a => by
    rw [wsVal_swap hil hjl]; dsimp only [p]
    by_cases hij : i = j <;> by_cases ha1 : a = i <;> by_cases ha2 : a = j <;> simp_all
  refine ⟨fun a ha => h1 a ▸ hcov.1 (p a) (hp_lt a ha),
    fun a ha b hb hab => h1 a ▸ h1 b ▸ hcov.2.1 (p a) (hp_lt a ha) (p b) (hp_lt b hb)
      (fun h => hab (hp_inj a b h)),
    fun l hl hsz => ?_⟩
  obtain ⟨k, hk, hkl⟩ := hcov.2.2 l hl hsz
  exact ⟨p k, hp_lt k hk, by rw [h1 (p k), hp_inv k]; exact hkl⟩

theorem wsCovers_of_perm_suffix {ws ws' : List (BitVec 32)} {n nlits : Nat} {sz : Nat → Nat}
    (hcov : WsCovers ws n nlits sz) (hperm : (ws'.take n).Perm (ws.take n))
    (hle : n ≤ ws.length) (hle' : n ≤ ws'.length) :
    WsCovers ws' n nlits sz := by
  have hmem1 : ∀ j < n, ∃ k < n, ws'[j]? = ws[k]? := fun j hj => by
    have hin0 : (ws'.take n)[j]'(by rw [List.length_take]; omega) ∈ ws'.take n :=
      List.getElem_mem _
    have hin : ws'[j]'(by omega) ∈ ws.take n :=
      hperm.mem_iff.mp (by simpa [List.getElem_take] using hin0)
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hin
    have hkn : k < n := by simp [hle] at hk; exact hk
    rw [List.getElem_take] at hkeq
    exact ⟨k, hkn, by rw [List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega), hkeq]⟩
  have hmem2 : ∀ k < n, ∃ j < n, ws'[j]? = ws[k]? := fun k hk => by
    have hin0 : (ws.take n)[k]'(by rw [List.length_take]; omega) ∈ ws.take n :=
      List.getElem_mem _
    have hin : ws[k]'(by omega) ∈ ws'.take n :=
      hperm.symm.mem_iff.mp (by simpa [List.getElem_take] using hin0)
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hin
    have hjn : j < n := by simp [hle'] at hj; exact hj
    rw [List.getElem_take] at hjeq
    exact ⟨j, hjn, by rw [List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega), hjeq]⟩
  have hnd : (ws.take n).Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    have hin : i < n := by simp [hle] at hi; exact hi
    have hjn : j < n := by simp [hle] at hj; exact hj
    simp only [List.getElem_take] at heq
    exact hcov.2.1 i hin j hjn (by omega) (by
      unfold Spec.wsVal; rw [List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (by omega), heq])
  have hnd' := hperm.nodup_iff.mpr hnd
  refine ⟨fun j hj => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · obtain ⟨k, hk, hjk⟩ := hmem1 j hj
    have hveq : Spec.wsVal ws' j = Spec.wsVal ws k := by unfold Spec.wsVal; rw [hjk]
    rw [hveq]; exact hcov.1 k hk
  · obtain ⟨ka, hka, hja⟩ := hmem1 a ha
    obtain ⟨kb, hkb, hjb⟩ := hmem1 b hb
    have hne_val : ws'[a]'(by omega) ≠ ws'[b]'(by omega) := fun heq => by
      have hpw := List.pairwise_iff_getElem.mp hnd'
      rcases Nat.lt_trichotomy a b with hlt | heq_ab | hgt
      · exact hpw a b (by simp; omega) (by simp; omega) hlt
          (by simpa [List.getElem_take] using heq)
      · exact hab heq_ab
      · exact hpw b a (by simp; omega) (by simp; omega) hgt
          (by simpa [List.getElem_take] using heq.symm)
    have hkab : ka ≠ kb := fun heq => by
      subst heq; apply hne_val
      have h1 := hja.trans hjb.symm
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
    have hva : Spec.wsVal ws' a = Spec.wsVal ws ka := by unfold Spec.wsVal; rw [hja]
    have hvb : Spec.wsVal ws' b = Spec.wsVal ws kb := by unfold Spec.wsVal; rw [hjb]
    rw [hva, hvb]; exact hcov.2.1 ka hka kb hkb hkab
  · obtain ⟨k, hk, hkl⟩ := hcov.2.2 l hl hsz
    obtain ⟨j, hj, hjk⟩ := hmem2 k hk
    exact ⟨j, hj, by unfold Spec.wsVal at hkl ⊢; rw [hjk]; exact hkl⟩

theorem wsortMaxHeap_root_ge {wvec ws : List (BitVec 32)} {n : Nat}
    (hmh : FullWsortMaxHeap wvec ws 0 n) (_hn : 0 < n) :
    ∀ j < n, Spec.fullWvecOff wvec (Spec.wsVal ws j) ≤
      Spec.fullWvecOff wvec (Spec.wsVal ws 0) := by
  intro j hj
  refine Nat.strongRecOn (motive := fun k =>
      k < n → Spec.fullWvecOff wvec (Spec.wsVal ws k) ≤ Spec.fullWvecOff wvec (Spec.wsVal ws 0))
    j (fun k ih hk => ?_) hj
  rcases Nat.eq_zero_or_pos k with rfl | _
  · exact Nat.le_refl _
  · have hle_par := ih ((k - 1) / 2) (by omega) (by omega)
    have hpar := hmh ((k - 1) / 2) (Nat.zero_le _) (by omega)
    dsimp only [Spec.fullWvecOff, Spec.wsVal] at hle_par hpar ⊢
    rcases (by omega : 2 * ((k - 1) / 2) + 1 = k ∨ 2 * ((k - 1) / 2) + 2 = k) with hc | hc
    · have h1 := hpar.1 (by omega); rw [hc] at h1; exact Nat.le_trans h1 hle_par
    · have h2 := hpar.2 (by omega); rw [hc] at h2; exact Nat.le_trans h2 hle_par

/-! ## 4. `FullMem`, `wvec`, & `ModeWatchesInv` Helpers -/

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
  rw [array_append] at h; exact h

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

theorem wvec_set_even_eq {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) :
    ∀ j,
      (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
      (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
      (wvec.set (2 * l) v)[2 * l]? = some v := fun j =>
  ⟨List.getElem?_set_ne (by omega), fun hj => List.getElem?_set_ne (by omega),
    List.getElem?_set_self hl⟩

theorem wvec_set_odd_eq {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l + 1 < wvec.length) :
    ∀ j,
      (wvec.set (2 * l + 1) v)[2 * j]? = wvec[2 * j]? ∧
      (j ≠ l → (wvec.set (2 * l + 1) v)[2 * j + 1]? = wvec[2 * j + 1]?) ∧
      (wvec.set (2 * l + 1) v)[2 * l + 1]? = some v := fun j =>
  ⟨List.getElem?_set_ne (by omega), fun hj => List.getElem?_set_ne (by omega),
    List.getElem?_set_self hl⟩

theorem wvec_set_size_off_self {wvec : List (BitVec 32)} {lit : Nat}
    (_h1 : 2 * lit + 1 < wvec.length) (sz' : BitVec 32) :
    (wvec.set (2 * lit + 1) sz')[2 * lit]?.getD 0#32 = wvec[2 * lit]?.getD 0#32 := by
  rw [List.getElem?_set_ne (by omega)]

theorem wvec_set_size_sz_self {wvec : List (BitVec 32)} {lit : Nat}
    (h1 : 2 * lit + 1 < wvec.length) (sz' : BitVec 32) :
    (wvec.set (2 * lit + 1) sz')[2 * lit + 1]?.getD 0#32 = sz' := by
  rw [List.getElem?_set_self h1, Option.getD_some]

theorem wvec_set_size_other {wvec : List (BitVec 32)} {lit l : Nat}
    (hne : l ≠ lit) (sz' : BitVec 32) :
    (wvec.set (2 * lit + 1) sz')[2 * l]?.getD 0#32 = wvec[2 * l]?.getD 0#32 ∧
    (wvec.set (2 * lit + 1) sz')[2 * l + 1]?.getD 0#32 = wvec[2 * l + 1]?.getD 0#32 :=
  ⟨by rw [List.getElem?_set_ne (by omega)], by rw [List.getElem?_set_ne (by omega)]⟩

theorem wvec_shl1_lt {c : FullCfg} {k : FullCoreState}
    (hlen : k.LengthsOk c) {lit : Val i32} (hlit : lit.toNat < 2 * k.cur_vars) :
    2 * lit.toNat < k.wvec.length ∧
    2 * lit.toNat + 1 < k.wvec.length ∧
    (lit.setWidth 64 <<< 1).toNat < k.wvec.length ∧
    (lit.setWidth 64 <<< 1 + 1).toNat < k.wvec.length ∧
    2 * lit.toNat % 2 ^ 64 < k.wvec.length ∧
    (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < k.wvec.length ∧
    2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat ∧
    (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have h0 : 2 * lit.toNat < k.wvec.length := by omega
  have h1 : 2 * lit.toNat + 1 < k.wvec.length := by omega
  have hm0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have hm1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  exact ⟨h0, h1, by rw [bv64_shl1_lit]; exact h0, by rw [bv64_shl1_add1_lit]; exact h1,
    by rw [hm0]; exact h0, by rw [hm1]; exact h1, hm0, hm1⟩

theorem wvec_init_off_eq {c : FullCfg} {k : FullCoreState}
    (_hl_k : FullCoreState.LengthsOk c k)
    {lit : Val i32} (_hlit : lit.toNat < 2 * k.cur_vars)
    (h0 : (BitVec.setWidth 64 lit <<< 1).toNat < k.wvec.length) :
    BitVec.setWidth 64 k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] =
      BitVec.ofNat 64 (fullWatchOffCore k lit.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hsh := bv64_shl1_lit lit
  have hwv0 : 2 * lit.toNat < k.wvec.length := hsh ▸ h0
  have hget : k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] = k.wvec[2 * lit.toNat] := by congr 1
  rw [hget]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, fullWatchOffCore,
    List.getElem?_eq_getElem hwv0, Option.getD_some]

theorem wvec_end_add_eq {c : FullCfg} {k : FullCoreState}
    (_hl_k : FullCoreState.LengthsOk c k)
    {lit : Val i32} (_hlit : lit.toNat < 2 * k.cur_vars)
    (h0 : (BitVec.setWidth 64 lit <<< 1).toNat < k.wvec.length)
    (h1 : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < k.wvec.length) :
    (BitVec.setWidth 64 k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] +
      BitVec.setWidth 64 k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]).toNat =
      fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat := by
  have hwv0 : 2 * lit.toNat < k.wvec.length := (bv64_shl1_lit lit) ▸ h0
  have hwv1 : 2 * lit.toNat + 1 < k.wvec.length := (bv64_shl1_add1_lit lit) ▸ h1
  have hg0 : k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] = k.wvec[2 * lit.toNat] := by
    congr 1; exact bv64_shl1_lit lit
  have hg1 : k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat] = k.wvec[2 * lit.toNat + 1] := by
    congr 1; exact bv64_shl1_add1_lit lit
  rw [hg0, hg1]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, fullWatchOffCore, fullWatchSizeCore,
    List.getElem?_eq_getElem hwv0, List.getElem?_eq_getElem hwv1, Option.getD_some]
  have := (k.wvec[2 * lit.toNat]'hwv0).isLt
  have := (k.wvec[2 * lit.toNat + 1]'hwv1).isLt
  omega

theorem modeWatchesInv_eq_watches {F_cur : List (List Nat)} {k : FullCoreState}
    (h : k.dense_mode = 0#64) : ModeWatchesInv F_cur k = WatchesInv F_cur k := by
  unfold ModeWatchesInv; simp [h]

theorem modeWatchesInv_eq_dense {F_cur : List (List Nat)} {k : FullCoreState}
    (h : k.dense_mode ≠ 0#64) : ModeWatchesInv F_cur k = DenseWatchesInv F_cur k := by
  unfold ModeWatchesInv; simp [h]

theorem modeWatchesInv_slice {F_cur : List (List Nat)} {k : FullCoreState} {l : Nat}
    (hw : ModeWatchesInv F_cur k) (hl : l < 2 * k.cur_vars) :
    WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  by_cases hdm : k.dense_mode = 0#64
  · rw [modeWatchesInv_eq_watches hdm] at hw; exact hw.slices l hl
  · rw [modeWatchesInv_eq_dense hdm] at hw; exact (hw.slices l hl).toWatchSliceOk

theorem modeWatchesInv_slice_mode {F_cur : List (List Nat)} {k : FullCoreState} {l : Nat}
    (hw : ModeWatchesInv F_cur k) (hl : l < 2 * k.cur_vars) :
    if k.dense_mode = 0#64 then
      WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)
    else DenseWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  by_cases hdm : k.dense_mode = 0#64
  · rw [modeWatchesInv_eq_watches hdm] at hw; simp [hdm, hw.slices l hl]
  · rw [modeWatchesInv_eq_dense hdm] at hw; simp [hdm, hw.slices l hl]

end

end LeanQbe.T.Examples.Kissat.Proof.Watch

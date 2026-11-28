/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp0
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

/-! # Watch WP Proofs Part 1: `full_wstack_radix_sort_m6`

Self-contained `CanonicalEnv` WP proof for `full_wstack_radix_sort_m6`. -/

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Std.ExtHashMap

private def countEqUpTo (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    (k b : Nat) : Nat :=
  ((xs.take k).filter (fun x => f x == b)).length

private def countLt (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    (k b : Nat) : Nat :=
  ((xs.take k).filter (fun x => f x < b)).length

private def bktPlace (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    (n j : Nat) : Nat :=
  countLt f xs n (f (xs[j]?.getD 0#32)) + countEqUpTo f xs j (f (xs[j]?.getD 0#32))

private theorem countLt_zero (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    (k : Nat) : countLt f xs k 0 = 0 := by
  unfold countLt
  induction (xs.take k) <;> simp [*]

private theorem countEqUpTo_zero (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    (b : Nat) : countEqUpTo f xs 0 b = 0 := by
  simp [countEqUpTo]

private theorem countEqUpTo_succ (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    {k : Nat} (hk : k < xs.length) (b : Nat) :
    countEqUpTo f xs (k + 1) b =
      countEqUpTo f xs k b + if f (xs[k]'hk) == b then 1 else 0 := by
  unfold countEqUpTo
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp

private theorem countEqUpTo_succ_self (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    {j : Nat} (hj : j < xs.length) :
    countEqUpTo f xs j (f (xs[j]?.getD 0#32)) + 1 ≤
      countEqUpTo f xs (j + 1) (f (xs[j]?.getD 0#32)) := by
  rw [countEqUpTo_succ f xs hj, List.getElem?_eq_getElem hj, Option.getD_some]
  simp

private theorem countEqUpTo_mono {f : BitVec 32 → Nat} {xs : List (BitVec 32)}
    {b a m : Nat} (ham : a ≤ m) :
    countEqUpTo f xs a b ≤ countEqUpTo f xs m b := by
  induction m with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact Nat.le_refl _
  | succ k ih =>
    by_cases hak : a = k + 1
    · subst hak; exact Nat.le_refl _
    · by_cases hklen : k < xs.length
      · have := countEqUpTo_succ f xs hklen b
        have := ih (by omega)
        omega
      · have h1 : countEqUpTo f xs (k + 1) b = countEqUpTo f xs k b := by
          unfold countEqUpTo
          rw [List.take_of_length_le (l := xs) (i := k + 1) (by omega),
            List.take_of_length_le (l := xs) (i := k) (by omega)]
        rw [h1]; exact ih (by omega)

private theorem countLt_succ_bkt (f : BitVec 32 → Nat) (xs : List (BitVec 32))
    (k b : Nat) :
    countLt f xs k (b + 1) = countLt f xs k b + countEqUpTo f xs k b := by
  unfold countLt countEqUpTo
  induction (xs.take k) with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    by_cases h1 : f a < b
    · have h2 : f a < b + 1 := by omega
      have h3 : (f a == b) = false := beq_false_of_ne (by omega)
      simp [h1, h2, h3, ih]; omega
    · by_cases h2 : f a = b
      · subst h2
        have h3 : f a < f a + 1 := Nat.lt_succ_self _
        simp [h1, h3, ih]; omega
      · have h3 : ¬ (f a < b + 1) := by omega
        have h4 : (f a == b) = false := beq_false_of_ne h2
        simp [h1, h3, h4, ih]

private theorem countLt_mono {f : BitVec 32 → Nat} {xs : List (BitVec 32)}
    {n a b : Nat} (hab : a ≤ b) :
    countLt f xs n a ≤ countLt f xs n b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact Nat.le_refl _
  | succ k ih =>
    by_cases hak : a = k + 1
    · subst hak; exact Nat.le_refl _
    · rw [countLt_succ_bkt]; have := ih (by omega); omega

private theorem countLt_eq_length {f : BitVec 32 → Nat} {xs : List (BitVec 32)}
    {n B : Nat} (hle : n ≤ xs.length) (hf : ∀ j < n, f (xs[j]?.getD 0#32) < B) :
    countLt f xs n B = n := by
  have h1 : (xs.take n).filter (fun x => f x < B) = xs.take n := by
    rw [List.filter_eq_self]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hjn : j < n := by simp [hle] at hj; exact hj
    rw [List.getElem_take]
    have hjf := hf j hjn
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hjf
    exact decide_eq_true hjf
  unfold countLt; rw [h1, List.length_take]; omega

private theorem countLt_add_countEq_lt {f : BitVec 32 → Nat} {xs : List (BitVec 32)}
    {n j : Nat} (hj : j < n) (hle : n ≤ xs.length)
    (hf : ∀ i < n, f (xs[i]?.getD 0#32) < 256) :
    bktPlace f xs n j < n := by
  unfold bktPlace
  let b := f (xs[j]?.getD 0#32)
  have hb : b < 256 := hf j hj
  have hs := countLt_succ_bkt f xs n b
  have hsucc : countEqUpTo f xs j b + 1 ≤ countEqUpTo f xs (j + 1) b :=
    countEqUpTo_succ_self f xs (Nat.lt_of_lt_of_le hj hle)
  have hmono := countEqUpTo_mono (f := f) (xs := xs) (b := b) (by omega : j + 1 ≤ n)
  have htot := countLt_mono (f := f) (xs := xs) (n := n) (by omega : b + 1 ≤ 256)
  rw [countLt_eq_length hle hf] at htot
  rw [hs] at htot
  change countLt f xs n b + countEqUpTo f xs j b < n
  omega

private theorem bktPlace_inj {f : BitVec 32 → Nat} {xs : List (BitVec 32)}
    {n i j : Nat} (hij : i < j) (hj : j < n) (hle : n ≤ xs.length)
    (_hf : ∀ k < n, f (xs[k]?.getD 0#32) < 256) :
    bktPlace f xs n i ≠ bktPlace f xs n j := by
  unfold bktPlace
  let bi := f (xs[i]?.getD 0#32)
  let bj := f (xs[j]?.getD 0#32)
  change countLt f xs n bi + countEqUpTo f xs i bi ≠ countLt f xs n bj + countEqUpTo f xs j bj
  rcases Nat.lt_trichotomy bi bj with hlt | heq | hgt
  · have hsucc : countEqUpTo f xs i bi + 1 ≤ countEqUpTo f xs (i + 1) bi :=
      countEqUpTo_succ_self f xs (by omega)
    have h1 := countEqUpTo_mono (f := f) (xs := xs) (b := bi) (by omega : i + 1 ≤ n)
    have h2 := countLt_succ_bkt f xs n bi
    have h3 := countLt_mono (f := f) (xs := xs) (n := n) (show bi + 1 ≤ bj from hlt)
    omega
  · rw [heq]
    have hsucc : countEqUpTo f xs i bj + 1 ≤ countEqUpTo f xs (i + 1) bj := by
      simpa only [bi, bj, heq] using countEqUpTo_succ_self f xs (by omega : i < xs.length)
    have h1 := countEqUpTo_mono (f := f) (xs := xs) (b := bj) (by omega : i + 1 ≤ j)
    omega
  · have hsucc : countEqUpTo f xs j bj + 1 ≤ countEqUpTo f xs (j + 1) bj :=
      countEqUpTo_succ_self f xs (by omega)
    have h1 := countEqUpTo_mono (f := f) (xs := xs) (b := bj) (by omega : j + 1 ≤ n)
    have h2 := countLt_succ_bkt f xs n bj
    have h3 := countLt_mono (f := f) (xs := xs) (n := n) (show bj + 1 ≤ bi from hgt)
    omega

private theorem radix_mod_split (key : BitVec 32 → Nat) (sh : Nat) (x : BitVec 32) :
    key x % 2 ^ (sh + 8) = ((key x / 2 ^ sh) % 256) * 2 ^ sh + key x % 2 ^ sh := by
  have hpow : 2 ^ (sh + 8) = 2 ^ sh * 256 := Nat.pow_add 2 sh 8
  have hdiv2 : key x / 2 ^ sh = (key x % 2 ^ (sh + 8)) / 2 ^ sh +
      256 * (key x / 2 ^ (sh + 8)) := by
    have hm1 := Nat.div_add_mod (key x) (2 ^ (sh + 8))
    have hm2 := Nat.div_add_mod (key x % 2 ^ (sh + 8)) (2 ^ sh)
    have h1 : key x = 2 ^ sh * ((key x % 2 ^ (sh + 8)) / 2 ^ sh +
        256 * (key x / 2 ^ (sh + 8))) + (key x % 2 ^ (sh + 8)) % 2 ^ sh := by
      rw [Nat.mul_add, ← Nat.mul_assoc, ← hpow]
      omega
    have hlt : (key x % 2 ^ (sh + 8)) % 2 ^ sh < 2 ^ sh :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero (by simp))
    calc key x / 2 ^ sh
        = (2 ^ sh * ((key x % 2 ^ (sh + 8)) / 2 ^ sh + 256 * (key x / 2 ^ (sh + 8))) +
            (key x % 2 ^ (sh + 8)) % 2 ^ sh) / 2 ^ sh := by rw [← h1]
      _ = (key x % 2 ^ (sh + 8)) / 2 ^ sh + 256 * (key x / 2 ^ (sh + 8)) := by
        rw [Nat.mul_add_div (Nat.pos_of_ne_zero (by simp)), Nat.div_eq_of_lt hlt, Nat.add_zero]
  have hlt_b : (key x % 2 ^ (sh + 8)) / 2 ^ sh < 256 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (by simp))]
    calc key x % 2 ^ (sh + 8) < 2 ^ (sh + 8) := Nat.mod_lt _ (Nat.pos_of_ne_zero (by simp))
      _ = 256 * 2 ^ sh := by rw [hpow, Nat.mul_comm]
  have hf_eq : (key x / 2 ^ sh) % 256 = (key x % 2 ^ (sh + 8)) / 2 ^ sh := by
    rw [hdiv2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_b]
  have hmod_eq : key x % 2 ^ sh = (key x % 2 ^ (sh + 8)) % 2 ^ sh := by
    rw [← Nat.mod_mod_of_dvd (key x) (Nat.pow_dvd_pow 2 (by omega : sh ≤ sh + 8))]
  have hm := Nat.div_add_mod (key x % 2 ^ (sh + 8)) (2 ^ sh)
  rw [hf_eq, hmod_eq, Nat.mul_comm _ (2 ^ sh)]; omega

private theorem radix_scatter_post {key : BitVec 32 → Nat} {sh n : Nat}
    {ws tmp : List (BitVec 32)}
    (hn_ws : n ≤ ws.length) (hn_tmp : n ≤ tmp.length)
    (hsrt0 : Spec.SortedRange (fun l => (key (BitVec.ofNat 32 l)) % 2 ^ sh) ws 0 n)
    (hplace : ∀ i < n,
      tmp[bktPlace (fun x => (key x / 2 ^ sh) % 256) ws n i]? = ws[i]?) :
    (tmp.take n).Perm (ws.take n) ∧
    Spec.SortedRange (fun l => (key (BitVec.ofNat 32 l)) % 2 ^ (sh + 8)) tmp 0 n := by
  let f := fun x : BitVec 32 => (key x / 2 ^ sh) % 256
  have hf : ∀ i < n, f (ws[i]?.getD 0#32) < 256 := fun _ _ => Nat.mod_lt _ (by decide)
  have hb_lt : ∀ i : Fin n, bktPlace f ws n i.1 < n := fun i =>
    countLt_add_countEq_lt i.2 hn_ws hf
  have hfin_inj :
      Function.Injective (fun i : Fin n => (⟨bktPlace f ws n i.1, hb_lt i⟩ : Fin n)) := by
    intro a b hab
    have hv := congrArg Fin.val hab
    rcases Nat.lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exact absurd hv (bktPlace_inj hlt b.2 hn_ws hf)
    · exact Fin.ext heq
    · exact absurd hv.symm (bktPlace_inj hgt a.2 hn_ws hf)
  let pFn : Fin n → Fin n := fun i => ⟨bktPlace f ws n i.1, hb_lt i⟩
  have hfin_nd : ((List.finRange n).map pFn).Nodup :=
    (List.nodup_finRange n).map pFn (fun _ _ h hne => h (hfin_inj hne))
  have hfin_perm : ((List.finRange n).map pFn).Perm (List.finRange n) :=
    perm_of_nodup_subset_len hfin_nd (fun u _ => List.mem_finRange u) (by simp)
  have hfin_surj : Function.Surjective pFn := fun u => by
    have hmem := hfin_perm.mem_iff.mpr (List.mem_finRange u)
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
    exact ⟨i, hi⟩
  have hmap_src : ∀ u < n, ∃ iu < n, bktPlace f ws n iu = u ∧ tmp[u]? = ws[iu]? := by
    intro u hu
    obtain ⟨⟨iu, hiu⟩, hvu⟩ := hfin_surj ⟨u, hu⟩
    have hveq : bktPlace f ws n iu = u := congrArg Fin.val hvu
    exact ⟨iu, hiu, hveq, hveq ▸ hplace iu hiu⟩
  have hperm_fin : (tmp.take n).Perm (ws.take n) := by
    have hmapped : ((List.finRange n).map (fun u : Fin n => tmp[u.1]'(by omega))).Perm
        ((List.finRange n).map (fun i : Fin n => ws[i.1]'(by omega))) := by
      have h1 := (hfin_perm.map (fun u : Fin n => tmp[u.1]'(by omega))).symm
      rw [List.map_map] at h1
      have hfn : ((fun u : Fin n => tmp[u.1]'(Nat.lt_of_lt_of_le u.2 hn_tmp)) ∘ pFn) =
          (fun i : Fin n => ws[i.1]'(Nat.lt_of_lt_of_le i.2 hn_ws)) := by
        funext i
        have hp := hplace i.1 i.2
        have hbi : bktPlace f ws n i.1 < tmp.length := Nat.lt_of_lt_of_le (hb_lt i) hn_tmp
        rw [List.getElem?_eq_getElem hbi,
          List.getElem?_eq_getElem (Nat.lt_of_lt_of_le i.2 hn_ws), Option.some.injEq] at hp
        exact hp
      simpa [hfn] using h1
    have htake_eq : ∀ {xs : List (BitVec 32)} (hl : n ≤ xs.length),
        xs.take n =
          (List.finRange n).map (fun i : Fin n => xs[i.1]'(Nat.lt_of_lt_of_le i.2 hl)) := by
      intro xs hl
      apply List.ext_getElem (by simp [hl])
      intro k hk1 hk2
      simp only [List.getElem_take, List.getElem_map, List.getElem_finRange, Fin.val_cast]
    rw [htake_eq hn_tmp, htake_eq hn_ws]; exact hmapped
  refine ⟨hperm_fin, fun u v _ huv hvn => ?_⟩
  obtain ⟨iu, hiu, hplace_u, htu⟩ := hmap_src u (by omega)
  obtain ⟨iv, hiv, hplace_v, htv⟩ := hmap_src v hvn
  have key_of_elem : ∀ {xs : List (BitVec 32)} {k : Nat} (hk : k < xs.length),
      key (BitVec.ofNat 32 (Spec.wsVal xs k)) = key (xs[k]'hk) := by
    intro xs k hk
    simp [Spec.wsVal, List.getElem?_eq_getElem hk]
  have hwu : Spec.wsVal tmp u = Spec.wsVal ws iu := by unfold Spec.wsVal; rw [htu]
  have hwv : Spec.wsVal tmp v = Spec.wsVal ws iv := by unfold Spec.wsVal; rw [htv]
  change key (BitVec.ofNat 32 (Spec.wsVal tmp u)) % 2 ^ (sh + 8) ≤
      key (BitVec.ofNat 32 (Spec.wsVal tmp v)) % 2 ^ (sh + 8)
  rw [hwu, hwv, key_of_elem (Nat.lt_of_lt_of_le hiu hn_ws),
    key_of_elem (Nat.lt_of_lt_of_le hiv hn_ws),
    radix_mod_split key sh, radix_mod_split key sh]
  let bu := f (ws[iu]'(Nat.lt_of_lt_of_le hiu hn_ws))
  let bv := f (ws[iv]'(Nat.lt_of_lt_of_le hiv hn_ws))
  have hwu_el : ws[iu]?.getD 0#32 = ws[iu]'(Nat.lt_of_lt_of_le hiu hn_ws) := by
    rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hiu hn_ws), Option.getD_some]
  have hwv_el : ws[iv]?.getD 0#32 = ws[iv]'(Nat.lt_of_lt_of_le hiv hn_ws) := by
    rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hiv hn_ws), Option.getD_some]
  have hbu_eq : bu = f (ws[iu]?.getD 0#32) := congrArg f hwu_el.symm
  have hbv_eq : bv = f (ws[iv]?.getD 0#32) := congrArg f hwv_el.symm
  rcases Nat.lt_trichotomy bu bv with hlt | heq | hgt
  · have hlt_mul : (bu + 1) * 2 ^ sh ≤ bv * 2 ^ sh := Nat.mul_le_mul_right (2 ^ sh) hlt
    have hrm : key (ws[iu]'(Nat.lt_of_lt_of_le hiu hn_ws)) % 2 ^ sh < 2 ^ sh :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero (by simp))
    have hm1 : bu * 2 ^ sh + key (ws[iu]'(Nat.lt_of_lt_of_le hiu hn_ws)) % 2 ^ sh <
        (bu + 1) * 2 ^ sh := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    change bu * 2 ^ sh + key (ws[iu]'(Nat.lt_of_lt_of_le hiu hn_ws)) % 2 ^ sh ≤
      bv * 2 ^ sh + key (ws[iv]'(Nat.lt_of_lt_of_le hiv hn_ws)) % 2 ^ sh
    omega
  · change bu * 2 ^ sh + key (ws[iu]'(Nat.lt_of_lt_of_le hiu hn_ws)) % 2 ^ sh ≤
      bv * 2 ^ sh + key (ws[iv]'(Nat.lt_of_lt_of_le hiv hn_ws)) % 2 ^ sh
    rw [heq]
    have hle_i : iu ≤ iv := by
      refine Classical.byContradiction fun hlt_i => ?_
      have hiv_lt : iv < iu := Nat.lt_of_not_le hlt_i
      have hsucc : countEqUpTo f ws iv bv + 1 ≤ countEqUpTo f ws (iv + 1) bv := by
        simpa only [bv, hbv_eq] using
          countEqUpTo_succ_self f ws (Nat.lt_of_lt_of_le hiv hn_ws)
      have h1 := countEqUpTo_mono (f := f) (xs := ws) (b := bv) (by omega : iv + 1 ≤ iu)
      have hb_eq : f (ws[iu]?.getD 0#32) = f (ws[iv]?.getD 0#32) := by
        rw [← hbu_eq, ← hbv_eq]; exact heq
      have hpu_ge : u = bktPlace f ws n iu := hplace_u.symm
      have hpv_eq : v = bktPlace f ws n iv := hplace_v.symm
      unfold bktPlace at hpu_ge hpv_eq
      rw [hb_eq, ← hbv_eq] at hpu_ge
      rw [← hbv_eq] at hpv_eq
      omega
    have hs := hsrt0 iu iv (Nat.zero_le _) hle_i hiv
    dsimp only at hs
    rw [key_of_elem (Nat.lt_of_lt_of_le hiu hn_ws),
      key_of_elem (Nat.lt_of_lt_of_le hiv hn_ws)] at hs
    omega
  · exfalso
    have hsucc : countEqUpTo f ws iv bv + 1 ≤ countEqUpTo f ws (iv + 1) bv := by
      simpa only [bv, hbv_eq] using
        countEqUpTo_succ_self f ws (Nat.lt_of_lt_of_le hiv hn_ws)
    have h1 := countEqUpTo_mono (f := f) (xs := ws) (b := bv) (by omega : iv + 1 ≤ n)
    have h2 := countLt_succ_bkt f ws n bv
    have h3 := countLt_mono (f := f) (xs := ws) (n := n) (show bv + 1 ≤ bu from hgt)
    unfold bktPlace at hplace_u hplace_v
    rw [← hbu_eq] at hplace_u
    rw [← hbv_eq] at hplace_v
    omega

private theorem radix_bkt_eq {wvec : List (BitVec 32)} {lit : BitVec 32} {shift : BitVec 64}
    (hlt : 2 * lit.toNat < wvec.length) (hsh : shift.toNat < 32) :
    let v := wvec[((lit.setWidth 64) <<< (1 : Nat)).toNat]'(by rw [bv64_lit2]; exact hlt)
    ((v.setWidth 64 >>> (shift.toNat % 64)) &&& (255 : BitVec 64)).toNat =
      (Spec.fullWvecOff wvec lit.toNat / 2 ^ shift.toNat) % 256 := by
  intro v
  have hshl := bv64_lit2 (lit := lit)
  have hmod : shift.toNat % 64 = shift.toNat := Nat.mod_eq_of_lt (by omega)
  have hv_eq : v = wvec[2 * lit.toNat]'(by omega) :=
    list_getElem_congr (by rw [hshl]; exact hlt) hshl
  have hv_off : v.toNat = Spec.fullWvecOff wvec lit.toNat := by
    unfold Spec.fullWvecOff
    rw [hv_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have h255 : (255 : BitVec 64).toNat = 255 := rfl
  rw [hmod, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    zext_toNat v (by decide), Nat.shiftRight_eq_div_pow, hv_off, h255]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 8]

private theorem radix_sorted_finish {wvec ws : List (BitVec 32)} {n sh : Nat}
    {max_off : BitVec 64} (hmax : max_off.toNat < 2 ^ 32)
    (hkeys : ∀ j < n, Spec.fullWvecOff wvec (Spec.wsVal ws j) ≤ max_off.toNat)
    (hstop : ¬ (sh < 32 ∧ (max_off >>> sh) ≠ 0#64)) (hsh_le : sh ≤ 32)
    (hsrt : Spec.SortedRange (fun l => Spec.fullWvecOff wvec l % 2 ^ sh) ws 0 n) :
    Spec.SortedRange (Spec.fullWvecOff wvec) ws 0 n := by
  have hlt_pow : ∀ k ≤ max_off.toNat, k < 2 ^ sh := by
    intro k hk
    by_cases h32 : sh < 32
    · have hzero : max_off >>> sh = 0#64 :=
        Classical.byContradiction fun hne => hstop ⟨h32, hne⟩
      have hdiv0 : max_off.toNat / 2 ^ sh = 0 := by
        have := congrArg BitVec.toNat hzero
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
        simpa using this
      have := (Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero (by simp))).mp hdiv0
      omega
    · have hsh32 : sh = 32 := by omega
      rw [hsh32]; omega
  intro i j _ hij hjn
  have hi := Nat.mod_eq_of_lt (hlt_pow _ (hkeys i (by omega)))
  have hj := Nat.mod_eq_of_lt (hlt_pow _ (hkeys j hjn))
  have hs := hsrt i j (Nat.zero_le _) hij hjn
  dsimp only at hs
  rw [hi, hj] at hs
  exact hs

private theorem sep4_rot1 {key value : Type _} [BEq key] [Hashable key] [EquivBEq key]
    [LawfulBEq key] (A B C D R : Std.ExtHashMap key value → Prop) :
    (D ⋆ (A ⋆ (B ⋆ (C ⋆ (R ⋆ emp))))) = (A ⋆ B ⋆ C ⋆ D ⋆ R) := by
  rw [sep_comm R emp, emp_sep, sep_comm_l D A, sep_comm_l D B, sep_comm_l D C,
    ← sep_assoc, ← sep_assoc, ← sep_assoc]

private theorem sep4_rot_cd {key value : Type _} [BEq key] [Hashable key] [EquivBEq key]
    [LawfulBEq key] (A B C D R : Std.ExtHashMap key value → Prop) :
    (C ⋆ (D ⋆ (A ⋆ (B ⋆ (R ⋆ emp))))) = (A ⋆ B ⋆ C ⋆ D ⋆ R) := by
  rw [sep_comm R emp, emp_sep, sep_comm_l D A, sep_comm_l C A, sep_comm_l D B, sep_comm_l C B,
    ← sep_assoc, ← sep_assoc, ← sep_assoc]

private theorem sep4_rot_b {key value : Type _} [BEq key] [Hashable key] [EquivBEq key]
    [LawfulBEq key] (A B C D R : Std.ExtHashMap key value → Prop) :
    (B ⋆ (A ⋆ (C ⋆ (D ⋆ (R ⋆ emp))))) = (A ⋆ B ⋆ C ⋆ D ⋆ R) := by
  rw [sep_comm R emp, emp_sep, sep_comm_l B A, ← sep_assoc, ← sep_assoc, ← sep_assoc]

private theorem bv64_add_one_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hx]

private theorem wsVal_lt_2p32 (xs : List (BitVec 32)) (i : Nat) :
    Spec.wsVal xs i < 2 ^ 32 := by
  unfold Spec.wsVal
  exact (xs[i]?.getD 0#32).isLt

private theorem sortedRange_u32_bridge {wvec ws : List (BitVec 32)} {n sh : Nat}
    (hsrt : Spec.SortedRange (fun l => Spec.fullWvecOff wvec l % 2 ^ sh) ws 0 n) :
    Spec.SortedRange
      (fun l => Spec.fullWvecOff wvec (BitVec.ofNat 32 l).toNat % 2 ^ sh) ws 0 n := by
  intro a b ha hab hb
  have ha32 : (BitVec.ofNat 32 (Spec.wsVal ws a)).toNat = Spec.wsVal ws a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wsVal_lt_2p32 ws a)]
  have hb32 : (BitVec.ofNat 32 (Spec.wsVal ws b)).toNat = Spec.wsVal ws b := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wsVal_lt_2p32 ws b)]
  change Spec.fullWvecOff wvec (BitVec.ofNat 32 (Spec.wsVal ws a)).toNat % 2 ^ sh ≤
    Spec.fullWvecOff wvec (BitVec.ofNat 32 (Spec.wsVal ws b)).toNat % 2 ^ sh
  rw [ha32, hb32]
  exact hsrt a b ha hab hb

private theorem sortedRange_u32_unbridge {wvec ws : List (BitVec 32)} {n sh : Nat}
    (hsrt : Spec.SortedRange
      (fun l => Spec.fullWvecOff wvec (BitVec.ofNat 32 l).toNat % 2 ^ sh) ws 0 n) :
    Spec.SortedRange (fun l => Spec.fullWvecOff wvec l % 2 ^ sh) ws 0 n := by
  intro a b ha hab hb
  have ha32 : (BitVec.ofNat 32 (Spec.wsVal ws a)).toNat = Spec.wsVal ws a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wsVal_lt_2p32 ws a)]
  have hb32 : (BitVec.ofNat 32 (Spec.wsVal ws b)).toNat = Spec.wsVal ws b := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wsVal_lt_2p32 ws b)]
  have h0 := hsrt a b ha hab hb
  dsimp only at h0
  rw [ha32, hb32] at h0
  exact h0

private theorem radix_hist_cnt_inv {f : BitVec 32 → Nat} {ws cnt2 : List (BitVec 32)}
    {j n : Nat} (hj_lt : j < n) (hn_ws : n ≤ ws.length) (hcnt2_len : 256 ≤ cnt2.length)
    (bkt : Nat) (hbkt_eq : bkt = f (ws[j]?.getD 0#32)) (hbkt_lt : bkt < 256)
    (hcnt_le_j : (cnt2[bkt]'(by omega)).toNat ≤ j) (hn_bd : n < 2 ^ 31)
    (hcnt2_eq : ∀ x < 256, (cnt2[x]?.getD 0#32).toNat = countEqUpTo f ws j x) :
    ∀ x < 256,
      ((cnt2.set bkt ((cnt2[bkt]'(by omega)) + (1 : BitVec 32)))[x]?.getD 0#32).toNat =
        countEqUpTo f ws (j + 1) x := by
  intro x hx
  rw [countEqUpTo_succ f ws (by omega) x]
  have hlit_ws : ws[j]'(by omega) = ws[j]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have h1_32 : (1 : BitVec 32).toNat = 1 := rfl
  by_cases hxb : bkt = x
  · subst hxb
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      bv32_add_small_eq (by rw [h1_32]; omega)]
    rw [hlit_ws, ← hbkt_eq]
    simp only [beq_self_eq_true, ↓reduceIte]
    have hprev := hcnt2_eq bkt hx
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hprev
    rw [h1_32]; exact congrArg (· + 1) hprev
  · rw [List.getElem?_set_ne hxb, hlit_ws, ← hbkt_eq]
    have hne_beq : (bkt == x) = false := beq_false_of_ne hxb
    rw [hne_beq]; simp
    exact hcnt2_eq x hx

private theorem radix_scatter_step_inv {f : BitVec 32 → Nat} {ws cnt4 : List (BitVec 32)}
    {j n bkt : Nat} (hj_lt : j < n) (hn_ws : n ≤ ws.length) (hcnt4_len : 256 ≤ cnt4.length)
    (hbkt_eq : bkt = f (ws[j]?.getD 0#32)) (hbkt_lt : bkt < 256)
    (hpos_eq : (cnt4[bkt]'(by omega)).toNat = bktPlace f ws n j)
    (hpos_lt : bktPlace f ws n j < n) (hn_bd : n < 2 ^ 31)
    (hcnt4_eq : ∀ x < 256,
      (cnt4[x]?.getD 0#32).toNat = countLt f ws n x + countEqUpTo f ws j x) :
    ∀ x < 256,
      ((cnt4.set bkt (((cnt4[bkt]'(by omega)).setWidth 64 + (1 : BitVec 64)).setWidth 32))[x]?.getD
        0#32).toNat = countLt f ws n x + countEqUpTo f ws (j + 1) x := by
  intro x hx
  rw [countEqUpTo_succ f ws (by omega) x]
  have hlit_ws : ws[j]'(by omega) = ws[j]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  by_cases hxb : bkt = x
  · subst hxb
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      BitVec.toNat_setWidth, BitVec.toNat_add, zext_toNat _ (by decide), h1_64,
      Nat.mod_eq_of_lt (by omega : _ + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : _ + 1 < 2 ^ 32), hpos_eq, hlit_ws, ← hbkt_eq]
    simp only [beq_self_eq_true, ↓reduceIte]
    have h1 := hcnt4_eq bkt hx
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
    unfold bktPlace at hpos_eq ⊢; rw [← hbkt_eq]; omega
  · rw [List.getElem?_set_ne hxb, hlit_ws, ← hbkt_eq]
    have hne_beq : (bkt == x) = false := beq_false_of_ne hxb
    rw [hne_beq]; simp
    exact hcnt4_eq x hx

public section

theorem full_wstack_radix_sort_m6_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullWstackRadixSortSpec a m Q X →
      Func.wp Γ full_wstack_radix_sort_m6_body a m Q X := by
  rintro ⟨wvec_ptr, ws_ptr, tmp_ptr, cnt_ptr, n, max_off, ⟨⟩⟩ m Q X
    ⟨wvec, ws, tmp, cnt, R, hn_ws, hn_tmp, hcnt_len, hn_bd, hmax_bd, hkeys, hm, hQ⟩
  have h0_64 : (0 : BitVec 64).toNat = 0 := rfl
  have h8_64 : (8 : BitVec 64).toNat = 8 := rfl
  have h32_64 : (32 : BitVec 64).toNat = 32 := rfl
  have h256_64 : (256 : BitVec 64).toNat = 256 := rfl
  dsimp only [Func.wp, full_wstack_radix_sort_m6_body]
  refine wp_loop_inv
    (fun (shift, ()) ms => shift.toNat ≤ 32 ∧ shift.toNat % 8 = 0 ∧
      ∃ wsS tmpS cntS : List (BitVec 32), wsS.length = ws.length ∧ tmpS.length = tmp.length ∧
        cntS.length = cnt.length ∧ (wsS.take n.toNat).Perm (ws.take n.toNat) ∧
        Spec.SortedRange (fun l => Spec.fullWvecOff wvec l % 2 ^ shift.toNat) wsS 0 n.toNat ∧
        (∀ i, n.toNat ≤ i → wsS[i]? = ws[i]?) ∧
        (∀ j < n.toNat,
          2 * Spec.wsVal wsS j + 1 < wvec.length ∧ Spec.fullWvecOff wvec (Spec.wsVal wsS j) ≤
            max_off.toNat) ∧
        (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
          array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cntS ⋆ R) ms)
    (fun (shift, ()) _ => 32 - shift.toNat)
    (fun Js hLoop => by
      c0_hstraight
      refine hLoop ((0 : BitVec 64), ()) m ⟨Nat.zero_le _, by simp, ws, tmp, cnt, rfl, rfl, rfl,
        List.Perm.refl _, fun _ _ _ _ _ => by simp [Nat.mod_one], fun _ _ => rfl, hkeys, hm⟩)
    ?_
  rintro Js ⟨shift, ⟨⟩⟩ ms
    ⟨hsh_le, hsh_mod, wsS, tmpS, cntS, hwsS_len, htmpS_len, hcntS_len, hpermS, hsrtS, hsufS,
     hkeysS, hmS⟩ ih
  c0_hsplit
  · rw [h32_64] at hc
    have hsh_lt : shift.toNat < 32 := by omega
    clear hc
    c0_hsplit
    · clear hc
      let f : BitVec 32 → Nat := fun x => (Spec.fullWvecOff wvec x.toNat / 2 ^ shift.toNat) % 256
      have hf_lt : ∀ i < n.toNat, f (wsS[i]?.getD 0#32) < 256 :=
        fun _ _ => Nat.mod_lt _ (by decide)
      -- Loop 1: zero cnt[0..255]
      refine wp_loop_inv
        (fun (b, ()) m1 => b.toNat ≤ 256 ∧ ∃ cnt1 : List (BitVec 32), cnt1.length = cntS.length ∧
          (∀ x < b.toNat, cnt1[x]? = some 0#32) ∧
          (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
            array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cnt1 ⋆ R) m1)
        (fun (b, ()) _ => 256 - b.toNat)
        (fun Js1 h1 => by
          c0_hstraight
          exact h1 ((0 : BitVec 64), ()) ms
            ⟨Nat.zero_le _, cntS, rfl, fun _ h => by rw [h0_64] at h; omega, hmS⟩)
        ?_
      rintro Js1 ⟨b, ⟨⟩⟩ m1 ⟨hb_le, cnt1, hcnt1_len, hcnt1_z, hm1⟩ ih1
      c0_hsplit
      · rw [h256_64] at hc
        have hb_lt : b.toNat < 256 := by omega
        clear hc
        c0_hstraight
        refine ih1 (b + (1 : BitVec 64), ()) _
          (by dsimp only; rw [bv64_add_one_toNat (by omega)]; omega)
          ⟨by rw [bv64_add_one_toNat (by omega)]; exact hb_lt,
           cnt1.set b.toNat 0#32, by rw [List.length_set, hcnt1_len], fun x hx => ?_, ?_⟩
        · rw [bv64_add_one_toNat (by omega)] at hx
          by_cases hxb : x = b.toNat
          · subst hxb; exact List.getElem?_set_self (by omega)
          · rw [List.getElem?_set_ne (Ne.symm hxb)]; exact hcnt1_z x (by omega)
        · rw [sep4_rot1] at hm; exact hm
      · rw [h256_64] at hc
        have hb_eq : b.toNat = 256 := by omega
        clear hc
        have hcnt1_all : ∀ x < 256, cnt1[x]? = some 0#32 := fun x hx => hcnt1_z x (hb_eq ▸ hx)
        -- Loop 2: histogram
        refine wp_loop_inv
          (fun (j, ()) m2 => j.toNat ≤ n.toNat ∧ ∃ cnt2 : List (BitVec 32),
            cnt2.length = cntS.length ∧
            (∀ x < 256, (cnt2[x]?.getD 0#32).toNat = countEqUpTo f wsS j.toNat x) ∧
            (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
              array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cnt2 ⋆ R) m2)
          (fun (j, ()) _ => n.toNat - j.toNat)
          (fun Js2 h2 => by
            c0_hstraight
            refine h2 ((0 : BitVec 64), ()) m1 ⟨Nat.zero_le _, cnt1, hcnt1_len, fun x hx => ?_, hm1⟩
            rw [h0_64, hcnt1_all x hx, Option.getD_some, countEqUpTo_zero]; rfl)
          ?_
        rintro Js2 ⟨j, ⟨⟩⟩ m2 ⟨hj_le, cnt2, hcnt2_len, hcnt2_eq, hm2⟩ ih2
        c0_hsplit
        · have hj_lt : j.toNat < n.toNat := by omega
          clear hc
          have hkey_j := hkeysS j.toNat hj_lt
          have hlit_ws : wsS[j.toNat]'(by omega) = wsS[j.toNat]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h2_lit : 2 * (wsS[j.toNat]'(by omega)).toNat < wvec.length := by
            have := hkey_j.1; rw [wsVal_getElem (by omega)] at this; omega
          have hwvec_idx : (((wsS[j.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat <
              wvec.length := by
            rw [bv64_lit2]; exact h2_lit
          have hbkt_eq : (((wvec[(((wsS[j.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat]'
                hwvec_idx).setWidth 64 >>> (shift.toNat % 64)) &&& (255 : BitVec 64)).toNat =
              f (wsS[j.toNat]?.getD 0#32) := by
            rw [← hlit_ws]
            exact radix_bkt_eq (lit := wsS[j.toNat]'(by omega)) (shift := shift) h2_lit hsh_lt
          let bkt64 : BitVec 64 :=
            (wvec[(((wsS[j.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat]'
              hwvec_idx).setWidth 64 >>> (shift.toNat % 64) &&& (255 : BitVec 64)
          have hbkt_lt : bkt64.toNat < 256 := by rw [hbkt_eq]; exact Nat.mod_lt _ (by decide)
          have hcnt_idx_lt :
              (((wvec[(((wsS[j.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat]'
                hwvec_idx).setWidth 64 >>> (shift.toNat % 64)) &&&
                (255 : BitVec 64)).toNat < cnt2.length := by
            have := hbkt_lt; dsimp only [bkt64] at this; omega
          have hcnt_le_j : (cnt2[bkt64.toNat]'(by omega)).toNat ≤ j.toNat := by
            have h1 := hcnt2_eq bkt64.toNat hbkt_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
            rw [h1]
            have := List.length_filter_le (fun x => f x == bkt64.toNat) (wsS.take j.toNat)
            unfold countEqUpTo
            have htl : (wsS.take j.toNat).length ≤ j.toNat := by
              rw [List.length_take]; exact Nat.min_le_left _ _
            omega
          c0_hstraight
          refine ih2 (j + (1 : BitVec 64), ()) _
            (by dsimp only; rw [bv64_add_one_toNat (by omega)]; omega)
            ⟨by rw [bv64_add_one_toNat (by omega)]; exact hj_lt,
             cnt2.set bkt64.toNat ((cnt2[bkt64.toNat]'(by omega)) + (1 : BitVec 32)),
             by rw [List.length_set, hcnt2_len], ?_, ?_⟩
          · rw [bv64_add_one_toNat (by omega)]
            exact radix_hist_cnt_inv hj_lt (by omega) (by omega) bkt64.toNat hbkt_eq hbkt_lt
              hcnt_le_j hn_bd hcnt2_eq
          · rw [sep4_rot1] at hm; exact hm
        · have hj_eq : j.toNat = n.toNat := by omega
          clear hc
          have hcnt2_all : ∀ x < 256,
              (cnt2[x]?.getD 0#32).toNat = countEqUpTo f wsS n.toNat x :=
            fun x hx => by simpa [hj_eq] using hcnt2_eq x hx
          -- Loop 3: prefix sums
          refine wp_loop_inv
            (fun (b, sum, ()) m3 => b.toNat ≤ 256 ∧ sum.toNat = countLt f wsS n.toNat b.toNat ∧
              ∃ cnt3 : List (BitVec 32), cnt3.length = cntS.length ∧
              (∀ x < b.toNat, (cnt3[x]?.getD 0#32).toNat = countLt f wsS n.toNat x) ∧
              (∀ x, b.toNat ≤ x → x < 256 →
                (cnt3[x]?.getD 0#32).toNat = countEqUpTo f wsS n.toNat x) ∧
              (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cnt3 ⋆ R) m3)
            (fun (b, _, ()) _ => 256 - b.toNat)
            (fun Js3 h3 => by
              c0_hstraight
              exact h3 ((0 : BitVec 64), (0 : BitVec 64), ()) m2 ⟨Nat.zero_le _,
                by rw [h0_64, countLt_zero], cnt2, hcnt2_len,
                fun _ h => by rw [h0_64] at h; omega,
                fun x _ hx => hcnt2_all x hx, hm2⟩)
            ?_
          rintro Js3 ⟨b, sum, ⟨⟩⟩ m3
            ⟨hb_le3, hsum_eq, cnt3, hcnt3_len, hcnt3_lo, hcnt3_hi, hm3⟩ ih3
          c0_hsplit
          · rw [h256_64] at hc
            have hb_lt3 : b.toNat < 256 := by omega
            clear hc
            have hcount_le_n : ∀ k, countLt f wsS n.toNat k ≤ n.toNat := fun k => by
              unfold countLt
              have h1 : ((wsS.take n.toNat).filter (fun x => f x < k)).length ≤
                  (wsS.take n.toNat).length := List.length_filter_le _ _
              have h2 : (wsS.take n.toNat).length ≤ n.toNat := by
                rw [List.length_take]; exact Nat.min_le_left _ _
              omega
            have hsum_le : sum.toNat ≤ n.toNat := by rw [hsum_eq]; exact hcount_le_n _
            have hc_b_eq : (cnt3[b.toNat]'(by omega)).toNat =
                countEqUpTo f wsS n.toNat b.toNat := by
              have := hcnt3_hi b.toNat (Nat.le_refl _) hb_lt3
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
            have hsum_next : sum.toNat + (cnt3[b.toNat]'(by omega)).toNat =
                countLt f wsS n.toNat (b.toNat + 1) := by
              rw [hsum_eq, hc_b_eq, ← countLt_succ_bkt]
            have hsum_next_le : sum.toNat + (cnt3[b.toNat]'(by omega)).toNat ≤ n.toNat := by
              rw [hsum_next]; exact hcount_le_n _
            c0_hstraight
            refine ih3 (b + (1 : BitVec 64), sum + (cnt3[b.toNat]'(by omega)).setWidth 64, ()) _
              (by dsimp only; rw [bv64_add_one_toNat (by omega)]; omega)
              ⟨by rw [bv64_add_one_toNat (by omega)]; exact hb_lt3, ?_,
               cnt3.set b.toNat (sum.setWidth 32), by rw [List.length_set, hcnt3_len],
               fun x hx => ?_, fun x hbx hx => ?_, ?_⟩
            · rw [BitVec.toNat_add, zext_toNat _ (by decide),
                Nat.mod_eq_of_lt (by omega : sum.toNat + _ < 2 ^ 64), hsum_next,
                bv64_add_one_toNat (by omega)]
            · rw [bv64_add_one_toNat (by omega)] at hx
              by_cases hxb : x = b.toNat
              · subst hxb
                rw [List.getElem?_set_self (by omega), Option.getD_some,
                  BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hsum_eq]
              · rw [List.getElem?_set_ne (Ne.symm hxb)]; exact hcnt3_lo x (by omega)
            · rw [bv64_add_one_toNat (by omega)] at hbx
              rw [List.getElem?_set_ne (by omega)]; exact hcnt3_hi x (by omega) hx
            · rw [sep4_rot1] at hm; exact hm
          · rw [h256_64] at hc
            have hb_eq3 : b.toNat = 256 := by omega
            clear hc
            -- Loop 4: scatter to tmp
            refine wp_loop_inv
              (fun (j, ()) m4 => j.toNat ≤ n.toNat ∧ ∃ tmp4 cnt4 : List (BitVec 32),
                tmp4.length = tmpS.length ∧ cnt4.length = cntS.length ∧
                (∀ x < 256,
                  (cnt4[x]?.getD 0#32).toNat =
                    countLt f wsS n.toNat x + countEqUpTo f wsS j.toNat x) ∧
                (∀ i < j.toNat, tmp4[bktPlace f wsS n.toNat i]? = wsS[i]?) ∧
                (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                  array (t := i32) tmp_ptr tmp4 ⋆ array (t := i32) cnt_ptr cnt4 ⋆ R) m4)
              (fun (j, ()) _ => n.toNat - j.toNat)
              (fun Js4 h4 => by
                c0_hstraight
                exact h4 ((0 : BitVec 64), ()) m3 ⟨Nat.zero_le _, tmpS, cnt3, rfl, hcnt3_len,
                  fun x hx => by
                    rw [h0_64, countEqUpTo_zero, Nat.add_zero]
                    exact hcnt3_lo x (hb_eq3 ▸ hx),
                  fun _ h => by rw [h0_64] at h; omega, hm3⟩)
              ?_
            rintro Js4 ⟨j, ⟨⟩⟩ m4
              ⟨hj_le4, tmp4, cnt4, htmp4_len, hcnt4_len, hcnt4_eq, hplace4, hm4⟩ ih4
            c0_hsplit
            · have hj_lt4 : j.toNat < n.toNat := by omega
              clear hc
              have hkey_j := hkeysS j.toNat hj_lt4
              have hlit_ws : wsS[j.toNat]'(by omega) = wsS[j.toNat]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have h2_lit : 2 * (wsS[j.toNat]'(by omega)).toNat < wvec.length := by
                have := hkey_j.1; rw [wsVal_getElem (by omega)] at this; omega
              have hwvec_idx : (((wsS[j.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat <
                  wvec.length := by
                rw [bv64_lit2]; exact h2_lit
              have hbkt_eq : (((wvec[(((wsS[j.toNat]'(by omega)).setWidth 64) <<<
                    (1 : Nat)).toNat]'hwvec_idx).setWidth 64 >>> (shift.toNat % 64)) &&&
                    (255 : BitVec 64)).toNat = f (wsS[j.toNat]?.getD 0#32) := by
                rw [← hlit_ws]
                exact radix_bkt_eq (lit := wsS[j.toNat]'(by omega)) (shift := shift) h2_lit hsh_lt
              let bkt64 : BitVec 64 :=
                (wvec[(((wsS[j.toNat]'(by omega)).setWidth 64) <<<
                  (1 : Nat)).toNat]'hwvec_idx).setWidth 64 >>> (shift.toNat % 64) &&&
                  (255 : BitVec 64)
              have hbkt_lt : bkt64.toNat < 256 := by rw [hbkt_eq]; exact Nat.mod_lt _ (by decide)
              have hcnt_idx_lt :
                  (((wvec[(((wsS[j.toNat]'(by omega)).setWidth 64) <<<
                    (1 : Nat)).toNat]'hwvec_idx).setWidth 64 >>> (shift.toNat % 64)) &&&
                    (255 : BitVec 64)).toNat < cnt4.length := by
                have := hbkt_lt; dsimp only [bkt64] at this; omega
              have hpos_eq : (cnt4[bkt64.toNat]'(by omega)).toNat =
                  bktPlace f wsS n.toNat j.toNat := by
                have h1 := hcnt4_eq bkt64.toNat hbkt_lt
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                unfold bktPlace; rw [← hbkt_eq, h1]
              have hpos_lt : bktPlace f wsS n.toNat j.toNat < n.toNat :=
                countLt_add_countEq_lt hj_lt4 (by omega) hf_lt
              have hpos64_lt :
                  ((cnt4[bkt64.toNat]'(by omega)).setWidth 64).toNat < tmp4.length := by
                rw [zext_toNat _ (by decide), hpos_eq]; omega
              c0_hstraight
              refine ih4 (j + (1 : BitVec 64), ()) _
                (by dsimp only; rw [bv64_add_one_toNat (by omega)]; omega)
                ⟨by rw [bv64_add_one_toNat (by omega)]; exact hj_lt4,
                 tmp4.set ((cnt4[bkt64.toNat]'(by omega)).setWidth 64).toNat
                   (wsS[j.toNat]'(by omega)),
                 cnt4.set bkt64.toNat
                   (((cnt4[bkt64.toNat]'(by omega)).setWidth 64 + (1 : BitVec 64)).setWidth 32),
                 by rw [List.length_set, htmp4_len], by rw [List.length_set, hcnt4_len],
                 ?_, fun i hi => ?_, ?_⟩
              · rw [bv64_add_one_toNat (by omega)]
                exact radix_scatter_step_inv hj_lt4 (by omega) (by omega) hbkt_eq hbkt_lt
                  hpos_eq hpos_lt hn_bd hcnt4_eq
              · rw [bv64_add_one_toNat (by omega)] at hi
                have hdst : ((cnt4[bkt64.toNat]'(by omega)).setWidth 64).toNat =
                    bktPlace f wsS n.toNat j.toNat := by
                  rw [zext_toNat _ (by decide), hpos_eq]
                rw [hdst]
                by_cases hij : i = j.toNat
                · subst hij
                  rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
                · rw [List.getElem?_set_ne
                    (Ne.symm (bktPlace_inj (by omega) hj_lt4 (by omega) hf_lt))]
                  exact hplace4 i (by omega)
              · rw [sep4_rot_cd] at hm; exact hm
            · have hj_eq4 : j.toNat = n.toNat := by omega
              clear hc
              have hpost := radix_scatter_post (by omega)
                (by rw [htmp4_len, htmpS_len]; exact hn_tmp)
                (sortedRange_u32_bridge hsrtS) (fun i hi => hplace4 i (hj_eq4 ▸ hi))
              -- Loop 5: copy back tmp -> ws
              refine wp_loop_inv
                (fun (j, ()) m5 => j.toNat ≤ n.toNat ∧ ∃ ws5 : List (BitVec 32),
                  ws5.length = wsS.length ∧ (∀ i < j.toNat, ws5[i]? = tmp4[i]?) ∧
                  (∀ i, n.toNat ≤ i → ws5[i]? = wsS[i]?) ∧
                  (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws5 ⋆
                    array (t := i32) tmp_ptr tmp4 ⋆ array (t := i32) cnt_ptr cnt4 ⋆ R) m5)
                (fun (j, ()) _ => n.toNat - j.toNat)
                (fun Js5 h5 => by
                  c0_hstraight
                  exact h5 ((0 : BitVec 64), ()) m4 ⟨Nat.zero_le _, wsS, rfl,
                    fun _ h => by rw [h0_64] at h; omega, fun _ _ => rfl, hm4⟩)
                ?_
              rintro Js5 ⟨j, ⟨⟩⟩ m5 ⟨hj_le5, ws5, hws5_len, hws5_pref, hws5_suf, hm5⟩ ih5
              c0_hsplit
              · have hj_lt5 : j.toNat < n.toNat := by omega
                clear hc
                c0_hstraight
                refine ih5 (j + (1 : BitVec 64), ()) _
                  (by dsimp only; rw [bv64_add_one_toNat (by omega)]; omega)
                  ⟨by rw [bv64_add_one_toNat (by omega)]; exact hj_lt5,
                   ws5.set j.toNat (tmp4[j.toNat]'(by omega)), by rw [List.length_set, hws5_len],
                   fun i hi => ?_, fun i hi => ?_, ?_⟩
                · rw [bv64_add_one_toNat (by omega)] at hi
                  by_cases hij : i = j.toNat
                  · subst hij
                    rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
                  · rw [List.getElem?_set_ne (Ne.symm hij)]; exact hws5_pref i (by omega)
                · rw [List.getElem?_set_ne (by omega : j.toNat ≠ i)]; exact hws5_suf i hi
                · rw [sep4_rot_b] at hm; exact hm
              · have hj_eq5 : j.toNat = n.toNat := by omega
                clear hc
                c0_hstraight
                have htake_ws5 : ws5.take n.toNat = tmp4.take n.toNat := by
                  apply List.ext_getElem
                    (by simp [hws5_len, htmp4_len, hwsS_len, htmpS_len, hn_ws, hn_tmp])
                  intro k hk1 _
                  simp only [List.length_take] at hk1
                  have hkn : k < n.toNat := by omega
                  have hk := hws5_pref k (hj_eq5 ▸ hkn)
                  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
                    Option.some.injEq] at hk
                  simp only [List.getElem_take]; exact hk
                have hsrt_ws5 :
                    Spec.SortedRange (fun l => Spec.fullWvecOff wvec l % 2 ^ (shift.toNat + 8))
                      ws5 0 n.toNat := by
                  refine sortedRange_u32_unbridge fun a b _ hab hbn => ?_
                  have ha := hws5_pref a (hj_eq5 ▸ (by omega))
                  have hb := hws5_pref b (hj_eq5 ▸ hbn)
                  have hwa : Spec.wsVal ws5 a = Spec.wsVal tmp4 a := by unfold Spec.wsVal; rw [ha]
                  have hwb : Spec.wsVal ws5 b = Spec.wsVal tmp4 b := by unfold Spec.wsVal; rw [hb]
                  change Spec.fullWvecOff wvec (BitVec.ofNat 32 (Spec.wsVal ws5 a)).toNat %
                      2 ^ (shift.toNat + 8) ≤
                    Spec.fullWvecOff wvec (BitVec.ofNat 32 (Spec.wsVal ws5 b)).toNat %
                      2 ^ (shift.toNat + 8)
                  rw [hwa, hwb]
                  exact hpost.2 a b (Nat.zero_le _) hab hbn
                have hsh_add : (shift + (8 : BitVec 64)).toNat = shift.toNat + 8 := by
                  rw [BitVec.toNat_add, h8_64, Nat.mod_eq_of_lt (by omega)]
                have htake_eq : ∀ j < n.toNat,
                    ∃ k < n.toNat, Spec.wsVal ws5 j = Spec.wsVal wsS k := by
                  intro j hj
                  have hin0 : (ws5.take n.toNat)[j]'(by
                        simp [hws5_len, hwsS_len, hn_ws, hj]) ∈
                      ws5.take n.toNat := List.getElem_mem _
                  have hin : ws5[j]'(by omega) ∈ ws5.take n.toNat := by
                    simpa [List.getElem_take] using hin0
                  have hin2 : ws5[j]'(by omega) ∈ wsS.take n.toNat :=
                    (htake_ws5 ▸ hpost.1).mem_iff.mp hin
                  obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hin2
                  have hkn : k < n.toNat := by simp [hwsS_len, hn_ws] at hk; exact hk
                  rw [List.getElem_take] at hkeq
                  refine ⟨k, hkn, ?_⟩
                  unfold Spec.wsVal
                  rw [List.getElem?_eq_getElem (by omega),
                    List.getElem?_eq_getElem (by omega), hkeq]
                refine ih (shift + (8 : BitVec 64), ()) m5
                  (by dsimp only; rw [hsh_add]; omega)
                  ⟨by rw [hsh_add]; omega, by rw [hsh_add]; omega, ws5, tmp4, cnt4,
                   hws5_len.trans hwsS_len, htmp4_len.trans htmpS_len, hcnt4_len.trans hcntS_len,
                   (htake_ws5 ▸ hpost.1).trans hpermS, by rw [hsh_add]; exact hsrt_ws5,
                   fun i hi => (hws5_suf i hi).trans (hsufS i hi), fun j hj => ?_, hm5⟩
                obtain ⟨k, hk, heq⟩ := htake_eq j hj
                rw [heq]; exact hkeysS k hk
    · have hzero : max_off >>> shift.toNat = 0#64 := by
        have hm0 : max_off >>> (shift.toNat % 64) = 0 := hc
        rw [Nat.mod_eq_of_lt (by omega)] at hm0
        exact hm0
      clear hc
      c0_hstraight
      have hsrt_full := radix_sorted_finish hmax_bd (fun j hj => (hkeysS j hj).2)
        (fun h => h.2 hzero) hsh_le hsrtS
      exact hQ wsS tmpS cntS ms hwsS_len htmpS_len hcntS_len hpermS hsrt_full hsufS hmS
  · rw [h32_64] at hc
    have hsh_ge32 : ¬ shift.toNat < 32 := by omega
    clear hc
    c0_hstraight
    have hsrt_full := radix_sorted_finish hmax_bd (fun j hj => (hkeysS j hj).2)
      (fun h => hsh_ge32 h.1) hsh_le hsrtS
    exact hQ wsS tmpS cntS ms hwsS_len htmpS_len hcntS_len hpermS hsrt_full hsufS hmS

end

end LeanQbe.T.Examples.Kissat.Proof.Watch

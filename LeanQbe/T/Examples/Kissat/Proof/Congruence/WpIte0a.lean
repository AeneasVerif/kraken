/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence ITE M7 WP Proofs — Part 0a (`sift`, `sort`, `bsearch`)

Canonical `Func.wp` proofs for `Src.Congruence`:
1. `full_cong_u64_sift_m7_wp` (`Spec.fullCongU64SiftM7Spec`)
2. `full_cong_u64_sort_m7_wp` (`Spec.fullCongU64SortM7Spec`)
3. `full_cong_bsearch_u64_m7_wp` (`Spec.fullCongBsearchU64M7Spec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

local macro "cong_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

/-! ## Pure Heap / Sort / Search Helpers -/

private theorem bv64_swap_preserves_elem (xs : List (BitVec 64)) {i j n k : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ xs.length) (hk : k < n) :
    ∃ m < n, ((xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega)))[k]? = xs[m]? := by
  by_cases hkj : k = j
  · subst hkj; refine ⟨i, hi, ?_⟩
    rw [List.getElem?_set_self (by simp only [List.length_set]; omega),
      List.getElem?_eq_getElem (by omega)]
  · rw [List.getElem?_set_ne (Ne.symm hkj)]
    by_cases hki : k = i
    · subst hki; refine ⟨j, hj, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hki)]; exact ⟨k, hk, rfl⟩

private theorem bv64_swap_tail {xs : List (BitVec 64)} {i j n k : Nat} {vi vj : BitVec 64}
    (hi : i < n) (hj : j < n) (hk : n ≤ k) :
    ((xs.set i vi).set j vj)[k]? = xs[k]? := by
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem maxHeap_le_root {xs : List (BitVec 64)} {hi : Nat}
    (hheap : MaxHeapRange xs 0 hi) :
    ∀ k < hi, xs[k]?.getD 0#64 ≤ xs[0]?.getD 0#64 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    cases k with
    | zero => exact BitVec.le_refl _
    | succ k' =>
      let j := k' / 2
      have hj_lt : j < k' + 1 := by omega
      have hhj := hheap j (Nat.zero_le _) (by omega)
      have hchild : xs[k' + 1]?.getD 0#64 ≤ xs[j]?.getD 0#64 := by
        rcases Nat.mod_two_eq_zero_or_one k' with hm | hm
        · have heq : 2 * j + 1 = k' + 1 := by omega
          simpa only [heq] using hhj.1 (by omega)
        · have heq : 2 * j + 2 = k' + 1 := by omega
          simpa only [heq] using hhj.2 (by omega)
      exact BitVec.le_trans hchild (ih j hj_lt (by omega))

/-! ## 1. `full_cong_u64_sift_m7_wp` -/

private theorem sift_swap_heap_step {xs : List (BitVec 64)} {start n pos best : Nat}
    (hst : start ≤ pos) (hpos : pos < n) (hbest : best < n) (hn : n ≤ xs.length)
    (hc1 : 2 * pos + 1 < n)
    (hbest_gt_pos : xs[pos]?.getD 0#64 < xs[best]?.getD 0#64)
    (hbest_c1 : xs[2 * pos + 1]?.getD 0#64 ≤ xs[best]?.getD 0#64)
    (hbest_c2 : 2 * pos + 2 < n → xs[2 * pos + 2]?.getD 0#64 ≤ xs[best]?.getD 0#64)
    (hbest_eq : best = 2 * pos + 1 ∨ (2 * pos + 2 < n ∧ best = 2 * pos + 2))
    (hother : ∀ j, start ≤ j → j < n → j ≠ pos → MaxHeapAt xs n j)
    (hpar : ∀ j, start ≤ j → (2 * j + 1 = pos ∨ 2 * j + 2 = pos) →
      (2 * pos + 1 < n → xs[2 * pos + 1]?.getD 0#64 ≤ xs[j]?.getD 0#64) ∧
      (2 * pos + 2 < n → xs[2 * pos + 2]?.getD 0#64 ≤ xs[j]?.getD 0#64)) :
    let xs1 := (xs.set pos (xs[best]'(by omega))).set best (xs[pos]'(by omega))
    (∀ j, start ≤ j → j < n → j ≠ best → MaxHeapAt xs1 n j) ∧
    (∀ j, start ≤ j → (2 * j + 1 = best ∨ 2 * j + 2 = best) →
      (2 * best + 1 < n → xs1[2 * best + 1]?.getD 0#64 ≤ xs1[j]?.getD 0#64) ∧
      (2 * best + 2 < n → xs1[2 * best + 2]?.getD 0#64 ≤ xs1[j]?.getD 0#64)) := by
  intro xs1
  have get1 : ∀ idx, idx < n →
      xs1[idx]?.getD 0#64 =
        if idx = best then xs[pos]?.getD 0#64
        else if idx = pos then xs[best]?.getD 0#64
        else xs[idx]?.getD 0#64 := by
    intro idx hidx
    by_cases h1 : idx = best
    · subst h1; simp only [↓reduceIte]
      have hset : xs1[idx]? = some (xs[pos]'(by omega)) := by
        dsimp only [xs1]
        exact List.getElem?_set_self (by simp only [List.length_set]; omega)
      rw [hset, Option.getD_some, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · simp only [h1, ↓reduceIte]
      have hne1 : xs1[idx]? = (xs.set pos (xs[best]'(by omega)))[idx]? := by
        dsimp only [xs1]; exact List.getElem?_set_ne (Ne.symm h1)
      rw [hne1]
      by_cases h2 : idx = pos
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by omega), Option.getD_some,
          List.getElem?_eq_getElem (by omega), Option.getD_some]
      · simp only [h2, ↓reduceIte, List.getElem?_set_ne (Ne.symm h2)]
  have hb_ne_p : best ≠ pos := by rcases hbest_eq with h | ⟨_, h⟩ <;> omega
  refine ⟨fun j hst_j hj_lt hj_ne => ?_, fun j hst_j hjpar => ?_⟩
  · have hj_eq_at : xs1[j]?.getD 0#64 =
        if j = pos then xs[best]?.getD 0#64 else xs[j]?.getD 0#64 := by
      rw [get1 j hj_lt]; simp only [hj_ne, ↓reduceIte]
    have hchild : ∀ c, c < n → 2 * j + 1 = c ∨ 2 * j + 2 = c →
        xs1[c]?.getD 0#64 ≤ xs1[j]?.getD 0#64 := by
      intro c hc hrel
      rw [get1 c hc, hj_eq_at]
      by_cases hjp : j = pos
      · subst hjp; simp only [↓reduceIte]
        by_cases hcb : c = best
        · simp only [hcb, ↓reduceIte]; exact BitVec.le_of_lt hbest_gt_pos
        · have hcne_j : c ≠ j := by rcases hrel with h | h <;> omega
          simp only [hcb, hcne_j, ↓reduceIte]
          rcases hrel with hrel | hrel
          · rw [← hrel]; exact hbest_c1
          · rw [← hrel]; exact hbest_c2 (by rw [hrel]; exact hc)
      · simp only [hjp, ↓reduceIte]
        have hmj := hother j hst_j hj_lt hjp
        have hjc : xs[c]?.getD 0#64 ≤ xs[j]?.getD 0#64 := by
          rcases hrel with hrel | hrel
          · rw [← hrel]; exact hmj.1 (by rw [hrel]; exact hc)
          · rw [← hrel]; exact hmj.2 (by rw [hrel]; exact hc)
        by_cases hcb : c = best
        · subst hcb; simp only [↓reduceIte]
          exact BitVec.le_trans (BitVec.le_of_lt hbest_gt_pos) hjc
        · simp only [hcb, ↓reduceIte]
          by_cases hcp : c = pos
          · subst hcp; simp only [↓reduceIte]
            have hpc := hpar j hst_j hrel
            rcases hbest_eq with h1 | ⟨hc2, h1⟩ <;> rw [h1]
            · exact hpc.1 hc1
            · exact hpc.2 hc2
          · simp only [hcp, ↓reduceIte]; exact hjc
    exact ⟨fun hc => hchild _ hc (Or.inl rfl), fun hc => hchild _ hc (Or.inr rfl)⟩
  · have hj_eq_pos : j = pos := by
      rcases hbest_eq with h | ⟨_, h⟩ <;> rcases hjpar with hp | hp <;> omega
    have hmb := hother best (by omega) hbest hb_ne_p
    have hp_val : xs1[j]?.getD 0#64 = xs[best]?.getD 0#64 := by
      rw [hj_eq_pos, get1 pos hpos]; simp only [Ne.symm hb_ne_p, ↓reduceIte]
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · have hgt1 : 2 * best + 1 ≠ best := by omega
      have hgt2 : 2 * best + 1 ≠ pos := by rcases hbest_eq with h | ⟨_, h⟩ <;> omega
      rw [get1 _ h1]; simp only [hgt1, hgt2, ↓reduceIte, hp_val]; exact hmb.1 h1
    · have hgt1 : 2 * best + 2 ≠ best := by omega
      have hgt2 : 2 * best + 2 ≠ pos := by rcases hbest_eq with h | ⟨_, h⟩ <;> omega
      rw [get1 _ h2]; simp only [hgt1, hgt2, ↓reduceIte, hp_val]; exact hmb.2 h2

/-- Canonical `Func.wp` proof for `full_cong_u64_sift_m7`. -/
theorem full_cong_u64_sift_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullCongU64SiftM7Spec a m Q X →
      Func.wp Γ full_cong_u64_sift_m7_body a m Q X := by
  rintro ⟨a, start, n, ⟨⟩⟩ m0 Q X ⟨xs, R, hst, hn, hlen, hheap_tail, hm0, hQ⟩
  unfold Func.wp full_cong_u64_sift_m7_body
  refine wp_join_group
    (fun (_ : Tup Val [i64]) mg =>
      ∃ xs' : List (BitVec 64), xs'.length = xs.length ∧
        (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) ∧
        MaxHeapRange xs' start.toNat n.toNat ∧
        (array64 a xs' ⋆ R) mg)
    ?_ (fun J_out hJ_out => ?_)
  · rintro J_out ⟨_, ⟨⟩⟩ mg ⟨xs', hlen', htail', hperm', hheap', hmg'⟩
    c0_hsteps!
    exact hQ xs' mg hlen' htail' hperm' hheap' hmg'
  · refine wp_loop_inv (ts := [i64])
      (fun (pos, ()) mg =>
        ∃ xs' : List (BitVec 64), xs'.length = xs.length ∧
          start.toNat ≤ pos.toNat ∧ pos.toNat ≤ n.toNat ∧
          (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) ∧
          (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) ∧
          (∀ j, start.toNat ≤ j → j < n.toNat → j ≠ pos.toNat → MaxHeapAt xs' n.toNat j) ∧
          (∀ j, start.toNat ≤ j → (2 * j + 1 = pos.toNat ∨ 2 * j + 2 = pos.toNat) →
            (2 * pos.toNat + 1 < n.toNat → xs'[2 * pos.toNat + 1]?.getD 0#64 ≤ xs'[j]?.getD 0#64) ∧
            (2 * pos.toNat + 2 < n.toNat → xs'[2 * pos.toNat + 2]?.getD 0#64 ≤ xs'[j]?.getD 0#64)) ∧
          (array64 a xs' ⋆ R) mg)
      (fun (pos, ()) _ => n.toNat - pos.toNat)
      (fun J hJ => by
        c0_hsteps!
        exact hJ (start, ()) m0 ⟨xs, rfl, Nat.le_refl _, hst, fun _ _ _ => rfl,
          fun k hk => ⟨k, hk, rfl⟩, fun j hj1 hj2 hjne => hheap_tail j (by omega) hj2,
          fun j hj1 hj2 => by omega, hm0⟩)
      (fun J (pos, ()) mg ⟨xs', hlen', hst_p, hp_n, htail', hperm', hother', hpar', hmg'⟩ ih => by
        c0_hsplit
        · have hpos_lt : pos.toNat < n.toNat := hc
          have h2bv : (2 : BitVec 64).toNat = 2 := rfl
          have h1bv : (1 : BitVec 64).toNat = 1 := rfl
          have hc1_nat : (pos * 2 + 1).toNat = 2 * pos.toNat + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_mul, h2bv, h1bv]; omega
          c0_hsplit
          · have hc1_ge : ¬(2 * pos.toNat + 1 < n.toNat) := by
              rw [h2bv, h1bv] at hc; omega
            have hmax_pos : MaxHeapAt xs' n.toNat pos.toNat :=
              ⟨fun h => absurd h hc1_ge, fun h => absurd (by omega) hc1_ge⟩
            have hheap' : MaxHeapRange xs' start.toNat n.toNat := fun j hj1 hj2 =>
              if hjp : j = pos.toNat then hjp ▸ hmax_pos else hother' j hj1 hj2 hjp
            c0_hsteps!
            exact hJ_out (pos, ()) mg ⟨xs', hlen', htail', hperm', hheap', hmg'⟩
          · have hc1_lt : 2 * pos.toNat + 1 < n.toNat := by
              rw [h2bv, h1bv] at hc; omega
            c0_hsteps_nogrp
            refine wp_join_group
              (fun (best, ()) mgb => mgb = mg ∧
                best.toNat < n.toNat ∧
                xs'[pos.toNat]?.getD 0#64 ≤ xs'[best.toNat]?.getD 0#64 ∧
                xs'[2 * pos.toNat + 1]?.getD 0#64 ≤ xs'[best.toNat]?.getD 0#64 ∧
                ((best = pos ∧ xs'[2 * pos.toNat + 1]?.getD 0#64 ≤ xs'[pos.toNat]?.getD 0#64) ∨
                  (best.toNat = 2 * pos.toNat + 1 ∧
                    xs'[pos.toNat]?.getD 0#64 < xs'[2 * pos.toNat + 1]?.getD 0#64)))
              ?_ (fun Jb hJb => ?_)
            · rintro Jb ⟨best, ⟨⟩⟩ mgb ⟨hmgb, hb_lt, hb_p, hb_c1, hb_case⟩
              subst mgb
              c0_hsteps_nogrp
              refine wp_join_group
                (fun (best2, ()) mgb2 => mgb2 = mg ∧
                  best2.toNat < n.toNat ∧
                  xs'[pos.toNat]?.getD 0#64 ≤ xs'[best2.toNat]?.getD 0#64 ∧
                  xs'[2 * pos.toNat + 1]?.getD 0#64 ≤ xs'[best2.toNat]?.getD 0#64 ∧
                  (2 * pos.toNat + 2 < n.toNat →
                    xs'[2 * pos.toNat + 2]?.getD 0#64 ≤ xs'[best2.toNat]?.getD 0#64) ∧
                  ((best2 = pos ∧ xs'[2 * pos.toNat + 1]?.getD 0#64 ≤ xs'[pos.toNat]?.getD 0#64 ∧
                      (2 * pos.toNat + 2 < n.toNat →
                        xs'[2 * pos.toNat + 2]?.getD 0#64 ≤ xs'[pos.toNat]?.getD 0#64)) ∨
                    (xs'[pos.toNat]?.getD 0#64 < xs'[best2.toNat]?.getD 0#64 ∧
                      (best2.toNat = 2 * pos.toNat + 1 ∨
                        (2 * pos.toNat + 2 < n.toNat ∧ best2.toNat = 2 * pos.toNat + 2)))))
                ?_ (fun Jb2 hJb2 => ?_)
              · rintro Jb2 ⟨best2, ⟨⟩⟩ mgb2 ⟨hmgb2, hb2_lt, hb2_p, hb2_c1, hb2_c2, hb2_case⟩
                subst mgb2
                c0_hsplit
                · have hmax_pos : MaxHeapAt xs' n.toNat pos.toNat := by
                    rcases hb2_case with ⟨_, h1, h2⟩ | ⟨hlt, h12⟩
                    · exact ⟨fun _ => h1, h2⟩
                    · exfalso; have htn := congrArg BitVec.toNat hc
                      rcases h12 with h1 | ⟨_, h1⟩ <;> omega
                  have hheap' : MaxHeapRange xs' start.toNat n.toNat := fun j hj1 hj2 =>
                    if hjp : j = pos.toNat then hjp ▸ hmax_pos else hother' j hj1 hj2 hjp
                  c0_hsteps!
                  exact hJ_out (pos, ()) mg ⟨xs', hlen', htail', hperm', hheap', hmg'⟩
                · have hb2_spec :
                      xs'[pos.toNat]?.getD 0#64 < xs'[best2.toNat]?.getD 0#64 ∧
                      (best2.toNat = 2 * pos.toNat + 1 ∨
                        (2 * pos.toNat + 2 < n.toNat ∧ best2.toNat = 2 * pos.toNat + 2)) := by
                    rcases hb2_case with ⟨rfl, _⟩ | h
                    · exact absurd rfl hc
                    · exact h
                  have hpos_len : pos.toNat < xs'.length := by omega
                  have hbest_len : best2.toNat < xs'.length := by omega
                  c0_hsteps!
                  let xs1 := (xs'.set pos.toNat (xs'[best2.toNat]'hbest_len)).set
                    best2.toNat (xs'[pos.toNat]'hpos_len)
                  have hmg1 : (array64 a xs1 ⋆ R) m := by
                    simpa only [xs1, List.getElem?_eq_getElem, Option.getD_some] using hm
                  have hstep := sift_swap_heap_step hst_p hpos_lt hb2_lt (by omega) hc1_lt
                    hb2_spec.1 hb2_c1 hb2_c2 hb2_spec.2 hother' hpar'
                  have hmu : n.toNat - best2.toNat < n.toNat - pos.toNat := by
                    rcases hb2_spec.2 with h | ⟨_, h⟩ <;> omega
                  exact ih (best2, ()) m hmu ⟨xs1, by simp [xs1, hlen'], by omega, by omega,
                    fun k hk1 hk2 => (bv64_swap_tail hpos_lt hb2_lt hk1).trans (htail' k hk1 hk2),
                    fun k hk => by
                      obtain ⟨m1, hm1, heq1⟩ :=
                        bv64_swap_preserves_elem xs' hpos_lt hb2_lt (by omega) hk
                      obtain ⟨m2, hm2, heq2⟩ := hperm' m1 hm1
                      exact ⟨m2, hm2, by simpa only [xs1] using heq1.trans heq2⟩,
                    hstep.1, hstep.2, hmg1⟩
              · have hc2_nat : (pos * 2 + 1 + 1).toNat = 2 * pos.toNat + 2 := by
                  rw [BitVec.toNat_add, hc1_nat, h1bv]; omega
                c0_hsplit
                · have hc2_lt : 2 * pos.toNat + 2 < n.toNat := by
                    rw [h2bv, h1bv] at hc; omega
                  have hb_len : best.toNat < xs'.length := by omega
                  have hc2_len : 2 * pos.toNat + 2 < xs'.length := by omega
                  have hc2_idx :
                      (pos.toNat * (2 : BitVec 64).toNat + (1 : BitVec 64).toNat +
                        (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * pos.toNat + 2 := by
                    rw [h2bv, h1bv]; omega
                  c0_hsteps!
                  c0_hsplit
                  · have hlt_nat : xs'[best.toNat].toNat < xs'[2 * pos.toNat + 2].toNat := by
                      rwa [list_getElem_congr hc2_idx (by omega) hc2_len] at hc
                    have hlt_bc2 : xs'[best.toNat]?.getD 0#64 <
                        xs'[2 * pos.toNat + 2]?.getD 0#64 := by
                      rw [List.getElem?_eq_getElem hb_len, List.getElem?_eq_getElem hc2_len,
                        Option.getD_some, Option.getD_some]
                      exact BitVec.lt_def.mpr hlt_nat
                    have hlt_pc2 : xs'[pos.toNat]?.getD 0#64 <
                        xs'[2 * pos.toNat + 2]?.getD 0#64 :=
                      BitVec.lt_def.mpr (Nat.lt_of_le_of_lt (BitVec.le_def.mp hb_p)
                        (BitVec.lt_def.mp hlt_bc2))
                    c0_hsteps!
                    exact hJb2 (pos * 2 + 1 + 1, ()) mg
                      ⟨rfl, by omega, hc2_nat ▸ BitVec.le_of_lt hlt_pc2,
                        hc2_nat ▸ BitVec.le_trans hb_c1 (BitVec.le_of_lt hlt_bc2),
                        fun _ => hc2_nat ▸ BitVec.le_refl _,
                        Or.inr ⟨hc2_nat ▸ hlt_pc2, Or.inr ⟨hc2_lt, hc2_nat⟩⟩⟩
                  · have hnat : xs'[2 * pos.toNat + 2].toNat ≤ xs'[best.toNat].toNat := by
                      rw [list_getElem_congr hc2_idx (by omega) hc2_len] at hc; omega
                    have hle_c2b : xs'[2 * pos.toNat + 2]?.getD 0#64 ≤
                        xs'[best.toNat]?.getD 0#64 := by
                      rw [List.getElem?_eq_getElem hb_len, List.getElem?_eq_getElem hc2_len,
                        Option.getD_some, Option.getD_some]
                      exact BitVec.le_def.mpr hnat
                    c0_hsteps!
                    refine hJb2 (best, ()) mg ⟨rfl, hb_lt, hb_p, hb_c1, fun _ => hle_c2b, ?_⟩
                    rcases hb_case with ⟨rfl, hc1p⟩ | ⟨hb1, hpc1⟩
                    · exact Or.inl ⟨rfl, hc1p, fun _ => hle_c2b⟩
                    · exact Or.inr ⟨by rw [hb1]; exact hpc1, Or.inl hb1⟩
                · have hc2_ge : ¬(2 * pos.toNat + 2 < n.toNat) := by
                    rw [h2bv, h1bv] at hc; omega
                  c0_hsteps!
                  refine hJb2 (best, ()) mg
                    ⟨rfl, hb_lt, hb_p, hb_c1, fun h => absurd h hc2_ge, ?_⟩
                  rcases hb_case with ⟨rfl, hc1p⟩ | ⟨hb1, hpc1⟩
                  · exact Or.inl ⟨rfl, hc1p, fun h => absurd h hc2_ge⟩
                  · exact Or.inr ⟨by rw [hb1]; exact hpc1, Or.inl hb1⟩
            · have hpos_len : pos.toNat < xs'.length := by omega
              have hc1_len : 2 * pos.toNat + 1 < xs'.length := by omega
              have hc1_idx :
                  (pos.toNat * (2 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                    2 * pos.toNat + 1 := by
                rw [h2bv, h1bv]; omega
              c0_hsteps!
              c0_hsplit
              · have hnat : xs'[pos.toNat].toNat < xs'[2 * pos.toNat + 1].toNat := by
                  rwa [list_getElem_congr hc1_idx (by omega) hc1_len] at hc
                have hlt_pc1 : xs'[pos.toNat]?.getD 0#64 <
                    xs'[2 * pos.toNat + 1]?.getD 0#64 := by
                  rw [List.getElem?_eq_getElem hpos_len, List.getElem?_eq_getElem hc1_len,
                    Option.getD_some, Option.getD_some]
                  exact BitVec.lt_def.mpr hnat
                c0_hsteps!
                exact hJb (pos * 2 + 1, ()) mg
                  ⟨rfl, by omega, hc1_nat ▸ BitVec.le_of_lt hlt_pc1,
                    hc1_nat ▸ BitVec.le_refl _, Or.inr ⟨hc1_nat, hlt_pc1⟩⟩
              · have hnat : xs'[2 * pos.toNat + 1].toNat ≤ xs'[pos.toNat].toNat := by
                  rw [list_getElem_congr hc1_idx (by omega) hc1_len] at hc; omega
                have hle_c1p : xs'[2 * pos.toNat + 1]?.getD 0#64 ≤
                    xs'[pos.toNat]?.getD 0#64 := by
                  rw [List.getElem?_eq_getElem hpos_len, List.getElem?_eq_getElem hc1_len,
                    Option.getD_some, Option.getD_some]
                  exact BitVec.le_def.mpr hnat
                c0_hsteps!
                exact hJb (pos, ()) mg
                  ⟨rfl, hpos_lt, BitVec.le_refl _, hle_c1p, Or.inl ⟨rfl, hle_c1p⟩⟩
        · have hheap' : MaxHeapRange xs' start.toNat n.toNat := fun j hj1 hj2 =>
            hother' j hj1 hj2 (by omega)
          c0_hsteps!
          exact hJ_out (pos, ()) mg ⟨xs', hlen', htail', hperm', hheap', hmg'⟩)

/-! ## 2. `full_cong_u64_sort_m7_wp` -/

private theorem sort_phase2_step {xs : List (BitVec 64)} {hi n : Nat}
    (hhi : 0 < hi) (hhi_n : hi < n) (hn : n ≤ xs.length)
    (hheap : MaxHeapRange xs 0 (hi + 1))
    (hsort : SortedRange64 xs (hi + 1) n)
    (hcross : ∀ p q, p < hi + 1 → hi + 1 ≤ q → q < n → xs[p]?.getD 0#64 ≤ xs[q]?.getD 0#64) :
    let xs1 := (xs.set hi (xs[0]'(by omega))).set 0 (xs[hi]'(by omega))
    MaxHeapRange xs1 1 hi ∧
    (∀ k, hi ≤ k → k < xs.length → xs1[k]? =
      if k = hi then xs[0]? else xs[k]?) ∧
    (∀ xs2 : List (BitVec 64), xs2.length = xs.length →
      (∀ k, hi ≤ k → k < xs.length → xs2[k]? = xs1[k]?) →
      (∀ k < hi, ∃ j < hi, xs2[k]? = xs1[j]?) →
      MaxHeapRange xs2 0 hi →
      SortedRange64 xs2 hi n ∧
      (∀ p q, p < hi → hi ≤ q → q < n → xs2[p]?.getD 0#64 ≤ xs2[q]?.getD 0#64)) := by
  intro xs1
  have get1 : ∀ k, k < xs.length → xs1[k]? =
      if k = 0 then xs[hi]? else if k = hi then xs[0]? else xs[k]? := by
    intro k hk
    by_cases h0 : k = 0
    · subst h0; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp only [List.length_set]; omega),
        List.getElem?_eq_getElem (by omega)]
    · simp only [h0, ↓reduceIte]
      rw [show xs1[k]? = (xs.set hi (xs[0]'(by omega)))[k]? from
        List.getElem?_set_ne (Ne.symm h0)]
      by_cases h1 : k = hi
      · subst h1; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · simp only [h1, ↓reduceIte, List.getElem?_set_ne (Ne.symm h1)]
  refine ⟨fun j hj1 hj2 => ?_, fun k hk1 hk2 => ?_, fun xs2 hlen2 htail2 hperm2 _ => ?_⟩
  · have hmj := hheap j (by omega) (by omega)
    have hneq : ∀ c, 1 ≤ c → c < hi → xs1[c]? = xs[c]? := fun c hc1 hc2 => by
      rw [get1 c (by omega)]; simp only [show c ≠ 0 by omega, show c ≠ hi by omega, ↓reduceIte]
    refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
    · rw [hneq _ (by omega) hc1, hneq j hj1 hj2]; exact hmj.1 (by omega)
    · rw [hneq _ (by omega) hc2, hneq j hj1 hj2]; exact hmj.2 (by omega)
  · rw [get1 k hk2]; simp only [show k ≠ 0 by omega, ↓reduceIte]
  · have h2_eq : ∀ k, hi ≤ k → k < xs.length →
        xs2[k]? = if k = hi then xs[0]? else xs[k]? := fun k hk1 hk2 => by
      rw [htail2 k hk1 hk2, get1 k hk2]; simp only [show k ≠ 0 by omega, ↓reduceIte]
    have h2_perm : ∀ k < hi, ∃ j, 0 < j ∧ j < hi + 1 ∧ xs2[k]? = xs[j]? := by
      intro k hk
      obtain ⟨j, hj, heq⟩ := hperm2 k hk
      have hj_eq : xs1[j]? = if j = 0 then xs[hi]? else xs[j]? := by
        rw [get1 j (by omega)]
        by_cases hj0 : j = 0
        · simp only [hj0, ↓reduceIte]
        · simp only [hj0, show j ≠ hi by omega, ↓reduceIte]
      rw [hj_eq] at heq
      split at heq
      · exact ⟨hi, hhi, by omega, heq⟩
      · exact ⟨j, by omega, by omega, heq⟩
    have hcross' : ∀ p q, p < hi → hi ≤ q → q < n →
        xs2[p]?.getD 0#64 ≤ xs2[q]?.getD 0#64 := by
      intro p q hp hq1 hq2
      obtain ⟨j, _, hj_hi1, hp_eq⟩ := h2_perm p hp
      rw [hp_eq, h2_eq q hq1 (by omega)]
      by_cases hqi : q = hi
      · simp only [hqi, ↓reduceIte]; exact maxHeap_le_root hheap j hj_hi1
      · simp only [hqi, ↓reduceIte]; exact hcross j q hj_hi1 (by omega) hq2
    refine ⟨fun i j hi1 hij hj2 => ?_, hcross'⟩
    by_cases hi_eq : i = hi
    · rw [hi_eq] at hij ⊢
      by_cases hj_eq : j = hi
      · rw [hj_eq]; exact BitVec.le_refl _
      · rw [h2_eq hi (Nat.le_refl _) (by omega)]; simp only [↓reduceIte]
        rw [h2_eq j (by omega) (by omega)]; simp only [hj_eq, ↓reduceIte]
        exact hcross 0 j (by omega) (by omega) hj2
    · rw [h2_eq i (by omega) (by omega)]; simp only [hi_eq, ↓reduceIte]
      rw [h2_eq j (by omega) (by omega)]; simp only [show j ≠ hi by omega, ↓reduceIte]
      exact hsort i j (by omega) hij hj2

/-- Canonical `Func.wp` proof for `full_cong_u64_sort_m7`. -/
theorem full_cong_u64_sort_m7_wp (Γ : Env)
    (hSift : Γ.Has "full_cong_u64_sift_m7" Spec.fullCongU64SiftM7Spec) :
    ∀ a m Q X, Spec.fullCongU64SortM7Spec a m Q X →
      Func.wp Γ full_cong_u64_sort_m7_body a m Q X := by
  rintro ⟨a, n, ⟨⟩⟩ m0 Q X ⟨xs, R, hn, hlen, hm0, hQ⟩
  unfold Func.wp full_cong_u64_sort_m7_body
  c0_hsteps_nogrp
  c0_hsplit
  · have hle1 : n.toNat ≤ 1 := by simpa only [show (1 : BitVec 64).toNat = 1 by rfl] using hc
    c0_hsteps!
    refine hQ xs m0 rfl (fun _ _ _ => rfl) (fun k hk => ⟨k, hk, rfl⟩) ?_ hm0
    intro i j hi hij hj
    have hij_eq : i = j := by omega
    rw [hij_eq]; exact BitVec.le_refl _
  · have h1bv : (1 : BitVec 64).toNat = 1 := rfl
    have h0bv : (0 : BitVec 64).toNat = 0 := rfl
    have hn_gt1 : 1 < n.toNat := by rw [h1bv] at hc; omega
    have hhalf_nat : (n >>> 1#64).toNat = n.toNat / 2 := bv64_shr1_toNat n
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) mg =>
        ∃ xs' : List (BitVec 64), xs'.length = xs.length ∧ i.toNat ≤ n.toNat / 2 ∧
          (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) ∧
          (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) ∧
          MaxHeapRange xs' i.toNat n.toNat ∧
          (array64 a xs' ⋆ R) mg)
      (fun (i, ()) _ => i.toNat)
      (fun J hJ => by
        c0_hsteps!
        exact hJ (n >>> 1#64, ()) m0 ⟨xs, rfl, by rw [hhalf_nat]; exact Nat.le_refl _,
          fun _ _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩,
          fun j hj1 hj2 =>
            ⟨fun h => absurd h (by rw [hhalf_nat] at hj1; omega),
             fun h => absurd h (by rw [hhalf_nat] at hj1; omega)⟩, hm0⟩)
      (fun J (i, ()) mg ⟨xs', hlen', hi_le, htail', hperm', hheap', hmg'⟩ ih => by
        c0_hsplit
        · have hi_pos : 0 < i.toNat := by rw [h0bv] at hc; omega
          have hi1_nat : (i - 1).toNat = i.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1bv]; omega)), h1bv]
          c0_hsteps_nogrp
          cong_call hSift
          dsimp only [vals, Arg.val]
          refine ⟨xs', R, by omega, by omega, by omega, ?_, hmg',
            fun xs'' m'' hlen'' htail'' hperm'' hheap'' hm'' => ?_⟩
          · simpa only [hi1_nat, show i.toNat - 1 + 1 = i.toNat by omega] using hheap'
          · c0_hsteps!
            exact ih (i - 1, ()) m'' (by dsimp only; omega)
              ⟨xs'', hlen''.trans hlen', by omega,
                fun k hk1 hk2 => (htail'' k hk1 (by omega)).trans (htail' k hk1 hk2),
                fun k hk => by
                  obtain ⟨m1, hm1, heq1⟩ := hperm'' k hk
                  obtain ⟨m2, hm2, heq2⟩ := hperm' m1 hm1
                  exact ⟨m2, hm2, heq1.trans heq2⟩,
                hheap'', hm''⟩
        · have hi_zero : i.toNat = 0 := by rw [h0bv] at hc; omega
          have hheap_full : MaxHeapRange xs' 0 n.toNat := by simpa only [hi_zero] using hheap'
          have hn1_nat : (n - 1).toNat = n.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1bv]; omega)), h1bv]
          c0_hsteps_nogrp
          refine wp_loop_inv (ts := [i64])
            (fun (hi, ()) mg2 =>
              ∃ xs2 : List (BitVec 64), xs2.length = xs.length ∧ hi.toNat < n.toNat ∧
                (∀ k, n.toNat ≤ k → k < xs.length → xs2[k]? = xs[k]?) ∧
                (∀ k < n.toNat, ∃ j < n.toNat, xs2[k]? = xs[j]?) ∧
                MaxHeapRange xs2 0 (hi.toNat + 1) ∧
                SortedRange64 xs2 (hi.toNat + 1) n.toNat ∧
                (∀ p q, p < hi.toNat + 1 → hi.toNat + 1 ≤ q → q < n.toNat →
                  xs2[p]?.getD 0#64 ≤ xs2[q]?.getD 0#64) ∧
                (array64 a xs2 ⋆ R) mg2)
            (fun (hi, ()) _ => hi.toNat)
            (fun J2 hJ2 => by
              c0_hsteps!
              exact hJ2 (n - 1, ()) mg ⟨xs', hlen', by omega, htail', hperm',
                by simpa only [hn1_nat, show n.toNat - 1 + 1 = n.toNat by omega] using hheap_full,
                fun _ _ _ _ _ => by omega, fun _ _ _ _ _ => by omega, hmg'⟩)
            (fun J2 (hi, ()) mg2
                ⟨xs2, hlen2, hhi_lt, htail2, hperm2, hheap2, hsort2, hcross2, hmg2⟩ ih2 => by
              c0_hsplit
              · have hhi_pos : 0 < hi.toNat := by rw [h0bv] at hc; omega
                have hhi1_nat : (hi - 1).toNat = hi.toNat - 1 := by
                  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1bv]; omega)), h1bv]
                have hstep := sort_phase2_step hhi_pos hhi_lt (by omega) hheap2 hsort2 hcross2
                have hhi_len : hi.toNat < xs2.length := by omega
                have h0_len : 0 < xs2.length := by omega
                have hzero_ext : (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 := by decide
                have hzero_ofNat : (BitVec.ofNat 64 0).toNat = 0 := rfl
                c0_hsteps_nogrp
                let xs3 := (xs2.set hi.toNat (xs2[0]'h0_len)).set 0 (xs2[hi.toNat]'hhi_len)
                have hxs3_len : xs3.length = xs2.length := by simp [xs3]
                have hmg3 : (array64 a xs3 ⋆ R) m := by
                  simpa only [xs3, hzero_ext, hzero_ofNat, List.getElem?_eq_getElem,
                    Option.getD_some] using hm
                cong_call hSift
                dsimp only [vals, Arg.val]
                refine ⟨xs3, R, by rw [h0bv]; omega, by omega, by omega,
                  by rw [h0bv]; exact hstep.1, hmg3,
                  fun xs4 m4 hlen4 htail4 hperm4 hheap4 hm4 => ?_⟩
                have hfin := hstep.2.2 xs4 (by omega)
                  (fun k hk1 hk2 => htail4 k hk1 (by rw [hxs3_len]; exact hk2)) hperm4
                  (by rwa [h0bv] at hheap4)
                c0_hsteps!
                exact ih2 (hi - 1, ()) m4 (by dsimp only; omega) ⟨xs4, by omega, by omega,
                  fun k hk1 hk2 => by
                    rw [htail4 k (by omega) (by omega), hstep.2.1 k (by omega) (by omega)]
                    simp only [show k ≠ hi.toNat by omega, ↓reduceIte]; exact htail2 k hk1 hk2,
                  fun k hk => by
                    by_cases hki : k < hi.toNat
                    · obtain ⟨j, hj, hj_eq⟩ := hperm4 k hki
                      obtain ⟨j0, hj0, hj0_eq⟩ := bv64_swap_preserves_elem xs2
                        (by omega : hi.toNat < hi.toNat + 1) (by omega : 0 < hi.toNat + 1)
                        (by omega) (by omega : j < hi.toNat + 1)
                      obtain ⟨j1, hj1, hj1_eq⟩ := hperm2 j0 (by omega)
                      exact ⟨j1, hj1, hj_eq.trans (hj0_eq.trans hj1_eq)⟩
                    · rw [htail4 k (by omega) (by omega), hstep.2.1 k (by omega) (by omega)]
                      split
                      · exact hperm2 0 (by omega)
                      · exact hperm2 k hk,
                  by rw [h0bv] at hheap4
                     simpa only [hhi1_nat, show hi.toNat - 1 + 1 = hi.toNat by omega] using hheap4,
                  by simpa only [hhi1_nat, show hi.toNat - 1 + 1 = hi.toNat by omega] using hfin.1,
                  by simpa only [hhi1_nat, show hi.toNat - 1 + 1 = hi.toNat by omega] using hfin.2,
                  hm4⟩
              · have hhi_zero : hi.toNat = 0 := by rw [h0bv] at hc; omega
                rw [hhi_zero] at hsort2 hcross2
                c0_hsteps!
                refine hQ xs2 mg2 hlen2 htail2 hperm2 (fun p q hp hpq hqn => ?_) hmg2
                by_cases hp0 : p = 0
                · subst hp0
                  by_cases hq0 : q = 0
                  · subst hq0; exact BitVec.le_refl _
                  · exact hcross2 0 q (by omega) (by omega) hqn
                · exact hsort2 p q (by omega) hpq hqn))

/-! ## 3. `full_cong_bsearch_u64_m7_wp` -/

/-- Canonical `Func.wp` proof for `full_cong_bsearch_u64_m7`. -/
theorem full_cong_bsearch_u64_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullCongBsearchU64M7Spec a m Q X →
      Func.wp Γ full_cong_bsearch_u64_m7_body a m Q X := by
  rintro ⟨a, lo, hi, key, ⟨⟩⟩ m0 Q X ⟨xs, R, hlo, hhi, hlen, hsorted, hm0, hQ⟩
  unfold Func.wp full_cong_bsearch_u64_m7_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (lo', hi', ()) mg => mg = m0 ∧
      lo.toNat ≤ lo'.toNat ∧ lo'.toNat ≤ hi'.toNat ∧ hi'.toNat ≤ hi.toNat ∧
      (∀ idx, lo.toNat ≤ idx → idx < hi.toNat → xs[idx]? = some key →
        lo'.toNat ≤ idx ∧ idx < hi'.toNat))
    (fun (lo', hi', ()) _ => hi'.toNat - lo'.toNat)
    (fun J hJ => by
      c0_hsteps!
      exact hJ (lo, hi, ()) m0 ⟨rfl, Nat.le_refl _, hlo, Nat.le_refl _,
        fun _ h1 h2 _ => ⟨h1, h2⟩⟩)
    (fun J (lo', hi', ()) mg ⟨hmg0, h1, h2, h3, hcontain⟩ ih => by
      subst mg
      c0_hsplit
      · have hlo_hi : lo'.toNat < hi'.toNat := hc
        have hdiff : (lo' + ((hi' - lo') >>> (1 : Nat))).toNat =
            lo'.toNat + (hi'.toNat - lo'.toNat) / 2 := by
          have hsub : (hi' - lo').toNat = hi'.toNat - lo'.toNat := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
          have hsh : ((hi' - lo') >>> (1 : Nat)).toNat = (hi'.toNat - lo'.toNat) / 2 := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsub, Nat.pow_one]
          rw [BitVec.toNat_add, hsh, Nat.mod_eq_of_lt (by omega)]
        have hmid_lt : (lo' + ((hi' - lo') >>> (1 : Nat))).toNat < xs.length := by omega
        have hmid_idx : (lo'.toNat + ((hi' - lo') >>> (1 : Nat)).toNat) % 2 ^ 64 =
            (lo' + ((hi' - lo') >>> (1 : Nat))).toNat := by
          rw [BitVec.toNat_add]
        c0_hsteps!
        c0_hsplit
        · have hmid_eq : xs[(lo' + ((hi' - lo') >>> (1 : Nat))).toNat]'hmid_lt = key := by
            rwa [list_getElem_congr hmid_idx (by omega) hmid_lt] at hc
          c0_hsteps!
          refine hQ true ⟨fun _ => ?_, fun _ => rfl⟩
          refine ⟨(lo' + ((hi' - lo') >>> (1 : Nat))).toNat, by omega, by omega, ?_⟩
          rw [List.getElem?_eq_getElem hmid_lt, hmid_eq]
        · have hlt_nat : (xs[(lo' + ((hi' - lo') >>> (1 : Nat))).toNat]'hmid_lt).toNat <
              key.toNat := by
            rwa [list_getElem_congr hmid_idx (by omega) hmid_lt] at hc
          have hlt_key : xs[(lo' + ((hi' - lo') >>> (1 : Nat))).toNat]'hmid_lt < key :=
            BitVec.lt_def.mpr hlt_nat
          have h1bv : (1 : BitVec 64).toNat = 1 := rfl
          have hmid1_nat : (lo' + ((hi' - lo') >>> (1 : Nat)) + 1).toNat =
              lo'.toNat + (hi'.toNat - lo'.toNat) / 2 + 1 := by
            rw [BitVec.toNat_add, hdiff, h1bv]; omega
          c0_hsteps!
          exact ih (lo' + ((hi' - lo') >>> (1 : Nat)) + 1, hi', ()) m0
            (by dsimp only; omega)
            ⟨rfl, by omega, by omega, h3, fun idx hi1 hi2 hkey => by
              have ⟨hl, hh⟩ := hcontain idx hi1 hi2 hkey
              refine ⟨?_, hh⟩
              exact Classical.byContradiction fun hlt => by
                have hle : idx ≤ (lo' + ((hi' - lo') >>> (1 : Nat))).toNat := by omega
                have hso := hsorted idx (lo' + ((hi' - lo') >>> (1 : Nat))).toNat
                  hi1 hle (by omega)
                rw [hkey, Option.getD_some, List.getElem?_eq_getElem hmid_lt,
                  Option.getD_some] at hso
                have hso_n := BitVec.le_def.mp hso
                have hlt_n := BitVec.lt_def.mp hlt_key
                omega⟩
        · rename_i hne_raw
          have hmid_ne : xs[(lo' + ((hi' - lo') >>> (1 : Nat))).toNat]'hmid_lt ≠ key := by
            rwa [list_getElem_congr hmid_idx (by omega) hmid_lt] at hne_raw
          have hnlt_nat : ¬(xs[(lo' + ((hi' - lo') >>> (1 : Nat))).toNat]'hmid_lt).toNat <
              key.toNat := by
            rwa [list_getElem_congr hmid_idx (by omega) hmid_lt] at hc
          c0_hsteps!
          exact ih (lo', lo' + ((hi' - lo') >>> (1 : Nat)), ()) m0
            (by dsimp only; omega)
            ⟨rfl, h1, by omega, by omega, fun idx hi1 hi2 hkey => by
              have ⟨hl, hh⟩ := hcontain idx hi1 hi2 hkey
              refine ⟨hl, ?_⟩
              exact Classical.byContradiction fun hlt => by
                have hle : (lo' + ((hi' - lo') >>> (1 : Nat))).toNat ≤ idx := by omega
                have hso := hsorted (lo' + ((hi' - lo') >>> (1 : Nat))).toNat idx
                  (by omega) hle (by omega)
                rw [hkey, Option.getD_some, List.getElem?_eq_getElem hmid_lt,
                  Option.getD_some] at hso
                have hkey_lt : key < xs[(lo' + ((hi' - lo') >>> (1 : Nat))).toNat]'hmid_lt :=
                  BitVec.lt_def.mpr (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnlt_nat)
                    fun he => hmid_ne (BitVec.eq_of_toNat_eq he.symm))
                have hso_n := BitVec.le_def.mp hso
                have hlt_n := BitVec.lt_def.mp hkey_lt
                omega⟩
      · rw [wp_ret]
        exact hQ false ⟨(fun h => by cases h),
          (fun ⟨idx, hi1, hi2, hkey⟩ => by have := hcontain idx hi1 hi2 hkey; omega)⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence

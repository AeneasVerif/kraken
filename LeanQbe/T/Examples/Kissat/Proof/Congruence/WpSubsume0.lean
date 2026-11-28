/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Pair-Sort WP Proofs (`sift_pairs_fid`, `sort_pairs_fid`)

Canonical `Func.wp` proofs for:
- `full_cong_sift_pairs_fid` (`Spec.fullCongSiftPairsFidSpec`)
- `full_cong_sort_pairs_fid` (`Spec.fullCongSortPairsFidSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

private theorem congPairsOk_swap {P : BitVec 32 → BitVec 32 → Prop}
    {a : List (BitVec 32)} {n i j : Nat}
    (hp : CongPairsOk P a n) (hi : i < n) (hj : j < n) (hn : 2 * n ≤ a.length) :
    let pi0 := a[2 * i]'(by omega)
    let pi1 := a[2 * i + 1]'(by omega)
    let pj0 := a[2 * j]'(by omega)
    let pj1 := a[2 * j + 1]'(by omega)
    let a' := (((a.set (2 * i) pj0).set (2 * i + 1) pj1).set (2 * j) pi0).set (2 * j + 1) pi1
    CongPairsOk P a' n := by
  intro pi0 pi1 pj0 pj1 a' k hk
  by_cases hkj : k = j
  · subst hkj
    simp only [a']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega),
      List.getElem?_set_self (by simp; omega), Option.getD_some, Option.getD_some]
    simpa [pi0, pi1, List.getElem?_eq_getElem (by omega : 2 * i < a.length),
      List.getElem?_eq_getElem (by omega : 2 * i + 1 < a.length)] using hp i hi
  · by_cases hki : k = i
    · subst hki
      simp only [a']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega), Option.getD_some, Option.getD_some]
      simpa [pj0, pj1, List.getElem?_eq_getElem (by omega : 2 * j < a.length),
        List.getElem?_eq_getElem (by omega : 2 * j + 1 < a.length)] using hp j hj
    · simp only [a']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hp k hk

private theorem congPairsOk_of_prefix {P : BitVec 32 → BitVec 32 → Prop}
    {a b : List (BitVec 32)} {n m : Nat}
    (hpm : CongPairsOk P b m) (hpn : CongPairsOk P a n)
    (heq : ∀ idx, 2 * m ≤ idx → b[idx]? = a[idx]?) :
    CongPairsOk P b n := by
  intro k hk
  by_cases hkm : k < m
  · exact hpm k hkm
  · rw [heq (2 * k) (by omega), heq (2 * k + 1) (by omega)]
    exact hpn k hk

private theorem swap_suffix_eq {a : List (BitVec 32)} {n i j : Nat}
    (hi : i < n) (hj : j < n) (hn : 2 * n ≤ a.length) {idx : Nat} (hidx : 2 * n ≤ idx) :
    let pi0 := a[2 * i]'(by omega)
    let pi1 := a[2 * i + 1]'(by omega)
    let pj0 := a[2 * j]'(by omega)
    let pj1 := a[2 * j + 1]'(by omega)
    ((((a.set (2 * i) pj0).set (2 * i + 1) pj1).set (2 * j) pi0).set (2 * j + 1) pi1)[idx]? =
      a[idx]? := by
  dsimp only
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem bv64_shl1_add1_toNat {x : BitVec 64} {bound : Nat} (hx : 2 * x.toNat + 1 < bound)
    (hb : bound < 2 ^ 64) : ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  bv_omega

private theorem bv64_shl1_toNat_of {x : BitVec 64} {bound : Nat} (hx : 2 * x.toNat < bound)
    (hb : bound < 2 ^ 64) : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  bv_omega

public section

/-- Canonical `Func.wp` proof for `full_cong_sift_pairs_fid`. -/
theorem full_cong_sift_pairs_fid_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongSiftPairsFidSpec args m Q X →
      Func.wp Γ full_cong_sift_pairs_fid_body args m Q X := by
  rintro ⟨ap, start, n, ⟨⟩⟩ m0 Q X ⟨P, a0, R, hstart, h2n, halen, hp0, hm0, hQ⟩
  have hn_lt : n.toNat < 2 ^ 60 := by omega
  unfold Func.wp full_cong_sift_pairs_fid_body
  c0_hstraight!
  refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
    (fun (_, ()) mf => ∃ af : List (BitVec 32),
      af.length = a0.length ∧ CongPairsOk P af n.toNat ∧
      (∀ idx, 2 * n.toNat ≤ idx → af[idx]? = a0[idx]?) ∧ (array (t := i32) ap af ⋆ R) mf)
    (fun rem (i, ()) mi => ∃ ai : List (BitVec 32),
      n.toNat - i.toNat ≤ rem ∧ i.toNat < n.toNat ∧ ai.length = a0.length ∧
      CongPairsOk P ai n.toNat ∧ (∀ idx, 2 * n.toNat ≤ idx → ai[idx]? = a0[idx]?) ∧
      (array (t := i32) ap ai ⋆ R) mi)
    (fun J _ mf ⟨af, hlen_f, hpf, hsuf_f, hmf⟩ => by
      c0_hsteps!; exact hQ af mf hlen_f hpf hsuf_f hmf)
    (fun _ Lp rem (i, ()) mi hBp hLp ⟨ai, hrem_i, hi_lt, hlen_i, hpi, hsuf_i, hmi⟩ => ?_)
    (fun _ L _ hL => by
      c0_hsteps!
      exact hL (n.toNat - start.toNat) (start, ()) m0
        ⟨a0, Nat.le_refl _, hstart, rfl, hp0, fun _ _ => rfl, hm0⟩)
  · c0_hsplit
    · clear hc
      c0_hsplit
      · c0_hsteps!; exact hBp (i, ()) mi ⟨ai, hlen_i, hpi, hsuf_i, hmi⟩
      · have hc_n : ((i <<< (1 : Nat)) + 1#64).toNat = 2 * i.toNat + 1 :=
          bv64_shl1_add1_toNat (bound := 2 * n.toNat) (by omega) (by omega)
        have hc_lt : 2 * i.toNat + 1 < n.toNat := by bv_omega
        clear hc
        have h2c : (((i <<< (1 : Nat)) + 1#64) <<< (1 : Nat)).toNat =
            2 * ((i <<< (1 : Nat)) + 1#64).toNat :=
          bv64_shl1_toNat_of (bound := 2 * n.toNat + 1) (by rw [hc_n]; omega) (by omega)
        have h2c1 : ((((i <<< (1 : Nat)) + 1#64) <<< (1 : Nat)) + 1#64).toNat =
            2 * ((i <<< (1 : Nat)) + 1#64).toNat + 1 :=
          bv64_shl1_add1_toNat (bound := 2 * n.toNat + 1) (by rw [hc_n]; omega) (by omega)
        have h2i : (i <<< (1 : Nat)).toNat = 2 * i.toNat :=
          bv64_shl1_toNat_of (bound := 2 * n.toNat + 1) (by omega) (by omega)
        have h2i1 : ((i <<< (1 : Nat)) + 1#64).toNat = 2 * i.toNat + 1 :=
          bv64_shl1_add1_toNat (bound := 2 * n.toNat + 1) (by omega) (by omega)
        have hc0_arr : (((i <<< (1 : Nat)) + 1#64) <<< (1 : Nat)).toNat < ai.length := by
          rw [h2c, hc_n]; omega
        have hc1_arr : ((((i <<< (1 : Nat)) + 1#64) <<< (1 : Nat)) + 1#64).toNat < ai.length := by
          rw [h2c1, hc_n]; omega
        have hi0_arr : (i <<< (1 : Nat)).toNat < ai.length := by omega
        have hi1_arr : ((i <<< (1 : Nat)) + 1#64).toNat < ai.length := by omega
        c0_hstraight!
        let Pbest : Tup Val [i64, i32, i32] → Mem 64 → Prop :=
          fun (best, b0, b1, ()) mb => mb = mi ∧ i.toNat ≤ best.toNat ∧ best.toNat < n.toNat ∧
            b0 = ai[2 * best.toNat]?.getD 0#32 ∧ b1 = ai[2 * best.toNat + 1]?.getD 0#32
        refine wp_join_group (ts := [i64, i32, i32]) Pbest ?_ ?_
        · rintro _ ⟨best, b0, b1, ⟨⟩⟩ _ ⟨rfl, hib, hbn, hb0, hb1⟩
          have hb0_eq : b0 = ai[2 * best.toNat]'(by omega) := by
            rw [hb0, List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hb1_eq : b1 = ai[2 * best.toNat + 1]'(by omega) := by
            rw [hb1, List.getElem?_eq_getElem (by omega), Option.getD_some]
          subst hb0_eq hb1_eq
          have hr_n : (((i <<< (1 : Nat)) + 1#64) + 1#64).toNat = 2 * i.toNat + 2 := by bv_omega
          c0_hstraight!
          refine wp_join_group (ts := [i64, i32, i32]) Pbest ?_ ?_
          · rintro _ ⟨best', b0', b1', ⟨⟩⟩ _ ⟨rfl, hib', hbn', hb0', hb1'⟩
            have hb0'_eq : b0' = ai[2 * best'.toNat]'(by omega) := by
              rw [hb0', List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hb1'_eq : b1' = ai[2 * best'.toNat + 1]'(by omega) := by
              rw [hb1', List.getElem?_eq_getElem (by omega), Option.getD_some]
            subst hb0'_eq hb1'_eq
            c0_hsplit
            · c0_hstraight!
              exact hBp (i, ()) _ ⟨ai, hlen_i, hpi, hsuf_i, hmi⟩
            · have hne : best'.toNat ≠ i.toNat := fun he => hc (BitVec.eq_of_toNat_eq he)
              clear hc
              have h2b' : (best' <<< (1 : Nat)).toNat = 2 * best'.toNat :=
                bv64_shl1_toNat_of (bound := 2 * n.toNat + 1) (by omega) (by omega)
              have h2b1' : ((best' <<< (1 : Nat)) + 1#64).toNat = 2 * best'.toNat + 1 :=
                bv64_shl1_add1_toNat (bound := 2 * n.toNat + 1) (by omega) (by omega)
              have hb0_arr : (best' <<< (1 : Nat)).toNat < ai.length := by omega
              have hb1_arr : ((best' <<< (1 : Nat)) + 1#64).toNat < ai.length := by omega
              c0_hstraight!
              have hp_sw := congPairsOk_swap hpi hi_lt hbn' (by omega)
              have hsuf_sw : ∀ idx, 2 * n.toNat ≤ idx →
                  ((((ai.set (2 * i.toNat) (ai[2 * best'.toNat]'(by omega))).set
                    (2 * i.toNat + 1) (ai[2 * best'.toNat + 1]'(by omega))).set
                    (2 * best'.toNat) (ai[2 * i.toNat]'(by omega))).set
                    (2 * best'.toNat + 1) (ai[2 * i.toNat + 1]'(by omega)))[idx]? = a0[idx]? := by
                intro idx hidx
                rw [swap_suffix_eq hi_lt hbn' (by omega) hidx, hsuf_i idx hidx]
              let ai' := (((ai.set (2 * i.toNat) (ai[2 * best'.toNat]'(by omega))).set
                (2 * i.toNat + 1) (ai[2 * best'.toNat + 1]'(by omega))).set
                (2 * best'.toNat) (ai[2 * i.toNat]'(by omega))).set
                (2 * best'.toNat + 1) (ai[2 * i.toNat + 1]'(by omega))
              have hm_sw : (array (t := i32) ap ai' ⋆ R) m := by
                dsimp only [ai']
                have h1_64 : (1 : BitVec 64) = 1#64 := rfl
                have hm' := hm
                simp only [h1_64] at hm'
                rw [list_getElem_congr h2i hi0_arr (by omega),
                  list_getElem_congr h2i1 hi1_arr (by omega),
                  h2i, h2i1, h2b', h2b1'] at hm'
                exact hm'
              exact hLp (n.toNat - best'.toNat) (best', ()) m (by omega)
                ⟨ai', Nat.le_refl _, hbn', by simp only [ai', List.length_set, hlen_i],
                 hp_sw, hsuf_sw, hm_sw⟩
          · intro J3 hJ3
            c0_hsplit
            · have hr_lt : 2 * i.toNat + 2 < n.toNat := by bv_omega
              clear hc
              have h2r : ((((i <<< (1 : Nat)) + 1#64) + 1#64) <<< (1 : Nat)).toNat =
                  4 * i.toNat + 4 := by bv_omega
              have h2r1 : (((((i <<< (1 : Nat)) + 1#64) + 1#64) <<< (1 : Nat)) + 1#64).toNat =
                  4 * i.toNat + 5 := by bv_omega
              have hr0_arr :
                  ((((i <<< (1 : Nat)) + 1#64) + 1#64) <<< (1 : Nat)).toNat < ai.length := by
                rw [h2r]; omega
              have hr1_arr :
                  (((((i <<< (1 : Nat)) + 1#64) + 1#64) <<< (1 : Nat)) + 1#64).toNat <
                    ai.length := by rw [h2r1]; omega
              c0_hstraight!
              refine wp_join_group (ts := [i64, i32, i32]) Pbest
                (fun _ ⟨b', b0', b1', ⟨⟩⟩ mb h => by
                  c0_hstraight!; exact hJ3 (b', b0', b1', ()) mb h) ?_
              intro J4 hJ4
              c0_hsplit
              · c0_hstraight!
                have h1_64 : (1 : BitVec 64) = 1#64 := rfl
                exact hJ4 (_, _, _, ()) _
                  ⟨rfl, by simp only [h1_64]; rw [hr_n]; omega,
                    by simp only [h1_64]; rw [hr_n]; exact hr_lt,
                    by simp only [h1_64]
                       rw [List.getElem?_eq_getElem (by rw [hr_n]; omega), Option.getD_some]
                       exact list_getElem_congr (by rw [h2r, hr_n]; omega) hr0_arr
                         (by rw [hr_n]; omega),
                    by simp only [h1_64]
                       rw [List.getElem?_eq_getElem (by rw [hr_n]; omega), Option.getD_some]
                       exact list_getElem_congr (by rw [h2r1, hr_n]; omega) hr1_arr
                         (by rw [hr_n]; omega)⟩
              · clear hc
                c0_hsplit
                · c0_hsplit
                  · c0_hstraight!
                    have h1_64 : (1 : BitVec 64) = 1#64 := rfl
                    exact hJ4 (_, _, _, ()) _
                      ⟨rfl, by simp only [h1_64]; rw [hr_n]; omega,
                        by simp only [h1_64]; rw [hr_n]; exact hr_lt,
                        by simp only [h1_64]
                           rw [List.getElem?_eq_getElem (by rw [hr_n]; omega), Option.getD_some]
                           exact list_getElem_congr (by rw [h2r, hr_n]; omega) hr0_arr
                             (by rw [hr_n]; omega),
                        by simp only [h1_64]
                           rw [List.getElem?_eq_getElem (by rw [hr_n]; omega), Option.getD_some]
                           exact list_getElem_congr (by rw [h2r1, hr_n]; omega) hr1_arr
                             (by rw [hr_n]; omega)⟩
                  · c0_hstraight!
                    exact hJ4 (best, ai[2 * best.toNat]'(by omega),
                      ai[2 * best.toNat + 1]'(by omega), ()) _ ⟨rfl, hib, hbn, hb0, hb1⟩
                · c0_hstraight!
                  exact hJ4 (best, ai[2 * best.toNat]'(by omega),
                    ai[2 * best.toNat + 1]'(by omega), ()) _ ⟨rfl, hib, hbn, hb0, hb1⟩
            · c0_hstraight!
              exact hJ3 (best, ai[2 * best.toNat]'(by omega),
                ai[2 * best.toNat + 1]'(by omega), ()) _ ⟨rfl, hib, hbn, hb0, hb1⟩
        · intro J2 hJ2
          c0_hsplit
          · c0_hstraight!
            exact hJ2 (((i <<< (1 : Nat)) + 1#64),
              ai[((i <<< (1 : Nat) + 1#64) <<< (1 : Nat)).toNat]'hc0_arr,
              ai[(((i <<< (1 : Nat)) + 1#64) <<< (1 : Nat) + 1#64).toNat]'hc1_arr, ()) _
              ⟨rfl, by rw [hc_n]; omega, by rw [hc_n]; exact hc_lt,
                by rw [List.getElem?_eq_getElem (by rw [hc_n]; omega), Option.getD_some]
                   exact list_getElem_congr h2c hc0_arr (by rw [hc_n]; omega),
                by rw [List.getElem?_eq_getElem (by rw [hc_n]; omega), Option.getD_some]
                   exact list_getElem_congr h2c1 hc1_arr (by rw [hc_n]; omega)⟩
          · clear hc
            c0_hsplit
            · c0_hsplit
              · c0_hstraight!
                exact hJ2 (((i <<< (1 : Nat)) + 1#64),
                  ai[((i <<< (1 : Nat) + 1#64) <<< (1 : Nat)).toNat]'hc0_arr,
                  ai[(((i <<< (1 : Nat)) + 1#64) <<< (1 : Nat) + 1#64).toNat]'hc1_arr, ()) _
                  ⟨rfl, by rw [hc_n]; omega, by rw [hc_n]; exact hc_lt,
                    by rw [List.getElem?_eq_getElem (by rw [hc_n]; omega), Option.getD_some]
                       exact list_getElem_congr h2c hc0_arr (by rw [hc_n]; omega),
                    by rw [List.getElem?_eq_getElem (by rw [hc_n]; omega), Option.getD_some]
                       exact list_getElem_congr h2c1 hc1_arr (by rw [hc_n]; omega)⟩
              · c0_hstraight!
                exact hJ2 (i, _, _, ()) _
                  ⟨rfl, Nat.le_refl _, hi_lt,
                    by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                       exact list_getElem_congr h2i hi0_arr (by omega),
                    by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                       simp only [show (1 : BitVec 64) = 1#64 from rfl]
                       exact list_getElem_congr h2i1 hi1_arr (by omega)⟩
            · c0_hstraight!
              exact hJ2 (i, _, _, ()) _
                ⟨rfl, Nat.le_refl _, hi_lt,
                  by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                     exact list_getElem_congr h2i hi0_arr (by omega),
                  by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                     simp only [show (1 : BitVec 64) = 1#64 from rfl]
                     exact list_getElem_congr h2i1 hi1_arr (by omega)⟩
    · exact absurd hc (by decide)

/-- Canonical `Func.wp` proof for `full_cong_sort_pairs_fid`. -/
theorem full_cong_sort_pairs_fid_wp (Γ : Env)
    (hSift : Γ.Has "full_cong_sift_pairs_fid" Spec.fullCongSiftPairsFidSpec) :
    ∀ args m Q X, Spec.fullCongSortPairsFidSpec args m Q X →
      Func.wp Γ full_cong_sort_pairs_fid_body args m Q X := by
  rintro ⟨ap, n, ⟨⟩⟩ m0 Q X ⟨P, a0, R, h2n, halen, hp0, hm0, hQ⟩
  have hn_lt : n.toNat < 2 ^ 60 := by omega
  unfold Func.wp full_cong_sort_pairs_fid_body
  c0_hsplit
  · c0_hsteps!; exact hQ a0 m0 rfl hp0 (fun _ _ => rfl) hm0
  · have hn_gt1 : 1 < n.toNat := by bv_omega
    clear hc
    c0_hstraight!
    refine wp_loop_inv (ts := [i64])
      (fun (s_i, ()) ms => ∃ as_ : List (BitVec 32),
        s_i.toNat ≤ n.toNat / 2 ∧ as_.length = a0.length ∧ CongPairsOk P as_ n.toNat ∧
        (∀ idx, 2 * n.toNat ≤ idx → as_[idx]? = a0[idx]?) ∧ (array (t := i32) ap as_ ⋆ R) ms)
      (fun (s_i, ()) _ => s_i.toNat)
      (fun J1 hJ1 => by
        c0_hsteps!
        have hshr : (n >>> BitVec.setWidth 64 1#32).toNat = n.toNat / 2 := by
          rw [show BitVec.setWidth 64 1#32 = 1#64 from by decide]
          simp [Nat.shiftRight_eq_div_pow]
        exact hJ1 (n >>> BitVec.setWidth 64 1#32, ()) m0
          ⟨a0, by rw [hshr]; exact Nat.le_refl _, rfl, hp0, fun _ _ => rfl, hm0⟩)
      (fun J1 (s_i, ()) ms ⟨as_, hsi_le, hlen_s, hps, hsuf_s, hms⟩ ih1 => ?_)
    c0_hsplit
    · have hs_pos : 0 < s_i.toNat := hc
      clear hc
      have hs1_n : (s_i - 1#64).toNat = s_i.toNat - 1 := by bv_omega
      c0_hstraight!
      c0_hcall (hSift _ _ _ _)
      exact ⟨P, as_, R, by bv_omega, by omega, by omega, hps, hms,
        fun as1 m1 hlen1 hp1 hsuf1 hm1 => by
          c0_hsteps!
          exact ih1 (s_i - 1#64, ()) m1 (by dsimp only; omega)
            ⟨as1, by omega, hlen1.trans hlen_s, hp1,
              fun idx hidx => (hsuf1 idx hidx).trans (hsuf_s idx hidx), hm1⟩⟩
    · clear hc
      c0_hstraight!
      refine wp_loop_inv (ts := [i64])
        (fun (e_i, ()) me => ∃ ae : List (BitVec 32),
          1 ≤ e_i.toNat ∧ e_i.toNat ≤ n.toNat ∧ ae.length = a0.length ∧
          CongPairsOk P ae n.toNat ∧ (∀ idx, 2 * n.toNat ≤ idx → ae[idx]? = a0[idx]?) ∧
          (array (t := i32) ap ae ⋆ R) me)
        (fun (e_i, ()) _ => e_i.toNat)
        (fun J2 hJ2 => by
          c0_hsteps!
          exact hJ2 (n, ()) ms ⟨as_, by omega, Nat.le_refl _, hlen_s, hps, hsuf_s, hms⟩)
        (fun J2 (e_i, ()) me ⟨ae, he1, hen, hlen_e, hpe, hsuf_e, hme⟩ ih2 => ?_)
      c0_hsplit
      · have he_gt1 : 1 < e_i.toNat := hc
        clear hc
        have he1_n : (e_i - 1#64).toNat = e_i.toNat - 1 := by bv_omega
        have h2e1 : ((e_i - 1#64) <<< (1 : Nat)).toNat = 2 * (e_i - 1#64).toNat :=
          bv64_shl1_toNat_of (bound := 2 * n.toNat + 1) (by omega) (by omega)
        have h2e1_1 : (((e_i - 1#64) <<< (1 : Nat)) + 1#64).toNat = 2 * (e_i - 1#64).toNat + 1 :=
          bv64_shl1_add1_toNat (bound := 2 * n.toNat + 1) (by omega) (by omega)
        have ha0_arr : (0#64 : BitVec 64).toNat < ae.length := by
          have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
        have ha1_arr : (1#64 : BitVec 64).toNat < ae.length := by
          have : (1#64 : BitVec 64).toNat = 1 := rfl; omega
        have he0_arr : ((e_i - 1#64) <<< (1 : Nat)).toNat < ae.length := by omega
        have he1_arr : (((e_i - 1#64) <<< (1 : Nat)) + 1#64).toNat < ae.length := by omega
        c0_hstraight!
        have hp_sw := congPairsOk_swap (i := 0) (j := (e_i - 1#64).toNat) hpe
          (by omega) (by omega) (by omega)
        have hsuf_sw : ∀ idx, 2 * n.toNat ≤ idx →
            ((((ae.set (2 * 0) (ae[2 * (e_i - 1#64).toNat]'(by omega))).set
              (2 * 0 + 1) (ae[2 * (e_i - 1#64).toNat + 1]'(by omega))).set
              (2 * (e_i - 1#64).toNat) (ae[2 * 0]'(by omega))).set
              (2 * (e_i - 1#64).toNat + 1) (ae[2 * 0 + 1]'(by omega)))[idx]? = a0[idx]? :=
          fun idx hidx => by
            rw [swap_suffix_eq (i := 0) (j := (e_i - 1#64).toNat) (by omega) (by omega)
              (by omega) hidx, hsuf_e idx hidx]
        let ae' := (((ae.set (2 * 0) (ae[2 * (e_i - 1#64).toNat]'(by omega))).set
          (2 * 0 + 1) (ae[2 * (e_i - 1#64).toNat + 1]'(by omega))).set
          (2 * (e_i - 1#64).toNat) (ae[2 * 0]'(by omega))).set
          (2 * (e_i - 1#64).toNat + 1) (ae[2 * 0 + 1]'(by omega))
        have hm_sw : (array (t := i32) ap ae' ⋆ R) m := by
          refine (congrArg (fun l => (array (t := i32) ap l ⋆ R) m) ?_).mp hm
          dsimp only [ae']
          have h0_n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 := by decide
          have h1_n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat = 1 := by decide
          have h1_64 : (1 : BitVec 64) = 1#64 := rfl
          simp only [h1_64, h0_n, h1_n]
          rw [List.getElem_set_ne (by rw [h2e1_1]; omega)]
          simp only [h2e1, h2e1_1]
        have hpe1 : CongPairsOk P ae' (e_i - 1#64).toNat := fun k hk => hp_sw k (by omega)
        c0_hcall (hSift _ _ _ _)
        exact ⟨P, ae', R, by bv_omega,
          by simp only [ae', List.length_set, hlen_e]; bv_omega,
          by simp only [ae', List.length_set, hlen_e]; omega, hpe1, hm_sw,
          fun ae2 m2 hlen2 hp2 hsuf2 hm2 => by
          c0_hsteps!
          exact ih2 (e_i - 1#64, ()) m2 (by dsimp only; omega)
            ⟨ae2, by bv_omega, by bv_omega,
             hlen2.trans (by simp [ae', hlen_e]),
             congPairsOk_of_prefix hp2 hp_sw hsuf2,
             fun idx hidx => (hsuf2 idx (by bv_omega)).trans (hsuf_sw idx hidx), hm2⟩⟩
      · c0_hsteps!; exact hQ ae me hlen_e hpe hsuf_e hme

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence

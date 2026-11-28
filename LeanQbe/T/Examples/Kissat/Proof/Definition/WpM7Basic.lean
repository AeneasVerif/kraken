/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Inv
public import LeanQbe.T.Examples.Kissat.Src.Definition

/-!
# Kissat M7 K6 Basic WP Proofs (`Proof.Definition.WpM7Basic`)

Flat `CanonicalEnv` `Func.wp` proofs for the `5` leaf M7 K6 micro-solver helpers of
`Src.Definition` (`0` legacy `Full*` imports; every decl `<= 450` LOC; `<= 100` cols):
- `full_k6_watch_m7_wp`
- `full_k6_assign_m7_wp`
- `full_k6_mtf_m7_wp`
- `full_k6_backtrack_m7_wp`
- `full_k6_ana_cl_m7_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics K6Tactics

@[local bv_c0]
private theorem k6_ofnat_one :
    @OfNat.ofNat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (instOfNatNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) = 1 := rfl

private theorem k6_c0 : (OfNat.ofNat 0 % 18446744073709551616 : Nat) = 0 := rfl
private theorem k6_c18 : (OfNat.ofNat 18 % 18446744073709551616 : Nat) = 18 := rfl
private theorem k6_c17 : (OfNat.ofNat 17 % 18446744073709551616 : Nat) = 17 := rfl
private theorem k6_c16 : (OfNat.ofNat 16 % 18446744073709551616 : Nat) = 16 := rfl

private theorem k6_ne_of_eq {a b x : Nat} (h1 : a = b) (h2 : b ≠ x) : a ≠ x := h1 ▸ h2

local macro "k6_ne" : tactic =>
  `(tactic| repeat rw [List.getElem?_set_ne (by
    first
    | exact @k6_ne_of_eq _ 3 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 4 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 5 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 6 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 7 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 8 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 9 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 10 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 11 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 16 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 17 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 18 _ rfl (by omega)
    | exact @k6_ne_of_eq _ 20 _ rfl (by omega)
    | c0_bound)])

private theorem k6_w0_lt {n : Nat} {cid : BitVec 32} (hc : cid.toNat < n) (hn : 2 * n ≤ 2 ^ 32) :
    (cid <<< (1 : Nat)).toNat = 2 * cid.toNat ∧ (cid <<< (1 : Nat)).toNat < 2 * n := by
  have h1 : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  exact ⟨h1, by omega⟩

private theorem k6_w1_lt {n : Nat} {cid : BitVec 32} (hc : cid.toNat < n) (hn : 2 * n ≤ 2 ^ 32) :
    ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 ∧
      ((cid <<< (1 : Nat)) ||| 1#32).toNat < 2 * n := by
  have h0 := (k6_w0_lt hc hn).1
  have h1 : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 := by
    rw [BitVec.toNat_or, h0, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      simp [Nat.mul_mod_right, show (2 * cid.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, by omega⟩

public section

/-! ## 1. `full_k6_watch_m7_wp` -/

/-- Certifies `fullK6WatchM7Spec` for `full_k6_watch_m7`. -/
theorem full_k6_watch_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6WatchM7Spec a m Q X →
      Func.wp Γ full_k6_watch_m7_body a m Q X := by
  rintro ⟨pk, cid, l0, l1, sz, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6WatchM7Spec_elim hSpec
  unfold Func.wp full_k6_watch_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) hm0
  · have hcid : cid.toNat < 256 := by c0_bound
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) hm0
    · have hl0 : l0.toNat < 128 := by c0_bound
      c0_hsplit
      · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) hm0
      · have hl1 : l1.toNat < 128 := by c0_bound
        have hw0 := k6_w0_lt hcid (by omega)
        have hw1 := k6_w1_lt hcid (by omega)
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun bf => (bf, ())) (fun _ => True)
          (fun _ bf _ => by
            c0_hsteps!
            refine hQ _ _ (by simp) (fun idx hi hor => ?_) hm
            repeat rw [List.getElem?_set_ne (by c0_bound)])
          (fun J hJ => by
            c0_hsplit
            · c0_hsteps!; exact hJ 0x80000000#32 trivial
            · c0_hsteps!; exact hJ 0#32 trivial)

/-! ## 2. `full_k6_assign_m7_wp` -/

/-- Certifies `fullK6AssignM7Spec` for `full_k6_assign_m7`. -/
theorem full_k6_assign_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6AssignM7Spec a m Q X →
      Func.wp Γ full_k6_assign_m7_body a m Q X := by
  rintro ⟨pk, lit, rsn_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6AssignM7Spec_elim hSpec
  unfold Func.wp full_k6_assign_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ => rfl) hm0
  · have hlit : lit.toNat < 128 := by c0_bound
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ => rfl) hm0
    · have hte : (kbuf[5]'(by omega)).toNat < 64 :=
        Nat.lt_of_not_le (show ¬64 ≤ (kbuf[5]'(by omega)).toNat from hc)
      obtain ⟨hv_eq, hv_lt⟩ := m7_p6_shr1_lt (n := 64) (l := lit) (by omega)
      obtain ⟨hln_eq, hln_lt⟩ := m8_bv32_xor1_lt (n := 64) lit (by omega)
      c0_hsteps_nogrp
      refine wp_join0
        (fun mj => ∃ kbufj : List (BitVec 32),
          kbufj.length = kbuf.length ∧
          (∀ idx < kbuf.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
            (idx < 608 ∨ 736 ≤ idx) → kbufj[idx]? = kbuf[idx]?) ∧
          (array (t := i32) pk kbufj ⋆ R) mj)
        (fun _ mj ⟨kbufj, hlj, hkj, hmj⟩ => by
          have hv416 : ((416#32 + (lit >>> (1 : Nat))).setWidth 64).toNat < 2912 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
            (fun nfl => (nfl, ())) (fun _ => True)
            (fun _ nfl _ => by
              c0_hsteps!
              refine hQ _ _ (by simp [hlj]) (fun idx hi h5 h6 ha hb => ?_) hm
              rw [List.getElem?_set_ne (by c0_bound)]
              exact hkj idx hi h5 h6 ha hb)
            (fun Jf hJf => by
              c0_hsplit
              · c0_hsteps!; exact hJf _ trivial
              · c0_hsteps!; exact hJf _ trivial))
        (fun J0 hJ0 => by
          c0_hsplit
          · c0_hsteps!
            refine hJ0 _ ⟨_, ?_, ?_, hm⟩
            · simp
            · intro idx hi h5 h6 ha hb; k6_ne
          · c0_hsteps!
            refine hJ0 _ ⟨_, ?_, ?_, hm⟩
            · simp
            · intro idx hi h5 h6 ha hb; k6_ne)

/-! ## 3. `full_k6_mtf_m7_wp` -/

/-- Certifies `fullK6MtfM7Spec` for `full_k6_mtf_m7`. -/
theorem full_k6_mtf_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6MtfM7Spec a m Q X →
      Func.wp Γ full_k6_mtf_m7_body a m Q X := by
  rintro ⟨pk, v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6MtfM7Spec_elim hSpec
  let nv := kbuf[0]'(by omega)
  unfold Func.wp full_k6_mtf_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ => rfl) hm0
  · have hnv : (kbuf[0]'(by omega)).toNat ≤ 64 :=
      Nat.le_of_not_lt (show ¬64 < (kbuf[0]'(by omega)).toNat from hc)
    have hnv_le : nv.toNat ≤ 64 := hnv
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ => rfl) hm0
    · have hv_lt : v.toNat < nv.toNat :=
        Nat.lt_of_not_le (show ¬nv.toNat ≤ v.toNat from hc)
      c0_hsplit
      · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ => rfl) hm0
      · let pv := kbuf[160 + v.toNat]'(by have := hnv_le; omega)
        let nxt := kbuf[224 + v.toNat]'(by have := hnv_le; omega)
        have hvv : ((608#32 + (v <<< (1 : Nat))).setWidth 64).toNat < kbuf.length := by
          have := k6_w0_lt hv_lt (by have := hnv_le; omega); c0_bound
        let finish := fun (kbuf6 : List (BitVec 32)) (m6 : Mem 64) =>
          (kbuf6.length = kbuf.length) ∧
          (∀ idx < kbuf.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
            (idx < 160 ∨ 352 ≤ idx) → kbuf6[idx]? = kbuf[idx]?) ∧
          (array (t := i32) pk kbuf6 ⋆ R) m6
        c0_hsteps_nogrp
        refine wp_join0 (fun m1 => ∃ kb1, finish kb1 m1) ?_ ?_
        · intro _ m1 ⟨kb1, hl1, hk1, hm1⟩
          c0_hsteps_nogrp
          refine wp_join0 (fun m2 => ∃ kb2, finish kb2 m2) ?_ ?_
          · intro _ m2 ⟨kb2, hl2, hk2, hm2⟩
            c0_hsteps_nogrp
            refine wp_join0 (fun m3 => ∃ kb3, finish kb3 m3) ?_ ?_
            · intro _ m3 ⟨kb3, hl3, hk3, hm3⟩
              c0_hsteps_nogrp
              refine wp_join0 (fun m4 => ∃ kb4, finish kb4 m4) ?_ ?_
              · intro _ m4 ⟨kb4, hl4, hk4, hm4⟩
                c0_hsteps_nogrp
                refine wp_join0 (fun m5 => ∃ kb5, finish kb5 m5) ?_ ?_
                · intro _ m5 ⟨kb5, hl5, hk5, hm5⟩
                  c0_hsteps_nogrp
                  refine wp_join0 (fun m6 => ∃ kb6, finish kb6 m6) ?_ ?_
                  · intro _ m6 ⟨kb6, hl6, hk6, hm6⟩
                    c0_hsteps!
                    exact hQ kb6 m6 hl6 hk6 hm6
                  · intro J6 hJ6
                    c0_hsplit
                    · c0_hsteps!
                      refine hJ6 m ⟨_, ?_, ?_, hm⟩
                      · simp [hl5]
                      · intro idx hi h8 h9 h10 h11 ha
                        k6_ne; exact hk5 idx hi h8 h9 h10 h11 ha
                    · c0_hsteps!; exact hJ6 m5 ⟨kb5, hl5, hk5, hm5⟩
                · intro J5 hJ5
                  c0_hsplit
                  · c0_hsteps!
                    refine hJ5 m ⟨_, ?_, ?_, hm⟩
                    · simp [hl4]
                    · intro idx hi h8 h9 h10 h11 ha
                      k6_ne; exact hk4 idx hi h8 h9 h10 h11 ha
                  · c0_hsteps!; exact hJ5 m4 ⟨kb4, hl4, hk4, hm4⟩
              · intro J4 hJ4
                c0_hsplit
                · c0_hsteps!
                  refine hJ4 m ⟨_, ?_, ?_, hm⟩
                  · simp [hl3]
                  · intro idx hi h8 h9 h10 h11 ha
                    k6_ne; exact hk3 idx hi h8 h9 h10 h11 ha
                · c0_hsteps!
                  refine hJ4 m ⟨_, ?_, ?_, hm⟩
                  · simp [hl3]
                  · intro idx hi h8 h9 h10 h11 ha
                    k6_ne; exact hk3 idx hi h8 h9 h10 h11 ha
            · intro J3 hJ3
              c0_hsplit
              · c0_hsteps!
                refine hJ3 m ⟨_, ?_, ?_, hm⟩
                · simp [hl2]
                · intro idx hi h8 h9 h10 h11 ha
                  k6_ne; exact hk2 idx hi h8 h9 h10 h11 ha
              · have hnxt : nxt.toNat < nv.toNat := by
                  have h1 : (224 + v.toNat) % 4294967296 = 224 + v.toNat := by
                    have := hnv_le; omega
                  exact Nat.lt_of_not_le (by simpa [nxt, k6_c0, h1] using hc)
                c0_hsteps!
                refine hJ3 m ⟨_, ?_, ?_, hm⟩
                · simp [hl2]
                · intro idx hi h8 h9 h10 h11 ha
                  k6_ne; exact hk2 idx hi h8 h9 h10 h11 ha
          · intro J2 hJ2
            c0_hsplit
            · c0_hsteps!
              refine hJ2 m ⟨_, ?_, ?_, hm⟩
              · simp [hl1]
              · intro idx hi h8 h9 h10 h11 ha
                k6_ne; exact hk1 idx hi h8 h9 h10 h11 ha
            · have hpv : pv.toNat < nv.toNat := by
                have h1 : (160 + v.toNat) % 4294967296 = 160 + v.toNat := by
                  have := hnv_le; omega
                exact Nat.lt_of_not_le (by simpa [pv, k6_c0, h1] using hc)
              c0_hsteps!
              refine hJ2 m ⟨_, ?_, ?_, hm⟩
              · simp [hl1]
              · intro idx hi h8 h9 h10 h11 ha
                k6_ne; exact hk1 idx hi h8 h9 h10 h11 ha
        · intro J1 hJ1
          c0_hsplit
          · c0_hsplit
            · c0_hsteps! <;> first
                | exact hJ1 m0 ⟨kbuf, rfl, fun _ _ _ _ _ _ _ => rfl, hm0⟩
                | (refine hJ1 m ⟨_, ?_, ?_, hm⟩
                   · simp
                   · intro idx hi h8 h9 h10 h11 ha; k6_ne)
            · c0_hsteps!; exact hJ1 m0 ⟨kbuf, rfl, fun _ _ _ _ _ _ _ => rfl, hm0⟩
          · c0_hsteps!; exact hJ1 m0 ⟨kbuf, rfl, fun _ _ _ _ _ _ _ => rfl, hm0⟩

/-! ## 4. `full_k6_backtrack_m7_wp` -/

/-- Certifies `fullK6BacktrackM7Spec` for `full_k6_backtrack_m7`. -/
theorem full_k6_backtrack_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6BacktrackM7Spec a m Q X →
      Func.wp Γ full_k6_backtrack_m7_body a m Q X := by
  rintro ⟨pk, target_lvl, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hlen, hm0, hQ⟩ := fullK6BacktrackM7Spec_elim hSpec
  let nv := kbuf[0]'(by omega)
  unfold Func.wp full_k6_backtrack_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ _ => rfl) hm0
  · have hnv : nv.toNat ≤ 64 :=
      Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
      (fun te => (te, ())) (fun te => te.toNat ≤ 64)
      (fun _ te hte => by
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun bs => (bs, ())) (fun _ => True)
          (fun _ bs _ => by
            let keep := fun (kb : List (BitVec 32)) =>
              kb.length = kbuf.length ∧
              (∀ idx < kbuf.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
                (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kb[idx]? = kbuf[idx]?)
            c0_hsteps_nogrp
            refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32, i32])
              (fun (te_b, _bs_b, ()) mb => ∃ kbb, keep kbb ∧ te_b.toNat ≤ 64 ∧
                (array (t := i32) pk kbb ⋆ R) mb)
              (fun rem (te_l, bs_l, ()) ml => ∃ kbl, keep kbl ∧ te_l.toNat ≤ 64 ∧
                rem = te_l.toNat ∧ (array (t := i32) pk kbl ⋆ R) ml)
              ?_ ?_ ?_
            · rintro _ ⟨te_b, _bs_b, ⟨⟩⟩ mb ⟨kbb, hkb_k, hte_b, hmb⟩
              have hkb_l := hkb_k.1
              c0_hsteps_nogrp
              refine wp_join0 (fun mj => ∃ kbj, keep kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
                (fun _ mj ⟨kbj, hkj_k, hmj⟩ => by
                  have hkj_l := hkj_k.1
                  c0_hsteps!
                  refine hQ _ _ (by simp [hkj_l]) (fun idx hi h3 h4 h5 h6 h10 ha hb => ?_) hm
                  k6_ne; exact hkj_k.2 idx hi h3 h4 h5 h6 h10 ha hb)
                (fun Jp hJp => by
                  c0_hsplit
                  · c0_hsteps!
                    refine hJp _ ⟨_, ⟨by simp [hkb_l], fun idx hi h3 h4 h5 h6 h10 ha hb => ?_⟩, hm⟩
                    k6_ne; exact hkb_k.2 idx hi h3 h4 h5 h6 h10 ha hb
                  · c0_hsteps!
                    refine hJp _ ⟨_, ⟨by simp [hkb_l], fun idx hi h3 h4 h5 h6 h10 ha hb => ?_⟩, hm⟩
                    k6_ne; exact hkb_k.2 idx hi h3 h4 h5 h6 h10 ha hb)
            · rintro B L rem ⟨te_l, bs_l, ⟨⟩⟩ ml hB hL ⟨kbl, hkl_k, hte_l, rfl, hml⟩
              have hkl_l := hkl_k.1
              have hkb_nv : kbl[0]'(by omega) = nv := by
                have := hkl_k.2 0 (by omega) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (Or.inl (by decide)) (Or.inl (by decide))
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by omega)] at this
                exact Option.some.inj this
              c0_hsplit
              · have hte_pos : 0 < te_l.toNat := by simpa using hc
                clear hc
                have hte1_lt : (te_l - 1#32).toNat < 64 := by
                  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                  have := hte_pos; have := hte_l; omega
                have hsub352 : (352#32 + te_l - 1#32).toNat = 351 + te_l.toNat := by
                  rw [BitVec.toNat_sub, BitVec.toNat_add]
                  simp only [BitVec.toNat_ofNat]; have := hte_pos; have := hte_l; omega
                c0_hsplit
                · c0_hsteps!; exact hB (te_l, bs_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
                · have hlit_idx : (BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat =
                      (4294967295 + (352 + te_l.toNat)) % 4294967296 := by
                    rw [BitVec.toNat_setWidth, hsub352]; have := hte_pos; have := hte_l; omega
                  have hlit_len1 :
                      (BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat < kbl.length := by
                    rw [BitVec.toNat_setWidth, hsub352]; have := hte_pos; have := hte_l; omega
                  have hlit_len2 : (4294967295 + (352 + te_l.toNat)) % 4294967296 < kbl.length := by
                    have := hte_pos; have := hte_l; omega
                  have hlit_ast :
                      (kbl[(BitVec.setWidth 64
                        (352#32 + te_l - 1#32)).toNat]'hlit_len1).toNat < 2 * nv.toNat := by
                    have htw : (kbuf[0].toNat * 2) % 4294967296 = 2 * nv.toNat := by
                      change (nv.toNat * 2) % 4294967296 = 2 * nv.toNat
                      have := hnv; omega
                    rw [m8_k6_get_congr hlit_idx hlit_len1 hlit_len2]
                    simpa [htw] using hc
                  clear hc
                  have hlit128 :
                      (kbl[(BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat]'hlit_len1).toNat <
                        128 := by
                    have := hnv; omega
                  let lit := kbl[(BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat]'hlit_len1
                  obtain ⟨hv_eq, hv_lt⟩ := m7_p6_shr1_lt (n := 64) (l := lit) (by omega)
                  obtain ⟨hln_eq, hln_lt⟩ := m8_bv32_xor1_lt (n := 64) lit (by omega)
                  have hln_bd :
                      (BitVec.setWidth 64 (608#32 + (lit ^^^ 1#32))).toNat < kbl.length := by
                    have := hln_lt; have := hkl_l; c0_bound
                  have hv_bd1 :
                      (BitVec.setWidth 64 (32#32 + (lit >>> (1 : Nat)))).toNat < kbl.length := by
                    have := hv_lt; have := hkl_l; c0_bound
                  have hv_bd2 :
                      (BitVec.setWidth 64 (96#32 + (lit >>> (1 : Nat)))).toNat < kbl.length := by
                    have := hv_lt; have := hkl_l; c0_bound
                  c0_hsplit
                  · c0_hsteps!; exact hB (te_l, bs_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
                  · c0_hsteps_nogrp
                    refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32))
                      (fun x => x.1)
                      (fun x mj => keep x.2 ∧ (array (t := i32) pk x.2 ⋆ R) mj) ?_ ?_
                    · rintro _ ⟨bs', kb'⟩ mj ⟨hk', hmj⟩
                      c0_hsteps!
                      have hsub_lt : (te_l - 1#32).toNat < te_l.toNat := by
                        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                        have := hte_pos; have := hte_l; omega
                      exact hL (te_l - 1#32).toNat (te_l - 1#32, bs', ()) mj hsub_lt
                        ⟨kb', hk', by omega, rfl, hmj⟩
                    · intro Js hJs
                      have hln_raw_lt : (BitVec.toNat
                          kbl[(4294967296 - 1 + (352 + BitVec.toNat te_l)) % 4294967296] ^^^ 1) <
                          128 := by
                        have heq352 :
                            (4294967296 - 1 + (352 + BitVec.toNat te_l)) % 4294967296 =
                            (BitVec.setWidth 64 (352#32 + te_l - 1#32)).toNat := by
                          rw [hlit_idx]
                        have hlt : BitVec.toNat
                            kbl[(4294967296 - 1 + (352 + BitVec.toNat te_l)) % 4294967296] <
                            128 := by
                          rw [m8_k6_get_congr heq352 hlit_len2 hlit_len1]
                          exact hlit128
                        exact Nat.xor_lt_two_pow (n := 7) hlt (by decide)
                      c0_hsplit
                      · c0_hsteps!
                        refine hJs (_, _) m ⟨⟨?_, ?_⟩, hm⟩
                        · simp [hkl_l]
                        · intro idx hi h3 h4 h5 h6 h10 ha hb
                          have := hln_raw_lt; k6_ne
                          exact hkl_k.2 idx hi h3 h4 h5 h6 h10 ha hb
                      · c0_hsteps!
                        refine hJs (bs_l, _) m ⟨⟨?_, ?_⟩, hm⟩
                        · simp [hkl_l]
                        · intro idx hi h3 h4 h5 h6 h10 ha hb
                          have := hln_raw_lt; k6_ne
                          exact hkl_k.2 idx hi h3 h4 h5 h6 h10 ha hb
              · c0_hsteps!; exact hB (te_l, bs_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
            · intro _ L _ hL; c0_hsteps!
              exact hL te.toNat (te, bs, ()) m0
                ⟨kbuf, ⟨rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩, hte, rfl, hm0⟩)
          (fun Jbs hJbs => by
            c0_hsplit
            · c0_hsteps!; exact hJbs _ trivial
            · c0_hsteps!; exact hJbs 0#32 trivial))
      (fun Jte hJte => by
        c0_hsplit
        · c0_hsteps!; exact hJte 64#32 (by decide)
        · c0_hsteps!; exact hJte _ (by c0_bound))

/-! ## 5. `full_k6_ana_cl_m7_wp` -/

/-- Certifies `fullK6AnaClM7Spec` for `full_k6_ana_cl_m7`. -/
theorem full_k6_ana_cl_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6AnaClM7Spec a m Q X →
      Func.wp Γ full_k6_ana_cl_m7_body a m Q X := by
  rintro ⟨pk, cid, skip_v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6AnaClM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let nc := kbuf[1]'(by omega)
  let nv := kbuf[0]'(by omega)
  let acap := kbuf[15]'(by omega)
  unfold Func.wp full_k6_ana_cl_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
  · have hcid : cid.toNat < nc.toNat :=
      Nat.lt_of_not_le (show ¬nc.toNat ≤ cid.toNat from hc)
    clear hc
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
    · have hnc_le : nc.toNat ≤ 256 :=
        Nat.le_of_not_lt (show ¬256 < nc.toNat from hc)
      clear hc
      c0_hsplit
      · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
      · have hnv_le : nv.toNat ≤ 64 :=
          Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
        clear hc
        let off := kbuf[1888 + cid.toNat]'(by omega)
        let cm := kbuf[2144 + cid.toNat]'(by omega)
        let sz := cm &&& 0xFFFF#32
        have hcl_ok := hok0.clause_ok (by rw [m8_k6_get_eq (by omega)]; exact hcid)
        rw [m8_k6_get_eq (by omega : 1888 + cid.toNat < kbuf.length),
          m8_k6_get_eq (by omega : 2144 + cid.toNat < kbuf.length),
          m8_k6_get_eq (by omega : 15 < kbuf.length)] at hcl_ok
        have hoff_sz : off.toNat + sz.toNat ≤ acap.toNat := hcl_ok.1
        have hlt28 := hok0.length_lt
        have hac_le := hok0.length_ge
        rw [m8_k6_get_eq (by omega : 15 < kbuf.length)] at hac_le
        change 2912 + acap.toNat ≤ kbuf.length at hac_le
        have hoff_sz_nowarp : off.toNat + sz.toNat < 2 ^ 32 := by omega
        c0_hsplit
        · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ _ _ _ _ _ => rfl) hm0
        · clear hc
          let keep := fun (kb : List (BitVec 32)) =>
            kb.length = kbuf.length ∧
            (∀ idx < kbuf.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
              (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) →
              kb[idx]? = kbuf[idx]?)
          refine wp_join0 (fun m1 => ∃ kb1, keep kb1 ∧ (array (t := i32) pk kb1 ⋆ R) m1) ?_ ?_
          · intro _ m1 ⟨kb1, hk1, hm1⟩
            have hkb1_l := hk1.1
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32])
              (fun rem (i, ()) mi => ∃ kbi, keep kbi ∧ i.toNat ≤ sz.toNat ∧
                rem = sz.toNat - i.toNat ∧ (array (t := i32) pk kbi ⋆ R) mi)
              ?_ ?_
            · rintro L rem ⟨i, ⟨⟩⟩ mi hL ⟨kbi, hki, hi_le, rfl, hmi⟩
              have hki_l := hki.1
              c0_hsplit
              · have hi_lt : i.toNat < sz.toNat := by
                  have h1 : (2144 + cid.toNat) % 4294967296 = 2144 + cid.toNat := by
                    have := hcid; have := hnc_le; omega
                  have hsz_nat : sz.toNat = cm.toNat % 65536 := by
                    change (cm &&& 0xFFFF#32).toNat = cm.toNat % 65536
                    rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
                      Nat.and_two_pow_sub_one_eq_mod]
                  rw [hsz_nat]; simpa [cm, h1] using hc
                clear hc
                have har_bd : (2912 + off.toNat + i.toNat) < kbi.length := by
                  have := hac_le; have := hoff_sz; have := hki_l; have := hi_lt; omega
                have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
                  have := hlt28; have := hac_le; have := hoff_sz; have := hi_lt; c0_bound
                have h1888_idx : (BitVec.setWidth 64 (1888#32 + cid)).toNat = 1888 + cid.toNat := by
                  have := hcid; have := hnc_le; c0_bound
                have har_c0_bd : (BitVec.setWidth 64
                    (2912#32 + kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                      rw [h1888_idx]; have := hcid; have := hnc_le; omega) + i)).toNat <
                    kbi.length := by
                  rw [m8_k6_get_congr h1888_idx _ _]
                  change (BitVec.setWidth 64 (2912#32 + off + i)).toNat < kbi.length
                  have := har_bd; have := hlt28; have := hki_l; c0_bound
                c0_hsteps_nogrp
                refine wp_join0 (fun mj => ∃ kbj, keep kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
                  ?_ ?_
                · intro _ mj ⟨kbj, hkj, hmj⟩
                  c0_hsteps!
                  exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj
                    (by have := hlt28; have := hac_le; have := hoff_sz; have := hi_lt; omega)
                    ⟨kbj, hkj, by omega, rfl, hmj⟩
                · intro J349 hJ349
                  let l := kbi[2912 + off.toNat + i.toNat]'(by omega)
                  let v := l >>> (1 : Nat)
                  have h1888_mod :
                      (1888 + cid.toNat) % 4294967296 = 1888 + cid.toNat := by
                    have := hcid; have := hnc_le; omega
                  have h2912_mod :
                      (2912 + off.toNat + i.toNat) % 4294967296 =
                      2912 + off.toNat + i.toNat := by
                    have := hoff_sz_nowarp; have := hi_lt; omega
                  have h1888_bd : (1888 + cid.toNat) % 4294967296 < kbuf.length := by
                    rw [h1888_mod]; have := hcid; have := hnc_le; omega
                  have h2912_c0_idx : (BitVec.setWidth 64
                      (2912#32 + kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                        rw [h1888_idx]; have := hcid; have := hnc_le; omega) + i)).toNat =
                      2912 + off.toNat + i.toNat := by
                    rw [m8_k6_get_congr h1888_idx _ _]
                    change (BitVec.setWidth 64 (2912#32 + off + i)).toNat =
                      2912 + off.toNat + i.toNat
                    have := har_bd; have := hlt28; have := hki_l; c0_bound
                  have hl_c0_eq : kbi[(BitVec.setWidth 64
                      (2912#32 + kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                        rw [h1888_idx]; have := hcid
                        have := hnc_le; omega) + i)).toNat]'har_c0_bd =
                      l := m8_k6_get_congr h2912_c0_idx har_c0_bd har_bd
                  c0_hsplit
                  · have hget1 : kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd = off :=
                      m8_k6_get_congr h1888_mod h1888_bd _
                    have h2912_raw_idx : (2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296 = 2912 + off.toNat + i.toNat := by
                      rw [hget1]; exact h2912_mod
                    have h2912_bd : (2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296 < kbi.length := by
                      rw [h2912_raw_idx]; exact har_bd
                    have hget2 : kbi[(2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296]'h2912_bd = l :=
                      m8_k6_get_congr h2912_raw_idx h2912_bd har_bd
                    have hv_div : v.toNat = l.toNat / 2 := by
                      dsimp only [v]; rw [BitVec.toNat_ushiftRight]
                      simp [Nat.shiftRight_eq_div_pow]
                    have hv_lt : v.toNat < nv.toNat := by
                      refine Nat.lt_of_not_le (show ¬nv.toNat ≤ v.toNat from ?_)
                      rw [hv_div]
                      simpa [nv, k6_c0, l, hget2] using hc
                    have hv_raw64 : (kbi[(2912 +
                        (kbuf[(1888 + cid.toNat) % 4294967296]'h1888_bd).toNat +
                        i.toNat) % 4294967296]'h2912_bd).toNat / 2 < 64 := by
                      rw [hget2, ← hv_div]; have := hv_lt; have := hnv_le; omega
                    clear hc
                    have hv416_c0 : (BitVec.setWidth 64 (416#32 +
                        (kbi[(BitVec.setWidth 64 (2912#32 +
                          kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                            rw [h1888_idx]; have := hcid; have := hnc_le; omega) +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change (BitVec.setWidth 64 (416#32 + v)).toNat < kbi.length
                      have := hv_lt; have := hnv_le; have := hki_l; have := hlen; c0_bound
                    have hv32_c0 : (BitVec.setWidth 64 (32#32 +
                        (kbi[(BitVec.setWidth 64 (2912#32 +
                          kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                            rw [h1888_idx]; have := hcid; have := hnc_le; omega) +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change (BitVec.setWidth 64 (32#32 + v)).toNat < kbi.length
                      have := hv_lt; have := hnv_le; have := hki_l; have := hlen; c0_bound
                    have hv96_c0 : (BitVec.setWidth 64 (96#32 +
                        (kbi[(BitVec.setWidth 64 (2912#32 +
                          kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                            rw [h1888_idx]; have := hcid; have := hnc_le; omega) +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change (BitVec.setWidth 64 (96#32 + v)).toNat < kbi.length
                      have := hv_lt; have := hnv_le; have := hki_l; have := hlen; c0_bound
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join0
                          (fun m361 => ∃ kb361, keep kb361 ∧ (array (t := i32) pk kb361 ⋆ R) m361)
                          ?_ ?_
                        · intro _ m361 ⟨kb361, hk361, hm361⟩
                          have hk361_l := hk361.1
                          c0_hsteps_nogrp
                          refine wp_join0
                            (fun m361b => ∃ kb361b, keep kb361b ∧
                              (array (t := i32) pk kb361b ⋆ R) m361b)
                            ?_ ?_
                          · intro _ m361b ⟨kb361b, hk361b, hm361b⟩
                            c0_hsteps!; exact hJ349 m361b ⟨kb361b, hk361b, hm361b⟩
                          · intro J361b hJ361b
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join0
                                (fun m367 => ∃ kb367, keep kb367 ∧
                                  (array (t := i32) pk kb367 ⋆ R) m367)
                                ?_ ?_
                              · intro _ m367 ⟨kb367, hk367, hm367⟩
                                c0_hsteps!; exact hJ361b m367 ⟨kb367, hk367, hm367⟩
                              · intro J367 hJ367
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join0
                                    (fun m367b => ∃ kb367b, keep kb367b ∧
                                      (array (t := i32) pk kb367b ⋆ R) m367b)
                                    ?_ ?_
                                  · intro _ m367b ⟨kb367b, hk367b, hm367b⟩
                                    c0_hsteps!; exact hJ367 m367b ⟨kb367b, hk367b, hm367b⟩
                                  · intro J367b hJ367b
                                    c0_hsplit
                                    · have hnr : (kb361[18]'(by omega)).toNat < 128 := by
                                        simpa [Nat.reducePow, k6_c18] using hc
                                      have h18_eq : (BitVec.ofNat 64 18).toNat = 18 := rfl
                                      have h2784_c0 : (BitVec.setWidth 64 ((2784 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 18).toNat]'(by
                                            rw [h18_eq]; omega))).toNat < kb361.length := by
                                        rw [m8_k6_get_congr (xs := kb361) h18_eq _ (by omega)]
                                        have := hnr; have := hlen; c0_bound
                                      have h2784_bd : (BitVec.setWidth 64 ((2784 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 18).toNat]'(by
                                            rw [h18_eq]; omega))).toNat =
                                          2784 + (kb361[18]'(by omega)).toNat := by
                                        rw [m8_k6_get_congr (xs := kb361) h18_eq _ (by omega)]
                                        have := hnr; c0_bound
                                      c0_hsteps!
                                      refine hJ367b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, List.length_set, hk361_l]
                                      · intro idx hidx h16 h17 h18 h20 ha hb
                                        rw [List.getElem?_set_ne (by change 18 ≠ idx; omega),
                                          List.getElem?_set_ne (by rw [h2784_bd]; omega)]
                                        exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                    · c0_hsteps!
                                      refine hJ367b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, hk361_l]
                                      · intro idx hidx h16 h17 h18 h20 ha hb
                                        rw [List.getElem?_set_ne (by change 18 ≠ idx; omega)]
                                        exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                · c0_hsteps!; exact hJ367 m361 ⟨kb361, hk361, hm361⟩
                            · refine wp_join0
                                (fun m385 => ∃ kb385, keep kb385 ∧
                                  (array (t := i32) pk kb385 ⋆ R) m385)
                                ?_ ?_
                              · intro _ m385 ⟨kb385, hk385, hm385⟩
                                c0_hsteps!; exact hJ361b m385 ⟨kb385, hk385, hm385⟩
                              · intro J385 hJ385
                                c0_hsplit
                                · c0_hsteps!
                                  refine hJ385 m ⟨_, ⟨?_, ?_⟩, hm⟩
                                  · rw [List.length_set, hk361_l]
                                  · intro idx hidx h16 h17 h18 h20 ha hb
                                    rw [List.getElem?_set_ne (by change 20 ≠ idx; omega)]
                                    exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                · c0_hsteps_nogrp
                                  refine wp_join0
                                    (fun m385b => ∃ kb385b, keep kb385b ∧
                                      (array (t := i32) pk kb385b ⋆ R) m385b)
                                    ?_ ?_
                                  · intro _ m385b ⟨kb385b, hk385b, hm385b⟩
                                    c0_hsteps!; exact hJ385 m385b ⟨kb385b, hk385b, hm385b⟩
                                  · intro J385b hJ385b
                                    c0_hsplit
                                    · have hnkl : (kb361[17]'(by omega)).toNat < 64 := by
                                        simpa [Nat.reducePow, k6_c17] using hc
                                      have h17_eq : (BitVec.ofNat 64 17).toNat = 17 := rfl
                                      have h544_c0 : (BitVec.setWidth 64 ((544 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 17).toNat]'(by
                                            rw [h17_eq]; omega))).toNat < kb361.length := by
                                        rw [m8_k6_get_congr (xs := kb361) h17_eq _ (by omega)]
                                        have := hnkl; have := hlen; c0_bound
                                      have h544_bd : (BitVec.setWidth 64 ((544 : BitVec 32) +
                                          kb361[(BitVec.ofNat 64 17).toNat]'(by
                                            rw [h17_eq]; omega))).toNat =
                                          544 + (kb361[17]'(by omega)).toNat := by
                                        rw [m8_k6_get_congr (xs := kb361) h17_eq _ (by omega)]
                                        have := hnkl; c0_bound
                                      c0_hsteps!
                                      refine hJ385b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, List.length_set, hk361_l]
                                      · intro idx hidx h16 h17 h18 h20 ha hb
                                        rw [List.getElem?_set_ne (by change 17 ≠ idx; omega),
                                          List.getElem?_set_ne (by rw [h544_bd]; omega)]
                                        exact hk361.2 idx hidx h16 h17 h18 h20 ha hb
                                    · c0_hsteps!; exact hJ385b m361 ⟨kb361, hk361, hm361⟩
                        · intro J361 hJ361
                          have h416_c0_idx : (BitVec.setWidth 64 ((416 : BitVec 32) +
                              (kbi[(BitVec.setWidth 64 ((2912 : BitVec 32) +
                                kbuf[(BitVec.setWidth 64 ((1888 : BitVec 32) + cid)).toNat]'(by
                                  rw [show (BitVec.setWidth 64 ((1888 : BitVec 32) + cid)).toNat =
                                    1888 + cid.toNat from h1888_idx]; omega) +
                                i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat =
                              416 + v.toNat := by
                            change (BitVec.setWidth 64 (416#32 +
                              (kbi[(BitVec.setWidth 64 (2912#32 +
                                kbuf[(BitVec.setWidth 64 (1888#32 + cid)).toNat]'(by
                                  rw [h1888_idx]; omega) +
                                i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat = 416 + v.toNat
                            rw [hl_c0_eq]
                            have := hv_lt; have := hnv_le; c0_bound
                          have hm1_eq := m8_k6_set_congr (xs := kbi) h416_c0_idx
                            (congrArg (· ||| (2 : BitVec 32))
                              (m8_k6_get_congr (xs := kbi) h416_c0_idx hv416_c0
                                (by have := hnv_le; omega)))
                          rw [hm1_eq] at hm
                          have hkbi1_ex : ∃ kbi1 : List (BitVec 32), kbi1.length = kbuf.length ∧
                              keep kbi1 ∧ (array (t := i32) pk kbi1 ⋆ R) m :=
                            ⟨kbi.set (416 + v.toNat)
                                ((kbi[416 + v.toNat]'(by have := hnv_le; omega)) ||| 2#32),
                              by simp [hki_l],
                              ⟨by simp [hki_l], fun idx hidx h16 h17 h18 h20 ha hb => by
                                rw [List.getElem?_set_ne (by have := hv_lt; have := hnv_le; omega)]
                                exact hki.2 idx hidx h16 h17 h18 h20 ha hb⟩, hm⟩
                          obtain ⟨kbi1, hk1_l, hki1, hm_n⟩ := hkbi1_ex
                          clear hm hm1_eq
                          try clear hv416_c0 h416_c0_idx hv32_c0 hv96_c0
                          try clear h2912_bd h1888_bd hget2 h2912_raw_idx hget1 h1888_mod h2912_mod
                          try clear hl_c0_eq h2912_c0_idx har_c0_bd hv_raw64 hv_div
                          try clear hv_lt hki hki_l hmi
                          have hm := hm_n; clear hm_n
                          have hkbi1_ge : 2912 ≤ kbi1.length := by rw [hk1_l]; exact hlen
                          c0_hsplit
                          · have hna : (kbi1[16]'(by omega)).toNat < 64 := by
                              simpa [Nat.reducePow, k6_c16] using hc
                            have h16_eq_c0 : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 16)).toNat = 16 := rfl
                            have h16_bd_c0 : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 16)).toNat < kbi1.length := by
                              rw [h16_eq_c0]; omega
                            have hk16_c0 : kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 16)).toNat]'h16_bd_c0 = kbi1[16]'(by omega) :=
                              m8_k6_get_congr (xs := kbi1) h16_eq_c0 h16_bd_c0 (by omega)
                            have h480_c0 : (BitVec.setWidth 64 ((480 : BitVec 32) +
                                kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 16)).toNat]'h16_bd_c0)).toNat < kbi1.length := by
                              rw [hk16_c0]; have := hna; c0_bound
                            have h480_bd : (BitVec.setWidth 64 ((480 : BitVec 32) +
                                kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 16)).toNat]'h16_bd_c0)).toNat =
                                480 + (kbi1[16]'(by omega)).toNat := by
                              rw [hk16_c0]; have := hna; c0_bound
                            c0_hsteps!
                            refine hJ361 m ⟨_, ⟨?_, ?_⟩, hm⟩
                            · rw [List.length_set, List.length_set, hk1_l]
                            · intro idx hidx h16 h17 h18 h20 ha hb
                              rw [List.getElem?_set_ne (by change 16 ≠ idx; omega),
                                List.getElem?_set_ne (by rw [h480_bd]; omega)]
                              exact hki1.2 idx hidx h16 h17 h18 h20 ha hb
                          · c0_hsteps!; exact hJ361 m ⟨kbi1, hki1, hm⟩
                      · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
                    · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
                  · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
              · c0_hsteps!; exact hQ kbi mi hki.1 hki.2 hmi
            · intro L hL; c0_hsteps!
              exact hL sz.toNat (0#32, ()) m1 ⟨kb1, hk1, Nat.zero_le _, by simp, hm1⟩
          · intro J343 hJ343
            c0_hsplit
            · have hnr : (kbuf[18]'(by omega)).toNat < 128 := by simpa [k6_c18] using hc
              have h18_eq : (BitVec.ofNat 64 18).toNat = 18 := rfl
              have h2784_bd : (BitVec.setWidth 64 ((2784 : BitVec 32) +
                  kbuf[(BitVec.ofNat 64 18).toNat]'(by rw [h18_eq]; omega))).toNat =
                  2784 + (kbuf[18]'(by omega)).toNat := by
                rw [m8_k6_get_congr (xs := kbuf) h18_eq _ (by omega)]
                have := hnr; c0_bound
              c0_hsteps!
              refine hJ343 m ⟨_, ⟨?_, ?_⟩, hm⟩
              · rw [List.length_set, List.length_set]
              · intro idx hidx h16 h17 h18 h20 ha hb
                rw [List.getElem?_set_ne (by change 18 ≠ idx; omega),
                  List.getElem?_set_ne (by rw [h2784_bd]; omega)]
            · c0_hsteps!
              refine hJ343 m ⟨_, ⟨?_, ?_⟩, hm⟩
              · rw [List.length_set]
              · intro idx hidx h16 h17 h18 h20 ha hb
                rw [List.getElem?_set_ne (by change 18 ≠ idx; omega)]

end

end LeanQbe.T.Examples.Kissat.Proof.Definition

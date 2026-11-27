/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpHelpers

/-!
# Kissat Gates WP Proofs — M8 Equivalence (`find_equiv_m8`)

`CanonicalEnv`-clean `Func.wp` proof for `full_bve_find_equiv_m8`
(`0` legacy `Full*` imports; every decl `<= 450` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Gates
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

public section

/-- Canonical `Func.wp` proof for `full_bve_find_equiv_m8`. -/
theorem full_bve_find_equiv_m8_wp (Γ : Env) :
    ∀ a m Q X, m8BveFindEquivSpec a m Q X →
      Func.wp Γ full_bve_find_equiv_m8_body a m Q X := by
  rintro ⟨h, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hnp, hnn, hp_ok, hn_ok, hm0, hQ⟩ :=
    m8BveFindEquivSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  unfold Func.wp full_bve_find_equiv_m8_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32])
    (fun rem1 (bin_p, i, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧ i.toNat ≤ np.toNat ∧ bin_p.toNat ≤ i.toNat ∧
      rem1 = np.toNat - i.toNat ∧
      (bin_p = 0#32 → ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8) ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        ∃ u < i.toNat,
          let wu := s0.scratch.scratch_buf[u]?.getD 0#32
          (wu &&& 0x80000000#32) ≠ 0#32 ∧ x = (wu &&& 0x7FFFFFFF#32).toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro L1 rem1 ⟨bin_p, i, ⟨⟩⟩ m1 hL1 ⟨lm1, hlm1, hi_le, hbp_le, rfl, hbp0, hmark1, hm1⟩
    c0_hsplit
    · have hi_lt : i.toNat < np.toNat := hc
      have hi_sc : (i.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; omega
      let wp0 := s0.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sc
      have hwp_get : s0.scratch.scratch_buf[i.toNat]?.getD 0#32 = wp0 := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact getElem_congr (zext32_toNat i) _ _
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
        (fun x => (x.1, ()))
        (fun x mj => x.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
          (x.1 = 0#32 → ∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 = 0#8) ∧
          (∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 ≠ 0#8 →
            ∃ u < i.toNat + 1,
              let wu := s0.scratch.scratch_buf[u]?.getD 0#32
              (wu &&& 0x80000000#32) ≠ 0#32 ∧ y = (wu &&& 0x7FFFFFFF#32).toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
        ?_ ?_
      · rintro _ ⟨bp', lm1'⟩ mj ⟨hlm1', hbp_le', hbp0', hmk1', hmj⟩
        dsimp only at hlm1' hbp_le' hbp0' hmk1' hmj
        c0_hsteps!
        exact hL1 (np.toNat - (i + 1#32).toNat) (bp', i + 1#32, ()) mj (by omega)
          ⟨lm1', hlm1', by omega, by rw [hi1]; exact hbp_le', rfl, hbp0',
           by simpa only [hi1] using hmk1', hmj⟩
      · intro _ hJ1
        c0_hsplit
        · have hwp_bin : (wp0 &&& 0x80000000#32) ≠ 0#32 := hc
          have hot_lt : (wp0 &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
            have h1 := hp_ok i.toNat hi_lt; dsimp only at h1; rw [hwp_get] at h1
            exact h1 hwp_bin
          have hot_v : ((wp0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s0.core.vals.length := by
            rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
          have hot_lm : ((wp0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm1.length := by
            rw [hlm1, zext32_toNat]; omega
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
            (fun x => (x.1, ()))
            (fun x mj => x.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
              (x.1 = 0#32 → ∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 = 0#8) ∧
              (∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 ≠ 0#8 →
                ∃ u < i.toNat + 1,
                  let wu := s0.scratch.scratch_buf[u]?.getD 0#32
                  (wu &&& 0x80000000#32) ≠ 0#32 ∧ y = (wu &&& 0x7FFFFFFF#32).toNat) ∧
              (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
            ?_ ?_
          · rintro _ ⟨bp', lm1'⟩ mj ⟨hlm1', hbp_le', hbp0', hmk1', hmj⟩
            dsimp only at hlm1' hbp_le' hbp0' hmk1' hmj
            c0_hsteps!
            exact hJ1 (bp', lm1') mj ⟨hlm1', hbp_le', hbp0', hmk1', hmj⟩
          · intro _ hJ_in
            c0_hsplit
            · have hbp1 : (bin_p + 1#32).toNat = bin_p.toNat + 1 := by c0_bound
              c0_hsteps!
              exact hJ_in (bin_p + 1#32, lm1.set ((wp0 &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8)
                _ ⟨by simp [hlm1], by dsimp only; rw [hbp1]; omega,
                 fun h0 => absurd (congrArg BitVec.toNat h0) (by rw [hbp1]; simp),
                 lm_set_at hlm1 (by rw [← hlm1]; exact hot_lm)
                   (fun y hy hnz => by
                     obtain ⟨u, hu, hw⟩ := hmark1 y hy hnz; exact ⟨u, by omega, hw⟩)
                   ⟨i.toNat, Nat.lt_succ_self _, by rw [hwp_get]; exact hwp_bin,
                    by rw [zext32_toNat, hwp_get]⟩,
                 hm⟩
            · c0_hsteps!
              exact hJ_in (bin_p, lm1) m1 ⟨hlm1, by dsimp only; omega, hbp0, fun y hy hnz => by
                obtain ⟨u, hu, hw⟩ := hmark1 y hy hnz; exact ⟨u, by omega, hw⟩, hm1⟩
        · c0_hsteps!
          exact hJ1 (bin_p, lm1) m1 ⟨hlm1, by dsimp only; omega, hbp0, fun y hy hnz => by
            obtain ⟨u, hu, hw⟩ := hmark1 y hy hnz; exact ⟨u, by omega, hw⟩, hm1⟩
    · have hi_eq : i.toNat = np.toNat := by omega
      c0_hsplit
      · have hclr : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 = 0#8 := hbp0 hc
        have hdw1 := fullDenseInvW_lm_scr hdw0 hlm1 hclr hdw0.1.scratch_ok.scratch_buf_len
        c0_hsteps!; exact hQ false lm1 s0.scratch.scratch_buf m1 hdw1
          hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm1
      · c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i32, i32, i32]) (lpTs := [i32])
          (fun (ml_b, mj_b, _, ()) mb =>
            mb = m1 ∧ (ml_b = 0xFFFFFFFF#32 ∨ mj_b.toNat < nn.toNat))
          (fun rem2 (j, ()) m2 => m2 = m1 ∧ j.toNat ≤ nn.toNat ∧ rem2 = nn.toNat - j.toNat)
          ?_ ?_ ?_
        · rintro _ ⟨ml_b, mj_b, _, ⟨⟩⟩ mb ⟨hmb, hmb_ok⟩
          subst mb
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem3 (ic, ()) m3 => ∃ lm3 : List (BitVec 8),
              let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
              lm3.length = 2 * c.max_vars ∧ ic.toNat ≤ np.toNat ∧ rem3 = np.toNat - ic.toNat ∧
              (∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 ≠ 0#8 →
                ∃ u, ic.toNat ≤ u ∧ u < np.toNat ∧
                  let w := s0.scratch.scratch_buf[u]?.getD 0#32
                  (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
              (FullMem c s3 ⋆ R) m3)
            ?_ ?_
          · rintro L3 rem3 ⟨ic, ⟨⟩⟩ m3 hL3 ⟨lm3, hlm3, hic_le, rfl, hrem3, hm3⟩
            c0_hsplit
            · have hic_lt : ic.toNat < np.toNat := hc
              have hic_sc : (ic.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
                rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; omega
              let wc := s0.scratch.scratch_buf[(ic.setWidth 64).toNat]'hic_sc
              have hwc_get : s0.scratch.scratch_buf[ic.toNat]?.getD 0#32 = wc := by
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                  Option.getD_some]
                exact getElem_congr (zext32_toNat ic) _ _
              have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by c0_bound
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ m3' => ∃ lm3' : List (BitVec 8),
                  let s3' : FullState := { s0 with core := { s0.core with lit_mark := lm3' } }
                  lm3'.length = 2 * c.max_vars ∧
                  (∀ x < 2 * c.max_vars, lm3'[x]?.getD 0#8 ≠ 0#8 →
                    ∃ u, ic.toNat + 1 ≤ u ∧ u < np.toNat ∧
                      let w := s0.scratch.scratch_buf[u]?.getD 0#32
                      (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                  (FullMem c s3' ⋆ R) m3')
                (fun _ _ m3' ⟨lm3', hlm3', hrem3', hm3'⟩ => by
                  c0_hsteps!
                  exact hL3 (np.toNat - (ic + 1#32).toNat) (ic + 1#32, ()) m3' (by omega)
                    ⟨lm3', hlm3', by omega, rfl, fun y hy hnz => by
                      obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem3' y hy hnz
                      exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm3'⟩)
                (fun _ hJ3 => by
                  c0_hsplit
                  · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
                    have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                      have h1 := hp_ok ic.toNat hic_lt; dsimp only at h1; rw [hwc_get] at h1
                      exact h1 hwc_bin
                    have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm3.length := by
                      rw [hlm3, zext32_toNat]; omega
                    c0_hsteps!
                    refine hJ3 () _
                      ⟨lm3.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8, by simp [hlm3],
                       fun y hy hnz => lm_clear_step
                         (P := fun x => ∃ u, ic.toNat + 1 ≤ u ∧ u < np.toNat ∧
                           let w := s0.scratch.scratch_buf[u]?.getD 0#32
                           (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat)
                         hot_lm (fun x hx hnzx => by
                           rw [hlm3] at hx
                           obtain ⟨u, hu1, hu2, hwu, hxe⟩ := hrem3 x hx hnzx
                           rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                           · left; rw [zext32_toNat, hxe, hwc_get]
                           · right; exact ⟨u, by omega, hu2, hwu, hxe⟩)
                         y (by rw [hlm3]; exact hy) hnz, hm⟩
                  · c0_hsteps!
                    refine hJ3 () m3
                      ⟨lm3, hlm3, fun y hy hnz => by
                        obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem3 y hy hnz
                        rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                        · have hwc_c0 :
                              s0.scratch.scratch_buf[ic.toNat]'(by
                                rw [hdw0.1.scratch_ok.scratch_buf_len]; omega) = wc := by
                            rw [← hwc_get, List.getElem?_eq_getElem (by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                          have h0 := hc; rw [hwc_c0] at h0
                          rw [hwc_get] at hwu; exact absurd h0 hwu
                        · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm3⟩)
            · have hic_eq : ic.toNat = np.toNat := by omega
              have hclr3 : ∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 = 0#8 := fun x hx =>
                Classical.byContradiction fun hnz => by
                  obtain ⟨u, hu1, hu2, _⟩ := hrem3 x hx hnz; omega
              let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
              have hdw3 :=
                fullDenseInvW_lm_scr hdw0 hlm3 hclr3 hdw0.1.scratch_ok.scratch_buf_len
              c0_hsplit
              · c0_hsteps!; exact hQ false lm3 s0.scratch.scratch_buf m3 hdw3
                  hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm3
              · have hml_ne : ml_b ≠ 0xFFFFFFFF#32 := hc
                have hmj_lt : mj_b.toNat < nn.toNat := hmb_ok.resolve_left hml_ne
                have hmj_m : (4066#32 + (mj_b >>> (5 : Nat))).toNat <
                    s0.scratch.scratch_buf.length := by
                  have hb := m8_mask_idx_lo 4066#32 mj_b (Or.inr rfl) (by omega)
                  rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32])
                  (fun rem4 (im, ()) m4 => m4 = m3 ∧ im.toNat ≤ np.toNat ∧
                    rem4 = np.toNat - im.toNat)
                  ?_ ?_
                · rintro L4 rem4 ⟨im, ⟨⟩⟩ m4 hL4 ⟨hm4, him_le, rfl⟩
                  subst m4
                  c0_hsplit
                  · have him_lt : im.toNat < np.toNat := hc
                    have him_sc : (im.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
                      rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; omega
                    have him1 : (im + 1#32).toNat = im.toNat + 1 := by c0_bound
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ m4' => m4' = m3)
                      (fun _ _ m4' hm4' => by
                        subst m4'
                        c0_hsteps!
                        exact hL4 (np.toNat - (im + 1#32).toNat) (im + 1#32, ()) m3
                          (by omega) ⟨rfl, by omega, rfl⟩)
                      (fun _ hJ4 => by
                        c0_hsplit
                        · c0_hsplit
                          · have him_m : (4002#32 + (im >>> (5 : Nat))).toNat <
                                s0.scratch.scratch_buf.length := by
                              have hb := m8_mask_idx_lo 4002#32 im (Or.inl rfl) (by omega)
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            have h4130 : 4130 < s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            have h4131 : 4131 < s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            c0_hsteps!
                            have hlen0 := hdw0.1.scratch_ok.scratch_buf_len
                            have him_bd := m8_mask_idx_lo 4002#32 im (Or.inl rfl) (by omega)
                            have hmj_bd := m8_mask_idx_lo 4066#32 mj_b (Or.inr rfl) (by omega)
                            refine hQ true lm3 ?_ m ?_ ?_ ?_ ?_
                            rotate_left 4
                            · exact hm
                            · exact fullDenseInvW_lm_scr hdw0 hlm3 hclr3 (by simp [hlen0])
                            · simp [hlen0]
                            · have him_idx :
                                  ((4002 + im >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    4002 + im.toNat / 32 := by
                                rw [zext32_toNat, BitVec.toNat_add,
                                  show (4002 : BitVec 32).toNat = 4002 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              have hmj_idx :
                                  ((4066 + mj_b >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    4066 + mj_b.toNat / 32 := by
                                rw [zext32_toNat, BitVec.toNat_add,
                                  show (4066 : BitVec 32).toNat = 4066 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              intro idx hidx hor
                              rw [him_idx, hmj_idx,
                                List.getElem?_set_ne
                                  (by rw [show (4131#64).toNat = 4131 from rfl]; omega),
                                List.getElem?_set_ne
                                  (by rw [show (4130#64).toNat = 4130 from rfl]; omega),
                                List.getElem?_set_ne (by omega),
                                List.getElem?_set_ne (by omega)]
                          · c0_hsteps!; exact hJ4 () m3 rfl
                        · c0_hsteps!; exact hJ4 () m3 rfl)
                  · c0_hsteps!; exact hQ false lm3 s0.scratch.scratch_buf m3 hdw3
                      hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm3
                · intro L4 hL4; c0_hsteps!; exact hL4 np.toNat (0#32, ()) m3
                    ⟨rfl, Nat.zero_le _, by simp⟩
          · intro L3 hL3; c0_hsteps!; exact hL3 np.toNat (0#32, ()) m1
              ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
                obtain ⟨u, hu, hw⟩ := hmark1 x hx hnz; exact ⟨u, Nat.zero_le _, by omega, hw⟩,
               hm1⟩
        · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ m2 hB2 hL2 ⟨hm2, hj_le, rfl⟩
          subst m2
          c0_hsplit
          · have hj_lt : j.toNat < nn.toNat := hc
            have hj_sc : ((2001#32 + j).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
              rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
            let wn := s0.scratch.scratch_buf[((2001#32 + j).setWidth 64).toNat]'hj_sc
            have hwn_get : s0.scratch.scratch_buf[2001 + j.toNat]?.getD 0#32 = wn := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact getElem_congr (by rw [zext32_toNat]; c0_bound) _ _
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_group (fun _ m2' => m2' = m1)
              (fun _ _ m2' hm2' => by
                subst m2'
                c0_hsteps!
                exact hL2 (nn.toNat - (j + 1#32).toNat) (j + 1#32, ()) m1 (by omega)
                  ⟨rfl, by omega, rfl⟩)
              (fun _ hJ2 => by
                c0_hsplit
                · have hwn_bin : (wn &&& 0x80000000#32) ≠ 0#32 := hc
                  have hot_lt : (wn &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                    have h1 := hn_ok j.toNat hj_lt; dsimp only at h1; rw [hwn_get] at h1
                    exact h1 hwn_bin
                  have hot_v : ((wn &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                      s0.core.vals.length := by
                    rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
                  have hotn_lm : (((wn &&& 0x7FFFFFFF#32) ^^^ 1#32).setWidth 64).toNat <
                      lm1.length := by
                    have := (bv32_xor1_lt (wn &&& 0x7FFFFFFF#32) hot_lt).2
                    rw [hlm1, zext32_toNat]; omega
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps!
                      exact hB2 (((wn &&& 0x7FFFFFFF#32) ^^^ 1#32), j, j, ()) m1
                        ⟨rfl, Or.inr hj_lt⟩
                    · c0_hsteps!; exact hJ2 _ m1 rfl
                  · c0_hsteps!; exact hJ2 _ m1 rfl
                · c0_hsteps!; exact hJ2 _ m1 rfl)
          · c0_hsteps!; exact hB2 (0xFFFFFFFF#32, 0#32, j, ()) m1 ⟨rfl, Or.inl rfl⟩
        · intro _ L2 _ hL2; c0_hsteps!; exact hL2 nn.toNat (0#32, ()) m1
            ⟨rfl, Nat.zero_le _, by simp⟩
  · intro L1 hL1; c0_hsteps!
    exact hL1 np.toNat (0#32, 0#32, ()) m0
      ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, Nat.zero_le _, by simp,
       fun _ => hdw0.2.2.1.2, fun x hx hnz => absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Gates

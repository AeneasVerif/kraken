/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity BVE Gate Finders — Part 0 (`equiv`, `and`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m8_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-- Parametric `Func.wp` proof for `full_bve_find_equiv_m8`. -/
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
        rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
      let wp0 := s0.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sc
      have hwp_get : s0.scratch.scratch_buf[i.toNat]?.getD 0#32 = wp0 := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact m6_getElem_congr (m6_zext32_toNat i) _ _
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
            rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
          have hot_lm : ((wp0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm1.length := by
            rw [hlm1, m6_zext32_toNat]; omega
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
              exact hJ_in (bin_p + 1#32, lm1.set ((wp0 &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8) _
                ⟨by simp [hlm1], by dsimp only; rw [hbp1]; omega,
                 fun h0 => absurd (congrArg BitVec.toNat h0) (by rw [hbp1]; simp),
                 m8_lm_set_at hlm1 (by rw [← hlm1]; exact hot_lm)
                   (fun y hy hnz => by obtain ⟨u, hu, hw⟩ := hmark1 y hy hnz; exact ⟨u, by omega,
                     hw⟩)
                   ⟨i.toNat, Nat.lt_succ_self _, by rw [hwp_get]; exact hwp_bin,
                    by rw [m6_zext32_toNat, hwp_get]⟩,
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
        have hdw1 := m8_fullDenseInvW_lm_scr hdw0 hlm1 hclr hdw0.1.scratch_ok.scratch_buf_len
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
                rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
              let wc := s0.scratch.scratch_buf[(ic.setWidth 64).toNat]'hic_sc
              have hwc_get : s0.scratch.scratch_buf[ic.toNat]?.getD 0#32 = wc := by
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                  Option.getD_some]
                exact m6_getElem_congr (m6_zext32_toNat ic) _ _
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
                      rw [hlm3, m6_zext32_toNat]; omega
                    c0_hsteps!
                    refine hJ3 () _
                      ⟨lm3.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8, by simp [hlm3],
                       fun y hy hnz => m8_lm_clear_step
                         (P := fun x => ∃ u, ic.toNat + 1 ≤ u ∧ u < np.toNat ∧
                           let w := s0.scratch.scratch_buf[u]?.getD 0#32
                           (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat)
                         hot_lm (fun x hx hnzx => by
                         rw [hlm3] at hx
                         obtain ⟨u, hu1, hu2, hwu, hxe⟩ := hrem3 x hx hnzx
                         rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                         · left; rw [m6_zext32_toNat, hxe, hwc_get]
                         · right; exact ⟨u, by omega, hu2, hwu,
                             hxe⟩) y (by rw [hlm3]; exact hy) hnz, hm⟩
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
                m8_fullDenseInvW_lm_scr hdw0 hlm3 hclr3 hdw0.1.scratch_ok.scratch_buf_len
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
                      rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
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
                            · exact m8_fullDenseInvW_lm_scr hdw0 hlm3 hclr3 (by simp [hlen0])
                            · simp [hlen0]
                            · have him_idx :
                                  ((4002 + im >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    4002 + im.toNat / 32 := by
                                rw [m6_zext32_toNat, BitVec.toNat_add,
                                  show (4002 : BitVec 32).toNat = 4002 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              have hmj_idx :
                                  ((4066 + mj_b >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    4066 + mj_b.toNat / 32 := by
                                rw [m6_zext32_toNat, BitVec.toNat_add,
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
              rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
            let wn := s0.scratch.scratch_buf[((2001#32 + j).setWidth 64).toNat]'hj_sc
            have hwn_get : s0.scratch.scratch_buf[2001 + j.toNat]?.getD 0#32 = wn := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact m6_getElem_congr (by rw [m6_zext32_toNat]; c0_bound) _ _
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
                    rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                  have hotn_lm : (((wn &&& 0x7FFFFFFF#32) ^^^ 1#32).setWidth 64).toNat <
                      lm1.length := by
                    have := (m8_bv32_xor1_lt (wn &&& 0x7FFFFFFF#32) hot_lt).2
                    rw [hlm1, m6_zext32_toNat]; omega
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

/-- Parametric `Func.wp` proof for `full_bve_find_and_m8`. -/
theorem full_bve_find_and_m8_wp (Γ : Env) :
    ∀ a m Q X, m8BveFindAndSpec a m Q X →
      Func.wp Γ full_bve_find_and_m8_body a m Q X := by
  rintro ⟨h, lit, lit_n, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hln, hon, hl_ok, ho_ok, hm0, hQ⟩ :=
    m8BveFindAndSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  unfold Func.wp full_bve_find_and_m8_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun lit_off => lit_off.toNat = if (lit &&& 1#32) ≠ 0#32 then 2001 else 0)
    ?_ ?_
  · rintro _ lit_off hlo
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun opp_off => opp_off.toNat = if (lit &&& 1#32) ≠ 0#32 then 0 else 2001)
      ?_ ?_
    · rintro _ opp_off hoo
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
        (fun lit_mask => lit_mask = 4002#32 ∨ lit_mask = 4066#32)
        ?_ ?_
      · rintro _ lit_mask hlm_k
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
          (fun opp_mask => opp_mask = 4002#32 ∨ opp_mask = 4066#32)
          ?_ ?_
        · rintro _ opp_mask hom_k
          have hl_ok' : ∀ i < lit_n.toNat, FullBveEntryOkW F_cur s0 lit.toNat
              (s0.scratch.scratch_buf[lit_off.toNat + i]?.getD 0#32) := by
            simpa only [← hlo] using hl_ok
          have ho_ok' : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s0 ((lit ^^^ 1#32).toNat)
              (s0.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32) := by
            simpa only [← hoo] using ho_ok
          have hlo_bnd : lit_off.toNat + lit_n.toNat ≤ 4002 := by split at hlo <;> omega
          have hoo_bnd : opp_off.toNat + opp_n.toNat ≤ 4002 := by split at hoo <;> omega
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32, i32])
            (fun rem1 (marked, j, ()) m1 => ∃ lm1 : List (BitVec 8),
              let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
              lm1.length = 2 * c.max_vars ∧ j.toNat ≤ opp_n.toNat ∧
              rem1 = opp_n.toNat - j.toNat ∧
              (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
                ∃ u < j.toNat,
                  let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32
                  (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
              (FullMem c s1 ⋆ R) m1)
            ?_ ?_
          ·
                    rintro L1 rem1 ⟨marked, j, ⟨⟩⟩ m1 hL1 ⟨lm1, hlm1, hj_le, rfl, hmk1, hm1⟩
                    c0_split
                    · have hj_lt : j.toNat < opp_n.toNat := hc
                      have hj_sc : ((opp_off + j).setWidth 64).toNat <
                          s0.scratch.scratch_buf.length := by
                        rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                      have hj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
                        rw [m6_zext32_toNat]; c0_bound
                      let w := s0.scratch.scratch_buf[((opp_off + j).setWidth 64).toNat]'hj_sc
                      have hw_get : s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 =
                        w := by
                        rw [List.getElem?_eq_getElem (by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                          Option.getD_some]
                        exact m6_getElem_congr hj_eq.symm _ _
                      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                      c0_hsteps_nogrp
                      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
                        (fun x => (x.1, ()))
                        (fun x mj => x.2.length = 2 * c.max_vars ∧
                          (∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 ≠ 0#8 →
                            ∃ u < j.toNat + 1,
                              let wu := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32
                              (wu &&& 0x80000000#32) ≠ 0#32 ∧
                              y = (wu &&& 0x7FFFFFFF#32).toNat) ∧
                          (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
                        ?_ ?_
                      · rintro _ ⟨mk', lm1'⟩ mj ⟨hlm1', hmk1', hmj⟩
                        dsimp only at hlm1' hmk1' hmj
                        c0_hsteps!
                        exact hL1 (opp_n.toNat - (j + 1#32).toNat) (mk', j + 1#32, ()) mj
                          (by omega) ⟨lm1', hlm1', by omega, rfl,
                           by simpa only [hj1] using hmk1', hmj⟩
                      · intro _ hJ1
                        have hstay := hJ1 (marked, lm1) m1 ⟨hlm1, fun y hy hnz => by
                          obtain ⟨u, hu, hwu⟩ := hmk1 y hy hnz; exact ⟨u, by omega, hwu⟩, hm1⟩
                        c0_hsplit
                        · have hw_bin : (w &&& 0x80000000#32) ≠ 0#32 := hc
                          have hot_lt : (w &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                            have h1 := ho_ok' j.toNat hj_lt; rw [hw_get] at h1
                            unfold FullBveEntryOkW at h1; rw [ite_eq_left hw_bin] at h1; exact h1.1
                          have hot_v : ((w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                              s0.core.vals.length := by
                            rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                          have hot_lm : ((w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                              lm1.length := by
                            rw [hlm1, m6_zext32_toNat]; omega
                          c0_hsteps! <;> first
                          | exact hstay
                          | exact hJ1 (marked + 1#32,
                              lm1.set ((w &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8) _
                              ⟨by simp [hlm1],
                               m8_lm_set_at hlm1 (by rw [← hlm1]; exact hot_lm)
                                 (fun y hy hnz => by
                                   obtain ⟨u, hu, hwu⟩ := hmk1 y hy hnz
                                   exact ⟨u, by omega, hwu⟩)
                                 ⟨j.toNat, Nat.lt_succ_self _, by rw [hw_get]; exact hw_bin,
                                  by rw [m6_zext32_toNat, hw_get]⟩,
                               hm⟩
                        · c0_hsteps!; exact hstay
                    · have hj_eq : j.toNat = opp_n.toNat := by omega
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i32])
                          (fun rem2 (jc, ()) m2 => ∃ lm2 : List (BitVec 8),
                            let s2 : FullState := { s0 with core := { s0.core with lit_mark :=
                              lm2 } }
                            lm2.length = 2 * c.max_vars ∧ jc.toNat ≤ opp_n.toNat ∧
                            rem2 = opp_n.toNat - jc.toNat ∧
                            (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 ≠ 0#8 →
                              ∃ u, jc.toNat ≤ u ∧ u < opp_n.toNat ∧
                                let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32
                                (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                            (FullMem c s2 ⋆ R) m2)
                          ?_ ?_
                        · rintro L2 rem2 ⟨jc, ⟨⟩⟩ m2 hL2 ⟨lm2, hlm2, hjc_le, rfl, hrem2, hm2⟩
                          c0_hsplit
                          · have hjc_lt : jc.toNat < opp_n.toNat := hc
                            have hoj_sc : ((opp_off + jc).setWidth 64).toNat <
                                s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                            have hoj_eq : ((opp_off + jc).setWidth 64).toNat =
                                opp_off.toNat + jc.toNat := by
                              rw [m6_zext32_toNat]; c0_bound
                            let wc := s0.scratch.scratch_buf[((opp_off +
                              jc).setWidth 64).toNat]'hoj_sc
                            have hwc_get : s0.scratch.scratch_buf[opp_off.toNat +
                              jc.toNat]?.getD 0#32 =
                                wc := by
                              rw [List.getElem?_eq_getElem (by
                                rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                              exact m6_getElem_congr hoj_eq.symm _ hoj_sc
                            have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [])
                              (fun _ m2' => ∃ lm2' : List (BitVec 8),
                                let s2' : FullState := { s0 with core := { s0.core with lit_mark :=
                                  lm2' } }
                                lm2'.length = 2 * c.max_vars ∧
                                (∀ x < 2 * c.max_vars, lm2'[x]?.getD 0#8 ≠ 0#8 →
                                  ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
                                    let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32
                                    (w &&& 0x80000000#32) ≠ 0#32 ∧
                                      x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                                (FullMem c s2' ⋆ R) m2')
                              (fun _ _ m2' ⟨lm2', hlm2', hrem2', hm2'⟩ => by
                                have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
                                c0_hsteps!
                                exact hL2 (opp_n.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) m2'
                                  (by omega) ⟨lm2', hlm2', by omega, rfl,
                                   by simpa only [hjc1] using hrem2', hm2'⟩)
                              (fun _ hJ2 => by
                                c0_hsplit
                                · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
                                  have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat <
                                    2 * s0.core.cur_vars := by
                                    have h1 := ho_ok' jc.toNat hjc_lt; rw [hwc_get] at h1
                                    unfold FullBveEntryOkW at h1; rw [ite_eq_left hwc_bin] at h1;
                                      exact h1.1
                                  have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                    lm2.length := by
                                    rw [hlm2, m6_zext32_toNat]; omega
                                  c0_hsteps!
                                  refine hJ2 () _
                                    ⟨lm2.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8,
                                      by simp [hlm2],
                                     fun y hy hnz => m8_lm_clear_step
                                       (P := fun x => ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
                                         let w := s0.scratch.scratch_buf[opp_off.toNat +
                                           u]?.getD 0#32
                                         (w &&& 0x80000000#32) ≠ 0#32 ∧
                                           x = (w &&& 0x7FFFFFFF#32).toNat)
                                       hot_lm (fun x hx hnzx => by
                                       rw [hlm2] at hx
                                       obtain ⟨u, hu1, hu2, hwu, hxe⟩ := hrem2 x hx hnzx
                                       rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                                       · left; rw [m6_zext32_toNat, hxe, hwc_get]
                                       · right; exact ⟨u, by omega, hu2, hwu, hxe⟩)
                                       y (by rw [hlm2]; exact hy) hnz, hm⟩
                                · c0_hsteps!
                                  refine hJ2 () m2
                                    ⟨lm2, hlm2, fun y hy hnz => by
                                      obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                                      rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                                      · have hwc_c0 :
                                            s0.scratch.scratch_buf[(opp_off.toNat +
                                              jc.toNat) % 2 ^ 32]'(by
                                              rw [hdw0.1.scratch_ok.scratch_buf_len,
                                                Nat.mod_eq_of_lt (by omega)]; omega) = wc := by
                                          rw [← hwc_get, List.getElem?_eq_getElem (by
                                            rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                                              Option.getD_some]
                                          exact m6_getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                                        have h0 := hc; rw [hwc_c0] at h0; rw [hwc_get] at hwu
                                        exact absurd h0 hwu
                                      · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2⟩)
                          · have hclr2 : ∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8 := fun x hx =>
                              Classical.byContradiction fun hnz => by
                                obtain ⟨u, hu1, hu2, _⟩ := hrem2 x hx hnz; omega
                            have hdw2 := m8_fullDenseInvW_lm_scr hdw0 hlm2 hclr2
                              hdw0.1.scratch_ok.scratch_buf_len
                            c0_hsteps!
                            exact hQ false lm2 s0.scratch.scratch_buf m2 hdw2
                              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm2
                        · intro L2 hL2; c0_hsteps!
                          exact hL2 opp_n.toNat (0#32, ()) m1
                            ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
                              obtain ⟨u, hu, hw⟩ := hmk1 x hx hnz
                              exact ⟨u, Nat.zero_le _, by omega, hw⟩, hm1⟩
                      · c0_hsteps_nogrp
                        refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32])
                          (fun (found_i, _ib, ()) mb => mb = m1 ∧
                            (found_i = 0xFFFFFFFF#32 ∨ (found_i.toNat < lit_n.toNat ∧
                              let wf := s0.scratch.scratch_buf[lit_off.toNat +
                                found_i.toNat]?.getD 0#32
                              (wf &&& 0x80000000#32) = 0#32)))
                          (fun rem_i (i, ()) mi => mi = m1 ∧ i.toNat ≤ lit_n.toNat ∧
                            rem_i = lit_n.toNat - i.toNat)
                          ?_ ?_ ?_
                        · rintro _ ⟨found_i, _ib, ⟨⟩⟩ mb ⟨rfl, hfound⟩
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem2 (jc, ()) m2 => ∃ lm2 : List (BitVec 8),
                              let s2 : FullState := { s0 with core := { s0.core with lit_mark :=
                                lm2 } }
                              lm2.length = 2 * c.max_vars ∧ jc.toNat ≤ opp_n.toNat ∧
                              rem2 = opp_n.toNat - jc.toNat ∧
                              (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 ≠ 0#8 →
                                ∃ u, jc.toNat ≤ u ∧ u < opp_n.toNat ∧
                                  let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32
                                  (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                              (FullMem c s2 ⋆ R) m2)
                            ?_ ?_
                          · rintro L2 rem2 ⟨jc, ⟨⟩⟩ m2 hL2 ⟨lm2, hlm2, hjc_le, rfl, hrem2, hm2⟩
                            c0_hsplit
                            · have hjc_lt : jc.toNat < opp_n.toNat := hc
                              have hoj_sc : ((opp_off + jc).setWidth 64).toNat <
                                  s0.scratch.scratch_buf.length := by
                                rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                              have hoj_eq : ((opp_off + jc).setWidth 64).toNat =
                                  opp_off.toNat + jc.toNat := by
                                rw [m6_zext32_toNat]; c0_bound
                              let wc := s0.scratch.scratch_buf[((opp_off +
                                jc).setWidth 64).toNat]'hoj_sc
                              have hwc_get : s0.scratch.scratch_buf[opp_off.toNat +
                                jc.toNat]?.getD 0#32 =
                                  wc := by
                                rw [List.getElem?_eq_getElem (by
                                  rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                                exact m6_getElem_congr hoj_eq.symm _ hoj_sc
                              have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ m2' => ∃ lm2' : List (BitVec 8),
                                  let s2' : FullState := { s0 with core :=
                                    { s0.core with lit_mark := lm2' } }
                                  lm2'.length = 2 * c.max_vars ∧
                                  (∀ x < 2 * c.max_vars, lm2'[x]?.getD 0#8 ≠ 0#8 →
                                    ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
                                      let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32
                                      (w &&& 0x80000000#32) ≠ 0#32 ∧
                                        x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                                  (FullMem c s2' ⋆ R) m2')
                                (fun _ _ m2' ⟨lm2', hlm2', hrem2', hm2'⟩ => by
                                  c0_hsteps!
                                  exact hL2 (opp_n.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) m2'
                                    (by omega) ⟨lm2', hlm2', by omega, rfl,
                                     by simpa only [hjc1] using hrem2', hm2'⟩)
                                (fun _ hJ2 => by
                                  c0_hsplit
                                  · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
                                    have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat <
                                      2 * s0.core.cur_vars := by
                                      have h1 := ho_ok' jc.toNat hjc_lt; rw [hwc_get] at h1
                                      unfold FullBveEntryOkW at h1; rw [ite_eq_left hwc_bin] at h1;
                                        exact h1.1
                                    have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                      lm2.length := by
                                      rw [hlm2, m6_zext32_toNat]; omega
                                    c0_hsteps!
                                    refine hJ2 () _
                                      ⟨lm2.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8,
                                        by simp [hlm2],
                                       fun y hy hnz => m8_lm_clear_step
                                         (P := fun x => ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
                                           let w := s0.scratch.scratch_buf[opp_off.toNat +
                                             u]?.getD 0#32
                                           (w &&& 0x80000000#32) ≠ 0#32 ∧
                                             x = (w &&& 0x7FFFFFFF#32).toNat)
                                         hot_lm (fun x hx hnzx => by
                                         rw [hlm2] at hx
                                         obtain ⟨u, hu1, hu2, hwu, hxe⟩ := hrem2 x hx hnzx
                                         rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                                         · left; rw [m6_zext32_toNat, hxe, hwc_get]
                                         · right; exact ⟨u, by omega, hu2, hwu,
                                             hxe⟩) y (by rw [hlm2]; exact hy) hnz, hm⟩
                                  · c0_hsteps!
                                    refine hJ2 () m2
                                      ⟨lm2, hlm2, fun y hy hnz => by
                                        obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                                        rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                                        · have hwc_c0 :
                                              s0.scratch.scratch_buf[(opp_off.toNat +
                                                jc.toNat) % 2 ^ 32]'(by
                                                rw [hdw0.1.scratch_ok.scratch_buf_len,
                                                  Nat.mod_eq_of_lt (by omega)]; omega) = wc := by
                                            rw [← hwc_get, List.getElem?_eq_getElem (by
                                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                                                Option.getD_some]
                                            exact m6_getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                                          have h0 := hc; rw [hwc_c0] at h0; rw [hwc_get] at hwu
                                          exact absurd h0 hwu
                                        · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2⟩)
                            · have hclr2 : ∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8 :=
                                fun x hx =>
                                Classical.byContradiction fun hnz => by
                                  obtain ⟨u, hu1, hu2, _⟩ := hrem2 x hx hnz; omega
                              have hdw2 := m8_fullDenseInvW_lm_scr hdw0 hlm2 hclr2
                                hdw0.1.scratch_ok.scratch_buf_len
                              c0_hsplit
                              · c0_hsteps!
                                exact hQ false lm2 s0.scratch.scratch_buf m2 hdw2
                                  hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm2
                              · have hfn_ne : found_i ≠ 0xFFFFFFFF#32 := hc
                                obtain ⟨hfi_lt, hfi_nb⟩ := hfound.resolve_left hfn_ne
                                have hfi_sc : ((lit_off + found_i).setWidth 64).toNat <
                                    s0.scratch.scratch_buf.length := by
                                  rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                                have hfi_eq : ((lit_off + found_i).setWidth 64).toNat =
                                    lit_off.toNat + found_i.toNat := by
                                  rw [m6_zext32_toNat]; c0_bound
                                let wf := s0.scratch.scratch_buf[((lit_off +
                                  found_i).setWidth 64).toNat]'hfi_sc
                                have hwf_get : s0.scratch.scratch_buf[lit_off.toNat +
                                  found_i.toNat]?.getD 0#32 =
                                    wf := by
                                  rw [List.getElem?_eq_getElem (by
                                    rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                                      Option.getD_some]
                                  exact m6_getElem_congr hfi_eq.symm _ hfi_sc
                                have hwf_ent : wf.toNat ∈ fullArenaClauseRefs s0 ∧
                                    fullArenaClauseGarb s0 wf.toNat = false := by
                                  have h1 := hl_ok' found_i.toNat hfi_lt
                                  rw [hwf_get] at h1; unfold FullBveEntryOkW at h1
                                  rw [hwf_get] at hfi_nb; rwa [ite_eq_right (fun h =>
                                    h hfi_nb)] at h1
                                have hwf_f := hdw0.2.1.arena.refs_wf wf.toNat hwf_ent.1
                                have hwf_bd : wf.toNat + 3 +
                                  fullArenaClauseSizeCore s0.core wf.toNat ≤
                                    c.arena_cap := by
                                  have := hwf_f.2.2.1; have := hwf_f.2.2.2.1; omega
                                have hwf2_ar : (wf.setWidth 64 + 2#64).toNat <
                                  s0.core.arena.length := by
                                  rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add,
                                    m6_zext32_toNat,
                                    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                  omega
                                let fsz := s0.core.arena[(wf.setWidth 64 + 2#64).toNat]'hwf2_ar
                                have hfsz_eq : fsz.toNat =
                                  fullArenaClauseSizeCore s0.core wf.toNat := by
                                  unfold fsz fullArenaClauseSizeCore
                                  rw [List.getElem?_eq_getElem (by
                                    rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                  exact congrArg BitVec.toNat (m6_getElem_congr (by
                                    rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega)]) _ _)
                                c0_hsteps_nogrp
                                refine wp_loop_group (ts := [i32, i32])
                                  (fun rem3 (uniq_need, k, ()) m3 => ∃ lm3 : List (BitVec 8),
                                    let s3 : FullState := { s0 with core :=
                                      { s0.core with lit_mark := lm3 } }
                                    lm3.length = 2 * c.max_vars ∧ k.toNat ≤ fsz.toNat ∧
                                    rem3 = fsz.toNat - k.toNat ∧
                                    (∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 ≠ 0#8 →
                                      (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                                      (x ^^^ 1) ≠ lit.toNat) ∧
                                    (FullMem c s3 ⋆ R) m3)
                                  ?_ ?_
                                · rintro L3 rem3 ⟨uniq_need, k, ⟨⟩⟩ m3 hL3
                                    ⟨lm3, hlm3, hk_le, rfl, hmk3, hm3⟩
                                  c0_hsplit
                                  · have hk_lt : k.toNat < fsz.toNat := hc
                                    have hwk_eq : (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                                        wf.toNat + 3 + k.toNat := by
                                      rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                                        m6_zext32_toNat, BitVec.toNat_ofNat]
                                      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                                    have hwk : (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                                        s0.core.arena.length := by
                                      rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                                    let lf := s0.core.arena[(wf.setWidth 64 + 3#64 +
                                      k.setWidth 64).toNat]'hwk
                                    have hlf_mem : lf.toNat ∈ fullArenaClauseLitsCore s0.core
                                      wf.toNat := by
                                      rw [mem_fullArenaClauseLitsCore_iff (by
                                        rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                                      exact ⟨k.toNat, by omega,
                                        congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                                    have hlf_lt : lf.toNat < 2 * s0.core.cur_vars :=
                                      hdw0.2.1.arena.lits_lt wf.toNat hwf_ent.1 hwf_ent.2 _ hlf_mem
                                    have hlf_v : (lf.setWidth 64).toNat < s0.core.vals.length := by
                                      rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                                    have hlfn_lt : lf.toNat ^^^ 1 < 2 * s0.core.cur_vars := by
                                      have := fullInv_var_xor1 lf.toNat; omega
                                    have hlfn_lm : ((lf ^^^ 1#32).setWidth 64).toNat <
                                      lm3.length := by
                                      rw [hlm3, m6_zext32_toNat, BitVec.toNat_xor,
                                        BitVec.toNat_ofNat]
                                      rw [show (1 : Nat) % 2 ^ 32 = 1 from rfl]; omega
                                    have hlfn_inv : ((lf ^^^ 1#32).setWidth 64).toNat ^^^ 1 =
                                      lf.toNat := by
                                      have h := congrArg BitVec.toNat
                                        (by rw [BitVec.xor_assoc, BitVec.xor_self,
                                          BitVec.xor_zero] :
                                          (lf ^^^ 1#32) ^^^ 1#32 = lf)
                                      rw [BitVec.toNat_xor, BitVec.toNat_ofNat,
                                        show (1 : Nat) % 2 ^ 32 = 1 from rfl] at h
                                      rw [m6_zext32_toNat]; exact h
                                    have hfi_mod : (lit_off.toNat + found_i.toNat) % 2 ^ 32 <
                                        s0.scratch.scratch_buf.length := by
                                      rw [Nat.mod_eq_of_lt (by omega),
                                        hdw0.1.scratch_ok.scratch_buf_len]
                                      omega
                                    have hwf_c0 : s0.scratch.scratch_buf[(lit_off.toNat +
                                      found_i.toNat) %
                                        2 ^ 32]'hfi_mod = wf := by
                                      rw [← hwf_get, List.getElem?_eq_getElem (by
                                        rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                                          Option.getD_some]
                                      exact m6_getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                                    have hlf_c0_idx :
                                        ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) %
                                            2 ^ 32]'hfi_mod).toNat + BitVec.toNat (3 : BitVec 64) +
                                          k.toNat) % 2 ^ 64 =
                                          (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat := by
                                      rw [hwf_c0, hwk_eq,
                                        show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                        Nat.mod_eq_of_lt (by omega)]
                                    have hlf_c0 : s0.core.arena[
                                        ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) %
                                            2 ^ 32]'hfi_mod).toNat + BitVec.toNat (3 : BitVec 64) +
                                          k.toNat) % 2 ^ 64]'(by rw [hlf_c0_idx]; exact hwk) = lf :=
                                      m6_getElem_congr hlf_c0_idx _ hwk
                                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                                    c0_hsteps_nogrp
                                    refine wp_join_state (ts := [i32]) (α :=
                                      BitVec 32 × List (BitVec 8))
                                      (fun x => (x.1, ()))
                                      (fun x mj => x.2.length = 2 * c.max_vars ∧
                                        (∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 ≠ 0#8 →
                                          (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                                          (y ^^^ 1) ≠ lit.toNat) ∧
                                        (FullMem c { s0 with core := { s0.core with lit_mark :=
                                          x.2 } } ⋆ R) mj)
                                      (fun _ ⟨un', lm'⟩ mj ⟨hlm', hmk', hmj⟩ => by
                                        c0_hsteps!
                                        exact hL3 (fsz.toNat - (k + 1#32).toNat) (un', k + 1#32,
                                          ()) mj
                                          (by omega) ⟨lm', hlm', by omega, rfl, hmk', hmj⟩)
                                      (fun _ hJ3 => by
                                        c0_hsplit
                                        · have hlf_ne : lf.toNat ≠ lit.toNat := by
                                            intro h; exact hc (by
                                              rw [hlf_c0]; exact BitVec.eq_of_toNat_eq h)
                                          c0_hsplit
                                          · c0_hsplit
                                            · c0_hsteps!
                                              exact hJ3 (uniq_need + 1#32,
                                                lm3.set ((lf ^^^ 1#32).setWidth 64).toNat 1#8) _
                                                ⟨by simp [hlm3],
                                                 m8_lm_set_at hlm3 (by
                                                   rw [← hlm3]; exact hlfn_lm) hmk3
                                                   ⟨by rw [hlfn_inv]; exact hlf_mem,
                                                    by rw [hlfn_inv]; exact hlf_ne⟩,
                                                 hm⟩
                                            · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3,
                                                hmk3, hm3⟩
                                          · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3,
                                              hm3⟩
                                        · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3,
                                            hm3⟩)
                                  · c0_hsteps_nogrp
                                    refine wp_loop_group (ts := [i32, i32])
                                      (fun rem4 (j4, matched, ()) m4 =>
                                        ∃ (lm4 : List (BitVec 8)) (scr4 : List (BitVec 32)),
                                          let s4 : FullState :=
                                            { s0 with
                                              core := { s0.core with lit_mark := lm4 }
                                              scratch := { s0.scratch with scratch_buf := scr4 } }
                                          lm4.length = 2 * c.max_vars ∧ j4.toNat ≤ opp_n.toNat ∧
                                          rem4 = opp_n.toNat - j4.toNat ∧
                                          (∀ x < 2 * c.max_vars, lm4[x]?.getD 0#8 ≠ 0#8 →
                                            (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                                            (x ^^^ 1) ≠ lit.toNat) ∧
                                          scr4.length = c.scratch_cap ∧
                                          (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4130 ≤ idx) →
                                            scr4[idx]? = s0.scratch.scratch_buf[idx]?) ∧
                                          (FullMem c s4 ⋆ R) m4)
                                      ?_ ?_
                                    · rintro L4 rem4 ⟨j4, matched, ⟨⟩⟩ m4 hL4
                                        ⟨lm4, scr4, hlm4, hj4_le, rfl, hmk4, hsc4, hout4, hm4⟩
                                      c0_hsplit
                                      · have hj4_lt : j4.toNat < opp_n.toNat := hc
                                        have hoj4_sc : ((opp_off + j4).setWidth 64).toNat <
                                          scr4.length := by
                                          rw [hsc4, m6_zext32_toNat]; c0_bound
                                        have hoj4_eq : ((opp_off + j4).setWidth 64).toNat =
                                            opp_off.toNat + j4.toNat := by
                                          rw [m6_zext32_toNat]; c0_bound
                                        let w4 := scr4[((opp_off + j4).setWidth 64).toNat]'hoj4_sc
                                        have hw4_eq : w4 =
                                            s0.scratch.scratch_buf[opp_off.toNat +
                                              j4.toNat]?.getD 0#32 := by
                                          have hget := hout4 (opp_off.toNat + j4.toNat) (by omega)
                                            (Or.inl (by omega))
                                          have ho4' : opp_off.toNat + j4.toNat < scr4.length := by
                                            omega
                                          have hw4_c : w4 = scr4[opp_off.toNat + j4.toNat]'ho4' :=
                                            m6_getElem_congr hoj4_eq hoj4_sc ho4'
                                          rw [hw4_c, ← Option.getD_some (b := 0#32)
                                            (a := scr4[opp_off.toNat + j4.toNat]'ho4'),
                                            ← List.getElem?_eq_getElem ho4', hget]
                                        have hj4_1 : (j4 + 1#32).toNat = j4.toNat + 1 := by c0_bound
                                        c0_hsteps_nogrp
                                        refine wp_join_state (ts := [i32])
                                          (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                                          (fun x => (x.1, ()))
                                          (fun x mj =>
                                            x.2.1.length = 2 * c.max_vars ∧
                                            (∀ y < 2 * c.max_vars, x.2.1[y]?.getD 0#8 ≠ 0#8 →
                                              (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                                              (y ^^^ 1) ≠ lit.toNat) ∧
                                            x.2.2.length = c.scratch_cap ∧
                                            (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4130 ≤ idx) →
                                              x.2.2[idx]? = s0.scratch.scratch_buf[idx]?) ∧
                                            (FullMem c { s0 with
                                              core := { s0.core with lit_mark := x.2.1 }
                                              scratch := { s0.scratch with scratch_buf :=
                                                x.2.2 } } ⋆ R) mj)
                                          ?_ ?_
                                        · rintro _ ⟨ma', lm4', scr4'⟩ mj
                                            ⟨hlm4', hmk4', hsc4', hout4', hmj⟩
                                          dsimp only at hlm4' hmk4' hsc4' hout4' hmj
                                          c0_hsteps!
                                          exact hL4 (opp_n.toNat - (j4 + 1#32).toNat)
                                            (j4 + 1#32, ma', ()) mj (by omega)
                                            ⟨lm4', scr4', hlm4', by omega, rfl, hmk4', hsc4',
                                             hout4', hmj⟩
                                        · intro _ hJ4
                                          c0_hsplit
                                          · have hw4_bin : (w4 &&& 0x80000000#32) ≠ 0#32 := hc
                                            have hot_lt : (w4 &&& 0x7FFFFFFF#32).toNat <
                                                2 * s0.core.cur_vars := by
                                              have h1 := ho_ok' j4.toNat hj4_lt; rw [← hw4_eq] at h1
                                              unfold FullBveEntryOkW at h1
                                              rw [ite_eq_left hw4_bin] at h1; exact h1.1
                                            have hot_lm : ((w4 &&&
                                              0x7FFFFFFF#32).setWidth 64).toNat <
                                                lm4.length := by
                                              rw [hlm4, m6_zext32_toNat]; omega
                                            have hm4_bd :=
                                              m8_mask_idx_lo opp_mask j4 hom_k (by omega)
                                            have hm4_eq : ((opp_mask +
                                              (j4 >>> (5 : Nat))).setWidth 64).toNat =
                                                opp_mask.toNat + j4.toNat / 32 := by
                                              rw [m6_zext32_toNat]; exact hm4_bd.1
                                            have hm4_sc : ((opp_mask +
                                              (j4 >>> (5 : Nat))).setWidth 64).toNat <
                                                scr4.length := by
                                              rw [hsc4, hm4_eq]; omega
                                            c0_hsteps!
                                            · refine hJ4 (matched + 1#32,
                                                lm4.set ((w4 &&&
                                                  0x7FFFFFFF#32).setWidth 64).toNat 0#8,
                                                scr4.set ((opp_mask +
                                                  (j4 >>> (5 : Nat))).setWidth 64).toNat _)
                                                _ ⟨by simp [hlm4], fun y hy hnz => by
                                                    by_cases heq : y = ((w4 &&&
                                                      0x7FFFFFFF#32).setWidth 64).toNat
                                                    · subst heq
                                                      rw [List.getElem?_set_self hot_lm] at hnz
                                                      exact absurd rfl hnz
                                                    · rw [List.getElem?_set_ne (Ne.symm heq)] at hnz
                                                      exact hmk4 y hy hnz,
                                                   by simp [hsc4], fun idx hidx hor => by
                                                     have hne : idx ≠
                                                         ((opp_mask +
                                                           (j4 >>> (5 : Nat))).setWidth
                                                             64).toNat := by
                                                       rw [hm4_eq]
                                                       rcases hom_k with rfl | rfl <;>
                                                         simp only [BitVec.toNat_ofNat] at hm4_bd ⊢
                                                           <;>
                                                         omega
                                                     rw [List.getElem?_set_ne hne.symm]; exact hout4
                                                       idx hidx hor,
                                                   hm⟩
                                            · exact hJ4 (matched, lm4, scr4) m4
                                                ⟨hlm4, hmk4, hsc4, hout4, hm4⟩
                                          · c0_hsteps!; exact hJ4 (matched, lm4, scr4) m4
                                              ⟨hlm4, hmk4, hsc4, hout4, hm4⟩
                                      · c0_hsteps_nogrp
                                        refine wp_loop_group (ts := [i32])
                                          (fun rem5 (kc, ()) m5 => ∃ lm5 : List (BitVec 8),
                                            let s5 : FullState :=
                                              { s0 with
                                                core := { s0.core with lit_mark := lm5 }
                                                scratch := { s0.scratch with scratch_buf := scr4 } }
                                            lm5.length = 2 * c.max_vars ∧ kc.toNat ≤ fsz.toNat ∧
                                            rem5 = fsz.toNat - kc.toNat ∧
                                            (∀ x < 2 * c.max_vars, lm5[x]?.getD 0#8 ≠ 0#8 →
                                              ∃ u, kc.toNat ≤ u ∧ u < fsz.toNat ∧
                                                let l := s0.core.arena[wf.toNat + 3 + u]?.getD 0#32
                                                l ≠ lit ∧ x = (l ^^^ 1#32).toNat) ∧
                                            (FullMem c s5 ⋆ R) m5)
                                          ?_ ?_
                                        · rintro L5 rem5 ⟨kc, ⟨⟩⟩ m5 hL5
                                            ⟨lm5, hlm5, hkc_le, rfl, hrem5, hm5⟩
                                          c0_hsplit
                                          · have hkc_lt : kc.toNat < fsz.toNat := hc
                                            have hwk_eq : (wf.setWidth 64 + 3#64 +
                                              kc.setWidth 64).toNat =
                                                wf.toNat + 3 + kc.toNat := by
                                              rw [BitVec.toNat_add, BitVec.toNat_add,
                                                m6_zext32_toNat,
                                                m6_zext32_toNat, BitVec.toNat_ofNat]
                                              rw [Nat.mod_eq_of_lt (by omega),
                                                Nat.mod_eq_of_lt (by omega)]
                                            have hwk : (wf.setWidth 64 + 3#64 +
                                              kc.setWidth 64).toNat <
                                                s0.core.arena.length := by
                                              rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                                            let l5 := s0.core.arena[(wf.setWidth 64 + 3#64 +
                                              kc.setWidth 64).toNat]'hwk
                                            have hl5_mem : l5.toNat ∈ fullArenaClauseLitsCore
                                              s0.core wf.toNat := by
                                              rw [mem_fullArenaClauseLitsCore_iff (by
                                                rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                                              exact ⟨kc.toNat, by omega,
                                                congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm
                                                  _ _)⟩
                                            have hl5_lt : l5.toNat < 2 * s0.core.cur_vars :=
                                              hdw0.2.1.arena.lits_lt wf.toNat hwf_ent.1 hwf_ent.2 _
                                                hl5_mem
                                            have hl5n_lm : ((l5 ^^^ 1#32).setWidth 64).toNat <
                                              lm5.length := by
                                              have := (m8_bv32_xor1_lt l5 hl5_lt).2
                                              rw [hlm5, m6_zext32_toNat]; omega
                                            have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := by
                                              c0_bound
                                            c0_hsteps_nogrp
                                            refine wp_join_group (ts := [])
                                              (fun _ m5' => ∃ lm5' : List (BitVec 8),
                                                let s5' : FullState :=
                                                  { s0 with
                                                    core := { s0.core with lit_mark := lm5' }
                                                    scratch := { s0.scratch with scratch_buf :=
                                                      scr4 } }
                                                lm5'.length = 2 * c.max_vars ∧
                                                (∀ x < 2 * c.max_vars, lm5'[x]?.getD 0#8 ≠ 0#8 →
                                                  ∃ u, kc.toNat + 1 ≤ u ∧ u < fsz.toNat ∧
                                                    let l := s0.core.arena[wf.toNat + 3 +
                                                      u]?.getD 0#32
                                                    l ≠ lit ∧ x = (l ^^^ 1#32).toNat) ∧
                                                (FullMem c s5' ⋆ R) m5')
                                              (fun _ _ m5' ⟨lm5', hlm5', hrem5', hm5'⟩ => by
                                                c0_hsteps!
                                                exact hL5 (fsz.toNat - (kc + 1#32).toNat)
                                                  (kc + 1#32, ()) m5' (by omega)
                                                  ⟨lm5', hlm5', by omega, rfl,
                                                   by simpa only [hkc1] using hrem5', hm5'⟩)
                                              (fun _ hJ5 => by
                                                have har_get : s0.core.arena[wf.toNat + 3 +
                                                  kc.toNat]?.getD 0#32 = l5 := by
                                                  rw [List.getElem?_eq_getElem (by
                                                    rw [hdw0.1.core_ok.arena_len_arr]; omega),
                                                      Option.getD_some]
                                                  exact m6_getElem_congr hwk_eq.symm _ hwk
                                                c0_hsplit
                                                · c0_hsteps!
                                                  refine hJ5 () _
                                                    ⟨lm5.set ((l5 ^^^ 1#32).setWidth 64).toNat 0#8,
                                                     by simp [hlm5],
                                                     fun y hy hnz => m8_lm_clear_step
                                                       (P := fun x => ∃ u, kc.toNat + 1 ≤ u ∧
                                                         u < fsz.toNat ∧
                                                         let l := s0.core.arena[wf.toNat + 3 +
                                                           u]?.getD 0#32
                                                         l ≠ lit ∧ x = (l ^^^ 1#32).toNat)
                                                       hl5n_lm (fun x hx hnzx => by
                                                         rw [hlm5] at hx
                                                         obtain ⟨u, hu1, hu2, hlu, hxe⟩ :=
                                                           hrem5 x hx hnzx
                                                         rcases Nat.eq_or_lt_of_le hu1 with rfl |
                                                           hgt
                                                         · left; rw [m6_zext32_toNat, hxe, har_get]
                                                         · right; exact ⟨u, by omega, hu2, hlu,
                                                             hxe⟩)
                                                       y (by rw [hlm5]; exact hy) hnz, hm⟩
                                                · c0_hsteps!
                                                  refine hJ5 () m5
                                                    ⟨lm5, hlm5, fun y hy hnz => by
                                                      obtain ⟨u, hu1, hu2, hlu, hyeq⟩ :=
                                                        hrem5 y hy hnz
                                                      rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                                                      · have hfi_mod : (lit_off.toNat +
                                                          found_i.toNat) % 2 ^ 32 <
                                                            s0.scratch.scratch_buf.length := by
                                                          rw [Nat.mod_eq_of_lt (by omega),
                                                            hdw0.1.scratch_ok.scratch_buf_len]
                                                          omega
                                                        have hwf_c0 :
                                                            s0.scratch.scratch_buf[(lit_off.toNat +
                                                              found_i.toNat) % 2 ^ 32]'hfi_mod =
                                                                wf :=
                                                          m6_getElem_congr (by
                                                            rw [Nat.mod_eq_of_lt (by omega),
                                                              m6_zext32_toNat]; c0_bound) _ _
                                                        have hceq : l5 = lit := by
                                                          have hidx : (wf.setWidth 64 + 3#64 +
                                                              kc.setWidth 64).toNat =
                                                              ((s0.scratch.scratch_buf[
                                                                (lit_off.toNat +
                                                                found_i.toNat) % 2 ^
                                                                  32]'hfi_mod).toNat + 3 +
                                                                kc.toNat) % 2 ^ 64 := by
                                                            rw [hwf_c0, hwk_eq,
                                                              Nat.mod_eq_of_lt (by omega)]
                                                          dsimp only [l5]
                                                          rw [m6_getElem_congr hidx hwk (by
                                                            rw [← hidx]; exact hwk)]
                                                          exact hc
                                                        rw [har_get] at hlu
                                                        exact absurd hceq hlu
                                                      · exact ⟨u, by omega, hu2, hlu, hyeq⟩, hm5⟩)
                                          · have hfi_mod : (lit_off.toNat +
                                              found_i.toNat) % 2 ^ 32 <
                                                s0.scratch.scratch_buf.length := by
                                              rw [Nat.mod_eq_of_lt (by omega),
                                                hdw0.1.scratch_ok.scratch_buf_len]
                                              omega
                                            have hwf_c0 :
                                                s0.scratch.scratch_buf[(lit_off.toNat +
                                                  found_i.toNat) % 2 ^ 32]'hfi_mod = wf :=
                                              m6_getElem_congr (by
                                                rw [Nat.mod_eq_of_lt (by omega),
                                                  m6_zext32_toNat]; c0_bound) _ _
                                            have hfsz_idx : (wf.setWidth 64 + 2#64).toNat =
                                                ((s0.scratch.scratch_buf[(lit_off.toNat +
                                                  found_i.toNat) % 2 ^ 32]'hfi_mod).toNat +
                                                    2) % 2 ^ 64 := by
                                              rw [hwf_c0, BitVec.toNat_add, m6_zext32_toNat,
                                                show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                Nat.mod_eq_of_lt (by omega)]
                                            have hkc_ge : fsz.toNat ≤ kc.toNat := by
                                              have hfeq : fsz =
                                                s0.core.arena[((s0.scratch.scratch_buf[
                                                  (lit_off.toNat +
                                                    found_i.toNat) % 2 ^ 32]'hfi_mod).toNat + 2) %
                                                  2 ^ 64]'(by rw [← hfsz_idx]; exact hwf2_ar) :=
                                                m6_getElem_congr hfsz_idx hwf2_ar _
                                              rw [hfeq]; exact Nat.le_of_not_lt hc
                                            have hclr5 : ∀ x < 2 * c.max_vars,
                                              lm5[x]?.getD 0#8 = 0#8 := fun x hx =>
                                              Classical.byContradiction fun hnz => by
                                                obtain ⟨u, hu1, hu2, _⟩ := hrem5 x hx hnz; omega
                                            have hdw5 :=
                                              m8_fullDenseInvW_lm_scr hdw0 hlm5 hclr5 hsc4
                                            c0_hsteps_nogrp
                                            refine wp_join_group (ts := []) (fun _ mf => mf = m5)
                                              ?_ ?_
                                            · rintro _ _ mf hmf
                                              subst mf
                                              c0_hsteps_nogrp
                                              refine wp_loop_group (ts := [i32])
                                                (fun rem6 (kz, ()) m6 => ∃ scr6 : List (BitVec 32),
                                                  let s6 : FullState :=
                                                    { s0 with
                                                      core := { s0.core with lit_mark := lm5 }
                                                      scratch := { s0.scratch with scratch_buf :=
                                                        scr6 } }
                                                  scr6.length = c.scratch_cap ∧ kz.toNat ≤ 64 ∧
                                                    rem6 = 64 - kz.toNat ∧
                                                  (∀ idx < c.scratch_cap, (idx < 4002 ∨
                                                    4130 ≤ idx) →
                                                    scr6[idx]? = s0.scratch.scratch_buf[idx]?) ∧
                                                  (FullMem c s6 ⋆ R) m6)
                                                ?_ ?_
                                              · rintro L6 rem6 ⟨kz, ⟨⟩⟩ m6 hL6
                                                  ⟨scr6, hsc6, hkz_le, rfl, hout6, hm6⟩
                                                c0_hsplit
                                                · have hkz_lt : kz.toNat < 64 := hc
                                                  have hm6_bd : (opp_mask + kz).toNat =
                                                    opp_mask.toNat + kz.toNat ∧
                                                      (opp_mask + kz).toNat < 4130 := by
                                                    rcases hom_k with rfl | rfl <;>
                                                      (rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                                                         Nat.mod_eq_of_lt (by omega)]; exact ⟨rfl,
                                                           by omega⟩)
                                                  have hm6_sc : ((opp_mask +
                                                    kz).setWidth 64).toNat < scr6.length := by
                                                    rw [hsc6, m6_zext32_toNat]; omega
                                                  have hkz1 : (kz + 1#32).toNat = kz.toNat + 1 :=
                                                    by c0_bound
                                                  c0_hsteps!
                                                  exact hL6 (64 - (kz + 1#32).toNat) (kz + 1#32,
                                                    ()) _ (by omega)
                                                    ⟨scr6.set ((opp_mask +
                                                      kz).setWidth 64).toNat 0#32,
                                                     by simp [hsc6], by omega, rfl,
                                                       fun idx hidx hor => by
                                                       have hne : idx ≠ ((opp_mask +
                                                         kz).setWidth 64).toNat := by
                                                         rw [m6_zext32_toNat, hm6_bd.1]
                                                         rcases hom_k with rfl | rfl <;> (
                                                           simp only [BitVec.toNat_ofNat] at hm6_bd
                                                           simp only [BitVec.toNat_ofNat]
                                                           omega)
                                                       rw [List.getElem?_set_ne hne.symm]; exact
                                                         hout6 idx hidx hor,
                                                     hm⟩
                                                · have hdw6 :=
                                                    m8_fullDenseInvW_lm_scr hdw0 hlm5 hclr5 hsc6
                                                  c0_hsteps!
                                                  exact hQ false lm5 scr6 m6 hdw6 hsc6
                                                    (fun idx hidx hor =>
                                                      hout6 idx hidx (by omega)) hm6
                                              · intro L6 hL6; c0_hsteps!
                                                exact hL6 64 (0#32, ()) m5 ⟨scr4, hsc4,
                                                  Nat.zero_le _, rfl, hout4, hm5⟩
                                            · intro _ hJfin
                                              c0_hsplit
                                              · c0_hsplit
                                                · have hfm_bd :=
                                                    m8_mask_idx_lo lit_mask found_i hlm_k (by omega)
                                                  have hfm_sc : ((lit_mask +
                                                    (found_i >>> (5 : Nat))).setWidth 64).toNat <
                                                      scr4.length := by
                                                    rw [hsc4, m6_zext32_toNat]; omega
                                                  have h4130 : 4130 < scr4.length := by
                                                    rw [hsc4]; omega
                                                  have h4131 : 4131 < scr4.length := by
                                                    rw [hsc4]; omega
                                                  c0_hsteps!
                                                  refine hQ true lm5 _ _ ?_ (by simp [hsc4]) ?_ hm
                                                  · exact m8_fullDenseInvW_lm_scr hdw0 hlm5 hclr5
                                                      (by simp [hsc4])
                                                  · intro idx hidx hor
                                                    have hne1 : idx ≠ ((lit_mask +
                                                      (found_i >>> (5 : Nat))).setWidth
                                                        64).toNat := by
                                                      rw [m6_zext32_toNat, hfm_bd.1]
                                                      rcases hlm_k with rfl | rfl <;>
                                                        simp only [BitVec.toNat_ofNat] at hfm_bd ⊢
                                                          <;> omega
                                                    rw [List.getElem?_set_ne (by
                                                        rw [show (4131#64).toNat = 4131 from rfl]
                                                        omega),
                                                      List.getElem?_set_ne (by
                                                        rw [show (4130#64).toNat = 4130 from rfl]
                                                        omega),
                                                      List.getElem?_set_ne hne1.symm]
                                                    exact hout4 idx hidx (by omega)
                                                · c0_hsteps!; exact hJfin () m5 rfl
                                              · c0_hsteps!; exact hJfin () m5 rfl
                                        · intro L5 hL5; c0_hsteps!
                                          exact hL5 fsz.toNat (0#32, ()) m4
                                            ⟨lm4, hlm4, Nat.zero_le _, by simp, fun x hx hnz => by
                                              obtain ⟨hm_mem, hm_ne⟩ := hmk4 x hx hnz
                                              rw [mem_fullArenaClauseLitsCore_iff (by
                                                rw [hdw0.1.core_ok.arena_len_arr]; omega)] at hm_mem
                                              obtain ⟨t, ht, hxt⟩ := hm_mem
                                              have ht_ar : wf.toNat + 3 + t <
                                                s0.core.arena.length := by
                                                rw [hdw0.1.core_ok.arena_len_arr]; omega
                                              exact ⟨t, Nat.zero_le _, by omega, by
                                                intro heq; apply hm_ne
                                                rw [List.getElem?_eq_getElem ht_ar,
                                                  Option.getD_some] at heq
                                                rw [← hxt, heq],
                                                by
                                                  rw [BitVec.toNat_xor,
                                                    show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                    List.getElem?_eq_getElem ht_ar,
                                                      Option.getD_some,
                                                    hxt, Nat.xor_assoc,
                                                      show (1 ^^^ 1 : Nat) = 0 from rfl,
                                                    Nat.xor_zero]⟩,
                                             hm4⟩
                                    · intro L4 hL4; c0_hsteps!; exact hL4 opp_n.toNat (0#32, 0#32,
                                        ()) m3
                                        ⟨lm3, s0.scratch.scratch_buf, hlm3, Nat.zero_le _, by simp,
                                         hmk3, hdw0.1.scratch_ok.scratch_buf_len, fun _ _ _ => rfl,
                                           hm3⟩
                                · intro L3 hL3; c0_hsteps!; exact hL3 fsz.toNat (0#32, 0#32, ()) m2
                                    ⟨lm2, hlm2, Nat.zero_le _, by simp, fun x hx hnz =>
                                      absurd (hclr2 x hx) hnz, hm2⟩
                          · intro L2 hL2; c0_hsteps!
                            exact hL2 opp_n.toNat (0#32, ()) _
                              ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
                                obtain ⟨u, hu, hwu⟩ := hmk1 x hx hnz
                                exact ⟨u, Nat.zero_le _, by omega, hwu⟩, hm1⟩
                        · rintro Bi Li rem_i ⟨i, ⟨⟩⟩ mi hBi hLi ⟨hmi, hi_le, rfl⟩
                          subst mi
                          c0_hsplit
                          · have hi_lt : i.toNat < lit_n.toNat := hc
                            have hi_sc : ((lit_off + i).setWidth 64).toNat <
                                s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                            have hi_eq : ((lit_off + i).setWidth 64).toNat =
                                lit_off.toNat + i.toNat := by
                              rw [m6_zext32_toNat]; c0_bound
                            let w := s0.scratch.scratch_buf[((lit_off + i).setWidth 64).toNat]'hi_sc
                            have hw_get : s0.scratch.scratch_buf[lit_off.toNat +
                              i.toNat]?.getD 0#32 = w := by
                              rw [List.getElem?_eq_getElem (by
                                rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                              exact m6_getElem_congr hi_eq.symm _ hi_sc
                            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [i32]) (fun _ mi' => mi' = m1)
                              ?_ ?_
                            · rintro _ _ mi' hmi'
                              subst mi'
                              c0_hsteps!
                              exact hLi (lit_n.toNat - (i + 1#32).toNat) (i + 1#32, ()) m1
                                (by omega) ⟨rfl, by omega, rfl⟩
                            · intro _ hJi
                              c0_hsplit
                              · have hw_nb : (w &&& 0x80000000#32) = 0#32 := hc
                                have hw_ent := hl_ok' i.toNat hi_lt
                                rw [hw_get] at hw_ent; unfold FullBveEntryOkW at hw_ent
                                rw [ite_eq_right (fun h => h hw_nb)] at hw_ent
                                have hwf := hdw0.2.1.arena.refs_wf w.toNat hw_ent.1
                                have hw_bd : w.toNat + 3 + fullArenaClauseSizeCore s0.core w.toNat ≤
                                    c.arena_cap := by
                                  have := hwf.2.2.1; have := hwf.2.2.2.1; omega
                                have hw2_ar : (w.setWidth 64 + 2#64).toNat <
                                  s0.core.arena.length := by
                                  rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add,
                                    m6_zext32_toNat,
                                    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                  omega
                                let sz := s0.core.arena[(w.setWidth 64 + 2#64).toNat]'hw2_ar
                                have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat :=
                                  by
                                  unfold sz fullArenaClauseSizeCore
                                  rw [List.getElem?_eq_getElem (by
                                    rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                  exact congrArg BitVec.toNat (m6_getElem_congr (by
                                    rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega)]) _ _)
                                c0_hsteps_nogrp
                                refine wp_loop_break_group (brkTs := [.bool, i32, i32])
                                  (lpTs := [i32, i32])
                                  (fun (ok_b, need_b, _, ()) mr => mr = m1)
                                  (fun rem_k (need_k, k, ()) mk => mk = m1 ∧ k.toNat ≤ sz.toNat ∧
                                    rem_k = sz.toNat - k.toNat)
                                  ?_ ?_ ?_
                                · rintro _ ⟨ok_b, need_b, _, ⟨⟩⟩ mr hmr
                                  subst mr
                                  c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps!
                                      exact hBi (i, i, ()) m1
                                        ⟨rfl, Or.inr ⟨hi_lt, by rw [hw_get]; exact hw_nb⟩⟩
                                    · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                                  · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                                · rintro Bk Lk rem_k ⟨need_k, k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                                  subst mk
                                  c0_hsplit
                                  · have hk_lt : k.toNat < sz.toNat := hc
                                    have hwk_eq : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                                        w.toNat + 3 + k.toNat := by
                                      rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                                        m6_zext32_toNat, BitVec.toNat_ofNat]
                                      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                                    have hwk : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                                        s0.core.arena.length := by
                                      rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                                    let l := s0.core.arena[(w.setWidth 64 + 3#64 +
                                      k.setWidth 64).toNat]'hwk
                                    have hl_mem : l.toNat ∈ fullArenaClauseLitsCore s0.core
                                      w.toNat := by
                                      rw [mem_fullArenaClauseLitsCore_iff (by
                                        rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                                      exact ⟨k.toNat, by omega,
                                        congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                                    have hl_lt : l.toNat < 2 * s0.core.cur_vars :=
                                      hdw0.2.1.arena.lits_lt w.toNat hw_ent.1 hw_ent.2 _ hl_mem
                                    have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                                      rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                                    have hln_lm : ((l ^^^ 1#32).setWidth 64).toNat < lm1.length :=
                                      by
                                      have := (m8_bv32_xor1_lt l hl_lt).2
                                      rw [hlm1, m6_zext32_toNat]; omega
                                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                                    c0_hsteps_nogrp
                                    refine wp_join_state_pure (ts := [.bool, i32]) (α := BitVec 32)
                                      (fun x => (true, x, ())) (fun _ => True)
                                      ?_ ?_
                                    · rintro _ need' _
                                      c0_hsteps!
                                      exact hLk (sz.toNat - (k + 1#32).toNat)
                                        (need', k + 1#32, ()) m1 (by omega)
                                        ⟨rfl, by omega, rfl⟩
                                    · intro Jk hJk
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        · c0_hsteps!; exact hBk (false, need_k, k, ()) m1 rfl
                                        · refine wp_join_state_pure (ts := [.bool, i32])
                                            (α := BitVec 32) (fun x => (true, x, ()))
                                            (fun _ => True)
                                            (fun _ nd' _ => by c0_hsteps!; exact hJk nd' trivial)
                                            (fun _ hJkn => by
                                              c0_hsplit
                                              · c0_hsplit
                                                · c0_hsteps!; exact hBk (false, need_k, k,
                                                    ()) m1 rfl
                                                · c0_hsteps!; exact hJkn (need_k + 1#32) trivial
                                              · c0_hsteps!; exact hJkn need_k trivial)
                                      · c0_hsteps!; exact hJk need_k trivial
                                  · c0_hsteps!; exact hBk (true, need_k, k, ()) m1 rfl
                                · intro _ Lk _ hLk; c0_hsteps!; exact hLk sz.toNat (0#32, 0#32,
                                    ()) m1
                                    ⟨rfl, Nat.zero_le _, by simp⟩
                              · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                          · c0_hsteps!; exact hBi (0xFFFFFFFF#32, i, ()) m1 ⟨rfl, Or.inl rfl⟩
                        · intro _ Li _ hLi; c0_hsteps!; exact hLi lit_n.toNat (0#32, ()) m1
                            ⟨rfl, Nat.zero_le _, by simp⟩
          · intro L1 hL1; c0_hsteps!
            exact hL1 opp_n.toNat (0#32, 0#32, ()) m0
              ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
               fun x hx hnz => absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩
        · intro Jom hJom
          c0_hsplit <;> (c0_hsteps!; exact hJom _ (by simp))
      · intro Jom hJom
        c0_hsplit <;> (c0_hsteps!; exact hJom _ (by simp))
    · intro Jom hJom
      c0_hsplit
      · c0_hsteps!; exact hJom _ (by rw [ite_eq_left (show lit &&& 1#32 ≠ 0#32 from hc)]; rfl)
      · c0_hsteps!; exact hJom _ (by rw [ite_eq_right (fun h =>
          h (show lit &&& 1#32 = 0#32 from hc))]; rfl)
  · intro Jom hJom
    c0_hsplit
    · c0_hsteps!; exact hJom _ (by rw [ite_eq_left (show lit &&& 1#32 ≠ 0#32 from hc)]; rfl)
    · c0_hsteps!; exact hJom _ (by rw [ite_eq_right (fun h =>
        h (show lit &&& 1#32 = 0#32 from hc))]; rfl)


end LeanQbe.T.Examples.Kissat.FullM8CoreParity

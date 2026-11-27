/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpHelpers

/-!
# Kissat Gates WP Proofs — M7 Basic (`get_tern`, `find_equiv`, `match_tern`, `xor_pat`)

`CanonicalEnv`-clean `Func.wp` proofs for the `4` leaf M7 gate-extraction functions of
`Kissat/Src/Gates.lean` (`0` legacy `Full*` imports; every decl `<= 450` LOC):
- `full_bve_get_tern_m7_wp`
- `full_bve_find_equiv_m7_wp`
- `full_bve_match_tern_m7_wp`
- `full_bve_xor_pat_m7_wp`
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

/-! ## 1. `full_bve_get_tern_m7` -/

/-- Canonical `Func.wp` proof for `full_bve_get_tern_m7`. -/
theorem full_bve_get_tern_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveGetTernM7Spec a m Q X →
      Func.wp Γ full_bve_get_tern_m7_body a m Q X := by
  rintro ⟨h, v_lit, cr, out_off, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, href, hng, hout, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx harc hsc
  have hwf := hdw0.2.1.arena.refs_wf cr.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let sz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_bve_get_tern_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32, i32, i32])
    (fun rem (cnt, l0, l1, i, ()) mi =>
      mi = m0 ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat)
    ?_ ?_
  · rintro L rem ⟨cnt, l0, l1, i, ⟨⟩⟩ mi hL ⟨hm_eq, hi_le, rfl⟩
    subst mi
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := hc
      have hcri : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
      let li := s0.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
      have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
        have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
          exact ⟨i.toNat, by omega, congrArg BitVec.toNat (getElem_congr (by c0_bound) _ _)⟩
        exact hdw0.2.1.arena.lits_lt cr.toNat href hng _ hmem
      have hli_v : (li.setWidth 64).toNat < s0.core.vals.length := by
        rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32, i32, i32]) (α := BitVec 32 × BitVec 32 × BitVec 32)
        (fun x => (x.1, x.2.1, x.2.2, ())) (fun _ => True)
        (fun _ ⟨c', a', b'⟩ _ => by
          c0_hsteps!
          exact hL (sz.toNat - (i + 1#32).toNat) (c', a', b', i + 1#32, ()) m0 (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun J hJ => by
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!
              exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
                (fun _ _ _ => rfl) hm0
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32, i32, i32])
                (α := BitVec 32 × BitVec 32 × BitVec 32)
                (fun x => (x.1, x.2.1, x.2.2, ())) (fun _ => True)
                (fun _ x _ => by c0_hsteps!; exact hJ x trivial)
                (fun J37 hJ37 => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                      (fun p => (p.1, p.2, ())) (fun _ => True)
                      (fun _ ⟨a', b'⟩ _ => by
                        c0_hsteps!; exact hJ37 (cnt + 1#32, a', b') trivial)
                      (fun J42 hJ42 => by
                        c0_hsplit
                        · c0_hsteps!; exact hJ42 (li, l1) trivial
                        · c0_hsplit
                          · c0_hsteps!; exact hJ42 (l0, li) trivial
                          · c0_hsteps!
                            exact hQ false s0.scratch.scratch_buf m0
                              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0)
                  · c0_hsteps!; exact hJ37 (cnt, l0, l1) trivial)
          · c0_hsteps!; exact hJ (cnt, l0, l1) trivial)
    · c0_hsplit
      · c0_hsteps!
        exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
          (fun _ _ _ => rfl) hm0
      · have ho0 : (out_off.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; omega
        have ho1 : ((out_off + 1#32).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
        c0_hsteps!
        exact hQ true _ _ (by simp [hdw0.1.scratch_ok.scratch_buf_len])
          (fun i hi hor => by
            rw [List.getElem?_set_ne (by rw [zext32_toNat]; c0_bound),
              List.getElem?_set_ne (by rw [zext32_toNat]; omega)]) hm
  · intro L hL; c0_hsteps!
    exact hL sz.toNat (0#32, 0#32, 0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩

/-! ## 2. `full_bve_find_equiv_m7` -/

/-- Canonical `Func.wp` proof for `full_bve_find_equiv_m7`. -/
theorem full_bve_find_equiv_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveFindEquivM7Spec a m Q X →
      Func.wp Γ full_bve_find_equiv_m7_body a m Q X := by
  rintro ⟨h, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1088, hnp512, hnn512, hp_ok, hn_ok, hm0, hQ⟩ :=
    fullBveFindEquivM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  unfold Func.wp full_bve_find_equiv_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32])
    (fun rem1 (bin_p, i, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧ i.toNat ≤ np.toNat ∧ rem1 = np.toNat - i.toNat ∧
      bin_p.toNat ≤ i.toNat ∧
      (bin_p = 0#32 → ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8) ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        ∃ u < i.toNat, let w := s0.scratch.scratch_buf[u]?.getD 0#32;
          (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro L1 rem1 ⟨bin_p, i, ⟨⟩⟩ m1 hL1 ⟨lm1, hlm1, hi_le, rfl, hbp_le, hbp0, hmark1, hm1⟩
    c0_hsplit
    · have hi_lt : i.toNat < np.toNat := hc
      have hi_sc : (i.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; omega
      let wp := s0.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sc
      have hwp_get : s0.scratch.scratch_buf[i.toNat]?.getD 0#32 = wp := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact getElem_congr (zext32_toNat i).symm _ _
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8)) (fun x => (x.1, ()))
        (fun x mj => x.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
          (x.1 = 0#32 → ∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 = 0#8) ∧
          (∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 ≠ 0#8 →
            ∃ u < i.toNat + 1, let w := s0.scratch.scratch_buf[u]?.getD 0#32;
              (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
        (fun _ ⟨bp', lm'⟩ mj ⟨hlm', hbp', hbp0', hmk', hmj⟩ => by
          dsimp only at hbp' hbp0' hmk' hmj
          c0_hsteps!
          exact hL1 (np.toNat - (i + 1#32).toNat) (bp', i + 1#32, ()) mj (by omega)
            ⟨lm', hlm', by omega, rfl, by omega, hbp0', fun z hz hnz => by
              obtain ⟨u, hu, hw⟩ := hmk' z hz hnz; exact ⟨u, by omega, hw⟩, hmj⟩)
        (fun J1 hJ1 => by
          have hkeep : J1 (bin_p, ()) m1 := by
            refine hJ1 (bin_p, lm1) m1 ⟨hlm1, by dsimp only; omega, hbp0, fun z hz hnz => ?_, hm1⟩
            obtain ⟨u, hu, hw⟩ := hmark1 z hz hnz; exact ⟨u, by omega, hw⟩
          c0_hsplit
          · have hwp_bin : (wp &&& 0x80000000#32) ≠ 0#32 := hc
            have hot_lt : (wp &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
              have h1 := hp_ok i.toNat hi_lt; dsimp only at h1; rw [hwp_get] at h1
              exact h1 hwp_bin
            have hot_v : ((wp &&& 0x7FFFFFFF#32).setWidth 64).toNat < s0.core.vals.length := by
              rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
              (fun x => (x.1, ()))
              (fun x mj => x.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
                (x.1 = 0#32 → ∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 = 0#8) ∧
                (∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 ≠ 0#8 →
                  ∃ u < i.toNat + 1, let w := s0.scratch.scratch_buf[u]?.getD 0#32;
                    (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
                (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
              (fun _ ⟨bp', lm'⟩ mj ⟨hlm', hbp', hbp0', hmk', hmj⟩ => by
                dsimp only at hbp' hbp0' hmk' hmj
                c0_hsteps!
                exact hJ1 (bp', lm') mj ⟨hlm', hbp', hbp0', hmk', hmj⟩)
              (fun J1i hJ1i => by
                c0_hsplit
                · have hot_lm : ((wp &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm1.length := by
                    rw [hlm1, zext32_toNat]; omega
                  have hbp1 : (bin_p + 1#32).toNat = bin_p.toNat + 1 := by c0_bound
                  have hcv := hdw0.1.core_ok.cur_vars_le
                  let lm_n := lm1.set ((wp &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8
                  have hbp_n_le : (bin_p + 1#32).toNat ≤ i.toNat + 1 := by omega
                  have hbp_n_ne : ∀ h : bin_p + 1#32 = 0#32, False := fun h => by
                    have h0 : (bin_p + 1#32).toNat = 0 := congrArg BitVec.toNat h
                    rw [hbp1] at h0; omega
                  c0_hsteps!
                  exact hJ1i (bin_p + 1#32, lm_n) _
                    ⟨by simp [lm_n, hlm1], by dsimp only; omega,
                      fun h => False.elim (hbp_n_ne h),
                      lm_set_at hlm1 (by rw [zext32_toNat]; omega)
                        (fun z hz hnz => by
                          obtain ⟨u, hu, hw⟩ := hmark1 z hz hnz; exact ⟨u, by omega, hw⟩)
                        ⟨i.toNat, by omega,
                          by rw [hwp_get, zext32_toNat]; exact ⟨hwp_bin, rfl⟩⟩,
                      hm⟩
                · c0_hsteps!
                  exact hJ1i (bin_p, lm1) m1
                    ⟨hlm1, by dsimp only; omega, hbp0, fun z hz hnz => by
                      obtain ⟨u, hu, hw⟩ := hmark1 z hz hnz; exact ⟨u, by omega, hw⟩, hm1⟩)
          · c0_hsteps!; exact hkeep)
    · have hi_eq : i.toNat = np.toNat := by omega
      c0_hsplit
      · have hclr1 : ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8 := hbp0 hc
        let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
        have hdw1 := fullDenseInvW_lm_scr hdw0 hlm1 hclr1 hdw0.1.scratch_ok.scratch_buf_len
        c0_hsteps!; exact hQ false lm1 s0.scratch.scratch_buf m1 hdw1
          hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm1
      · c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i32, i32, i32]) (lpTs := [i32])
          (fun (ml_b, mj_b, _, ()) mb => mb = m1 ∧
            (ml_b = 0xFFFFFFFF#32 ∨ mj_b.toNat < nn.toNat))
          (fun rem2 (j, ()) m2 => m2 = m1 ∧ j.toNat ≤ nn.toNat ∧ rem2 = nn.toNat - j.toNat)
          ?_ ?_ ?_
        · rintro _ ⟨ml_b, mj_b, _, ⟨⟩⟩ mb ⟨hmb, hmb_ok⟩
          subst mb
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem3 (ic, ()) m3 => ∃ lm3 : List (BitVec 8),
              let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
              lm3.length = 2 * c.max_vars ∧ ic.toNat ≤ np.toNat ∧
              rem3 = np.toNat - ic.toNat ∧
              (∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 ≠ 0#8 →
                ∃ u, ic.toNat ≤ u ∧ u < np.toNat ∧
                  let w := s0.scratch.scratch_buf[u]?.getD 0#32;
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
                exact getElem_congr (zext32_toNat ic).symm _ _
              have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by c0_bound
              have hcv := hdw0.1.core_ok.cur_vars_le
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ m3' => ∃ lm3' : List (BitVec 8),
                  let s3' : FullState := { s0 with core := { s0.core with lit_mark := lm3' } }
                  lm3'.length = 2 * c.max_vars ∧
                  (∀ x < 2 * c.max_vars, lm3'[x]?.getD 0#8 ≠ 0#8 →
                    ∃ u, ic.toNat + 1 ≤ u ∧ u < np.toNat ∧
                      let w := s0.scratch.scratch_buf[u]?.getD 0#32;
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
                       lm_clear_step_maxv hlm3 (by rw [zext32_toNat]; omega) (fun y hy hnz => by
                         obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem3 y hy hnz
                         rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                         · left; rw [zext32_toNat, hyeq, hwc_get]
                         · right; exact ⟨u, by omega, hu2, hwu, hyeq⟩), hm⟩
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
                have hmj_m : (1040#32 + (mj_b >>> (5 : Nat))).toNat <
                    s0.scratch.scratch_buf.length := by
                  have hb := m7_mask_idx_lo 1040#32 mj_b (Or.inr rfl) (by omega)
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
                          · have him_m : (1024#32 + (im >>> (5 : Nat))).toNat <
                                s0.scratch.scratch_buf.length := by
                              have hb := m7_mask_idx_lo 1024#32 im (Or.inl rfl) (by omega)
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            have h1056 : 1056 < s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            have h1057 : 1057 < s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            c0_hsteps!
                            have hlen0 := hdw0.1.scratch_ok.scratch_buf_len
                            have him_bd := m7_mask_idx_lo 1024#32 im (Or.inl rfl) (by omega)
                            have hmj_bd := m7_mask_idx_lo 1040#32 mj_b (Or.inr rfl) (by omega)
                            refine hQ true lm3 ?_ m ?_ ?_ ?_ ?_
                            rotate_left 4
                            · exact hm
                            · exact fullDenseInvW_lm_scr hdw0 hlm3 hclr3 (by simp [hlen0])
                            · simp [hlen0]
                            · have him_idx :
                                  ((1024 + im >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    1024 + im.toNat / 32 := by
                                rw [zext32_toNat, BitVec.toNat_add,
                                  show (1024 : BitVec 32).toNat = 1024 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              have hmj_idx :
                                  ((1040 + mj_b >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    1040 + mj_b.toNat / 32 := by
                                rw [zext32_toNat, BitVec.toNat_add,
                                  show (1040 : BitVec 32).toNat = 1040 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              intro idx hidx hor
                              rw [him_idx, hmj_idx,
                                List.getElem?_set_ne
                                  (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                                List.getElem?_set_ne
                                  (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
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
            have hj_sc : ((512#32 + j).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
              rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
            let wn := s0.scratch.scratch_buf[((512#32 + j).setWidth 64).toNat]'hj_sc
            have hwn_get : s0.scratch.scratch_buf[512 + j.toNat]?.getD 0#32 = wn := by
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
                  have hotn_lt :
                      ((wn &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
                    change (wn &&& 0x7FFFFFFF#32).toNat ^^^ 1 < 2 * s0.core.cur_vars
                    have := fullInv_var_xor1 (wn &&& 0x7FFFFFFF#32).toNat; omega
                  have hotn_lm : (((wn &&& 0x7FFFFFFF#32) ^^^ 1#32).setWidth 64).toNat <
                      lm1.length := by
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
      ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
       Nat.zero_le _, fun _ => hdw0.2.2.1.2, fun x hx hnz =>
         absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩

/-! ## 3. `full_bve_match_tern_m7` -/

/-- Canonical `Func.wp` proof for `full_bve_match_tern_m7`. -/
theorem full_bve_match_tern_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveMatchTernM7Spec a m Q X →
      Func.wp Γ full_bve_match_tern_m7_body a m Q X := by
  rintro ⟨h, opp_lit, x, y, opp_off, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hooff, hon512, hent_n, hm0, hQ⟩ :=
    fullBveMatchTernM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  unfold Func.wp full_bve_match_tern_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (j, ()) mj => ∃ scr_j : List (BitVec 32),
      let sj : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_j } }
      scr_j.length = c.scratch_cap ∧ j.toNat ≤ opp_n.toNat ∧ rem = opp_n.toNat - j.toNat ∧
      (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
        scr_j[i]? = s0.scratch.scratch_buf[i]?) ∧
      (FullMem c sj ⋆ R) mj)
    ?_ ?_
  · rintro L rem ⟨j, ⟨⟩⟩ mj hL ⟨scr_j, hscj, hj_le, rfl, hout_j, hmj⟩
    have h1058 : 1058 < scr_j.length := by rw [hscj]; omega
    c0_hsplit
    · c0_hsplit
      · have hj_lt : j.toNat < opp_n.toNat := by assumption
        have hoj_sc : ((opp_off + j).setWidth 64).toNat < scr_j.length := by
          rw [hscj, zext32_toNat]; c0_bound
        have hwj_orig :
            scr_j[((opp_off + j).setWidth 64).toNat]'hoj_sc =
              s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
            rw [zext32_toNat]; c0_bound
          have hget := hout_j (opp_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
          have hoj' : opp_off.toNat + j.toNat < scr_j.length := by omega
          rw [List.getElem?_eq_getElem hoj'] at hget
          rw [← hget, Option.getD_some]
          exact getElem_congr hoj_eq hoj_sc hoj'
        let scr_s := scr_j.set 1058 (scr_j[1058]'h1058 + 1#32)
        have hsc_s : scr_s.length = c.scratch_cap := by simp [scr_s, hscj]
        have hout_s : ∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
            scr_s[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor => by
          dsimp only [scr_s]; rw [List.getElem?_set_ne (by omega)]; exact hout_j i hi hor
        have hoj_sc_s : ((opp_off + j).setWidth 64).toNat < scr_s.length := by
          rw [hsc_s, zext32_toNat]; c0_bound
        have hwj_s : scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s =
            s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          rw [← hwj_orig]
          dsimp only [scr_s]
          rw [List.getElem_set_ne (by c0_bound)]
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mj' => mj' = m)
          (fun _ _ mj' hmj' => by
            subst mj'
            c0_hsteps!
            exact hL (opp_n.toNat - (j + 1#32).toNat) (j + 1#32, ()) m
              (by omega) ⟨scr_s, hsc_s, by omega, rfl, hout_s, hm⟩)
          (fun _ hJj => by
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ mb' => mb' = m)
                (fun _ _ mb' hmb' => by
                  subst mb'
                  c0_hsteps!; exact hQ (j ||| 0x80000000#32) scr_s m hsc_s hout_s
                    (Or.inr (by rw [u32_and7fff_or8000_toNat j (by omega)]; exact hj_lt)) hm)
                (fun _ hJret => by
                  c0_hsplit
                  · c0_hsteps!; exact hJret () m rfl
                  · c0_hsplit
                    · c0_hsteps!; exact hJret () m rfl
                    · c0_hsteps!; exact hJj () m rfl)
            · let w := scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s
              have hent_j := hent_n j.toNat hj_lt
              rw [← hwj_s] at hent_j; unfold FullBveEntryOkW at hent_j
              rw [ite_eq_right (fun h => h hc)] at hent_j
              have href_j : w.toNat ∈ fullArenaClauseRefs s0 := hent_j.1
              have hng_j : fullArenaClauseGarb s0 w.toNat = false := hent_j.2
              have hwf := hdw0.2.1.arena.refs_wf w.toNat href_j
              have hw_bd : w.toNat + 3 + fullArenaClauseSizeCore s0.core w.toNat ≤
                  c.arena_cap := by
                have := hwf.2.2.1; have := hwf.2.2.2.1; omega
              have hsz_ge : 3 ≤ fullArenaClauseSizeCore s0.core w.toNat := hwf.2.1
              have hw2_ar : (w.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, zext32_toNat,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                omega
              let sz := s0.core.arena[(w.setWidth 64 + 2#64).toNat]'hw2_ar
              have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat := by
                unfold sz fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (getElem_congr (by
                  rw [BitVec.toNat_add, zext32_toNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega)]) _ _)
              c0_hsteps_nogrp
              refine wp_loop_break_group (brkTs := [.bool, .bool, .bool, i32])
                (lpTs := [.bool, .bool, i32])
                (fun (ok_b, sx_b, sy_b, _, ()) mb => mb = m)
                (fun rem_k (sx_k, sy_k, k, ()) mk => mk = m ∧ k.toNat ≤ sz.toNat ∧
                  rem_k = sz.toNat - k.toNat)
                ?_ ?_ ?_
              · rintro _ ⟨ok_b, sx_b, sy_b, _, ⟨⟩⟩ mb hmb
                subst mb
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mb' => mb' = m)
                  (fun _ _ mb' hmb' => by subst mb'; c0_hsteps!; exact hJj () m rfl)
                  (fun _ hJskip => by
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ ms' => ms' = m)
                        (fun _ _ ms' hms' => by
                          subst ms'
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ mo' => mo' = m)
                            (fun _ _ mo' hmo' => by
                              subst mo'
                              c0_hsteps!
                              exact hQ (j ||| 0x80000000#32) scr_s m hsc_s hout_s
                                (Or.inr (by
                                  rw [u32_and7fff_or8000_toNat j (by omega)]; exact hj_lt)) hm)
                            (fun _ hJor => by
                              c0_hsplit
                              · c0_hsteps!; exact hJor () m rfl
                              · c0_hsplit
                                · c0_hsteps!; exact hJor () m rfl
                                · c0_hsteps!; exact hJskip () m rfl))
                        (fun _ hJns => by
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps!; exact hQ j scr_s m hsc_s hout_s
                                (Or.inr (by
                                  rw [u32_and7fff_self j (by omega)]; exact hj_lt)) hm
                            · c0_hsteps!; exact hJns () m rfl
                          · c0_hsteps!; exact hJns () m rfl)
                    · c0_hsteps!; exact hJskip () m rfl)
              · rintro Bk Lk rem_k ⟨sx_k, sy_k, k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                subst mk
                c0_hsplit
                · have hk_lt : k.toNat < sz.toNat := hc
                  have hwk_eq : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                      w.toNat + 3 + k.toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add, zext32_toNat,
                      zext32_toNat, BitVec.toNat_ofNat]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                  have hwk : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                      s0.core.arena.length := by
                    rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                  let l := s0.core.arena[(w.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                  have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
                    have hmem : l.toNat ∈ fullArenaClauseLitsCore s0.core w.toNat := by
                      rw [mem_fullArenaClauseLitsCore_iff (by
                        rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                      exact ⟨k.toNat, by omega,
                        congrArg BitVec.toNat (getElem_congr hwk_eq.symm _ _)⟩
                    exact hdw0.2.1.arena.lits_lt w.toNat href_j hng_j _ hmem
                  have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                    rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
                  have hk1 : (k + 1 : BitVec 32).toNat = k.toNat + 1 := by c0_bound
                  c0_hsplit
                  · c0_hsteps!; exact hBk (false, sx_k, sy_k, k, ()) m rfl
                  · c0_hsteps_nogrp
                    refine wp_join_group (fun _ mk' => mk' = m)
                      (fun _ _ mk' hmk' => by
                        subst mk'
                        c0_hsteps!
                        exact hLk (sz.toNat - (k + 1 : BitVec 32).toNat) _ m (by omega)
                          ⟨rfl, by omega, rfl⟩)
                      (fun _ hJk => by
                        c0_hsplit
                        · c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_group (fun _ mk' => mk' = m)
                              (fun _ _ mk' hmk' => by subst mk'; c0_hsteps!; exact hJk _ m rfl)
                              (fun _ hJxy => by
                                c0_hsplit
                                · c0_hsteps!; exact hJxy _ m rfl
                                · c0_hsplit
                                  · c0_hsteps!; exact hJxy _ m rfl
                                  · c0_hsteps!; exact hBk (false, sx_k, sy_k, k, ()) m rfl)
                          · c0_hsteps!; exact hJk _ m rfl
                        · c0_hsteps!; exact hJk _ m rfl)
                · c0_hsteps!; exact hBk (true, sx_k, sy_k, k, ()) m rfl
              · intro _ Lk _ hLk; c0_hsteps!
                exact hLk sz.toNat (false, false, 0#32, ()) m ⟨rfl, Nat.zero_le _, by simp⟩)
      · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
  · intro L hL; c0_hsteps!
    exact hL opp_n.toNat (0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
       fun _ _ _ => rfl, hm0⟩

/-! ## 4. `full_bve_xor_pat_m7` -/

/-- Canonical `Func.wp` proof for `full_bve_xor_pat_m7` (read-only). -/
theorem full_bve_xor_pat_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveXorPatM7Spec a m Q X →
      Func.wp Γ full_bve_xor_pat_m7_body a m Q X := by
  rintro ⟨h, v_lit, cr, k, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hlen0, hw0, href, hng, hk1, hk4, hm0, hQ⟩ :=
    fullBveXorPatM7Spec_elim hSpec
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf := hw0.arena.refs_wf cr.toNat href
  have hal_le := hlen0.core_ok.arena_len_le
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hlen0.core_ok.arena_len_arr]; c0_bound
  let sz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_bve_xor_pat_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32, i32])
    (fun rem (pat, seen, i, ()) mi =>
      mi = m0 ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧ pat.toNat < 16)
    ?_ ?_
  · rintro L rem ⟨pat, seen, i, ⟨⟩⟩ mi hL ⟨rfl, hi_le, rfl, hpat_lt⟩
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := hc
      have hcri : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
        rw [hlen0.core_ok.arena_len_arr]; c0_bound
      let li := s0.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
      have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
        have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hlen0.core_ok.arena_len_arr]; omega)]
          exact ⟨i.toNat, by omega, congrArg BitVec.toNat (getElem_congr (by c0_bound) _ _)⟩
        exact hw0.arena.lits_lt cr.toNat href hng _ hmem
      have hli_v : (li.setWidth 64).toNat < s0.core.vals.length := by
        rw [hlen0.core_ok.vals_len, zext32_toNat]; omega
      have hli_lm : (li.setWidth 64).toNat < s0.core.lit_mark.length := by
        rw [hlen0.core_ok.lit_mark_len, zext32_toNat]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
        (fun x => (x.1, x.2, ())) (fun x => x.1.toNat < 16)
        (fun _ ⟨pat', seen'⟩ hpat' => by
          c0_hsteps!
          exact hL (sz.toNat - (i + 1#32).toNat) (pat', seen', i + 1#32, ()) mi
            (by omega) ⟨rfl, by omega, rfl, hpat'⟩)
        (fun J hJ => by
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                (fun x => (x.1, x.2, ())) (fun x => x.1.toNat < 16)
                (fun _ ⟨pat', seen'⟩ hp' => by
                  c0_hsteps!; exact hJ (pat', seen') hp')
                (fun _ hJi => by
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                    · c0_hsplit
                      · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                      · c0_hsplit
                        · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                        · have hidx_ar :
                              (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64 < s0.core.arena.length := by
                            rw [hlen0.core_ok.arena_len_arr]; c0_bound
                          have hli_c0 :
                              s0.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64]'hidx_ar = li :=
                            getElem_congr (by c0_bound) _ hcri
                          have hidx_lm :
                              (s0.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64]'hidx_ar).toNat <
                                s0.core.lit_mark.length := by
                            rw [hli_c0, hlen0.core_ok.lit_mark_len]; omega
                          have hm_ge := (by assumption :
                            ((s0.core.lit_mark[(s0.core.arena[(cr.toNat +
                              BitVec.toNat (3 : BitVec 64) +
                              i.toNat) % 2 ^ 64]'hidx_ar).toNat]'hidx_lm).setWidth 32
                              ).slt 2#32 = false)
                          have hk_n := (by assumption :
                            ¬ k.toNat ≤ (2 ^ 32 - OfNat.ofNat 2 % 2 ^ 32 +
                              (s0.core.lit_mark[(s0.core.arena[(cr.toNat +
                                BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64]'hidx_ar).toNat]'hidx_lm).toNat) %
                                2 ^ 32 / 2)
                          have hm_ge_li :
                              ((s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm).setWidth 32
                                ).slt 2#32 = false := by
                            simpa only [zext32_toNat, ← hli_c0] using hm_ge
                          have hk_n_li :
                              ¬ k.toNat ≤ (2 ^ 32 - 2 % 2 ^ 32 +
                                (s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm).toNat) %
                                  2 ^ 32 / 2 := by
                            simpa only [zext32_toNat, ← hli_c0] using hk_n
                          have hidx_lt :
                              (((s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm).setWidth 32 -
                                2#32) >>> (1 : Nat)).toNat < 4 := by
                            have hlt := m7_xor_idx_lt
                              (s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm) k
                              hm_ge_li hk_n_li
                            omega
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                            (fun x => (x, ())) (fun x => x.toNat < 16)
                            (fun _ pat' hp' => by
                              c0_hsteps!; exact hJi (pat', seen ||| _) hp')
                            (fun _ hJp => by
                              c0_hsplit
                              · c0_hsteps!
                                refine hJp _ (by
                                  rw [BitVec.toNat_or]
                                  refine Nat.or_lt_two_pow
                                    (show pat.toNat < 2 ^ 4 from hpat_lt) ?_
                                  have hbit := m7_xor_bit_lt _ hidx_lt
                                  dsimp only [li] at hbit
                                  exact hbit)
                              · c0_hsteps!; exact hJp pat hpat_lt)
                  · c0_hsteps!; exact hJi (pat, seen) hpat_lt)
          · c0_hsteps!; exact hJ (pat, seen) hpat_lt)
    · c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun r => (r, ()))
        (fun r => r = 0xFFFFFFFF#32 ∨ r.toNat < 16)
        (fun _ r hr => by c0_hsteps!; exact hQ r hr)
        (fun _ hJ => by
          c0_hsplit
          · c0_hsteps!; exact hJ pat (Or.inr hpat_lt)
          · c0_hsteps!; exact hJ 0xFFFFFFFF#32 (Or.inl rfl))
  · intro L hL; c0_hsteps!
    exact hL sz.toNat (0#32, 0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp, by decide⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Gates

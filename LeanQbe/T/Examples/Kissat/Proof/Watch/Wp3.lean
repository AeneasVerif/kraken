/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp3a
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp3b
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.C0HeadStep

/-! # Watch WP Proofs Part 3: `full_watch_push_slow_m6_wp`

Proves `Func.wp Γ full_watch_push_slow_m6_body fullWatchPushSpec` cleanly on flat
`Src.Watch` using `CanonicalEnv` (`Γ.Sat Spec.specs`) and `Proof.Watch.Wp3{a,b}` helpers. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

public section

theorem full_watch_push_slow_m6_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X, Proof.Spec.fullWatchPushSpec a m Q X →
      Func.wp Γ full_watch_push_slow_m6_body a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hw0, hw1, hm, hQ⟩
  have hcv32 : s.core.cur_vars < 2 ^ 30 :=
    Nat.lt_of_le_of_lt hlen.core_ok.cur_vars_le (Nat.lt_of_lt_of_le c.hmaxv (by decide))
  have hwcap32 : c.wcap < 2 ^ 32 := wpush_wcap_lt32 c
  have hwlen32 : s.core.wlen < 2 ^ 32 := Nat.lt_of_le_of_lt hlen.core_ok.wlen_le hwcap32
  c0_hstraight; c0_hsplit
  · c0_hstraight
    exact wpush_fail_post hQ s.core.wvec s.core.wstk s.scratch.wsort s.core.wlen s.core.wusable
      hlen hlay (watchPresAll_refl s) (Or.inl (by bv_omega)) hm
  · c0_hstraight
    have hlit : lit.toNat < 2 * s.core.cur_vars := by bv_omega
    apply wp_join_group (fun _ m0 => m0 = m ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2))
    rotate_left 1
    · intro J hJ; c0_hstraight; c0_hsplit
      · c0_hstraight; c0_hsplit
        · c0_hstraight
          exact wpush_fail_post hQ s.core.wvec s.core.wstk s.scratch.wsort s.core.wlen
            s.core.wusable hlen hlay (watchPresAll_refl s)
            (Or.inr (Or.inl ⟨by bv_omega, by bv_omega⟩)) hm
        · c0_hstraight; exact hJ () m ⟨rfl, Or.inr (by bv_omega)⟩
      · c0_hstraight; exact hJ () m ⟨rfl, Or.inl (by bv_omega)⟩
    · rintro J ⟨⟩ m0 ⟨rfl, hc12⟩
      c0_hstraight
      apply wp_join_group (fun _ m1 => ∃ s1 : FullState, WPushInvState c s R s1 m1)
      rotate_left 1
      · intro J1 hJ1; c0_hstraight; c0_hsplit
        · c0_hstraight; c0_hsplit
          · c0_hstraight
            exact wpush_fail_post hQ s.core.wvec s.core.wstk s.scratch.wsort s.core.wlen
              s.core.wusable hlen hlay (watchPresAll_refl s) (Or.inr (Or.inr (Or.inl rfl))) hm
          · have hw0_eq : s.core.wlen = 0 := by bv_omega
            have hcap1 : 1 ≤ c.wcap := by bv_omega
            have hws_pos : 0 < s.core.wstk.length := by rw [hlen.core_ok.wstk_len_arr]; omega
            c0_hstraight
            obtain ⟨hlen1, hlay1, hpres1⟩ := wpush_init_wlen0 hlen hlay hw0_eq hcap1
            refine hJ1 (true, ()) _ ⟨_, ⟨hlen1, hlay1, hpres1, Nat.le_refl 1,
              ⟨s.core.wvec, s.core.wstk.set 0 0#32, s.scratch.wsort, 1, s.core.wusable, rfl⟩,
              ?_⟩⟩
            simpa [BitVec.toNat_ofNat] using ‹(FullMem c _ ⋆ R) _›
        · c0_hstraight; exact hJ1 (false, ()) _ ⟨s, wpush_inv_state_self hlen hlay (by bv_omega) hm⟩
      · rintro J1 ⟨b_init, ⟨⟩⟩ m1 ⟨s1, hinv1⟩
        have hinv1_keep := hinv1
        obtain ⟨hlen1, hlay1, _, _, _, hm1⟩ := hinv1
        c0_hstraight
        apply wp_join_group (fun _ m2 => ∃ s2 : FullState, WPushInvState c s R s2 m2)
        rotate_left 1
        · intro J2 hJ2; c0_hstraight
          apply wp_join_group (fun _ m2 => m2 = m1)
          rotate_left 1
          · intro J3 hJ3; c0_hstraight; c0_hsplit
            · c0_hstraight; exact hJ3 () m1 rfl
            · c0_hstraight; c0_hsplit
              · c0_hstraight; exact hJ3 () m1 rfl
              · c0_hstraight; exact hJ2 (b_init, ()) m1 ⟨s1, hinv1_keep⟩
          · rintro J3 ⟨⟩ m1' rfl; c0_hstraight; c0_hsplit
            · c0_hstraight
              c0_hcall (Spec.has_full_wstack_defrag_m6 hΓ)
              · refine ⟨c, s1, R, rfl, hlen1, hlay1, hm1, fun wv' ws' wl' wso' m' => ?_⟩
                intro _ hlen' hlay' hw1' hpres' hm'
                c0_hstraight
                exact hJ2 (true, ()) m' ⟨_, wpush_inv_state_defrag hinv1_keep hlen' hlay' hw1'
                  hpres' hm'⟩
            · c0_hstraight; exact hJ2 (b_init, ()) m1' ⟨s1, hinv1_keep⟩
        · rintro J2 ⟨b_def, ⟨⟩⟩ m2 ⟨s2, hinv2⟩
          have hinv2_keep := hinv2
          have ⟨hcv2, hwl2_32, _⟩ := wpush_inv_core_eq hinv2_keep
          obtain ⟨hlen2, hlay2, hpres2, hwlen2, ⟨wv2, ws2, wso2, wl2, wu2, hs2_eq⟩, hm2⟩ := hinv2
          have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
          obtain ⟨hwv_lt0, hwv_lt1, hwv_lt0_bv, hwv_lt1_bv, hj0, hj1, hm0_, hm1_⟩ :=
            wpush_wvec_lt hlen2 hlit2
          c0_hstraight
          apply wp_join_group (fun _ m3 => m3 = m2 ∧ 0 < wOff s2.core.wvec lit.toNat)
          rotate_left 1
          · intro JA hJA; c0_hstraight
            c0_hsplit
            · c0_hstraight; c0_hsplit
              · c0_hstraight
                have hsz2_0 : wSz s2.core.wvec lit.toNat = 0 :=
                  wpush_list_zext64_eq_zero hwv_lt1 hj1 hm1_ ‹_›
                apply wp_join_group (fun _ m3 => ∃ s3 : FullState, WPushInvState c s R s3 m3 ∧
                  wSz s3.core.wvec lit.toNat = 0 ∧
                  (c.wcap - s3.core.wlen < cnt.toNat → s3.core.wusable = 0#64))
                rotate_left 1
                · intro JA1 hJA1; c0_hstraight; c0_hsplit
                  · c0_hstraight; c0_hsplit
                    · c0_hstraight
                      c0_hcall (Spec.has_full_wstack_defrag_m6 hΓ)
                      · refine ⟨c, s2, R, rfl, hlen2, hlay2, hm2, fun wv' ws' wl' wso' m' => ?_⟩
                        intro _ hlen' hlay' hw1' hpres' hm'
                        c0_hstraight
                        have hinv3 := wpush_inv_state_defrag hinv2_keep hlen' hlay' hw1' hpres' hm'
                        have hsz3 : wSz wv' lit.toNat = 0 := by
                          have hpe := (hpres' lit.toNat hlit2).1
                          change wSz wv' lit.toNat = wSz s2.core.wvec lit.toNat at hpe; omega
                        exact hJA1 () m' ⟨_, hinv3, hsz3, fun _ => rfl⟩
                    · c0_hstraight
                      exact hJA1 () m2 ⟨s2, hinv2_keep, hsz2_0,
                        fun _ => wpush_bv64_eq_zero_of_not_pos (by bv_omega)⟩
                  · c0_hstraight; have hwle2 := hlen2.core_ok.wlen_le
                    exact hJA1 () m2 ⟨s2, hinv2_keep, hsz2_0, fun hgt => by exfalso; bv_omega⟩
                · rintro JA1 ⟨⟩ m3 ⟨s3, hinv3, hsz3, hwu3⟩
                  have ⟨hcv3, hwl3_32, _⟩ := wpush_inv_core_eq hinv3
                  obtain ⟨hlen3, hlay3, hpres3, hwlen3, ⟨wv3, ws3, wso3, wl3, wu3, hs3_eq⟩,
                    hm3⟩ := hinv3
                  have hwle3 := hlen3.core_ok.wlen_le
                  c0_hstraight; c0_hsplit
                  · c0_hstraight; have hwu0 := hwu3 (by bv_omega); subst hs3_eq
                    exact wpush_fail_post hQ wv3 ws3 wso3 wl3 wu3 hlen3 hlay3 hpres3
                      (Or.inr (Or.inr (Or.inr hwu0))) hm3
                  · have hfit3 : s3.core.wlen + cnt.toNat ≤ c.wcap := by bv_omega
                    have hwstk_lt0 : s3.core.wlen < s3.core.wstk.length := by
                      rw [hlen3.core_ok.wstk_len_arr]; omega
                    c0_hstraight
                    apply wp_join_group (fun _ m4 => ∃ wstk4 : List (BitVec 32),
                        WPushAppendInv c s3 R s3.core.wlen w0 w1 cnt s3.core.wstk wstk4 m4)
                    rotate_left 1
                    · intro J4 hJ4; c0_hstraight; c0_hsplit
                      · have hc2 : cnt.toNat = 2 := by bv_omega
                        have hwstk_lt1 : s3.core.wlen + 1 <
                            (s3.core.wstk.set s3.core.wlen w0).length := by
                          simp [hlen3.core_ok.wstk_len_arr]; omega
                        c0_hstraight
                        obtain ⟨hof_wl, hof_wl1⟩ :=
                          wpush_caseA_wlen_bv (by omega : s3.core.wlen < c.wcap)
                        have hm_new := ‹(FullMem c _ ⋆ R) _›; dsimp only at hm_new
                        simp only [hof_wl, hof_wl1] at hm_new
                        exact hJ4 () _ (wpush_append_set2 hlen3.core_ok.wstk_len_arr (by omega) hc2
                          hm_new)
                      · have hcnt1 : cnt.toNat = 1 := by
                          rcases hc12 with h2 | h2; exact h2; exfalso; bv_omega
                        obtain ⟨hof_wl, _⟩ :=
                          wpush_caseA_wlen_bv (by omega : s3.core.wlen < c.wcap)
                        have hm_new := ‹(FullMem c _ ⋆ R) _›; dsimp only at hm_new
                        simp only [hof_wl] at hm_new
                        exact hJ4 () _ (wpush_append_set1 hlen3.core_ok.wstk_len_arr (by omega)
                          hcnt1 hm_new)
                    · rintro J4 ⟨⟩ m4 ⟨wstk4, hws4_len, hws4_lt, hat0_4, hat1_4, hm4⟩
                      obtain ⟨hwv3_lt0, hwv3_lt1, hwl_add, hwl_32, hso3_len⟩ :=
                        wpush_caseA_fin_setup hs3_eq hlen3 (hcv3 ▸ hlit) hc12 hfit3
                      c0_hstraight; have hres_m := ‹(FullMem c _ ⋆ R) _›
                      simp only [wpush_lit2, wpush_lit2p1, hwl_add, hwl_32] at hres_m
                      rw [full_state_update_wpush_no_wu hs3_eq] at hres_m
                      exact wpush_caseA_fin hQ hlen hlen3 hlay3 hpres3 hlit hc12 hw0 hw1
                        (Or.inr hsz3) hwlen3 hfit3 wu3 (wsort' := wso3) hws4_len hso3_len
                        (fun i hi => hws4_lt i (Or.inl hi)) hat0_4 hat1_4 _ rfl hres_m
              · c0_hstraight; exact hJA () m2 ⟨rfl, wpush_list_zext64_pos hwv_lt0 hj0 hm0_ ‹_›⟩
            · c0_hstraight; exact hJA () m2 ⟨rfl, hlay2.pos_off lit.toNat hlit2
                (wpush_list_zext64_pos hwv_lt1 hj1 hm1_ ‹_›)⟩
          · rintro JA ⟨⟩ m3 ⟨rfl, hoff_pos⟩; c0_hstraight
            apply wp_join_group (fun _ m4 => m4 = m3)
            rotate_left 1
            · intro JD hJD; c0_hstraight; c0_hsplit
              · clear hc; c0_hstraight
                apply wp_join_group (fun _ m4 => m4 = m3)
                rotate_left 1
                · intro JC hJC; c0_hstraight; c0_hsplit
                  · have hbc_eq := hc; clear hc; c0_hstraight; c0_hsplit
                    · obtain ⟨hoff_eq, hfitB, hpos_eq, hpos_lt⟩ := wpush_caseB_bounds hlen2 hlay2
                        hlit2 hwv_lt0 hwv_lt1 hwv_lt0_bv hwv_lt1_bv hj0 hj1 hbc_eq hc hc12
                      clear hc
                      c0_hstraight
                      apply wp_join_group (fun _ mw => ∃ wstk' : List (BitVec 32),
                        WPushAppendInv c s2 R s2.core.wlen w0 w1 cnt s2.core.wstk wstk' mw)
                      rotate_left 1
                      · intro JB hJB; c0_hstraight; c0_hsplit
                        · have hc2' : cnt.toNat = 2 := by
                            have := congrArg BitVec.toNat hc; simpa using this
                          clear hc
                          obtain ⟨hpos1_eq, _, hpos1_lt, _⟩ := wpush_case_pos1_lt hlen2 hwv_lt0
                            hwv_lt1 hwv_lt0_bv hwv_lt1_bv hj0 hj1 hpos_eq (by omega) w0
                          c0_hstraight
                          have hresB := ‹(FullMem c _ ⋆ R) _›; dsimp only at hresB
                          simp only [hpos_eq, hpos1_eq] at hresB
                          exact hJB () _ (wpush_append_set2 hlen2.core_ok.wstk_len_arr (by omega)
                            hc2' hresB)
                        · have hcnt1 : cnt.toNat = 1 := by
                            have hne : cnt.toNat ≠ 2 := fun h2 =>
                              hc (BitVec.eq_of_toNat_eq (by simp [h2]))
                            omega
                          clear hc
                          have hresB := ‹(FullMem c _ ⋆ R) _›; simp only [hpos_eq] at hresB
                          exact hJB () _ (wpush_append_set1 hlen2.core_ok.wstk_len_arr (by omega)
                            hcnt1 hresB)
                      · rintro JB ⟨⟩ mw ⟨wstk', hwl', hpres', hat0', hat1', hmw⟩; c0_hstraight
                        have hres_m := ‹(FullMem c _ ⋆ R) _›; dsimp only at hres_m
                        obtain ⟨hsz_rw, hadd3⟩ := wpush_caseB_mem_rw hlen2 hlay2 hlit2 hwv_lt0
                          hwv_lt1 hwv_lt0_bv hwv_lt1_bv hoff_eq hfitB hc12
                        simp only [wpush_lit2, wpush_lit2p1] at hres_m
                        rw [hsz_rw, hadd3] at hres_m
                        exact wpush_caseB_s3 hQ hlen hlen2 hlay2 hpres2 hs2_eq hlit hc12 hw0 hw1
                          hoff_pos hoff_eq hfitB hwl' (fun i hi => hpres' i (Or.inl hi)) hat0'
                          hat1' hres_m
                    · clear hc; exact hJC () m3 rfl
                  · clear hc; exact hJC () m3 rfl
                · rintro JC ⟨⟩ m4 rfl; c0_hstraight; c0_hsplit
                  · obtain ⟨hpos_eq, hleC, hpos_lt, hpos_lt_m⟩ := wpush_caseC_bounds hlen2 hlay2
                      hlit2 hwv_lt0 hwv_lt1 hwv_lt0_bv hwv_lt1_bv hj0 hj1 hc hc12; clear hc
                    c0_hstraight; c0_hsplit
                    · have hsent0' := wpush_caseC_sent0 hwv_lt0 hwv_lt1 hj0 hj1 hpos_lt_m hc
                      clear hc
                      c0_hstraight
                      apply wp_join_group (fun _ mw => mw = m4 ∧ ∀ k < cnt.toNat,
                        s2.core.wstk[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat +
                          k]? = some 0xFFFFFFFF#32)
                      rotate_left 1
                      · intro JC2 hJC2; c0_hstraight; c0_hsplit
                        · have hcnt1 : cnt.toNat = 1 := by
                            have := congrArg BitVec.toNat hc; simpa using this
                          clear hc
                          exact hJC2 () m4 ⟨rfl, fun k hk => by
                            have : k = 0 := by omega
                            rw [this, Nat.add_zero]; exact hsent0'⟩
                        · have hcnt2 : cnt.toNat = 2 := by
                            have hne1 : cnt.toNat ≠ 1 := fun h =>
                              hc (BitVec.eq_of_toNat_eq (by simp [h])); omega
                          clear hc
                          obtain ⟨hpos1_eq, hpos1_lt, _, hpos1_lt_m⟩ := wpush_case_pos1_lt hlen2
                            hwv_lt0 hwv_lt1 hwv_lt0_bv hwv_lt1_bv hj0 hj1 hpos_eq
                            (by have := hlen2.core_ok.wlen_le; omega) w0
                          c0_hstraight; c0_hsplit
                          · exact hJC2 () m4 ⟨rfl, wpush_caseC_sent1 hwv_lt0 hwv_lt1 hj0 hj1
                              hcnt2 hpos1_lt_m hsent0' hc⟩
                          · clear hc; exact hJD () m4 rfl
                      · rintro JC2 ⟨⟩ mw ⟨rfl, hsent⟩
                        have hposC_lt := hpos_lt; c0_hstraight
                        let pC := wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat
                        apply wp_join_group (fun _ mw2 => ∃ wstk' : List (BitVec 32),
                          WPushAppendInv c s2 R pC w0 w1 cnt s2.core.wstk wstk' mw2)
                        rotate_left 1
                        · intro JC3 hJC3; c0_hstraight; c0_hsplit
                          · have hc2' : cnt.toNat = 2 := by
                              have := congrArg BitVec.toNat hc; simpa using this
                            clear hc
                            obtain ⟨hpos1_eq, _, hpos1_lt, _⟩ := wpush_case_pos1_lt hlen2 hwv_lt0
                              hwv_lt1 hwv_lt0_bv hwv_lt1_bv hj0 hj1 hpos_eq
                              (by have := hlen2.core_ok.wlen_le; omega) w0
                            c0_hstraight
                            have hresC := ‹(FullMem c _ ⋆ R) _›; dsimp only at hresC
                            simp only [hpos_eq, hpos1_eq] at hresC
                            exact hJC3 () _ (wpush_append_set2 hlen2.core_ok.wstk_len_arr
                              (by have := hlen2.core_ok.wlen_le; omega) hc2' hresC)
                          · have hcnt1 : cnt.toNat = 1 := by
                              have hne : cnt.toNat ≠ 2 := fun h2 =>
                                hc (BitVec.eq_of_toNat_eq (by simp [h2]))
                              omega
                            clear hc
                            have hresC := ‹(FullMem c _ ⋆ R) _›; simp only [hpos_eq] at hresC
                            exact hJC3 () _ (wpush_append_set1 hlen2.core_ok.wstk_len_arr
                              (by have := hlen2.core_ok.wlen_le; omega) hcnt1 hresC)
                        · rintro JC3 ⟨⟩ mw2 ⟨wstk', hwl', hpres', hat0', hat1', hmw2⟩; c0_hstraight
                          apply wp_join_group (fun _ mw3 => ∃ wu' : BitVec 64,
                            (FullMem c { s2 with core := { s2.core with
                              wvec := s2.core.wvec.set (2 * lit.toNat + 1)
                                (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat))
                              wstk := wstk', wusable := wu' } } ⋆ R) mw3)
                          rotate_left 1
                          · intro Jwu hJwu; c0_hstraight; c0_hsplit
                            · clear hc; c0_hstraight; have hrm := ‹(FullMem c _ ⋆ R) _›
                              dsimp only at hrm; simp only [wpush_lit2p1] at hrm
                              rw [wpush_bv_sz_add_cnt hwv_lt1 (by omega) (by omega)] at hrm
                              exact hJwu () _ ⟨_, hrm⟩
                            · clear hc; have hrm := ‹(FullMem c _ ⋆ R) _›
                              dsimp only at hrm; simp only [wpush_lit2p1] at hrm
                              rw [wpush_bv_sz_add_cnt hwv_lt1 (by omega) (by omega)] at hrm
                              exact hJwu () _ ⟨_, hrm⟩
                          · rintro Jwu ⟨⟩ mw3 ⟨wu', hres_m⟩; c0_hstraight
                            exact wpush_caseC_s3 hQ hlen hlen2 hlay2 hpres2 hs2_eq hlit hc12
                              hw0 hw1 hoff_pos hleC hsent hwl' hpres' hat0' hat1' hres_m
                    · clear hc; exact hJD () m4 rfl
                  · clear hc; exact hJD () m4 rfl
              · clear hc; exact hJD () m3 rfl
            · -- Case D: reallocate and relocate slice to `wlen`
              rintro JD ⟨⟩ m4 rfl; c0_hstraight
              apply wp_join_group (ts := [i64]) (fun nc1 mw => mw = m4 ∧
                nc1.fst.toNat = if wSz s2.core.wvec lit.toNat = 0 then 2 else
                  2 * wSz s2.core.wvec lit.toNat)
              rotate_left 1
              · intro Jnc1 hJnc1; c0_hstraight; c0_hsplit
                · have hsz_eq : wSz s2.core.wvec lit.toNat = 0 :=
                    wpush_list_zext64_eq_zero hwv_lt1 hj1 hm1_ hc
                  clear hc; exact hJnc1 (2#64, ()) m4 ⟨rfl, by simp [hsz_eq]⟩
                · c0_hstraight; exact hJnc1 _ m4 ⟨rfl, wpush_nc1_nz hwv_lt1 hj1 hwv_lt1_bv hc⟩
              · rintro Jnc1 ⟨nc1, ⟨⟩⟩ mw ⟨rfl, hnc1⟩; c0_hstraight
                have hsz_le : wSz s2.core.wvec lit.toNat ≤ c.wcap := by
                  have hbd := hlay2.bounds lit.toNat hlit2; have := hlen2.core_ok.wlen_le
                  unfold fullWatchOffCore fullWatchSizeCore wOff wSz at *; omega
                apply wp_join_group (ts := [i64]) (fun nc2 mw' => mw' = mw ∧
                  wSz s2.core.wvec lit.toNat + cnt.toNat ≤ nc2.fst.toNat ∧
                  nc2.fst.toNat ≤ max 2 (2 * c.wcap) + 2)
                rotate_left 1
                · intro Jnc2 hJnc2
                  have ⟨hlt_fn, hge_fn⟩ := wpush_nc2_cmp hwv_lt1 hj1 hwv_lt1_bv hc12 hnc1 hsz_le
                  c0_hstraight; c0_hsplit
                  · exact hJnc2 _ mw ⟨rfl, hlt_fn hc⟩
                  · exact hJnc2 _ mw ⟨rfl, hge_fn hc⟩
                · rintro Jnc2 ⟨nc2, ⟨⟩⟩ mw2 ⟨rfl, hnc2_lo, hnc2_hi⟩; c0_hstraight
                  apply wp_join_group (ts := [i64, i64, i64]) (fun xs m5 =>
                    ∃ s3 : FullState, WPushInvState c s R s3 m5 ∧
                      xs.fst.toNat = wOff s3.core.wvec lit.toNat ∧
                      xs.snd.fst.toNat = wSz s3.core.wvec lit.toNat ∧
                      xs.snd.snd.fst.toNat < 2 ^ 64 ∧
                      s3.core.wlen + xs.snd.snd.fst.toNat ≤ c.wcap ∧
                      wSz s3.core.wvec lit.toNat + cnt.toNat ≤ xs.snd.snd.fst.toNat)
                  rotate_left 1
                  · intro Jdf hJdf; c0_hstraight; c0_hsplit
                    · clear hc; c0_hstraight
                      apply wp_join_group (ts := [i64, i64]) (fun xs m5 =>
                        ∃ s3 : FullState, WPushInvState c s R s3 m5 ∧ s3.core.wusable = 0#64 ∧
                          xs.fst.toNat = wOff s3.core.wvec lit.toNat ∧
                          xs.snd.fst.toNat = wSz s3.core.wvec lit.toNat)
                      rotate_left 1
                      · intro Jd2 hJd2; c0_hstraight; c0_hsplit
                        · clear hc; c0_hstraight
                          c0_hcall (Spec.has_full_wstack_defrag_m6 hΓ)
                          · refine ⟨c, s2, R, rfl, hlen2, hlay2, hm2, fun wv' ws' wl' wso' m5 => ?_⟩
                            intro _ h1 h2 h3 h4 hm5
                            have hinv3 := wpush_inv_state_defrag hinv2_keep h1 h2 h3 h4 hm5
                            obtain ⟨hwv3_0, hwv3_1, _, _, _, _, _, _⟩ := wpush_wvec_lt h1 hlit2
                            c0_hstraight
                            refine hJd2 _ m5 ⟨_, hinv3, rfl, ?_, ?_⟩
                            · simp only [wpush_lit2]; exact wpush_getElem_toNat hwv3_0 rfl
                            · simp only [wpush_lit2p1]; exact wpush_getElem_toNat hwv3_1 rfl
                        · exact hJd2 _ mw2 ⟨s2, hinv2_keep, wpush_bv64_eq_zero_of_not_pos hc,
                            by simp only [wpush_lit2]; exact wpush_getElem_toNat hwv_lt0 rfl,
                            by simp only [wpush_lit2p1]; exact wpush_getElem_toNat hwv_lt1 rfl⟩
                      · rintro Jd2 ⟨off3, sz3, ⟨⟩⟩ m5 ⟨s3, hinv3, hwu3, hoff3, hsz3⟩
                        obtain ⟨hlen3, hlay3, hpres3, hwlen3, ⟨wv3, ws3, wso3, wl3, wu3, hs3_eq⟩,
                          hm3⟩ := hinv3
                        have hsz3_eq : wSz s3.core.wvec lit.toNat = wSz s2.core.wvec lit.toNat := by
                          rw [(hpres3.2 lit.toNat hlit).1, (hpres2.2 lit.toNat hlit).1]
                        c0_hstraight; have hle_w3 := hlen3.core_ok.wlen_le
                        apply wp_join_group (ts := [i64]) (fun xs mw => mw = m5 ∧
                          wSz s3.core.wvec lit.toNat + cnt.toNat ≤ xs.fst.toNat ∧
                          xs.fst.toNat ≤ max 2 (2 * c.wcap) + 2)
                        rotate_left 1
                        · intro Jd3 hJd3; c0_hstraight; c0_hsplit
                          · clear hc; c0_hstraight
                            exact hJd3 _ m5 ⟨rfl, wpush_jd3_fit hsz3 hc12
                              (by rw [hsz3, hsz3_eq]; exact hsz_le)⟩
                          · clear hc; exact hJd3 _ m5 ⟨rfl,
                              by dsimp only [vals, Arg.val]; rw [hsz3_eq]; exact hnc2_lo, hnc2_hi⟩
                        · rintro Jd3 ⟨v3, ⟨⟩⟩ m5 ⟨rfl, hv3_lo, hv3_hi⟩; c0_hstraight; c0_hsplit
                          · clear hc
                            have hwu_raw : wu3 = 0#64 := by rw [hs3_eq] at hwu3; exact hwu3
                            subst hs3_eq
                            exact wpush_fail_post hQ wv3 ws3 wso3 wl3 wu3 hlen3 hlay3 hpres3
                              (Or.inr (Or.inr (Or.inr hwu_raw))) hm3
                          · have hle3 := wpush_fit_of_cmp hle_w3 hc; clear hc
                            exact hJdf _ m5 ⟨s3, ⟨hlen3, hlay3, hpres3, hwlen3,
                              ⟨wv3, ws3, wso3, wl3, wu3, hs3_eq⟩, hm3⟩,
                              hoff3, hsz3, by omega, hle3, hv3_lo⟩
                    · have hleD := wpush_fit_of_cmp hlen2.core_ok.wlen_le hc; clear hc
                      refine hJdf _ mw2 ⟨s2, hinv2_keep, ?_, ?_, BitVec.isLt _, hleD, hnc2_lo⟩
                      · simp only [wpush_lit2]; exact wpush_getElem_toNat hwv_lt0 rfl
                      · simp only [wpush_lit2p1]; exact wpush_getElem_toNat hwv_lt1 rfl
                  · rintro Jdf ⟨off3, sz3, ncap3, ⟨⟩⟩ m5 ⟨s3, hinv3, hoff3, hsz3, _, hfit3, hlo3⟩
                    dsimp only at hoff3 hsz3 hfit3 hlo3
                    obtain ⟨hlen3, hlay3, hpres3, hwlen3, ⟨wv3, ws3, wso3, wl3, wu3, hs3_eq⟩,
                      hm3⟩ := hinv3
                    have hlit3 : lit.toNat < 2 * s3.core.cur_vars := by rw [hpres3.1]; exact hlit
                    have hoff3_bd : off3.toNat + sz3.toNat ≤ s3.core.wlen := by
                      rw [hoff3, hsz3]; exact hlay3.bounds lit.toNat hlit3
                    c0_hstraight
                    apply wp_loop_group (ts := [i64]) (WPushRelocCopyInv c s3 R lit sz3)
                    · intro Jcp n ⟨k_bv, ⟨⟩⟩ mw hIH ⟨wstk_cp, hk_le, hn_eq, hcp_len, hcp_inv, hmw⟩
                      dsimp only at hk_le hn_eq hcp_inv; c0_hstraight; c0_hsplit
                      · have hk_lt : k_bv.toNat < sz3.toNat := by simpa [BitVec.ult] using hc
                        clear hc
                        obtain ⟨hk_off, hk_dst, hdst_lt, hoff_lt⟩ := wpush_reloc_step_bounds
                          hlen3 hcp_len hoff3_bd (by omega) hk_lt
                        c0_hstraight
                        have hrm := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm
                        rw (occs := .pos [1]) [hk_dst] at hrm; simp only [hk_off] at hrm
                        obtain ⟨hdec, hnext⟩ := wpush_reloc_copy_next hlen3 hlay3 hlit3 hoff3 hsz3
                          hcp_len hcp_inv (by omega) hk_lt
                          (by have h := hoff_lt 0#32; rw [List.length_set, hk_off] at h; exact h)
                          hrm
                        exact hIH _ _ _ (by rw [hn_eq]; exact hdec) hnext
                      · have hk_ge : ¬ k_bv.toNat < sz3.toNat := by simpa [BitVec.ult] using hc
                        clear hc
                        have hk_eq : k_bv.toNat = sz3.toNat := by omega
                        have hk_bv_eq : k_bv = sz3 := BitVec.eq_of_toNat_eq hk_eq
                        obtain ⟨hp0_eq, hp0_lt⟩ := wpush_reloc_p0_bounds (s3 := s3)
                          hcp_len hk_eq (by omega)
                        c0_hstraight
                        have hrm0 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm0; rw [hp0_eq] at hrm0
                        apply wp_join_group (ts := []) (fun _ mw2 => ∃ wstk_w : List (BitVec 32),
                          WPushAppendInv c s3 R (s3.core.wlen + sz3.toNat) w0 w1 cnt wstk_cp
                            wstk_w mw2)
                        rotate_left 1
                        · intro Jw1 hJw1; c0_hstraight; c0_hsplit
                          · have hc2' : cnt.toNat = 2 := by
                              have := congrArg BitVec.toNat hc; simpa using this
                            clear hc
                            have hp1_eq := wpush_bv64_add_off_sz_1 hp0_eq (by omega)
                            have hp1_lt : (BitVec.ofNat 64 s3.core.wlen + k_bv + 1#64).toNat <
                                (wstk_cp.set (s3.core.wlen + sz3.toNat) w0).length := by
                              have h1bv : (1#64 : BitVec 64) = 1 := rfl
                              rw [List.length_set, h1bv, hk_bv_eq, hp1_eq, hcp_len]; omega
                            c0_hstraight
                            have hrm1 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm1
                            rw [hp1_eq] at hrm1
                            exact hJw1 () _ (wpush_append_set2 hcp_len (by omega) hc2' hrm1)
                          · have hcnt1 : cnt.toNat = 1 := by
                              have hne : cnt.toNat ≠ 2 := fun h =>
                                hc (BitVec.eq_of_toNat_eq (by simp [h]))
                              omega
                            clear hc
                            exact hJw1 () _ (wpush_append_set1 hcp_len (by omega) hcnt1 hrm0)
                        · rintro Jw1 ⟨⟩ mw2 ⟨wstk_w, hwl_w, hpr_w, h0_w, h1_w, hmw2⟩; c0_hstraight
                          apply wp_loop_group (ts := [i64])
                            (WPushRelocFillInv c s3 R sz3 ncap3 w0 w1 cnt wstk_cp)
                          · intro Jfl n2 ⟨j_bv, ⟨⟩⟩ mw3 hIHf ⟨wstk_f, hj_lo, hj_hi, hn2_eq,
                              hfl_len, hpr_f, h0_f, h1_f, hmw3⟩
                            dsimp only at hj_lo hj_hi hn2_eq; c0_hstraight; c0_hsplit
                            · have hj_lt : j_bv.toNat < ncap3.toNat := by
                                simpa [BitVec.ult] using hc
                              clear hc
                              obtain ⟨hj_eq, hj_bound⟩ := wpush_reloc_fill_next_bounds hfl_len
                                hj_lt hfit3
                              c0_hstraight
                              have hrmf := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrmf
                              rw [hj_eq] at hrmf
                              obtain ⟨hdec, hnext⟩ := wpush_reloc_fill_next hfl_len hj_lo hj_lt
                                hpr_f h0_f h1_f hc12 hrmf
                              exact hIHf _ _ _ (by rw [hn2_eq]; exact hdec) hnext
                            · have hj_ge : ¬ j_bv.toNat < ncap3.toNat := by
                                simpa [BitVec.ult] using hc
                              clear hc; have hj_eq_n : j_bv.toNat = ncap3.toNat := by omega
                              obtain ⟨hwv3_0, hwv3_1, _, _, _, _, _, _⟩ := wpush_wvec_lt hlen3 hlit3
                              c0_hstraight
                              have hrmf := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrmf
                              simp only [wpush_lit2, wpush_lit2p1] at hrmf
                              exact wpush_reloc_s3_post hQ hlen hlen3 hlay3 hpres3 hs3_eq hlit hc12
                                hw0 hw1 hwlen3 hsz3 hlo3 hfit3 (by rw [← hk_eq]; exact hcp_inv)
                                hfl_len hpr_f h0_f h1_f hrmf
                          · intro Jfl hJfl; c0_hstraight
                            exact hJfl _ _ mw2 (wpush_reloc_fill_init hlen3
                              (by rw [hsz3]; exact hlo3) (by omega) hwl_w
                              (fun i hi => hpr_w i (Or.inl hi)) h0_w h1_w hmw2)
                    · intro Jcp hJcp; c0_hstraight
                      exact hJcp sz3.toNat (0#64, ()) m5 (wpush_reloc_copy_init hlen3 hm3)

end

end LeanQbe.T.Examples.Kissat.Proof.Watch

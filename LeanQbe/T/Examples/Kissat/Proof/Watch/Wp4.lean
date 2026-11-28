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

/-! # Watch WP Proofs Part 4: `full_watch_push_m6_wp` and `full_watch_push_wp`

Proves `Func.wp` for `full_watch_push_m6` and `full_watch_push` against `fullWatchPushSpec`
using `CanonicalEnv` (`Γ.Sat Spec.specs`) and `Proof.Watch.Wp3a` helpers. -/

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

private theorem wpush_bv_sz_add_cnt32 {wvec : List (BitVec 32)} {lit cnt : BitVec 32}
    (h1 : 2 * lit.toNat + 1 < wvec.length) :
    BitVec.setWidth 32 (BitVec.setWidth 64 wvec[2 * lit.toNat + 1]) +
      BitVec.setWidth 32 (BitVec.setWidth 64 cnt) =
      BitVec.ofNat 32 (wSz wvec lit.toNat + cnt.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hsz : wSz wvec lit.toNat = wvec[2 * lit.toNat + 1].toNat := by
    simp [wSz, List.getElem?_eq_getElem h1]
  simp [hsz]

private theorem wpush_caseB_hoff_eq {c : FullCfg} {s : FullState} {lit : Val i32}
    (hlen : s.LengthsOk c)
    (hw0 : 2 * lit.toNat < s.core.wvec.length) (hw1 : 2 * lit.toNat + 1 < s.core.wvec.length)
    (hj0 : 2 * lit.toNat % 2 ^ 64 < s.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s.core.wvec.length)
    (hc : BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64] +
      BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64] =
      BitVec.ofNat 64 s.core.wlen) :
    wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat = s.core.wlen := by
  have hwcap32 := wpush_wcap_lt32 c; have hwlen := hlen.core_ok.wlen_le
  have hwvl := hlen.core_ok.wvec_len; have := c.hmaxv; unfold dimacsBound at *
  have h1bv : BitVec.toNat (1 : BitVec 64) = 1 := rfl
  have hmod0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
    rw [h1bv]; exact Nat.mod_eq_of_lt (by omega)
  have heq_bv : BitVec.setWidth 64 s.core.wvec[2 * lit.toNat] +
      BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1] = BitVec.ofNat 64 s.core.wlen := by
    simpa only [hmod0, hmod1] using hc
  have hto := congrArg BitVec.toNat heq_bv
  rw [wpush_bv_off_sz_add hw0 hw1 (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)] at hto
  exact hto

theorem full_watch_push_m6_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X,
      fullWatchPushSpec a m Q X → Func.wp Γ full_watch_push_m6_body a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hw0, hw1, hm, hQ⟩
  unfold full_watch_push_m6_body
  have hcv32 : s.core.cur_vars < 2 ^ 30 := by
    have := c.hmaxv; have := hlen.core_ok.cur_vars_le; unfold dimacsBound at *; omega
  have hwcap32 : c.wcap < 2 ^ 32 := wpush_wcap_lt32 c
  have hwl_le := hlen.core_ok.wlen_le
  have hwlen32 : s.core.wlen < 2 ^ 32 := Nat.lt_of_le_of_lt hwl_le hwcap32
  dsimp only [Func.wp]
  c0_hstraight
  c0_hsplit
  · have hge := hc; clear hc
    have hlt_bad : 2 * s.core.cur_vars ≤ lit.toNat := by
      simpa [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] using hge
    exact wpush_fail_post hQ s.core.wvec s.core.wstk s.scratch.wsort s.core.wlen s.core.wusable
      hlen hlay (watchPresAll_refl s) (Or.inl hlt_bad) hm
  · have hlt_v := hc; clear hc
    have hlit : lit.toNat < 2 * s.core.cur_vars := by
      simpa [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] using hlt_v
    c0_hstraight
    apply wp_join_group (fun _ m0 => m0 = m ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2))
    rotate_left 1
    · intro J hJ
      c0_hstraight
      c0_hsplit
      · have hne1 := hc; clear hc
        c0_hstraight
        c0_hsplit
        · have hne2 := hc; clear hc
          exact wpush_fail_post hQ s.core.wvec s.core.wstk s.scratch.wsort s.core.wlen
            s.core.wusable hlen hlay (watchPresAll_refl s)
            (Or.inr (Or.inl ⟨wpush_bv32_ne_nat 1 (by decide) hne1,
              wpush_bv32_ne_nat 2 (by decide) hne2⟩)) hm
        · have hc2 := hc; clear hc
          exact hJ () m ⟨rfl, Or.inr (wpush_bv32_eq_nat 2 (by decide) hc2)⟩
      · have hc1 := hc; clear hc
        exact hJ () m ⟨rfl, Or.inl (wpush_bv32_eq_nat 1 (by decide) hc1)⟩
    · rintro J ⟨⟩ m0 ⟨rfl, hc12⟩
      have hwv_lt0 : 2 * lit.toNat < s.core.wvec.length := by
        rw [hlen.core_ok.wvec_len]; have := hlen.core_ok.cur_vars_le; omega
      have hwv_lt1 : 2 * lit.toNat + 1 < s.core.wvec.length := by
        rw [hlen.core_ok.wvec_len]; have := hlen.core_ok.cur_vars_le; omega
      have hwv_lt0_bv : (BitVec.setWidth 64 lit <<< 1).toNat < s.core.wvec.length := by
        rw [wpush_lit2]; exact hwv_lt0
      have hwv_lt1_bv : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < s.core.wvec.length := by
        rw [wpush_lit2p1]; exact hwv_lt1
      c0_hstraight
      apply wp_join_group (fun _ mw => mw = m0)
      · rintro Js ⟨⟩ mw rfl
        c0_hstraight
        c0_hcall (Spec.has_full_watch_push_slow_m6 hΓ)
        · exact ⟨c, s, R, rfl, hlen, hlay,
            fun h => hw0 (by simpa using h), fun h => hw1 (by simpa using h), ‹_›,
            fun ok wvec' wstk' wlen' wusable' wsort' m' h1 h2 h3 h4 h5 hm' => by
              have hcnt_sw : (BitVec.setWidth 32 (BitVec.setWidth 64 cnt)).toNat = cnt.toNat := by
                simp
              rw [hcnt_sw] at h4 h5
              exact hQ ok wvec' wstk' wlen' wusable' wsort' m' h1 h2 h3 h4 h5 hm'⟩
      · intro Js hJs
        c0_hstraight
        c0_hsplit
        · have hne0 := hc; clear hc
          c0_hstraight
          apply wp_join_group (fun _ mw => mw = m0)
          rotate_left 1
          · intro Jf hJf
            c0_hstraight
            apply wp_join_group (fun _ mw => mw = m0)
            rotate_left 1
            · intro Jg hJg
              c0_hstraight
              c0_hsplit
              · clear hc; c0_hstraight; c0_hsplit
                · clear hc; exact hJf () m0 rfl
                · clear hc; exact hJg () m0 rfl
              · clear hc; exact hJg () m0 rfl
            · rintro Jg ⟨⟩ mw rfl
              c0_hstraight
              c0_hsplit
              · clear hc; exact hJf () mw rfl
              · clear hc; exact hJs () mw rfl
          · rintro Jf ⟨⟩ mw rfl
            have hne0_nat : 1 ≤ s.core.wlen := by
              have hwlen_lt := hlen.core_ok.wlen_le
              have hlt64 : s.core.wlen < 2 ^ 64 := by omega
              have hne : s.core.wlen ≠ 0 :=
                fun h => hne0 (BitVec.eq_of_toNat_eq (by simp [h]))
              omega
            obtain ⟨hwv0, hwv1, hwv0_bv, hwv1_bv, hj0, hj1, hmod0, hmod1⟩ :=
              wpush_wvec_lt hlen hlit
            c0_hstraight
            apply wp_join_group (fun _ mw1 => mw1 = mw)
            rotate_left 1
            · intro Ja hJa
              c0_hstraight
              c0_hsplit
              · have hpos_gt : 0 < wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat := by
                  simp only [wOff, wSz, List.getElem?_eq_getElem hwv0,
                    List.getElem?_eq_getElem hwv1, Option.getD_some]
                  simp only [hmod0, hmod1] at hc
                  have h0 : s.core.wvec[2 * lit.toNat].toNat < 2 ^ 32 := BitVec.isLt _
                  have h1 : s.core.wvec[2 * lit.toNat + 1].toNat < 2 ^ 32 := BitVec.isLt _
                  rwa [Nat.mod_eq_of_lt (by omega)] at hc
                have hoff_pos : 1 ≤ wOff s.core.wvec lit.toNat := by
                  by_cases hsz : 0 < wSz s.core.wvec lit.toNat
                  · exact hlay.pos_off lit.toNat hlit hsz
                  · omega
                clear hc
                apply wp_join_group (fun _ mw1 => mw1 = mw)
                rotate_left 1
                · intro Jb hJb
                  c0_hstraight
                  c0_hsplit
                  · obtain ⟨hpos_eq, hleC, hpos_lt, hpos_lt_m⟩ := wpush_caseC_bounds
                      hlen hlay hlit hwv0 hwv1 hwv0_bv hwv1_bv hj0 hj1 hc hc12
                    clear hc
                    c0_hstraight
                    c0_hsplit
                    · have hsent0 := wpush_caseC_sent0 hwv0 hwv1 hj0 hj1 hpos_lt_m hc
                      clear hc
                      c0_hstraight
                      apply wp_join_group (fun _ mw1 => mw1 = mw ∧ ∀ k < cnt.toNat,
                        s.core.wstk[wOff s.core.wvec lit.toNat +
                          wSz s.core.wvec lit.toNat + k]? = some 0xFFFFFFFF#32)
                      rotate_left 1
                      · intro Jc2 hJc2
                        c0_hstraight
                        c0_hsplit
                        · have hc1 : cnt.toNat = 1 := by
                            have := congrArg BitVec.toNat hc
                            simpa [Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64)] using this
                          clear hc
                          refine hJc2 () mw ⟨rfl, fun k hk => ?_⟩
                          have : k = 0 := by omega
                          subst this; simpa using hsent0
                        · have hc2 : cnt.toNat = 2 := by
                            have hne1 : cnt.toNat ≠ 1 :=
                              fun h => hc (BitVec.eq_of_toNat_eq (by simp [h]))
                            omega
                          clear hc
                          have hpos1_lt : (BitVec.setWidth 64 (s.core.wvec[
                              (BitVec.setWidth 64 lit <<< 1).toNat]'hwv0_bv) +
                              BitVec.setWidth 64 (s.core.wvec[
                              (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hwv1_bv) +
                              1#64).toNat < s.core.wstk.length := by
                            have h1bv : (1#64 : BitVec 64) = 1 := rfl
                            rw [h1bv, wpush_bv64_add_off_sz_1 hpos_eq (by omega)]
                            rw [hlen.core_ok.wstk_len_arr]; omega
                          c0_hstraight
                          c0_hsplit
                          · have hpos1_lt_m : (s.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
                                s.core.wvec[(2 * lit.toNat +
                                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                                s.core.wstk.length := by
                              have h1bv : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                              have hwvl := hlen.core_ok.wvec_len
                              have := c.hmaxv; unfold dimacsBound at *
                              simp only [hmod0, h1bv,
                                Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
                              have hbd := hlay.bounds lit.toNat hlit
                              simp only [wOff, wSz, List.getElem?_eq_getElem hwv0,
                                List.getElem?_eq_getElem hwv1, Option.getD_some] at hbd hleC
                              rw [Nat.mod_eq_of_lt (by omega), hlen.core_ok.wstk_len_arr]
                              omega
                            have hsent := wpush_caseC_sent1 hwv0 hwv1 hj0 hj1 hc2
                              hpos1_lt_m hsent0 hc
                            clear hc
                            exact hJc2 () mw ⟨rfl, hsent⟩
                          · clear hc; exact hJb () mw rfl
                      · rintro Jc2 ⟨⟩ mw1 ⟨hmw1, hsent⟩; subst hmw1
                        c0_hstraight
                        apply wp_join_group (ts := []) (fun _ mw2 =>
                          ∃ wstk' : List (BitVec 32), WPushAppendInv c s R
                            (wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat)
                            w0 w1 cnt s.core.wstk wstk' mw2)
                        rotate_left 1
                        · intro Jw hJw
                          c0_hstraight
                          c0_hsplit
                          · have hc2 : cnt.toNat = 2 := by
                              have := congrArg BitVec.toNat hc
                              simpa [Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64)] using this
                            clear hc
                            have hpos1_lt : (BitVec.setWidth 64 (s.core.wvec[
                                (BitVec.setWidth 64 lit <<< 1).toNat]'hwv0_bv) +
                                BitVec.setWidth 64 (s.core.wvec[
                                (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hwv1_bv) +
                                1#64).toNat < (s.core.wstk.set (wOff s.core.wvec lit.toNat +
                                  wSz s.core.wvec lit.toNat) w0).length := by
                              have h1bv : (1#64 : BitVec 64) = 1 := rfl
                              rw [List.length_set, h1bv,
                                wpush_bv64_add_off_sz_1 hpos_eq (by omega)]
                              rw [hlen.core_ok.wstk_len_arr]; omega
                            c0_hstraight
                            have hrm1 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm1
                            simp only [wpush_lit2, wpush_lit2p1] at hrm1
                            have hadd_pos : (BitVec.setWidth 64 s.core.wvec[2 * lit.toNat] +
                                BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1]).toNat =
                                wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat :=
                              wpush_bv_off_sz_add hwv0 hwv1 (by omega)
                            have hadd1 := wpush_bv64_add_off_sz_1 hadd_pos (by omega)
                            rw [hadd_pos, hadd1] at hrm1
                            exact hJw () _ (wpush_append_set2 hlen.core_ok.wstk_len_arr
                              (by omega) hc2 hrm1)
                          · have hc1 : cnt.toNat = 1 := by
                              have hne : cnt.toNat ≠ 2 :=
                                fun h => hc (BitVec.eq_of_toNat_eq (by simp [h]))
                              omega
                            clear hc
                            have hrm0 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm0
                            simp only [wpush_lit2, wpush_lit2p1] at hrm0
                            rw [wpush_bv_off_sz_add hwv0 hwv1 (by omega)] at hrm0
                            exact hJw () _ (wpush_append_set1 hlen.core_ok.wstk_len_arr
                              (by omega) hc1 hrm0)
                        · rintro Jw ⟨⟩ mw2 ⟨wstk', hwl', hpres', hat0', hat1', hmw2⟩
                          c0_hstraight
                          have hsz_lt32 : wSz s.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 := by
                            have hbd := hlay.bounds lit.toNat hlit; omega
                          apply wp_join_group (ts := []) (fun _ mw3 => ∃ wu' : BitVec 64,
                            (FullMem c { s with core := { s.core with
                              wvec := s.core.wvec.set (2 * lit.toNat + 1)
                                (BitVec.ofNat 32
                                  (wSz s.core.wvec lit.toNat + cnt.toNat))
                              wstk := wstk', wusable := wu' } } ⋆ R) mw3)
                          rotate_left 1
                          · intro Ju hJu
                            c0_hstraight
                            c0_hsplit
                            · clear hc; c0_hstraight
                              have hrm := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm
                              simp only [wpush_lit2p1] at hrm
                              rw [wpush_bv_sz_add_cnt32 hwv1] at hrm
                              exact hJu () _ ⟨_, hrm⟩
                            · clear hc
                              have hrm := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm
                              simp only [wpush_lit2p1] at hrm
                              rw [wpush_bv_sz_add_cnt32 hwv1] at hrm
                              exact hJu () _ ⟨_, hrm⟩
                          · rintro Ju ⟨⟩ mw3 ⟨wu', hrm3⟩
                            c0_hstraight
                            exact wpush_caseC_s3 hQ hlen hlen hlay (watchPresAll_refl s) rfl
                              hlit hc12 hw0 hw1 hoff_pos hleC
                              hsent hwl' hpres' hat0' hat1' hrm3
                    · clear hc; exact hJb () mw rfl
                  · clear hc; exact hJb () mw rfl
                · rintro Jb ⟨⟩ m1 hm1
                  rw [hm1]; clear m1 hm1
                  c0_hstraight
                  c0_hsplit
                  · have hbv_eq := hc
                    have hoff_eq := wpush_caseB_hoff_eq hlen hwv0 hwv1 hj0 hj1 hc
                    clear hc
                    c0_hstraight
                    c0_hsplit
                    · obtain ⟨_, hfitB, hpos_eq, hpos_lt⟩ := wpush_caseB_bounds
                        hlen hlay hlit hwv0 hwv1 hwv0_bv hwv1_bv hj0 hj1 hbv_eq hc hc12
                      clear hc
                      c0_hstraight
                      apply wp_join_group (ts := []) (fun _ mw2 =>
                        ∃ wstk' : List (BitVec 32), WPushAppendInv c s R
                          s.core.wlen w0 w1 cnt s.core.wstk wstk' mw2)
                      rotate_left 1
                      · intro JwB hJwB
                        c0_hstraight
                        c0_hsplit
                        · have hc2 : cnt.toNat = 2 := by
                            have := congrArg BitVec.toNat hc
                            simpa [Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64)] using this
                          clear hc
                          have hpos1_lt : (BitVec.setWidth 64 (s.core.wvec[
                              (BitVec.setWidth 64 lit <<< 1).toNat]'hwv0_bv) +
                              BitVec.setWidth 64 (s.core.wvec[
                              (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hwv1_bv) +
                              1#64).toNat < (s.core.wstk.set s.core.wlen w0).length := by
                            have h1bv : (1#64 : BitVec 64) = 1 := rfl
                            rw [List.length_set, h1bv, wpush_bv64_add_off_sz_1 hpos_eq (by omega)]
                            rw [hlen.core_ok.wstk_len_arr]; omega
                          c0_hstraight
                          have hrm1 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm1
                          simp only [wpush_lit2, wpush_lit2p1] at hrm1
                          have hadd_pos : (BitVec.setWidth 64 s.core.wvec[2 * lit.toNat] +
                              BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1]).toNat =
                              wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat :=
                            wpush_bv_off_sz_add hwv0 hwv1 (by omega)
                          have hadd1 := wpush_bv64_add_off_sz_1 hadd_pos (by omega)
                          rw [hadd_pos, hadd1, hoff_eq] at hrm1
                          exact hJwB () _ (wpush_append_set2 hlen.core_ok.wstk_len_arr
                            (by omega) hc2 hrm1)
                        · have hc1 : cnt.toNat = 1 := by
                            have hne : cnt.toNat ≠ 2 :=
                              fun h => hc (BitVec.eq_of_toNat_eq (by simp [h]))
                            omega
                          clear hc
                          have hrm0 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm0
                          simp only [wpush_lit2, wpush_lit2p1] at hrm0
                          rw [wpush_bv_off_sz_add hwv0 hwv1 (by omega), hoff_eq] at hrm0
                          exact hJwB () _ (wpush_append_set1 hlen.core_ok.wstk_len_arr
                            (by omega) hc1 hrm0)
                      · rintro JwB ⟨⟩ mw2 ⟨wstk', hwl', hpres', hat0', hat1', hmw2⟩
                        c0_hstraight
                        have hres_m := ‹(FullMem c _ ⋆ R) _›; dsimp only at hres_m
                        have hsz_lt32 : wSz s.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 := by
                          have hbd := hlay.bounds lit.toNat hlit; omega
                        simp only [wpush_lit2, wpush_lit2p1] at hres_m
                        rw [wpush_bv_sz_add_cnt32 hwv1,
                          wpush_bv64_add3_eq hwv0 hwv1 (by omega) hoff_eq (by omega)] at hres_m
                        exact wpush_caseB_fin hQ hlen hlen hlay (watchPresAll_refl s) hlit
                          hc12 hw0 hw1 hoff_pos hoff_eq hfitB s.core.wusable
                          (wsort' := s.scratch.wsort) hwl' hlen.scratch_ok.wsort_len
                          (fun i hi => hpres' i (Or.inl hi)) hat0' hat1' _ rfl hres_m
                    · clear hc; exact hJa () mw rfl
                  · clear hc; exact hJa () mw rfl
              · have hpos0 : wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat = 0 := by
                  simp only [wOff, wSz, List.getElem?_eq_getElem hwv0,
                    List.getElem?_eq_getElem hwv1, Option.getD_some]
                  simp only [hmod0, hmod1] at hc
                  have h0 : s.core.wvec[2 * lit.toNat].toNat < 2 ^ 32 := BitVec.isLt _
                  have h1 : s.core.wvec[2 * lit.toNat + 1].toNat < 2 ^ 32 := BitVec.isLt _
                  have hle0 : ¬ 0 < (s.core.wvec[2 * lit.toNat].toNat +
                    s.core.wvec[2 * lit.toNat + 1].toNat) % 2 ^ 64 := hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hle0; omega
                have hoff0 : wOff s.core.wvec lit.toNat = 0 := by omega
                clear hc
                c0_hstraight
                c0_hsplit
                · have hfitA : s.core.wlen + cnt.toNat ≤ c.wcap := by
                    simp only [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64)] at hc
                    have hsub_lt : 2 ^ 64 - s.core.wlen + c.wcap ≥ 2 ^ 64 := by omega
                    omega
                  clear hc
                  have hwl1 : s.core.wlen < c.wcap := by omega
                  obtain ⟨hbw0, hbw1⟩ := wpush_caseA_wlen_bv hwl1
                  have hbw0_stk : (BitVec.ofNat 64 s.core.wlen).toNat < s.core.wstk.length := by
                    rw [hbw0, hlen.core_ok.wstk_len_arr]; omega
                  c0_hstraight
                  apply wp_join_group (ts := []) (fun _ mw2 => ∃ wstk' : List (BitVec 32),
                    WPushAppendInv c s R s.core.wlen w0 w1 cnt s.core.wstk wstk' mw2)
                  rotate_left 1
                  · intro JwA hJwA
                    c0_hstraight
                    c0_hsplit
                    · have hc2 : cnt.toNat = 2 := by
                        have := congrArg BitVec.toNat hc
                        simpa [Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64)] using this
                      clear hc
                      have hpos1_lt : (BitVec.ofNat 64 s.core.wlen + 1#64).toNat <
                          (s.core.wstk.set s.core.wlen w0).length := by
                        have h1bv : (1#64 : BitVec 64) = 1 := rfl
                        rw [List.length_set, h1bv, hbw1, hlen.core_ok.wstk_len_arr]; omega
                      c0_hstraight
                      have hrm1 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm1
                      rw [hbw0, hbw1] at hrm1
                      exact hJwA () _ (wpush_append_set2 hlen.core_ok.wstk_len_arr
                        (by omega) hc2 hrm1)
                    · have hc1 : cnt.toNat = 1 := by
                        have hne : cnt.toNat ≠ 2 :=
                          fun h => hc (BitVec.eq_of_toNat_eq (by simp [h]))
                        omega
                      clear hc
                      have hrm0 := ‹(FullMem c _ ⋆ R) _›; dsimp only at hrm0
                      rw [hbw0] at hrm0
                      exact hJwA () _ (wpush_append_set1 hlen.core_ok.wstk_len_arr
                        (by omega) hc1 hrm0)
                  · rintro JwA ⟨⟩ mw2 ⟨wstk', hwl', hpres', hat0', hat1', hmw2⟩
                    c0_hstraight
                    have hres_m := ‹(FullMem c _ ⋆ R) _›; dsimp only at hres_m
                    simp only [wpush_lit2, wpush_lit2p1, wpush_bv32_ofNat_64] at hres_m
                    have hwlen_eq : (BitVec.ofNat 64 s.core.wlen +
                        BitVec.setWidth 64 cnt).toNat = s.core.wlen + cnt.toNat := by
                      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
                        Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                    have hcnt_rw : BitVec.setWidth 32 (BitVec.setWidth 64 cnt) = cnt := by simp
                    rw [hwlen_eq, hcnt_rw] at hres_m
                    exact wpush_caseA_fin hQ hlen hlen hlay (watchPresAll_refl s) hlit hc12
                      hw0 hw1 (Or.inl hoff0) hne0_nat hfitA s.core.wusable
                      (wsort' := s.scratch.wsort) hwl' hlen.scratch_ok.wsort_len
                      (fun i hi => hpres' i (Or.inl hi)) hat0' hat1' _ rfl hres_m
                · clear hc; exact hJa () mw rfl
            · rintro Ja ⟨⟩ mw1 rfl; exact hJs () mw1 rfl
        · clear hc; exact hJs () m0 rfl

theorem full_watch_push_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X,
      fullWatchPushSpec a m Q X → Func.wp Γ full_watch_push_body a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X hspec
  unfold full_watch_push_body
  dsimp only [Func.wp]
  c0_hcall (Spec.has_full_watch_push_m6 hΓ)
  · exact hspec

end

end LeanQbe.T.Examples.Kissat.Proof.Watch

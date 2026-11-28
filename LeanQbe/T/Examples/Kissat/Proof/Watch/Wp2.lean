/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp2a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-! # Watch WP Proofs Part 2: `full_wstack_defrag_m6` and `full_wstack_defrag`

Self-contained `CanonicalEnv` WP proofs for `full_wstack_defrag_m6` and `full_wstack_defrag`. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

public section

theorem full_wstack_defrag_m6_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X, Proof.Spec.fullWstackDefragSpec a m Q X →
      Func.wp Γ full_wstack_defrag_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hSift := Spec.has_full_wsort_sift hΓ
  have hRadix := Spec.has_full_wstack_radix_sort_m6 hΓ
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap; unfold dimacsBound at hwcap
  have hcv_le := hcl.cur_vars_le; have hwle := hcl.wlen_le
  have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr; have hwsrt_l := hsl.wsort_len
  have h0_64 : (0 : BitVec 64).toNat = 0 := rfl
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  have h256_64 : (256 : BitVec 64).toNat = 256 := rfl
  dsimp only [Func.wp, full_wstack_defrag_m6_body]; c0_hsplit
  · rw [Nat.mod_eq_of_lt (by omega), h1_64] at hc; clear hc; c0_hstraight
    exact hQ s.core.wvec s.core.wstk s.core.wlen s.scratch.wsort _
      ⟨{ hcl with wlen_le := hwle }, hsl⟩ (hlay.with_wstk rfl rfl rfl rfl) id
      (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hm
  · rw [Nat.mod_eq_of_lt (by omega), h1_64] at hc
    have hwlen_gt1 : 1 < s.core.wlen := by omega
    have hwsl_pos : 0 < s.core.wstk.length := by omega
    have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
      rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat_id (by omega), Nat.shiftLeft_eq]; simp; omega
    clear hc; c0_hstraight
    refine wp_loop_inv (DefragScanInv c s R)
      (fun (_, l, _, _, _, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J hLoop => by
        c0_hstraight
        refine hLoop _ _ ⟨by omega, by omega, by omega, by omega, s.core.wvec, s.scratch.wsort,
          hwvl, hwsrt_l, fun _ _ => rfl, fun _ _ _ => rfl,
          fun _ hj => by rw [h0_64] at hj; omega,
          ⟨fun _ hi => by rw [h0_64] at hi; omega, fun _ hi => by rw [h0_64] at hi; omega,
           fun _ hl => by rw [h0_64] at hl; omega⟩,
          fun _ hi => by rw [h0_64] at hi; omega,
          fun _ => ⟨fun _ _ _ _ hj => by rw [h0_64] at hj; omega,
            fun _ hi => by rw [h0_64] at hi; omega⟩, hm⟩)
      ?_
    rintro J ⟨n, l, max_off, prev_off, sorted, ⟨⟩⟩ m1
      ⟨hl_le, hn_le, hmax_le, hprev_le, wvec1, wsort1, hwv1, hws1,
       hsz1, hoff1, hzero1, hcov1, hmax_elt, hsrt1, hm1⟩ hLoop
    clear hm; c0_hsplit
    · rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
      have hl_lt : l.toNat < 2 * s.core.cur_vars := hc; clear hc
      have hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_mod (by omega)
      have hl2p1 : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add1_nat (by omega), hl2]
      have hl2_lt : (l <<< (1 : Nat)).toNat < wvec1.length := by omega
      have hl2p1_lt : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvec1.length := by omega
      have hsz_eq : (wvec1[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hl2p1_lt).toNat =
          fullWatchSize s l.toNat := by
        unfold fullWatchSize fullWatchSizeCore; have h1 := hsz1 l.toNat hl_lt; rw [← h1]
        rw [list_getElem_toNat_eq (by omega) hl2p1, List.getElem?_eq_getElem (by omega),
          Option.getD_some]
      have hidx_eq : (2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
          ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat := by
        rw [h1_64, hl2p1, Nat.mod_eq_of_lt (by omega)]
      have h2_idx : 2 * l.toNat % 2 ^ 64 = (l <<< (1 : Nat)).toNat := by
        rw [hl2, Nat.mod_eq_of_lt (by omega)]
      c0_hstraight
      refine wp_join_group (ts := [i64, i64, i64, Ty.bool])
        (fun (n', mo', po', srt', ()) m' =>
          DefragScanInv c s R (n', l + (1 : BitVec 64), mo', po', srt', ()) m')
        ?_ ?_
      · rintro _ ⟨n', mo', po', srt', ⟨⟩⟩ m' hInv
        have hlp1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1_nat (by omega)
        c0_hstraight
        exact hLoop _ _ (by dsimp only; rw [hlp1]; omega) hInv
      · intro Js hJs
        clear hLoop J
        c0_hsplit
        · have hsz0 : fullWatchSize s l.toNat = 0 := by
            have h := congrArg BitVec.toNat hc
            rw [list_getElem_toNat_eq (by omega) hidx_eq, hsz_eq] at h; exact h
          clear hc
          have hset := wvec_set_even_eq (wvec := wvec1) (l := l.toNat) (v := 0#32)
            (by omega)
          have hlp1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1_nat (by omega)
          c0_hstraight
          exact hJs _ _
            (defrag_scan_zero_inv hl_lt hn_le hmax_le hprev_le hwv1 hws1 hsz1 hoff1 hzero1 hcov1
              hmax_elt hsrt1 hsz0 hl2 hlp1
              (fun j => by
                have hs := hset j
                refine ⟨?_, fun hj => ?_, hs.2.2⟩
                · rw [hl2]; exact hs.1
                · rw [hl2]; exact hs.2.1 hj)
              hm)
        · have hszp : 0 < fullWatchSize s l.toNat := by
            rw [← hsz_eq]
            exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by
              rw [list_getElem_toNat_eq (by omega) hidx_eq, h0]; rfl))
          clear hc
          have hoff_eq_s : (wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt).toNat =
              fullWatchOff s l.toNat := by
            have h1 := hoff1 l.toNat hl_lt hszp
            unfold fullWatchOff fullWatchOffCore; rw [← h1]
            rw [list_getElem_toNat_eq (by omega) hl2, List.getElem?_eq_getElem (by omega),
              Option.getD_some]
          have hoff_le_cap : fullWatchOff s l.toNat ≤ c.wcap := by
            have := hlay.bounds l.toNat hl_lt; unfold fullWatchOff fullWatchSize at *; omega
          let off64 : BitVec 64 := (wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt).setWidth 64
          have hoff64_nat : off64.toNat = fullWatchOff s l.toNat := by
            rw [zext_toNat _ (by decide), hoff_eq_s]
          have hlp1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1_nat (by omega)
          have hnp1 : (n + (1 : BitVec 64)).toNat = n.toNat + 1 := bv64_add1_nat (by omega)
          have htr : (l.setWidth 32).toNat = l.toNat := by
            rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
          let new_sorted : Bool := if off64.ult prev_off then false else sorted
          let new_max : BitVec 64 := if max_off.ult off64 then off64 else max_off
          c0_hstraight
          refine wp_join_group (ts := [.bool])
            (fun (nsort, ()) mJ => nsort = new_sorted ∧
              (FullMem c { s with core := { s.core with wvec := wvec1 },
                                  scratch := { s.scratch with wsort := wsort1 } } ⋆ R) mJ) ?_ ?_
          · rintro _ ⟨nsort, ⟨⟩⟩ mJ ⟨rfl, hmJ⟩; c0_hstraight
            refine wp_join_group (ts := [i64])
              (fun (nmax, ()) mJ2 => nmax = new_max ∧
                (FullMem c { s with core := { s.core with wvec := wvec1 },
                                    scratch := { s.scratch with wsort := wsort1 } } ⋆ R) mJ2) ?_ ?_
            · rintro _ ⟨nmax, ⟨⟩⟩ mJ2 ⟨rfl, hmJ2⟩
              c0_hstraight
              exact hJs _ _ (defrag_scan_pos_inv hl_lt hn_le hmax_le hprev_le hwv1 hws1 (by omega)
                hsz1 hoff1 hzero1 hcov1 hmax_elt hsrt1 hszp hoff_le_cap hoff64_nat hlp1 hnp1 htr hm)
            · intro J2 hJ2; c0_hsplit
              · have hult2 : max_off.ult off64 = true := by
                  unfold BitVec.ult; rw [decide_eq_true_eq, zext_toNat _ (by decide)]; exact hc
                clear hc; c0_hstraight; exact hJ2 (off64, ()) mJ ⟨by simp [new_max, hult2], hmJ⟩
              · have hult2 : max_off.ult off64 = false := by
                  unfold BitVec.ult; rw [decide_eq_false_iff_not, zext_toNat _ (by decide)]
                  exact hc
                clear hc; c0_hstraight
                exact hJ2 (max_off, ()) mJ ⟨by simp [new_max, hult2], hmJ⟩
          · intro J0 hJ0; c0_hsplit
            · have hult1 : off64.ult prev_off = true := by
                unfold BitVec.ult; rw [decide_eq_true_eq, zext_toNat _ (by decide)]; exact hc
              clear hc; c0_hstraight
              exact hJ0 (false, ()) m1 ⟨by simp only [new_sorted, hult1, ↓reduceIte], hm1⟩
            · have hult1 : off64.ult prev_off = false := by
                unfold BitVec.ult; rw [decide_eq_false_iff_not, zext_toNat _ (by decide)]
                exact hc
              clear hc; c0_hstraight
              exact hJ0 (sorted, ()) m1
                ⟨by simp only [new_sorted, hult1, Bool.false_eq_true, ↓reduceIte], hm1⟩
    · rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
      have hl_eq : l.toNat = 2 * s.core.cur_vars := by omega
      clear hc; rw [hl_eq] at hzero1 hcov1 hn_le; c0_hsplit
      · have hn0 : n.toNat = 0 := by rw [hc, h0_64]
        clear hc; have hwstk_pos : 0 < s.core.wstk.length := by omega
        c0_hstraight
        have hfin := defrag_finalize (s := s) (wvecC := wvec1)
          (wstkC := s.core.wstk.set 0 (0 : BitVec 32)) (wsort2 := wsort1) (n := 0) (p := 1)
          hlay (by simpa [hn0] using hcov1) (Nat.le_refl 1)
          ⟨fun j hj => by have := hsz1 j hj; unfold fullWatchSize fullWatchSizeCore; rw [this],
           fun j hj hz => by rw [hzero1 j hj hz]; rfl,
           fun _ h => by omega, fun _ h => by omega, fun _ _ h => by omega⟩
        exact hQ wvec1 (s.core.wstk.set 0 (0 : BitVec 32)) 1 wsort1 _
          ⟨{ hcl with wvec_len := hwv1, wstk_len_arr := by simp [hwsl],
                      wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws1 }⟩
          hfin.1 (fun _ => by omega) hfin.2 hm
      · have hn_pos : 0 < n.toNat :=
          Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h0, h0_64]))
        clear hc hLoop J; c0_hstraight
        refine wp_join_group (ts := []) (DefragSortPost c s R wvec1 n.toNat) ?_ ?_
        · rintro _ _ m2 ⟨wstk2, wsort2, hwst2, hws2, hwstk_pre, hcov2, hsrt2, hm2⟩
          clear hm1 wsort1 hws1 hcov1 hmax_elt hsrt1; c0_hstraight
          refine wp_loop_inv (DefragCompactInv c s R n.toNat wsort2)
            (fun (_, i, ()) _ => n.toNat - i.toNat)
            (fun JC hLoopC => by
              c0_hstraight
              exact hLoopC _ _ (defrag_compact_init_inv hwv1 hwst2 hwlen_gt1 hn_pos hlay hsz1 hoff1
                hzero1 hwstk_pre hcov2 hm2))
            ?_
          · rintro JC ⟨p, i, ⟨⟩⟩ mC ⟨hp1, hple, hile, hp_off, wvecC, wstkC,
              hwvC, hwsC, hcopC, hmC⟩ hLoopC
            have ⟨hszC, hzeroC, hdoneC, hdisjC, hremC⟩ := hcopC
            clear hm2; c0_hsplit
            · have hi_lt : i.toNat < n.toNat := hc; clear hc
              have hlit_info := hcov2.1 i.toNat hi_lt
              let wi := wsort2[i.toNat]'(by omega)
              have hlit_eq : wi.toNat = Spec.wsVal wsort2 i.toNat := (wsVal_getElem (by omega)).symm
              have hlit_cv : wi.toNat < 2 * s.core.cur_vars := hlit_eq ▸ hlit_info.1
              have hlit2 : (wi.setWidth 64 <<< (1 : Nat)).toNat =
                  2 * Spec.wsVal wsort2 i.toNat := by rw [bv64_shl1_lit, hlit_eq]
              have hlit2p1 : ((wi.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
                  2 * Spec.wsVal wsort2 i.toNat + 1 := by rw [bv64_add1_nat (by omega), hlit2]
              have hlit2_lt : (wi.setWidth 64 <<< (1 : Nat)).toNat < wvecC.length := by omega
              have hlit2p1_lt :
                  ((wi.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecC.length := by
                omega
              have hoff_i : (wvecC[(wi.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).toNat =
                  fullWatchOff s (Spec.wsVal wsort2 i.toNat) := by
                rw [list_getElem_toNat_eq (by omega) hlit2]
                have h1 := (hremC i.toNat (by omega) hi_lt).1
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
              have hsz_i : (wvecC[((wi.setWidth 64 <<< (1 : Nat)) +
                  (1 : BitVec 64)).toNat]'hlit2p1_lt).toNat =
                    fullWatchSize s (Spec.wsVal wsort2 i.toNat) := by
                rw [list_getElem_toNat_eq (by omega) hlit2p1]
                have h1 := hszC _ hlit_info.1
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
              have hbd_i : fullWatchOff s (Spec.wsVal wsort2 i.toNat) +
                  fullWatchSize s (Spec.wsVal wsort2 i.toNat) ≤ s.core.wlen :=
                hlay.bounds _ hlit_info.1
              have hp_le_off := hp_off hi_lt
              have hps_le : p.toNat + fullWatchSize s (Spec.wsVal wsort2 i.toNat) ≤ s.core.wlen :=
                by omega
              have hip1 : (i + (1 : BitVec 64)).toNat = i.toNat + 1 := bv64_add1_nat (by omega)
              have hpnxt :
                  (p + (wvecC[((wi.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'
                    hlit2p1_lt).setWidth 64).toNat =
                    p.toNat + fullWatchSize s (Spec.wsVal wsort2 i.toNat) := by
                rw [BitVec.toNat_add, zext_toNat _ (by decide), hsz_i, Nat.mod_eq_of_lt (by omega)]
              c0_hstraight
              refine wp_join_group (ts := [])
                (DefragCopyPost c s R wsort2 i.toNat p.toNat n.toNat) ?_ ?_
              · rintro _ _ mD ⟨wvecD, wstkD, hwvD, hwsD, hcopD, hmD⟩
                c0_hstraight; dsimp only
                exact hLoopC _ _ (by dsimp only; rw [hip1]; omega)
                  (defrag_compact_copy_next_inv hlay hcov2 hsrt2 hi_lt hp1 hp_le_off hps_le hip1
                    hpnxt hwvD hwsD hcopD hmD)
              · intro JD hJD; clear hLoopC hQ
                c0_hsplit
                · have hne : fullWatchOff s (Spec.wsVal wsort2 i.toNat) ≠ p.toNat := by
                    intro heq; apply hc; apply BitVec.eq_of_toNat_eq
                    have h2m : 2 * wsort2[i.toNat].toNat % 2 ^ 64 =
                        (wi.setWidth 64 <<< (1 : Nat)).toNat := by
                      change 2 * wi.toNat % 2 ^ 64 = _
                      rw [hlit2, hlit_eq, Nat.mod_eq_of_lt (by omega)]
                    exact (zext_toNat _ (by decide)).trans
                      (by rw [list_getElem_toNat_eq (by omega) h2m, hoff_i, heq])
                  clear hc
                  refine wp_loop_inv (DefragKInv c s R wvecC wstkC wsort2 i.toNat p.toNat)
                    (fun (k, ()) _ => fullWatchSize s (Spec.wsVal wsort2 i.toNat) - k.toNat)
                    (fun JK hLoopK => by
                      c0_hstraight
                      exact hLoopK _ _ ⟨by omega, wstkC, hwsC, fun _ _ => rfl, fun _ _ => rfl,
                        fun _ hr => by rw [h0_64] at hr; omega,
                        fun r _ hr => (hremC i.toNat (by omega) hi_lt).2 r hr, hmC⟩)
                    ?_
                  rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hpreK, hpostK, hcopK, hsrcK, hmK⟩ hLoopK
                  have hsz_i' :
                      wvecC[(2 * wsort2[i.toNat].toNat + (1 : BitVec 64).toNat) % 2 ^ 64].toNat =
                        fullWatchSize s (Spec.wsVal wsort2 i.toNat) := by
                    have h1 : (2 * wsort2[i.toNat].toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                        ((wi.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat := by
                      change (2 * wi.toNat + 1) % 2 ^ 64 = _
                      rw [hlit2p1, hlit_eq, Nat.mod_eq_of_lt (by omega)]
                    rw [list_getElem_toNat_eq (by omega) h1, hsz_i]
                  clear hmC; c0_hsplit
                  · have hk_lt : k.toNat < fullWatchSize s (Spec.wsVal wsort2 i.toNat) :=
                      hsz_i' ▸ hc
                    clear hc
                    have hkp1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 :=
                      bv64_add1_nat (by omega)
                    have hpk : (p + k).toNat = p.toNat + k.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                    have hok_eq :
                        ((wvecC[(wi.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).setWidth 64 +
                          k).toNat = fullWatchOff s (Spec.wsVal wsort2 i.toNat) + k.toNat := by
                      rw [BitVec.toNat_add, zext_toNat _ (by decide), hoff_i,
                        Nat.mod_eq_of_lt (by omega)]
                    have hok_lt :
                        ((wvecC[(wi.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).setWidth 64 +
                          k).toNat < wstkK.length := by rw [hok_eq, hwsK]; omega
                    have hpk_lt : (p + k).toNat < wstkK.length := by rw [hpk, hwsK]; omega
                    have hp_lt_off : p.toNat < fullWatchOff s (Spec.wsVal wsort2 i.toNat) :=
                      Nat.lt_of_le_of_ne hp_le_off hne.symm
                    c0_hstraight
                    exact hLoopK _ _ (by dsimp only; rw [hkp1]; omega)
                      (defrag_k_loop_step_inv hk_lt hp_lt_off hwsK rfl hpk hkp1 hpk_lt hok_lt
                        hok_eq hpreK hpostK hcopK hsrcK hm)
                  · have hk_eq : k.toNat = fullWatchSize s (Spec.wsVal wsort2 i.toNat) := by
                      rw [hsz_i'] at hc; omega
                    clear hc
                    have hp32 : (p.setWidth 32).toNat = p.toNat := by
                      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                    rw [hk_eq] at hcopK hpostK; c0_hstraight
                    have hcopD := defrag_compact_copy_inv hi_lt hp1 hp32 hcov2 hlay hsrt2
                      (by omega) hcopC hpreK hpostK hcopK
                    dsimp only at hm; rw [hlit2] at hm
                    exact hJD _ _ ⟨_, wstkK, by rw [List.length_set, hwvC], hwsK, hcopD, hm⟩
                · have hoff_eq_p : fullWatchOff s (Spec.wsVal wsort2 i.toNat) = p.toNat := by
                    have h := congrArg BitVec.toNat hc
                    have h2m : 2 * wsort2[i.toNat].toNat % 2 ^ 64 =
                        (wi.setWidth 64 <<< (1 : Nat)).toNat := by
                      change 2 * wi.toNat % 2 ^ 64 = _
                      rw [hlit2, hlit_eq, Nat.mod_eq_of_lt (by omega)]
                    rw [zext_toNat _ (by decide), list_getElem_toNat_eq (by omega) h2m, hoff_i]
                      at h
                    exact h
                  clear hc; c0_hstraight
                  exact hJD _ _ ⟨wvecC, wstkC, hwvC, hwsC,
                    defrag_compact_keep_inv hp1 hi_lt hcopC hoff_eq_p, hmC⟩
            · have hi_eq : i.toNat = n.toNat := by omega
              clear hc; c0_hstraight
              have hfin := defrag_finalize hlay hcov2 hp1 (hi_eq ▸ hcopC)
              exact hQ wvecC wstkC p.toNat wsort2 _
                ⟨{ hcl with wvec_len := hwvC, wstk_len_arr := hwsC,
                            wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws2 }⟩
                hfin.1 (fun _ => hp1) hfin.2 hm
        · intro JS hJS
          clear hQ hcl hsl hsz1 hzero1 hwvl hwle hwsrt_l hwlen_gt1 hwsl_pos hnlits
          let s1 : FullState :=
            { s with core := { s.core with wvec := wvec1 },
                     scratch := { s.scratch with wsort := wsort1 } }
          have hlen1 : FullState.LengthsOk c s1 :=
            ⟨{ hlen.core_ok with wvec_len := hwv1 }, { hlen.scratch_ok with wsort_len := hws1 }⟩
          c0_hsplit
          · refine hJS _ _
              ⟨s.core.wstk, wsort1, hwsl, hws1, fun _ _ => rfl, hcov1, (hsrt1 hc).1, hm1⟩
          · clear hc; c0_hsplit
            · have hn_gt1 : 1 < n.toNat := hc
              clear hc
              refine wp_join_group (ts := []) (DefragSortPost c s R wvec1 n.toNat)
                (fun _ _ _ hp => by c0_hstraight; exact hJS _ _ hp) fun JS hJS => ?_
              c0_hsplit
              · have h2n_le : 2 * n.toNat + 256 ≤ 2 * c.max_vars := by
                  simp only [h256_64,
                    Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : 2 * c.max_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : 2 * n.toNat + 256 < 2 ^ 64)] at hc
                  exact hc
                clear hc; c0_hstraight; c0_hcall hRadix
                exact defrag_b1_pre hlen1 hwsl hoff1 hcov1 (by omega) (by omega) h2n_le hm1
                  hmax_le hmax_elt fun m' hp => by
                    first | exact hJS _ _ hp | (c0_hstraight; exact hJS _ _ hp)
              · clear hc
                refine wp_join_group (ts := []) (DefragSortPost c s R wvec1 n.toNat)
                  (fun _ _ _ hp => by c0_hstraight; exact hJS _ _ hp) fun JS hJS => ?_
                c0_hsplit
                · have hcap_le : s.core.wlen + n.toNat + 256 ≤ c.wcap := by
                    have hle : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
                    simp only [h256_64,
                      Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : n.toNat + 256 < 2 ^ 64)] at hc
                    omega
                  clear hc; c0_hstraight; c0_hcall hRadix
                  exact defrag_b2_pre hlen1 hoff1 hcov1 (by omega) (by omega) (by omega) hcap_le hm1
                    hmax_le hmax_elt fun m' hp => by
                      first | exact hJS _ _ hp | (c0_hstraight; exact hJS _ _ hp)
                · clear hc hRadix hmax_elt hprev_le hmax_le; c0_hstraight
                  refine wp_loop_inv (DefragHeapInv c s R wvec1 n.toNat)
                    (fun ((st : Val i64), ()) _ => st.toNat)
                    (fun JB hLoopB => by
                      c0_hstraight
                      have hshr : (n >>> (1 : Nat)).toNat = n.toNat / 2 := bv64_shr1_nat n
                      refine hLoopB _ _ ⟨by rw [hshr]; exact Nat.div_le_self _ _, wsort1, hws1,
                        hcov1, fun _ hi _ => by rw [hshr] at hi; exact ⟨by omega, by omega⟩, hm1⟩)
                    ?_
                  rintro JB ⟨st, ⟨⟩⟩ mB ⟨hst_le, wsB, hwsB, hcovB, hmaxB, hmB⟩ hLoopB
                  clear hm1; c0_hsplit
                  · have hst_pos : 0 < st.toNat := by rw [h0_64] at hc; exact hc
                    clear hc
                    have hstm1 : (st - (1 : BitVec 64)).toNat = st.toNat - 1 :=
                      bv64_sub1_nat hst_pos
                    c0_hstraight; c0_hcall hSift
                    refine ⟨2 * s.core.cur_vars, wvec1, wsB, _, by rw [hwv1]; omega,
                      Nat.lt_of_lt_of_le
                        (by rw [hstm1]; exact Nat.sub_lt hst_pos Nat.one_pos) hst_le,
                      by omega, by rw [hwsB]; exact Nat.le_trans hn_le (by omega),
                      fun i hi => (hcovB.1 i hi).1,
                      by rw [hstm1, show st.toNat - 1 + 1 = st.toNat by omega]; exact hmaxB,
                      focus_wvec_wsort hmB, ?_⟩
                    intro ws' m' hws' hperm' hsuf' hmax' hm'
                    have hm'' := unfocus_wvec_wsort (s := { s with
                      core := { s.core with wvec := wvec1 },
                      scratch := { s.scratch with wsort := wsB } }) hm'
                    c0_hstraight
                    exact hLoopB _ _
                      (by dsimp only; rw [hstm1]; exact Nat.sub_lt hst_pos Nat.one_pos)
                      (defrag_heap_step_inv hn_le hcv_le hst_pos hst_le hstm1 hwsB hcovB hws' hperm'
                        (fun i hi => hsuf' i (Or.inr (by omega))) hmax' hm'')
                  · have hst0 : st.toNat = 0 := by rw [h0_64] at hc; omega
                    clear hc hLoopB JB hst_le; rw [hst0] at hmaxB
                    c0_hstraight
                    refine wp_loop_inv (DefragExtractInv c s R wvec1 n.toNat)
                      (fun ((e : Val i64), ()) _ => e.toNat)
                      (fun JE hLoopE => by
                        c0_hstraight
                        have hnm1 : (n - (1 : BitVec 64)).toNat = n.toNat - 1 :=
                          bv64_sub1_nat hn_pos
                        have hnm1p1 : (n - (1 : BitVec 64)).toNat + 1 = n.toNat := by
                          rw [hnm1]; omega
                        refine hLoopE _ _ ⟨by rw [hnm1]; exact Nat.sub_lt hn_pos Nat.one_pos,
                          wsB, hwsB, hcovB, by rw [hnm1p1]; exact hmaxB,
                          fun _ hi _ _ _ => by rw [hnm1p1] at hi; omega,
                          fun _ _ hi _ _ => by rw [hnm1p1] at hi; omega, hmB⟩)
                      ?_
                    rintro JE ⟨e, ⟨⟩⟩ mE ⟨he_lt, wsE, hwsE, hcovE, hmaxE, hspE, hsrtE, hmE⟩ hLoopE
                    clear hmB wsB hwsB hcovB hmaxB; c0_hsplit
                    · have he_pos : 0 < e.toNat := by rw [h0_64] at hc; exact hc
                      clear hc
                      have hem1 : (e - (1 : BitVec 64)).toNat = e.toNat - 1 := bv64_sub1_nat he_pos
                      have h0_lt : 0 < wsE.length := hwsE ▸ Nat.lt_of_lt_of_le he_pos
                        (Nat.le_trans (Nat.le_of_lt he_lt)
                          (Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le)))
                      have he_len : e.toNat < wsE.length := hwsE ▸ Nat.lt_of_lt_of_le he_lt
                        (Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
                      c0_hstraight; c0_hcall hSift
                      have hsw_step := wsort_extract_swap_step hmaxE hspE hsrtE he_pos he_lt
                        (by rw [hwsE]; exact Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
                      have hsw_cov := wsCovers_swap hcovE (i := 0) (j := e.toNat) (by omega)
                        he_lt (by omega) he_len
                      let wsSwap := swapIdx wsE 0 e.toNat
                      have hsw_eq : wsSwap =
                          (wsE.set 0 (wsE[e.toNat]'he_len)).set e.toNat (wsE[0]'h0_lt) := by
                        unfold wsSwap swapIdx; split; rfl; omega
                      have hm_sw : (FullMem c { s with
                          core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsSwap } } ⋆ R) m := by
                        rw [hsw_eq]; exact hm
                      refine ⟨2 * s.core.cur_vars, wvec1, wsSwap, _, by rw [hwv1]; omega,
                        by omega, by omega, by rw [hsw_eq]; simp; omega,
                        fun i hi => (hsw_cov.1 i (by omega)).1, hsw_step.1,
                        focus_wvec_wsort hm_sw, ?_⟩
                      intro ws' m' hws' hperm' hsuf' hmax' hm'
                      have hm'' := unfocus_wvec_wsort (s := { s with
                        core := { s.core with wvec := wvec1 },
                        scratch := { s.scratch with wsort := wsSwap } }) hm'
                      c0_hstraight
                      rw [hsw_eq] at hws' hperm'
                      exact hLoopE _ _
                        (by dsimp only; rw [hem1]; exact Nat.sub_lt he_pos Nat.one_pos)
                        (defrag_extract_next
                          (Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
                          he_pos he_lt hem1 hwsE hws' hmaxE hspE hsrtE hcovE hperm'
                          (fun i hi => hsw_eq ▸ hsuf' i hi) hmax' hm'')
                    · have he0 : e.toNat = 0 := by rw [h0_64] at hc; omega
                      clear hc; rw [he0] at hspE hsrtE
                      c0_hstraight
                      exact hJS _ _ ⟨s.core.wstk, wsE, hwsl, hwsE, fun _ _ => rfl,
                        hcovE, defrag_extract_done hoff1 hcovE hspE hsrtE, hmE⟩
            · have hn1 : n.toNat ≤ 1 := by omega
              clear hc; c0_hstraight
              exact hJS _ _ ⟨s.core.wstk, wsort1, hwsl, hws1, fun _ _ => rfl,
                hcov1, fun i j _ hij hj => by
                  have heq : i = j := by omega
                  subst heq; exact Nat.le_refl _, hm1⟩

theorem full_wstack_defrag_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X, Proof.Spec.fullWstackDefragSpec a m Q X →
      Func.wp Γ full_wstack_defrag_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, full_wstack_defrag_body]
  c0_hcall (Spec.has_full_wstack_defrag_m6 hΓ)
  exact hPre

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-! # Watch WP Proofs Part 0: `full_wsort_sift`

Self-contained `CanonicalEnv` WP proof for `full_wsort_sift`. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Std.ExtHashMap
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private def FullWsortHoleParent (wvec ws : List (BitVec 32)) (lo n root : Nat) : Prop :=
  lo ≤ root ∧ root < n ∧
  ∀ c, c = 2 * root + 1 ∨ c = 2 * root + 2 → c < n → root ≠ lo →
    (wvec[2 * Spec.wsVal ws c]?.getD 0#32).toNat ≤
    (wvec[2 * Spec.wsVal ws ((root - 1) / 2)]?.getD 0#32).toNat

private def FullWsortMaxHeapExcept (wvec ws : List (BitVec 32))
    (lo n root : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n → i ≠ root →
    have p := (wvec[2 * Spec.wsVal ws i]?.getD 0#32).toNat
    (2 * i + 1 < n → (wvec[2 * Spec.wsVal ws (2 * i + 1)]?.getD 0#32).toNat ≤ p) ∧
    (2 * i + 2 < n → (wvec[2 * Spec.wsVal ws (2 * i + 2)]?.getD 0#32).toNat ≤ p)

private theorem fullWsortMaxHeap_sift_done {wvec ws : List (BitVec 32)} {lo n root : Nat}
    (hmax : FullWsortMaxHeapExcept wvec ws lo n root)
    (h1 : 2 * root + 1 < n →
      (wvec[2 * Spec.wsVal ws (2 * root + 1)]?.getD 0#32).toNat ≤
      (wvec[2 * Spec.wsVal ws root]?.getD 0#32).toNat)
    (h2 : 2 * root + 2 < n →
      (wvec[2 * Spec.wsVal ws (2 * root + 2)]?.getD 0#32).toNat ≤
      (wvec[2 * Spec.wsVal ws root]?.getD 0#32).toNat) :
    FullWsortMaxHeap wvec ws lo n := fun i hlo hi =>
  if hir : i = root then hir ▸ ⟨h1, h2⟩ else hmax i hlo hi hir

private theorem fullWsort_sift_step {wvec ws : List (BitVec 32)} {lo n root ch : Nat}
    (hlo : lo ≤ root) (hch : ch < n) (hrel : ch = 2 * root + 1 ∨ ch = 2 * root + 2)
    (hil : root < ws.length) (hjl : ch < ws.length)
    (hmax : FullWsortMaxHeapExcept wvec ws lo n root)
    (hpar : FullWsortHoleParent wvec ws lo n root)
    (hlt : (wvec[2 * Spec.wsVal ws root]?.getD 0#32).toNat <
           (wvec[2 * Spec.wsVal ws ch]?.getD 0#32).toNat)
    (hmaxch : (2 * root + 1 < n →
        (wvec[2 * Spec.wsVal ws (2 * root + 1)]?.getD 0#32).toNat ≤
        (wvec[2 * Spec.wsVal ws ch]?.getD 0#32).toNat) ∧
      (2 * root + 2 < n →
        (wvec[2 * Spec.wsVal ws (2 * root + 2)]?.getD 0#32).toNat ≤
        (wvec[2 * Spec.wsVal ws ch]?.getD 0#32).toNat)) :
    FullWsortMaxHeapExcept wvec (swapIdx ws root ch) lo n ch ∧
    FullWsortHoleParent wvec (swapIdx ws root ch) lo n ch := by
  let ws' := swapIdx ws root ch
  let key : List (BitVec 32) → Nat → Nat :=
    fun xs k => (wvec[2 * Spec.wsVal xs k]?.getD 0#32).toNat
  have hk_root : key ws' root = key ws ch := by simp [key, ws', wsVal_swap hil hjl]
  have hk_ch : key ws' ch = key ws root := by
    have : root < ch := by omega
    simp [key, ws', wsVal_swap hil hjl, show ch ≠ root by omega]
  have hk_other : ∀ k, k ≠ root → k ≠ ch → key ws' k = key ws k := fun k hkr hkc => by
    simp [key, ws', wsVal_swap hil hjl, hkr, hkc]
  have hrc : root < ch := by omega
  have hpar_ch : (ch - 1) / 2 = root := by omega
  dsimp only [key] at hk_root hk_ch hk_other
  refine ⟨fun i hloi hi hich => ?_, ⟨by omega, hch, fun c hc hc_lt _ => ?_⟩⟩
  · change (2 * i + 1 < n → key ws' (2 * i + 1) ≤ key ws' i) ∧
      (2 * i + 2 < n → key ws' (2 * i + 2) ≤ key ws' i)
    dsimp only [key]
    by_cases hir : i = root
    · subst hir; rw [hk_root]
      refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
      · by_cases h1c : 2 * i + 1 = ch
        · rw [h1c, hk_ch]; omega
        · rw [hk_other _ (by omega) h1c]; exact hmaxch.1 hc1
      · by_cases h2c : 2 * i + 2 = ch
        · rw [h2c, hk_ch]; omega
        · rw [hk_other _ (by omega) h2c]; exact hmaxch.2 hc2
    · rw [hk_other i hir hich]; have hold := hmax i hloi hi hir
      refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
      · by_cases h1c : 2 * i + 1 = ch
        · have : (ch - 1) / 2 = i := by rw [← h1c]; omega
          omega
        · by_cases h1r : 2 * i + 1 = root
          · rw [h1r, hk_root]
            have hpr : (root - 1) / 2 = i := by rw [← h1r]; omega
            rw [← hpr]; exact hpar.2.2 ch hrel hch (by omega)
          · rw [hk_other _ h1r h1c]; exact hold.1 hc1
      · by_cases h2c : 2 * i + 2 = ch
        · have : (ch - 1) / 2 = i := by rw [← h2c]; omega
          omega
        · by_cases h2r : 2 * i + 2 = root
          · rw [h2r, hk_root]
            have hpr : (root - 1) / 2 = i := by rw [← h2r]; omega
            rw [← hpr]; exact hpar.2.2 ch hrel hch (by omega)
          · rw [hk_other _ h2r h2c]; exact hold.2 hc2
  · change key ws' c ≤ key ws' ((ch - 1) / 2)
    dsimp only [key]; rw [hpar_ch, hk_root, hk_other c (by omega) (by omega)]
    have hmch := hmax ch (by omega) hch (by omega)
    rcases hc with rfl | rfl
    · exact hmch.1 hc_lt
    · exact hmch.2 hc_lt

private theorem wsort_wvec_get {wvec ws : List (BitVec 32)} {k n nlits idx : Nat}
    (hk : k < n) (hn : n ≤ ws.length) (hcov : ∀ i < n, (ws[i]?.getD 0#32).toNat < nlits)
    (_hnl : 2 * nlits ≤ wvec.length) (hidx : idx = 2 * (ws[k]'(by omega)).toNat)
    (hlt : idx < wvec.length) :
    wvec[idx]'hlt = wvec[2 * Spec.wsVal ws k]?.getD 0#32 := by
  have h1 : idx = 2 * Spec.wsVal ws k := by rw [hidx, wsVal_getElem (by omega)]
  have hbd : (ws[k]'(by omega)).toNat < nlits := by
    have := hcov k hk; rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact list_getElem_congr hlt h1

public section

theorem full_wsort_sift_wp (Γ : Env) :
    ∀ a m Q X, fullWsortSiftSpec a m Q X → Func.wp Γ full_wsort_sift_body a m Q X := by
  rintro ⟨wvec_ptr, ws_ptr, start, n, ⟨⟩⟩ m Q X
    ⟨nlits, wvec, ws, R, hnl, hst_lt, hn_bd, hn_len, hcov, hmax0, hm, hQ⟩
  dsimp only [Func.wp, full_wsort_sift_body]
  c0_hsteps_nogrp
  refine wp_join_group (fun _ m1 =>
    ∃ ws' : List (BitVec 32), ws'.length = ws.length ∧ ws'.Perm ws ∧
      (∀ i, i < start.toNat ∨ n.toNat ≤ i → ws'[i]? = ws[i]?) ∧
      FullWsortMaxHeap wvec ws' start.toNat n.toNat ∧
      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws' ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ws', hwsl, hperm, hpres, hmax, hm1⟩
    c0_hsteps_nogrp; exact hQ ws' m1 hwsl hperm hpres hmax hm1
  · intro Js hJs
    refine wp_loop_inv
      (fun (root, ()) mS =>
        start.toNat ≤ root.toNat ∧ root.toNat < n.toNat ∧ ∃ wsS : List (BitVec 32),
          wsS.length = ws.length ∧ wsS.Perm ws ∧
          (∀ i, i < start.toNat ∨ n.toNat ≤ i → wsS[i]? = ws[i]?) ∧
          (∀ i < n.toNat, (wsS[i]?.getD 0#32).toNat < nlits) ∧
          FullWsortMaxHeapExcept wvec wsS start.toNat n.toNat root.toNat ∧
          FullWsortHoleParent wvec wsS start.toNat n.toNat root.toNat ∧
          (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆ R) mS)
      (fun (root, ()) _ => n.toNat - root.toNat)
      (fun Js_1 hLoopS => by
        c0_hsteps_nogrp
        refine hLoopS (start, ()) m ⟨Nat.le_refl _, hst_lt, ws, rfl, .refl _,
          fun _ _ => rfl, hcov, fun i _ h2 _ => hmax0 i (by omega) h2,
          ⟨Nat.le_refl _, hst_lt, fun _ _ _ hne => absurd rfl hne⟩, hm⟩)
      (fun Js_1 ⟨root, ⟨⟩⟩ mS
          ⟨hloS, hrt_lt, wsS, hwsS, hpermS, hpresS, hcovS, hmaxS, hparS, hmS⟩ hLoopS => ?_)
    have hch1_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by
        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
      rw [BitVec.toNat_add, hsh]; simp; omega
    have h1_bv : (1 : BitVec 64).toNat = 1 := rfl
    c0_hsplit
    · clear hc; c0_hsplit
      · rw [h1_bv] at hc; have hge : n.toNat ≤ 2 * root.toNat + 1 := by omega
        clear hc; c0_hsteps_nogrp
        exact hJs (root, ()) mS ⟨wsS, hwsS, hpermS, hpresS,
          fullWsortMaxHeap_sift_done hmaxS (fun h => by omega) (fun h => by omega), hmS⟩
      · rw [h1_bv] at hc; have hch1_lt : 2 * root.toNat + 1 < n.toNat := by omega
        clear hc
        have hws_c1_bd : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wsS.length := by omega
        have hws_c1_val : wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd =
            wsS[2 * root.toNat + 1]'(by omega) := list_getElem_congr hws_c1_bd hch1_eq
        have hwc1_bd : (wsS[2 * root.toNat + 1]'(by omega)).toNat < nlits := by
          have h0 := hcovS _ hch1_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
        have hwvc1 : (((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).setWidth
            64) <<< (1 : Nat)).toNat < wvec.length := by
          rw [bv64_shl1_lit, hws_c1_val]; omega
        have hco1_eq := wsort_wvec_get hch1_lt (hwsS ▸ hn_len) hcovS hnl
          (by rw [bv64_shl1_lit, hws_c1_val]) hwvc1
        have hco1_mod_bd :
            2 * (wsS[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hws_c1_bd).toNat % 2 ^ 64 <
              wvec.length := by
          rw [hws_c1_val, Nat.mod_eq_of_lt (by omega)]; omega
        have hco1_mod := wsort_wvec_get hch1_lt (hwsS ▸ hn_len) hcovS hnl
          (by rw [hws_c1_val, Nat.mod_eq_of_lt (by omega)]) hco1_mod_bd
        c0_hstraight
        refine wp_join_group (fun (ch, co, ()) mJ =>
          (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
          ch.toNat < n.toNat ∧ co = wvec[2 * Spec.wsVal wsS ch.toNat]?.getD 0#32 ∧
          (2 * root.toNat + 1 < n.toNat →
            (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat ≤ co.toNat) ∧
          (2 * root.toNat + 2 < n.toNat →
            (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat ≤ co.toNat) ∧
          mS = mJ) ?_ ?_
        · rintro _ ⟨ch, co, ⟨⟩⟩ mJ ⟨hch_or, hch_lt, hco_eq, hmax_c1, hmax_c2, hmJ⟩
          subst hmJ
          have hwr : (wsS[root.toNat]'(by omega)).toNat < nlits := by
            have h0 := hcovS root.toNat hrt_lt
            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
          have hwvr : (((wsS[root.toNat]'(by omega)).setWidth 64) <<< (1 : Nat)).toNat <
              wvec.length := by rw [bv64_shl1_lit]; omega
          have hro_mod_bd : 2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64 < wvec.length := by
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          have hro_eq := wsort_wvec_get hrt_lt (hwsS ▸ hn_len) hcovS hnl
            (Nat.mod_eq_of_lt (by omega)) hro_mod_bd
          c0_hstraight; c0_hsplit
          · have hge : co.toNat ≤ (wvec[2 * Spec.wsVal wsS root.toNat]?.getD 0#32).toNat := by
              rw [← hro_eq]; omega
            clear hc; c0_hstraight
            exact hJs (root, ()) mS ⟨wsS, hwsS, hpermS, hpresS,
              fullWsortMaxHeap_sift_done hmaxS (fun h => Nat.le_trans (hmax_c1 h) hge)
                (fun h => Nat.le_trans (hmax_c2 h) hge), hmS⟩
          · have hlt : (wvec[2 * Spec.wsVal wsS root.toNat]?.getD 0#32).toNat <
                (wvec[2 * Spec.wsVal wsS ch.toNat]?.getD 0#32).toNat := by
              rw [← hro_eq, ← hco_eq]; omega
            clear hc; c0_hstraight
            have hws'_eq : (wsS.set root.toNat (wsS[ch.toNat]'(by omega))).set ch.toNat
                (wsS[root.toNat]'(by omega)) = swapIdx wsS root.toNat ch.toNat := by
              simp [swapIdx, show root.toNat < wsS.length by omega,
                show ch.toNat < wsS.length by omega]
            have hstep := fullWsort_sift_step hloS hch_lt hch_or (by omega) (by omega)
              hmaxS hparS hlt ⟨fun h => by rw [← hco_eq]; exact hmax_c1 h,
                fun h => by rw [← hco_eq]; exact hmax_c2 h⟩
            refine hLoopS (ch, ()) _ (by dsimp only; omega)
              ⟨by omega, hch_lt, swapIdx wsS root.toNat ch.toNat,
                by rw [swapIdx_length, hwsS], swapIdx_perm.trans hpermS,
                fun i hi => ?_, fun i hi => ?_, hstep.1, hstep.2, ?_⟩
            · by_cases hil : i < wsS.length
              · rw [List.getElem?_eq_getElem (by rw [swapIdx_length]; exact hil),
                  swapIdx_getElem_other (by omega) (by omega) hil
                    (by rcases hi with h | h <;> omega) (by rcases hi with h | h <;> omega),
                  ← List.getElem?_eq_getElem hil]
                exact hpresS i hi
              · rw [List.getElem?_eq_none (by rw [swapIdx_length]; omega),
                  List.getElem?_eq_none (by omega)]
            · rw [List.getElem?_eq_getElem (by rw [swapIdx_length, hwsS]; omega), Option.getD_some]
              have hcov_fn : ∀ (k : Nat) (hk : k < n.toNat),
                  (wsS[k]'(Nat.lt_of_lt_of_le hk (hwsS ▸ hn_len))).toNat < nlits := fun k hk => by
                have h0 := hcovS k hk
                rwa [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hk (hwsS ▸ hn_len)),
                  Option.getD_some] at h0
              by_cases kir : i = root.toNat
              · subst kir; rw [(swapIdx_getElem_self (by omega) (by omega)).1]
                exact hcov_fn _ hch_lt
              · by_cases kic : i = ch.toNat
                · subst kic; rw [(swapIdx_getElem_self (by omega) (by omega)).2]
                  exact hcov_fn _ hrt_lt
                · rw [swapIdx_getElem_other (by omega) (by omega) (by omega) kir kic]
                  exact hcov_fn i hi
            · have hmem := hm
              rw [hws'_eq, sep_comm R emp, emp_sep, sep_comm_l, ← sep_assoc] at hmem
              exact hmem
        · intro J2 hJ2; c0_hstraight; c0_hsplit
          · rw [h1_bv] at hc
            have hc2_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                2 * root.toNat + 2 := by rw [BitVec.toNat_add, hch1_eq]; simp; omega
            have hch2_lt : 2 * root.toNat + 2 < n.toNat := by omega
            have hws_c2_bd :
                ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat < wsS.length := by
              omega
            have hws_c2_val :
                wsS[((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat]'hws_c2_bd =
                  wsS[2 * root.toNat + 2]'(by omega) := list_getElem_congr hws_c2_bd hc2_eq
            have hwc2_bd : (wsS[2 * root.toNat + 2]'(by omega)).toNat < nlits := by
              have h0 := hcovS _ hch2_lt
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
            have hwvc2 : (((wsS[((root <<< (1 : Nat)) + (1 : BitVec 64) +
                (1 : BitVec 64)).toNat]'hws_c2_bd).setWidth 64) <<< (1 : Nat)).toNat <
                wvec.length := by rw [bv64_shl1_lit, hws_c2_val]; omega
            have hco2_eq := wsort_wvec_get hch2_lt (hwsS ▸ hn_len) hcovS hnl
              (by rw [bv64_shl1_lit, hws_c2_val]) hwvc2
            have hi1 : (2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * root.toNat + 1 := by
              rw [h1_bv, Nat.mod_eq_of_lt (by omega)]
            have hi2 : (2 * root.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                2 * root.toNat + 2 := by rw [h1_bv, Nat.mod_eq_of_lt (by omega)]
            have hco1_raw_bd :
                2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                  rw [hi1]; omega)).toNat % 2 ^ 64 < wvec.length := by
              rw [list_getElem_congr _ hi1, Nat.mod_eq_of_lt (by omega)]; omega
            have hco1_raw := wsort_wvec_get hch1_lt (hwsS ▸ hn_len) hcovS hnl
              (by rw [list_getElem_congr _ hi1, Nat.mod_eq_of_lt (by omega)]) hco1_raw_bd
            have hco2_raw_bd :
                2 * (wsS[(2 * root.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) %
                  2 ^ 64]'(by rw [hi2]; omega)).toNat % 2 ^ 64 < wvec.length := by
              rw [list_getElem_congr _ hi2, Nat.mod_eq_of_lt (by omega)]; omega
            have hco2_raw := wsort_wvec_get hch2_lt (hwsS ▸ hn_len) hcovS hnl
              (by rw [list_getElem_congr _ hi2, Nat.mod_eq_of_lt (by omega)]) hco2_raw_bd
            clear hc; c0_hstraight
            refine wp_join_group (fun (ch, co, ()) mJ =>
              mS = mJ ∧
              (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
              ch.toNat < n.toNat ∧ co = wvec[2 * Spec.wsVal wsS ch.toNat]?.getD 0#32 ∧
              (2 * root.toNat + 1 < n.toNat →
                (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat ≤ co.toNat) ∧
              (2 * root.toNat + 2 < n.toNat →
                (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat ≤ co.toNat)) ?_ ?_
            · rintro _ ⟨ch, co, ⟨⟩⟩ mJ ⟨hmJ, h1, h2, h3, h4, h5⟩
              subst hmJ; c0_hstraight; exact hJ2 (ch, co, ()) mS ⟨h1, h2, h3, h4, h5, rfl⟩
            · intro J3 hJ3; c0_hsplit
              · have hgt : (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat <
                    (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat := by
                  rw [← hco1_raw, ← hco2_raw]; omega
                clear hc; c0_hstraight
                exact hJ3 _ mS ⟨rfl, Or.inr hc2_eq, by rw [hc2_eq]; exact hch2_lt,
                  by rw [hco2_eq, hc2_eq], fun _ => by rw [hco2_eq]; omega,
                  fun _ => by rw [hco2_eq]; exact Nat.le_refl _⟩
              · have hle : (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 2)]?.getD 0#32).toNat ≤
                    (wvec[2 * Spec.wsVal wsS (2 * root.toNat + 1)]?.getD 0#32).toNat := by
                  rw [← hco1_raw, ← hco2_raw]; omega
                clear hc; c0_hstraight
                exact hJ3 _ mS ⟨rfl, Or.inl hch1_eq, by rw [hch1_eq]; omega,
                  by rw [hco1_eq, hch1_eq], fun _ => by rw [hco1_eq]; exact Nat.le_refl _,
                  fun _ => by rw [hco1_eq]; omega⟩
          · rw [h1_bv] at hc
            have hc2_ge : n.toNat ≤ 2 * root.toNat + 2 := by
              have : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                  2 * root.toNat + 2 := by rw [BitVec.toNat_add, hch1_eq]; simp; omega
              omega
            clear hc; c0_hstraight
            exact hJ2 _ mS ⟨Or.inl hch1_eq, by rw [hch1_eq]; omega, by rw [hco1_eq, hch1_eq],
              fun _ => by rw [hco1_eq]; exact Nat.le_refl _, fun h => by omega, rfl⟩
    · cases hc

end

end LeanQbe.T.Examples.Kissat.Proof.Watch

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Leaf and Read-Only WP Proofs for `Src.Factor` (`7` Functions)

Proves parametric `Func.wp` contracts (`0` legacy imports, `0` placeholders,
`XPost`-polymorphic) for:
- `full_bva_steps_cap_fid` (`fidBvaStepsCapSpec`)
- `full_bva_clines_fid` (`fidBvaClinesSpec`)
- `full_fheap_up_fid` (`fidFheapUpSpec`)
- `full_fheap_down_fid` (`fidFheapDownSpec`)
- `full_bva_count_lit_deg_fid` (`fidBvaCountLitDegSpec`)
- `full_bva_match_large_bva_fid` (`fidBvaMatchLargeBvaSpec`)
- `full_has_factor_cands_fid` (`step13HasFactorCandsSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

/-! ## 1. Pure Leaf Proofs: `full_bva_steps_cap_fid`, `full_bva_clines_fid` -/

theorem full_bva_steps_cap_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaStepsCapSpec a m Q X → Func.wp Γ full_bva_steps_cap_fid_body a m Q X := by
  rintro ⟨cap, ⟨⟩⟩ m Q X hQ
  unfold fidBvaStepsCapSpec at hQ
  unfold Func.wp full_bva_steps_cap_fid_body
  c0_hsteps
  · have h1 : 8192 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : 1024 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1, h2] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : ¬ (1024 ≤ cap.toNat) := by c0_bound
    have h3 : 256 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1, h2, h3] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : ¬ (1024 ≤ cap.toNat) := by c0_bound
    have h3 : ¬ (256 ≤ cap.toNat) := by c0_bound
    have h4 : 64 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1, h2, h3, h4] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : ¬ (1024 ≤ cap.toNat) := by c0_bound
    have h3 : ¬ (256 ≤ cap.toNat) := by c0_bound
    have h4 : ¬ (64 ≤ cap.toNat) := by c0_bound
    simpa [fidStepsCap, h1, h2, h3, h4] using hQ

theorem full_bva_clines_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaClinesSpec a m Q X → Func.wp Γ full_bva_clines_fid_body a m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_bva_clines_fid_body
  c0_hsteps <;> exact hQ _

/-! ## 2. Exact-Degree Heap Sift Proofs: `full_fheap_up_fid`, `full_fheap_down_fid` -/

theorem full_fheap_up_fid_wp (Γ : Env) :
    ∀ a m Q X, fidFheapUpSpec a m Q X → Func.wp Γ full_fheap_up_fid_body a m Q X := by
  rintro ⟨hp_ptr, ps_ptr, deg_ptr, p0, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, deg, R, hhp_len, hps_len, hdeg_len, hnl_lt, hp0_lt, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := fid_bv64_32
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat (Nat.le_refl _)
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  unfold Func.wp full_fheap_up_fid_body
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat ≤ p0.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, p0.toNat < i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) deg_ptr deg ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_le, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) deg_ptr deg ⋆ R) m := by
      dsimp only [hpf', psf']; simp only [hset] at hm; exact sep_ac hm
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie; refine ⟨p0.toNat, Nat.le_refl _, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat ≤ p0.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, p0.toNat < i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) deg_ptr deg ⋆ R) ml)
      (fun (p, ()) _ => p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, Nat.le_refl _, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    c0_hsteps
    · have hp_pos : 0 < p.toNat := by c0_bound
      have hpp_nat : ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat = (p.toNat - 1) / 2 :=
        bv32_sub1_ushr1 hp_pos
      have hpp_lt : ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat < p.toNat := by omega
      have hpl_ok :
          (hpl[((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat (by omega)
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hpl_ok_sw :
          (hpl[(BitVec.setWidth 64 ((p - (1 : BitVec 32)) >>> (1 : BitVec 32))).toNat]'(by
            simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hpl_ok
      c0_hsteps
      · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩
      · let par := (p - (1 : BitVec 32)) >>> (1 : BitVec 32)
        have hpar_nat : par.toNat = (p.toNat - 1) / 2 := hpp_nat
        let hpl' := hpl.set p.toNat (hpl[par.toNat]'(by omega))
        let psl' := psl.set (hpl[par.toNat]'(by omega)).toNat p
        have hmem : (array (t := i32) hp_ptr hpl' ⋆ array (t := i32) ps_ptr psl' ⋆
            array (t := i32) deg_ptr deg ⋆ R) m := by
          dsimp only [hpl', psl', par]; simp only [hset] at hm; exact sep_ac hm
        refine ih (par, ()) _ (by dsimp only; omega)
          ⟨hpl', psl', by omega, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
           fun i hi => ?_,
           fun i hi => by
             dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
           hmem⟩
        dsimp only [hpl']
        by_cases hie : i = p.toNat
        · subst hie
          obtain ⟨j, hj, heq⟩ := hsub par.toNat (by omega)
          refine ⟨j, hj, ?_⟩
          rw [List.getElem?_set_self (by omega), ← heq, List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩

theorem full_fheap_down_fid_wp (Γ : Env) :
    ∀ a m Q X, fidFheapDownSpec a m Q X → Func.wp Γ full_fheap_down_fid_body a m Q X := by
  rintro ⟨hp_ptr, ps_ptr, deg_ptr, p0, n, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, deg, R, hhp_len, hps_len, hdeg_len, hnl_lt, hp0_lt, hn_le, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := fid_bv64_32
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat hp0_lt
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  unfold Func.wp full_fheap_down_fid_body
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat < n.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i < n.toNat, ∃ j < n.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, n.toNat ≤ i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) deg_ptr deg ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_lt, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) deg_ptr deg ⋆ R) m := by
      dsimp only [hpf', psf']; simp only [hset] at hm; exact sep_ac hm
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie; refine ⟨p0.toNat, hp0_lt, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat < n.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i < n.toNat, ∃ j < n.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, n.toNat ≤ i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) deg_ptr deg ⋆ R) ml)
      (fun (p, ()) _ => n.toNat - p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, hp0_lt, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    have hlc_nat : ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat = 2 * p.toNat + 1 :=
      bv32_shl1_add1 (by omega)
    c0_hsteps_nogrp
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
    · have hlc_lt : ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat < n.toNat := by c0_bound
      have hcl_ok :
          (hpl[((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat hlc_lt
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hcl_ok_sw :
          (hpl[(BitVec.setWidth 64 ((p <<< (1 : BitVec 32)) + (1 : BitVec 32))).toNat]'(by
            simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hcl_ok
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
        (fun ⟨best, bd⟩ => (best, bd, ()))
        (fun ⟨best, _⟩ mf =>
          p.toNat < best.toNat ∧ best.toNat < n.toNat ∧ ml = mf)
        (fun _ ⟨best, bd⟩ mf ⟨hgt_p, hbest_lt, hmf⟩ => ?_)
        (fun Jc hJc => ?_)
      · rcases hmf with rfl
        have hbl_ok : (hpl[best.toNat]'(by omega)).toNat < nlits := by
          obtain ⟨j, hj, heq⟩ := hsub best.toNat hbest_lt
          have h1 := hhp0_ok j hj
          rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
        c0_hsteps
        · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
        · let hpl' := hpl.set p.toNat (hpl[best.toNat]'(by omega))
          let psl' := psl.set (hpl[best.toNat]'(by omega)).toNat p
          have hmem : (array (t := i32) hp_ptr hpl' ⋆ array (t := i32) ps_ptr psl' ⋆
              array (t := i32) deg_ptr deg ⋆ R) m := by
            dsimp only [hpl', psl']; simp only [hset] at hm; exact sep_ac hm
          refine ih (best, ()) _ (by dsimp only; omega)
            ⟨hpl', psl', hbest_lt, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
             fun i hi => ?_,
             fun i hi => by
               dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
             hmem⟩
          dsimp only [hpl']
          by_cases hie : i = p.toNat
          · subst hie
            obtain ⟨j, hj, heq⟩ := hsub best.toNat hbest_lt
            refine ⟨j, hj, ?_⟩
            rw [List.getElem?_set_self (by omega), ← heq, List.getElem?_eq_getElem (by omega)]
          · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
      · c0_hsteps_nogrp
        · have hrc_nat :
              (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat =
                2 * p.toNat + 2 :=
            bv32_shl1_add2 (by omega)
          have hrc_lt :
              (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat < n.toNat := by
            c0_bound
          have hrl_ok :
              (hpl[(((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat]'(by
                omega)).toNat < nlits := by
            obtain ⟨j, hj, heq⟩ :=
              hsub (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat hrc_lt
            have h1 := hhp0_ok j hj
            rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
          have hrl_ok_sw :
              (hpl[(BitVec.setWidth 64 (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) +
                (1 : BitVec 32))).toNat]'(by simp only [hset]; omega)).toNat < nlits := by
            simp only [hset]; exact hrl_ok
          c0_hsteps
          · exact hJc ((((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)), _) ml
              ⟨by omega, hrc_lt, rfl⟩
          · exact hJc (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)), _) ml ⟨by omega, hlc_lt, rfl⟩
        · c0_hsteps
          exact hJc (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)), _) ml ⟨by omega, hlc_lt, rfl⟩
    · exact False.elim (Bool.noConfusion (by assumption))

/-! ## 3. Read-Only Dense Watch & Clause-Match Proofs -/

theorem full_bva_count_lit_deg_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Func.wp Γ full_bva_count_lit_deg_fid_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hlit_lt, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hcl := hdw.1.core_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have hwl_le := hcl.wlen_le
  have hlay := (m6_denseWatchesInv_of_w hdw).layout
  have hwb := hlay.bounds lit.toNat hlit_lt
  have hlit2 : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat = 2 * lit.toNat := by c0_bound
  have hlit21 : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 := by
    c0_bound
  have hoff_eq :
      (s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by omega)).toNat =
        fullWatchOffCore s.core lit.toNat := by
    unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by simp only [hlit2])
  have hsz_eq :
      (s.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
        fullWatchSizeCore s.core lit.toNat := by
    unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by simp only [hlit21])
  unfold Func.wp full_bva_count_lit_deg_fid_body
  c0_hsteps_nogrp
  let off_bv := BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by
    omega))
  let sz_bv := BitVec.setWidth 64 (s.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
    1#64).toNat]'(by omega))
  let end_bv := off_bv + sz_bv
  have hend_nat : end_bv.toNat =
      fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
    dsimp only [end_bv, off_bv, sz_bv]
    rw [BitVec.toNat_add, fid_bv64_32, fid_bv64_32, hoff_eq, hsz_eq]
    exact Nat.mod_eq_of_lt (by omega)
  refine wp_loop_inv
    (fun (p, _cnt, ()) ml => ml = m ∧ p.toNat ≤ end_bv.toNat)
    (fun (p, _, _) _ => end_bv.toNat - p.toNat)
    (fun J hJ => by
      c0_hsteps
      exact hJ (off_bv, 0#32, ()) m ⟨rfl, by
        dsimp only [off_bv]; rw [fid_bv64_32, hoff_eq, hend_nat]; omega⟩)
    (fun J (p, cnt, ()) ml ⟨hml, hp_le⟩ ih => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hp_lt : p.toNat < end_bv.toNat := by c0_bound
    have hp1 : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
    c0_hsteps
    · exact ih (p + 1#64, cnt + 1#32, ()) ml (by dsimp only; omega) ⟨rfl, by omega⟩
    · have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
      have hp1_lt : p.toNat + 1 < end_bv.toNat := by
        have h1' : (BitVec.toNat p + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have h2m : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
        have h21m : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
            2 * lit.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have hoff' : s.core.wvec[2 * lit.toNat % 2 ^ 64].toNat =
            fullWatchOffCore s.core lit.toNat := by simpa only [hlit2, h2m] using hoff_eq
        have hsz' : s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat =
            fullWatchSizeCore s.core lit.toNat := by simpa only [hlit21, h21m] using hsz_eq
        rw [h1', hoff', hsz', Nat.mod_eq_of_lt (by omega)] at hc
        omega
      exact ih (p + 1#64 + 1#64, cnt + 1#32, ()) ml (by dsimp only; omega) ⟨rfl, by omega⟩
    · exact ih (p + 1#64, cnt, ()) ml (by dsimp only; omega) ⟨rfl, by omega⟩
  · c0_hsteps; exact hQ cnt

theorem full_bva_match_large_bva_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Func.wp Γ full_bva_match_large_bva_fid_body a m Q X := by
  rintro ⟨h, cur_cr, next_lit, d_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R_mem, R_set, rfl, hslen, hw, hnodup, hl0, hdm, hcur_ref, hcur_ng, hd_ref,
     hR_nd, hR_lt, hcur_sz, hlm2_sub, hm, hQ⟩
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcl := hslen.core_ok; have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le
  have hlm_len := hcl.lit_mark_len; have hcv_le := hcl.cur_vars_le
  have hcur_wf := hw.arena.refs_wf cur_cr.toNat hcur_ref
  have hd_wf := hw.arena.refs_wf d_ref.toNat hd_ref
  have hcur_sz_eq : (s.core.arena[cur_cr.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSize s cur_cr.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hd_sz_eq : (s.core.arena[d_ref.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSize s d_ref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcur2_idx : (BitVec.setWidth 64 cur_cr + 2).toNat = cur_cr.toNat + 2 := by
    change (BitVec.setWidth 64 cur_cr + 2#64).toNat = _; c0_bound
  have hd2_idx : (BitVec.setWidth 64 d_ref + 2).toNat = d_ref.toNat + 2 := by
    change (BitVec.setWidth 64 d_ref + 2#64).toNat = _; c0_bound
  have hd0_idx : (BitVec.setWidth 64 d_ref).toNat = d_ref.toNat := by c0_bound
  unfold Func.wp full_bva_match_large_bva_fid_body
  c0_hsteps
  · exact hQ false (fun h => by cases h)
  · exact hQ false (fun h => by cases h)
  · have hsz_eq : fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat := by
      have h1 : s.core.arena[(BitVec.setWidth 64 d_ref + 2).toNat]'(by rw [hd2_idx]; omega) =
          s.core.arena[(BitVec.setWidth 64 cur_cr + 2).toNat]'(by rw [hcur2_idx]; omega) := by
        assumption
      have h2 := congrArg BitVec.toNat h1; simp only [hd2_idx, hcur2_idx] at h2; omega
    have h0248 : (s.core.arena[d_ref.toNat]'(by omega) &&& 0x02480000#32) = 0#32 := by
      have h1 : (s.core.arena[(BitVec.setWidth 64 d_ref).toNat]'(by rw [hd0_idx]; omega) &&&
          0x02480000#32) = 0#32 := by assumption
      simpa only [hd0_idx] using h1
    have hd_ng : fullArenaClauseGarb s d_ref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [fid_bv32_garb_zero_of_and_02480000 h0248]
    have hd_nbvaq : (fullArenaHdr s d_ref.toNat &&& 0x02000000#32) = 0#32 := by
      unfold fullArenaHdr fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact fid_bv32_bvaq_zero_of_and_02480000 h0248
    let sz_bv := s.core.arena[(BitVec.setWidth 64 cur_cr + 2).toNat]'(by rw [hcur2_idx]; omega)
    have hsz_bv_nat : sz_bv.toNat = fullArenaClauseSize s cur_cr.toNat := by
      dsimp only [sz_bv]; simp only [hcur2_idx]; exact hcur_sz_eq
    have hd_lits_len : (fullArenaClauseLits s d_ref.toNat).length = sz_bv.toNat := by
      unfold fullArenaClauseLits
      rw [fullArenaClauseLitsCore_length (by
        have := hd_wf.2.2.1; have := hd_wf.2.2.2.1; omega)]
      unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega
    have hcur2_mod : (cur_cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        cur_cr.toNat + 2 := by
      rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
    have hsz_mod : sz_bv = s.core.arena[(cur_cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
        rw [hcur2_mod]; omega) := by
      dsimp only [sz_bv]; simp only [hcur2_idx, hcur2_mod]
    refine wp_loop_inv
      (fun (j, seen_next, ()) ml =>
        ml = m ∧ j.toNat ≤ sz_bv.toNat ∧
        (seen_next = true → next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat) ∧
        (∀ k < j.toNat, let dl := (s.core.arena[d_ref.toNat + 3 + k]?.getD 0#32).toNat
          dl ≠ next_lit.toNat → dl ∈ R_set))
      (fun (j, _, _) _ => sz_bv.toNat - j.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (0#32, false, ()) m ⟨rfl, Nat.zero_le _, (fun h => by cases h),
          fun _ h => by simp only [bv_c0] at h; omega⟩)
      (fun J (j, seen_next, ()) ml ⟨hml, hj_le, hseen, hall⟩ ih => ?_)
    rcases hml with rfl
    c0_hsteps
    · have hj_lt : j.toNat < sz_bv.toNat := by rw [hsz_mod]; c0_bound
      have hj_lt_d : j.toNat < fullArenaClauseSizeCore s.core d_ref.toNat := by
        unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega
      have hdl_idx : (BitVec.setWidth 64 d_ref + 3 + BitVec.setWidth 64 j).toNat =
          d_ref.toNat + 3 + j.toNat := by
        change (BitVec.setWidth 64 d_ref + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
      have hdl_mod : (d_ref.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
          d_ref.toNat + 3 + j.toNat := by
        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
      have hdl_mem : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)).toNat ∈
          fullArenaClauseLits s d_ref.toNat :=
        List.mem_of_getElem? (fullArenaClauseLitsCore_getElem hj_lt_d (by omega))
      have hdl_lt := hw.arena.lits_lt d_ref.toNat hd_ref hd_ng _ hdl_mem
      have hdl_lt_lm : (s.core.arena[(BitVec.setWidth 64 d_ref + 3 +
          BitVec.setWidth 64 j).toNat]'(by rw [hdl_idx]; omega)).toNat <
            s.core.lit_mark.length := by
        have h1 : s.core.arena[(BitVec.setWidth 64 d_ref + 3 +
            BitVec.setWidth 64 j).toNat]'(by rw [hdl_idx]; omega) =
            s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega) := by simp only [hdl_idx]
        rw [h1]; omega
      c0_hsteps
      · exact hQ false (fun h => by cases h)
      · have hdl_eq : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)) = next_lit := by
          have h1 : s.core.arena[(d_ref.toNat + BitVec.toNat (3 : BitVec 64) +
              j.toNat) % 2 ^ 64]'(by rw [hdl_mod]; omega) = next_lit := by assumption
          simpa only [hdl_mod] using h1
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        refine ih (j + 1#32, true, ()) ml (by dsimp only; rw [hj1]; omega)
          ⟨rfl, by rw [hj1]; omega, fun _ => by rw [← hdl_eq]; exact hdl_mem, fun k hk hne => ?_⟩
        rw [hj1] at hk
        by_cases hkj : k = j.toNat
        · subst hkj
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hdl_eq] at hne
          exact absurd rfl hne
        · exact hall k (by omega) hne
      · exact hQ false (fun h => by cases h)
      · have hdl_in : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)).toNat ∈ R_set := by
          apply hlm2_sub _ hdl_lt
          have h1 : ¬ (BitVec.setWidth 32 (s.core.lit_mark[(s.core.arena[(d_ref.toNat +
              BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64]'(by
              rw [hdl_mod]; omega)).toNat]'(by simp only [hdl_mod]; omega)) &&&
              BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)) =
              BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := by assumption
          simp only [hdl_mod] at h1; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          intro h0; apply h1; apply BitVec.eq_of_toNat_eq
          have h0' := congrArg BitVec.toNat h0
          simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
            show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)).toNat = 2 from rfl,
            show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).toNat = 0 from rfl,
            show (2#8 : BitVec 8).toNat = 2 from rfl,
            show (0#8 : BitVec 8).toNat = 0 from rfl] at h0' ⊢
          have hlt8 := (s.core.lit_mark[(s.core.arena[d_ref.toNat + 3 + j.toNat]'(by
            omega)).toNat]'(by omega)).isLt
          rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))]; exact h0'
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        refine ih (j + 1#32, seen_next, ()) ml (by dsimp only; rw [hj1]; omega)
          ⟨rfl, by rw [hj1]; omega, hseen, fun k hk hne => ?_⟩
        rw [hj1] at hk
        by_cases hkj : k = j.toNat
        · subst hkj; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdl_in
        · exact hall k (by omega) hne
    · have hj_eq : j.toNat = sz_bv.toNat := by rw [hsz_mod]; c0_bound
      refine hQ seen_next fun htrue => ?_
      have hnext_in := hseen htrue
      have hD_nd : (fullArenaClauseLits s d_ref.toNat).Nodup :=
        nodup_of_map_div2 (hnodup d_ref.toNat hd_ref hd_ng)
      have hsub : ∀ x ∈ fullArenaClauseLits s d_ref.toNat, x ≠ next_lit.toNat → x ∈ R_set := by
        intro x hx hne
        obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hx
        have hk_sz : k < sz_bv.toNat := by rw [← hd_lits_len]; exact hk_lt
        have hk_get := fullArenaClauseLitsCore_getElem (k := s.core)
          (r := d_ref.toNat) (j := k) (by unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega)
          (by have := hd_wf.2.2.1; have := hd_wf.2.2.2.1
              unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega)
        have hx_eq : x = (s.core.arena[d_ref.toNat + 3 + k]?.getD 0#32).toNat := by
          have h1 : (fullArenaClauseLits s d_ref.toNat)[k]? = some x := by
            rw [List.getElem?_eq_getElem hk_lt, hk_eq]
          unfold fullArenaClauseLits at h1; rw [hk_get] at h1
          rw [← Option.some.inj h1, List.getElem?_eq_getElem (by
            have := hd_wf.2.2.1; have := hd_wf.2.2.2.1; have := hcl.arena_len_le
            unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega), Option.getD_some]
        rw [hx_eq] at hne ⊢; exact hall k (by omega) hne
      have ⟨hperm, hfilt⟩ := bva_match_large_perm hR_nd hD_nd hnext_in
        (by rw [hd_lits_len, hsz_bv_nat, hcur_sz]) hsub
      exact ⟨hd_ng, hd_nbvaq, hsz_eq, hnext_in, hperm, hfilt,
        clause_entails_of_perm hperm (hw.arena.entails d_ref.toNat hd_ref hd_ng)⟩

theorem full_has_factor_cands_fid_wp (Γ : Env) :
    ∀ a m Q X, step13HasFactorCandsSpec a m Q X →
      Func.wp Γ full_has_factor_cands_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_has_factor_cands_fid_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (v, ()) mv => mv = m ∧ v.toNat ≤ s.core.cur_vars ∧ rem = s.core.cur_vars - v.toNat)
    ?_ (fun _ hL => by
      c0_hsteps!; exact hL s.core.cur_vars (0#64, ()) m ⟨rfl, Nat.zero_le _, rfl⟩)
  · rintro L rem ⟨v, ⟨⟩⟩ mv hL ⟨rfl, hv_le, rfl⟩
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hv_fl : v.toNat < s.core.flags.length := by rw [hlen.core_ok.flags_len]; omega
      have hv_vals : (v <<< (1 : Nat)).toNat < s.core.vals.length := by
        rw [hlen.core_ok.vals_len]; c0_bound
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join0 (fun mj => mj = mv)
        (fun _ mj hmj => by
          rcases hmj.symm with rfl; c0_hsteps!
          exact hL (s.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) mv (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun Jx hJx => by
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · c0_hsteps!; exact hQ true
              · c0_hsteps!; exact hJx mv rfl
            · c0_hsteps!; exact hJx mv rfl
          · c0_hsteps!; exact hJx mv rfl)
    · c0_hsteps!; exact hQ false

end

end LeanQbe.T.Examples.Kissat.Proof.Factor

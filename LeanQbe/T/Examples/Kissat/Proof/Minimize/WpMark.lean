/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Logic.C0Step

/-!
# `full_min_mark` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_min_mark_body ...` against canonical `Spec.fullMinMarkSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullArenaTactics
open scoped FullArenaTactics FullMinTactics

public section

theorem full_min_mark_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullMinMarkSpec args m Q X →
      Func.wp Γ full_min_mark_body args m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmrk_len := hlen.core_ok.mrk_len
  have hmclr_len := hlen.core_ok.min_clr_len_arr
  have hmcl_le := hlen.core_ok.min_clr_len_le
  unfold Func.wp full_min_mark_body; dsimp only [full_min_mark_body]
  ml_lets; rw [wp]; refine ⟨_, load_full_cur_vars hm, ?_⟩; ml_lets
  ml_jnz; refine ⟨fun hoob_bv => ?_, fun hlt_bv => ?_⟩
  · c0_cond hoob_bv
    have hoob : s.core.cur_vars ≤ v.toNat := by bv_omega
    ml_lets; rw [wp]
    simpa only [hoob, true_or, ↓reduceIte] using hQ
  · have hvlt : v.toNat < s.core.cur_vars := by c0_cond hlt_bv; bv_omega
    have hnot_oob : ¬ s.core.cur_vars ≤ v.toNat := by omega
    have hv_mrk : v.toNat < s.core.mrk.length := by omega
    ml_lets; rw [wp]; refine ⟨_, load_full_mark_ptr hm, ?_⟩; ml_lets
    rw [wp]; refine ⟨_, c0_load_full_mrk (i := v.setWidth 64) (by bv_omega) hm, ?_⟩
    c0_steps!
    · have hne : (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 := by
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]; exact hc
      simpa [hnot_oob, hne] using hQ
    · have hcl_lt : s.core.min_clr_len < s.core.cur_vars := by bv_omega
      have hadd1 : (BitVec.ofNat 64 s.core.min_clr_len + 1).toNat = s.core.min_clr_len + 1 := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8, hadd1, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : s.core.min_clr_len < 2 ^ 64)] at hm
      dsimp only [fullMinMarkState, fullMinMarkCore] at hQ
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
      have hcur0 : s.core.mrk[v.toNat] = 0#8 := by assumption
      have hbv_v : BitVec.ofNat 32 v.toNat = v := by simp
      simp only [hnot_oob, hcur0, BitVec.zero_and, BitVec.zero_or, ne_eq, not_true_eq_false,
        or_self, ↓reduceIte, hcl_lt, hbv_v, and_self] at hQ
      simp only [hcur0, BitVec.zero_or] at hm
      exact hQ _ hm
    · have hcl_ge : ¬ s.core.min_clr_len < s.core.cur_vars := by bv_omega
      simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm
      dsimp only [fullMinMarkState, fullMinMarkCore] at hQ
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
      have hcur0 : s.core.mrk[v.toNat] = 0#8 := by assumption
      simp only [hnot_oob, hcur0, BitVec.zero_and, BitVec.zero_or, ne_eq, not_true_eq_false,
        or_self, ↓reduceIte, hcl_ge, not_false_eq_true, and_self] at hQ
      simp only [hcur0, BitVec.zero_or] at hm
      exact hQ _ hm
    · simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm
      dsimp only [fullMinMarkState, fullMinMarkCore] at hQ
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
      have htag0 : s.core.mrk[v.toNat] &&& tag = 0#8 := by assumption
      have hcur_nz : s.core.mrk[v.toNat] ≠ 0#8 := by assumption
      simp only [hnot_oob, htag0, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        hcur_nz, false_and] at hQ
      exact hQ _ hm

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize

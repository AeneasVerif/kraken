/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Logic.C0Step

/-!
# `full_min_mark` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_min_mark_body ...` against canonical `Spec.minMarkSpec`.
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
    ∀ args m Q X, Spec.minMarkSpec args m Q X →
      Func.wp Γ full_min_mark_body args m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, _, R, rfl, hlen, _, hm, hQ⟩ := FullContract.elim hs
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
    exact hQ () s m hlen (by simp [hoob]) hm
  · have hvlt : v.toNat < s.core.cur_vars := by c0_cond hlt_bv; bv_omega
    have hnot_oob : ¬ s.core.cur_vars ≤ v.toNat := by omega
    have hv_mrk : v.toNat < s.core.mrk.length := by omega
    ml_lets; rw [wp]; refine ⟨_, load_full_mark_ptr hm, ?_⟩; ml_lets
    rw [wp]; refine ⟨_, c0_load_full_mrk (i := v.setWidth 64) (by bv_omega) hm, ?_⟩
    c0_steps!
    · have hne : (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 := by
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]; exact hc
      exact hQ () s m hlen (by simp [hnot_oob, hne]) hm
    · have hcl_lt : s.core.min_clr_len < s.core.cur_vars := by bv_omega
      have hadd1 : (BitVec.ofNat 64 s.core.min_clr_len + 1).toNat = s.core.min_clr_len + 1 := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8, hadd1, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : s.core.min_clr_len < 2 ^ 64)] at hm
      have hcur0 : s.core.mrk[v.toNat] = 0#8 := by assumption
      have hcur0' : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]; exact hcur0
      have hbv_v : BitVec.ofNat 32 v.toNat = v := by simp
      have hcond : ¬ (s.core.cur_vars ≤ v.toNat ∨
          (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) := by
        simp [hnot_oob, hcur0']
      have hlen' : (fullMinMarkState s v.toNat tag).LengthsOk c := by
        dsimp only [fullMinMarkState, fullMinMarkCore]
        simp only [hcur0', ↓reduceIte, hcl_lt, and_self, not_true_eq_false, and_false]
        exact ⟨{ hlen.core_ok with
          mrk_len := by simp [hlen.core_ok.mrk_len]
          min_clr_len_arr := by simp [hlen.core_ok.min_clr_len_arr]
          min_clr_len_le := by dsimp only; omega }, hlen.scratch_ok⟩
      simp only [hcur0, BitVec.zero_or] at hm
      have hm' : (FullMem c (fullMinMarkState s v.toNat tag) ⋆ R) m := by
        dsimp only [fullMinMarkState, fullMinMarkCore]
        simp only [hcur0', hcl_lt, ↓reduceIte, hbv_v, BitVec.zero_or, and_self,
          not_true_eq_false, and_false]
        exact hm
      exact hQ () (fullMinMarkState s v.toNat tag) m hlen' (by simp [hcond]) hm'
    · have hcl_ge : ¬ s.core.min_clr_len < s.core.cur_vars := by bv_omega
      simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm
      have hcur0 : s.core.mrk[v.toNat] = 0#8 := by assumption
      have hcur0' : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]; exact hcur0
      have hcond : ¬ (s.core.cur_vars ≤ v.toNat ∨
          (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) := by
        simp [hnot_oob, hcur0']
      have hlen' : (fullMinMarkState s v.toNat tag).LengthsOk c := by
        dsimp only [fullMinMarkState, fullMinMarkCore]
        simp only [hcur0', hcl_ge, and_false, not_false_eq_true, and_true, ↓reduceIte]
        exact ⟨{ hlen.core_ok with mrk_len := by simp [hlen.core_ok.mrk_len] }, hlen.scratch_ok⟩
      simp only [hcur0, BitVec.zero_or] at hm
      have hm' : (FullMem c (fullMinMarkState s v.toNat tag) ⋆ R) m := by
        dsimp only [fullMinMarkState, fullMinMarkCore]
        simp only [hcur0', hcl_ge, BitVec.zero_or, and_false, and_true,
          not_false_eq_true, ↓reduceIte]
        exact hm
      exact hQ () (fullMinMarkState s v.toNat tag) m hlen' (by simp [hcond]) hm'
    · simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm
      have htag0 : s.core.mrk[v.toNat] &&& tag = 0#8 := by assumption
      have hcur_nz : s.core.mrk[v.toNat] ≠ 0#8 := by assumption
      have hget : s.core.mrk[v.toNat]?.getD 0#8 = s.core.mrk[v.toNat] := by
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]
      have hcond : ¬ (s.core.cur_vars ≤ v.toNat ∨
          (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) := by
        simp [hnot_oob, hget, htag0]
      have hlen' : (fullMinMarkState s v.toNat tag).LengthsOk c := by
        dsimp only [fullMinMarkState, fullMinMarkCore]
        simp only [hget, hcur_nz, false_and, ↓reduceIte]
        exact ⟨{ hlen.core_ok with mrk_len := by simp [hlen.core_ok.mrk_len] }, hlen.scratch_ok⟩
      refine hQ () (fullMinMarkState s v.toNat tag) _ hlen' (by simp [hcond]) ?_
      simpa only [fullMinMarkState, fullMinMarkCore, hget, hcur_nz, false_and, ↓reduceIte] using hm

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Substitute

/-!
# WP Proof for `full_tarjan_pop_scc` (`Proof.Substitute.WpTarjanPop`)

Proves `full_tarjan_pop_scc_wp` parametrically over `Γ : Env` against `fullTarjanPopSccSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Substitute
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics
open Kraken.Bedrock2.Test

public section

/-- `full_tarjan_pop_scc` satisfies canonical `fullTarjanPopSccSpec` parametrically in `Γ`. -/
theorem full_tarjan_pop_scc_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullTarjanPopSccSpec args m Q X →
      Func.wp Γ full_tarjan_pop_scc_body args m Q X := by
  rintro ⟨h, root_lit, lit, mark_root, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, k0, R, rfl, hlen, hw, hinc0, hroot_lt, hlit_lt, htc_le, hrsz_le,
     hk0_lt, hk0_eq, hk0_last, hscc_lt, hscc_eq, hrepr_inv, hunits_inv, hreach, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le
  have hscc_len := hsl.work_stk1_len; have hrepr_len := hcl.repr_len
  have htrc_len := hsl.tarjan_reach_len; have htmk_len := hsl.tarjan_mark_len
  have hunits_len := hsl.shrink_stk_len
  unfold Func.wp full_tarjan_pop_scc_body
  c0_hsteps_nogrp
  refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
    (fun (k, min_l, ()) mb => mb = m ∧ k.toNat = k0 ∧
      min_l.toNat < 2 * s.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) min_l.toNat lit.toNat)
    (fun rem (k, min_l, ()) ml => rem = k.toNat ∧ ml = m ∧
      k0 < k.toNat ∧ k.toNat ≤ s.core.tmp_cnt ∧
      min_l.toNat < 2 * s.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) min_l.toNat lit.toNat)
    ?_ ?_ ?_
  · rintro _ ⟨k, min_l, ⟨⟩⟩ mb ⟨rfl, hk_eq, hmin_lt, hmin_eq⟩
    have hfail_init :
        (mark_root == 0xFFFFFFFF#32) = false → mark_root ≠ 0xFFFFFFFF#32 := by
      simp
    have hmin_ne_ff : min_l ≠ 0xFFFFFFFF#32 := fun heq => by
      rw [heq] at hmin_lt; revert hmin_lt; simp; omega
    c0_hsteps_nogrp
    refine wp_loop_break_group (brkTs := [.bool, i64]) (lpTs := [.bool, i64])
      (fun (failed_b, _j, ()) mb =>
        ∃ sb : FullState,
          AgreesExcept fullPopSccMask s sb ∧
          sb.LengthsOk c ∧ FullWitnessInv c F0 F_cur sb.core ∧
          sb.scratch.res_sz.toNat ≤ c.max_vars ∧
          FullPartialReprInv F_cur sb.core ∧ FullUnitsSoundInv F_cur sb sb.scratch.res_sz.toNat ∧
          (sb.core.inconsistent = 0#64 ∨ sb.core.inconsistent = 1#64) ∧
          (sb.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) ∧
          (sb.core.inconsistent = 0#64 →
            (∀ i, k0 ≤ i → i < s.core.tmp_cnt →
              let x := (s.scratch.work_stk1[i]?.getD 0#32).toNat
              sb.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
              sb.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32) ∧
            (∀ l < 2 * s.core.cur_vars,
              (∀ i, k0 ≤ i → i < s.core.tmp_cnt →
                (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ l) →
              sb.core.repr[l]? = s.core.repr[l]? ∧
              sb.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]?)) ∧
          (FullMem c sb ⋆ R) mb)
      (fun rem (failed_b, j, ()) ml =>
        ∃ st : FullState,
          AgreesExcept fullPopSccMask s st ∧
          st.core.inconsistent = 0#64 ∧
          rem = s.core.tmp_cnt - j.toNat ∧
          k0 ≤ j.toNat ∧ j.toNat ≤ s.core.tmp_cnt ∧
          st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
          st.scratch.res_sz.toNat ≤ c.max_vars ∧
          FullPartialReprInv F_cur st.core ∧ FullUnitsSoundInv F_cur st st.scratch.res_sz.toNat ∧
          (failed_b = false → mark_root ≠ 0xFFFFFFFF#32) ∧
          (∀ i, k0 ≤ i → i < j.toNat →
            let x := (s.scratch.work_stk1[i]?.getD 0#32).toNat
            st.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
            st.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32) ∧
          (∀ l < 2 * s.core.cur_vars,
            (∀ i, k0 ≤ i → i < j.toNat →
              (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ l) →
            st.core.repr[l]? = s.core.repr[l]? ∧
            st.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]?) ∧
          (FullMem c st ⋆ R) ml)
      ?_ ?_ ?_
    · rintro _ ⟨failed_b, _j, ⟨⟩⟩ mb
        ⟨sb, hag, hlen', hw', hrsz', hpr', hus', hinc_d, hinc_u, hinc_eff, hmb⟩
      c0_hsteps
      exact hQ failed_b { sb with core := { sb.core with tmp_cnt := k.toNat } } _
        (hag.update _) hk_eq
        ⟨{ hlen'.core_ok with vals_len := hlen'.core_ok.vals_len }, hlen'.scratch_ok⟩
        { hw' with
          arena := { hw'.arena with len_ok := hw'.arena.len_ok }
          watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
        hrsz' hpr' hus' hinc_d hinc_u hinc_eff hm
    · rintro B L _ ⟨failed_b, j, ⟨⟩⟩ ml hB hL
        ⟨st, hag, hst_inc0, rfl, hj_ge, hj_le, hst_len, hst_w, hrsz', hpr', hus',
         hfb_mr, hdone, hkeep, hml⟩
      have hst_cv : st.core.cur_vars = s.core.cur_vars := hag.get (·.core.cur_vars)
      have hst_scc : st.scratch.work_stk1 = s.scratch.work_stk1 := hag.get (·.scratch.work_stk1)
      have hst_tmk : st.scratch.tarjan_mark = s.scratch.tarjan_mark :=
        hag.get (·.scratch.tarjan_mark)
      have hst_cl := hst_len.core_ok; have hst_sl := hst_len.scratch_ok
      have hrp_l : st.core.repr.length = 2 * c.max_vars := hst_cl.repr_len
      have htr_l : st.scratch.tarjan_reach.length = 2 * c.max_vars := hst_sl.tarjan_reach_len
      have hun_l : st.scratch.shrink_stk.length = c.max_vars := hst_sl.shrink_stk_len
      have hscc_l : st.scratch.work_stk1.length = 2 * c.max_vars := hst_sl.work_stk1_len
      have htmk_l : st.scratch.tarjan_mark.length = 2 * c.max_vars := hst_sl.tarjan_mark_len
      c0_hsplit
      · have hj_lt : j.toNat < s.core.tmp_cnt := by c0_bound
        let other := st.scratch.work_stk1[j.toNat]'(by omega)
        have hoth_get : other = s.scratch.work_stk1[j.toNat]?.getD 0#32 := by
          have hj_s : j.toNat < s.scratch.work_stk1.length := by omega
          simp [other, hst_scc, List.getElem?_eq_getElem hj_s]
        have hoth_lt : other.toNat < 2 * s.core.cur_vars := by
          rw [hoth_get]; exact hscc_lt j.toNat hj_lt
        have hoth_lt' : (st.scratch.work_stk1[j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars :=
          hoth_lt
        have hnoth_lt : (other ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_toNat]; exact litNeg_lt_two_mul hoth_lt
        have hnoth_lt' :
            (st.scratch.work_stk1[j.toNat]'(by omega)).toNat ^^^ 1 < 2 * s.core.cur_vars := by
          rw [← bv32_xor1_toNat]; exact hnoth_lt
        have hoth_eq_lit : LitEquiv (cnfOfClauses F_cur) other.toNat lit.toNat := by
          rw [hoth_get]; exact hscc_eq j.toNat hj_ge hj_lt
        have hoth_eq_min : LitEquiv (cnfOfClauses F_cur) other.toNat min_l.toNat :=
          hoth_eq_lit.trans hmin_eq.symm
        let st1 : FullState :=
          { st with
            core := { st.core with repr := st.core.repr.set other.toNat min_l }
            scratch := { st.scratch with
              tarjan_reach := st.scratch.tarjan_reach.set other.toNat 0xFFFFFFFF#32 } }
        have hag1 : AgreesExcept fullPopSccMask s st1 := hag.update _
        have hlen1 : st1.LengthsOk c :=
          ⟨{ hst_cl with repr_len := by simp [st1, hrp_l] },
           { hst_sl with tarjan_reach_len := by simp [st1, htr_l] }⟩
        have hw1 : FullWitnessInv c F0 F_cur st1.core :=
          { hst_w with
            arena := { hst_w.arena with len_ok := hst_w.arena.len_ok }
            watches := hst_w.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
        have hpr1 : FullPartialReprInv F_cur st1.core := by
          intro l hl; dsimp only [st1] at hl ⊢; rw [hst_cv] at hl; intro hne
          by_cases hlo : l = other.toNat
          · subst hlo; rw [List.getElem?_set_self (by omega), Option.getD_some]
            exact ⟨by omega, hoth_eq_min⟩
          · rw [List.getElem?_set_ne (Ne.symm hlo)] at hne ⊢
            exact hpr' l (by omega) hne
        have hdone1 : ∀ i, k0 ≤ i → i < j.toNat + 1 →
            let x := (s.scratch.work_stk1[i]?.getD 0#32).toNat
            st1.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
            st1.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32 := by
          intro i hi1 hi2; dsimp only [st1]
          by_cases hij : i = j.toNat
          · have hx : (s.scratch.work_stk1[i]?.getD 0#32).toNat = other.toNat := by
              rw [hij, ← hoth_get]
            rw [hx, List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
              Option.getD_some, Option.getD_some]
            exact ⟨hmin_ne_ff, rfl⟩
          · have hx_lt := hscc_lt i (by omega)
            by_cases hxo : (s.scratch.work_stk1[i]?.getD 0#32).toNat = other.toNat
            · rw [hxo, List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
                Option.getD_some, Option.getD_some]
              exact ⟨hmin_ne_ff, rfl⟩
            · rw [List.getElem?_set_ne (Ne.symm hxo), List.getElem?_set_ne (Ne.symm hxo)]
              exact hdone i hi1 (by omega)
        have hkeep1 : ∀ l < 2 * s.core.cur_vars,
            (∀ i, k0 ≤ i → i < j.toNat + 1 →
              (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ l) →
            st1.core.repr[l]? = s.core.repr[l]? ∧
            st1.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]? := by
          intro l hl hall
          have hne_o : other.toNat ≠ l := by
            have := hall j.toNat hj_ge (by omega); rwa [← hoth_get] at this
          dsimp only [st1]
          rw [List.getElem?_set_ne hne_o, List.getElem?_set_ne hne_o]
          exact hkeep l hl fun i hi1 hi2 => hall i hi1 (by omega)
        have hus1_keep : FullUnitsSoundInv F_cur st1 st1.scratch.res_sz.toNat := hus'
        have hz_other : (BitVec.setWidth 64 other).toNat = other.toNat :=
          zext_toNat other (by decide)
        have htmk1_l : st1.scratch.tarjan_mark.length = 2 * c.max_vars :=
          hlen1.scratch_ok.tarjan_mark_len
        have hun1_l : st1.scratch.shrink_stk.length = c.max_vars := hlen1.scratch_ok.shrink_stk_len
        c0_hsplit
        · have hro_eq : st1.core.repr[(other ^^^ 1#32).toNat]'(by
              simp only [st1, List.length_set, hrp_l]; omega) = min_l := by
            have h1 : (BitVec.setWidth 64 (st.scratch.work_stk1[j.toNat]'(by omega) ^^^
                (1 : BitVec 32))).toNat = other.toNat ^^^ 1 := by
              rw [zext_toNat _ (by decide), show (1 : BitVec 32) = 1#32 from rfl, bv32_xor1_toNat]
            dsimp only [other] at hz_other
            simpa only [st1, other, hz_other, h1, bv32_xor1_toNat] using hc
          have hunsat : (cnfOfClauses F_cur).Unsat := by
            have hro_get : st1.core.repr[(other ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = min_l := by
              rw [List.getElem?_eq_getElem (by simp only [st1, List.length_set, hrp_l]; omega),
                Option.getD_some]
              exact hro_eq
            have hno_eq :=
              (hpr1 (other ^^^ 1#32).toNat (by simp [st1, hst_cv]; exact hnoth_lt)
                (by rw [hro_get]; exact hmin_ne_ff)).2
            rw [hro_get, bv32_xor1_toNat] at hno_eq
            exact litEquiv_contra_unsat hoth_eq_min hno_eq
          have hm_st1 : (FullMem c st1 ⋆ R) m := hm
          clear hm
          c0_hsteps
          · have hrsz_lt : st1.scratch.res_sz.toNat < c.max_vars := by c0_bound
            have hrsz_inc : (st1.scratch.res_sz + 1#64).toNat = st1.scratch.res_sz.toNat + 1 := by
              c0_bound
            dsimp only [st1] at hrsz_lt hrsz_inc
            let st2 : FullState :=
              { st1 with
                core := { st1.core with inconsistent := 1#64 }
                scratch := { st1.scratch with
                  shrink_stk := st1.scratch.shrink_stk.set st1.scratch.res_sz.toNat min_l
                  res_sz := st1.scratch.res_sz + 1#64 } }
            have hus2 : FullUnitsSoundInv F_cur st2 st2.scratch.res_sz.toNat := by
              intro i hi; dsimp only [st2, st1] at hi ⊢
              by_cases hir : i = st.scratch.res_sz.toNat
              · subst hir; rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact ⟨by omega, CNF.entails_clause_def.mpr fun α hα =>
                  absurd hα (CNF.unsat_iff_not_sat.mp hunsat α)⟩
              · rw [List.getElem?_set_ne (Ne.symm hir)]; exact hus' i (by omega)
            exact hB (failed_b, j, ()) _
              ⟨st2, hag1.update _,
               ⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len },
                { hlen1.scratch_ok with shrink_stk_len := by simp [st2, st1, hun_l] }⟩,
               { hw1 with
                 inconsistent_sound := fun _ => hunsat
                 arena := { hw1.arena with len_ok := hw1.arena.len_ok }
                 watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
               by dsimp only [st2, st1]; omega, hpr1, hus2, Or.inr rfl,
               fun _ => hunsat, (fun h => by cases h), hm⟩
          · let st2 : FullState := { st1 with core := { st1.core with inconsistent := 1#64 } }
            exact hB (failed_b, j, ()) _
              ⟨st2, hag1.update _,
               ⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len }, hlen1.scratch_ok⟩,
               { hw1 with
                 inconsistent_sound := fun _ => hunsat
                 arena := { hw1.arena with len_ok := hw1.arena.len_ok }
                 watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
               hrsz', hpr1, hus1_keep, Or.inr rfl, fun _ => hunsat, (fun h => by cases h), hm⟩
        · have hm_st1 : (FullMem c st1 ⋆ R) m := hm
          clear hm
          have hj1 : (j + 1#64).toNat = j.toNat + 1 := by c0_bound
          c0_hsteps
          · exact hL (s.core.tmp_cnt - (j.toNat + 1)) (failed_b, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, hfb_mr,
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
          · have hfb_f : failed_b = false := by assumption
            have hmr_ne : mark_root ≠ 0xFFFFFFFF#32 := hfb_mr hfb_f
            have hmr_le : mark_root.toNat ≤
                (s.scratch.tarjan_mark[(other ^^^ 1#32).toNat]?.getD 0#32).toNat := by
              rw [← hst_tmk, List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hle : mark_root.toNat ≤
                  (st1.scratch.tarjan_mark[other.toNat ^^^ 1]'(by
                    rw [← bv32_xor1_toNat]; omega)).toNat := by
                dsimp only [other]; c0_bound
              simpa only [st1, ← bv32_xor1_toNat] using hle
            have hbr1 : BinReach (cnfOfClauses F_cur) root_lit.toNat other.toNat := by
              have := (hreach hmr_ne).1 j.toNat hj_ge hj_lt; rwa [← hoth_get] at this
            have hbr2 : BinReach (cnfOfClauses F_cur) root_lit.toNat (litNeg other.toNat) := by
              have := (hreach hmr_ne).2 (other ^^^ 1#32).toNat hnoth_lt hmr_le
              rwa [bv32_xor1_toNat] at this
            have hent_rf :
                (cnfOfClauses F_cur).EntailsClause (cnfClause [(root_lit ^^^ 1#32).toNat]) := by
              rw [bv32_xor1_toNat]; exact binReach_failed_of_pair hbr1 hbr2
            have hrsz_lt : st1.scratch.res_sz.toNat < c.max_vars := by c0_bound
            have hrsz_inc : (st1.scratch.res_sz + 1#64).toNat = st1.scratch.res_sz.toNat + 1 := by
              c0_bound
            dsimp only [st1] at hrsz_lt hrsz_inc
            let st2 : FullState :=
              { st1 with
                scratch := { st1.scratch with
                  shrink_stk :=
                    st1.scratch.shrink_stk.set st1.scratch.res_sz.toNat (root_lit ^^^ 1#32)
                  res_sz := st1.scratch.res_sz + 1#64 } }
            have hus2 : FullUnitsSoundInv F_cur st2 st2.scratch.res_sz.toNat := by
              intro i hi; dsimp only [st2, st1] at hi ⊢
              by_cases hir : i = st.scratch.res_sz.toNat
              · subst hir; rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact ⟨by rw [hst_cv, bv32_xor1_toNat]; exact litNeg_lt_two_mul hroot_lt, hent_rf⟩
              · rw [List.getElem?_set_ne (Ne.symm hir)]; exact hus' i (by omega)
            exact hL (s.core.tmp_cnt - (j.toNat + 1)) (true, j + 1#64, ()) _ (by omega)
              ⟨st2, hag1.update _, hst_inc0, by omega, by omega, by omega,
               ⟨hlen1.core_ok,
                { hlen1.scratch_ok with shrink_stk_len := by simp [st2, st1, hun_l] }⟩,
               hw1, by dsimp only [st2, st1]; omega, hpr1, hus2, (fun h => by cases h),
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm⟩
          · exact hL (s.core.tmp_cnt - (j.toNat + 1)) (true, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, (fun h => by cases h),
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
          · exact hL (s.core.tmp_cnt - (j.toNat + 1)) (failed_b, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, hfb_mr,
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
          · exact hL (s.core.tmp_cnt - (j.toNat + 1)) (failed_b, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, hfb_mr,
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
      · have hj_eq : j.toNat = s.core.tmp_cnt := by c0_bound
        c0_hsteps
        exact hB (failed_b, j, ()) ml
          ⟨st, hag, hst_len, hst_w, hrsz', hpr', hus', Or.inl hst_inc0,
           fun h => absurd hst_inc0 h,
           fun _ => ⟨fun i hi1 hi2 => hdone i hi1 (by omega),
                     fun l hl hall => hkeep l hl fun i hi1 hi2 => hall i hi1 (by omega)⟩, hml⟩
    · intro B L _ hL
      c0_hsteps
      exact hL (s.core.tmp_cnt - k0) (mark_root == 0xFFFFFFFF#32, k, ()) mb
        ⟨s, AgreesExcept.refl _ _, hinc0, by omega, by omega, by omega, hlen, hw, hrsz_le,
         hrepr_inv, hunits_inv, hfail_init, fun _ _ _ => by omega,
         fun _ _ _ => ⟨rfl, rfl⟩, hm⟩
  · rintro B L _ ⟨k, min_l, ⟨⟩⟩ ml hB hL ⟨rfl, rfl, hk_gt, hk_le, hmin_lt, hmin_eq⟩
    have hk_sub : (k - 1#64).toNat = k.toNat - 1 := by c0_bound
    have hx_get : s.scratch.work_stk1[(k - 1#64).toNat]'(by omega) =
        s.scratch.work_stk1[k.toNat - 1]?.getD 0#32 := by
      have hk1_s : k.toNat - 1 < s.scratch.work_stk1.length := by omega
      simp [hk_sub, List.getElem?_eq_getElem hk1_s]
    have hx_lt : (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega)).toNat < 2 * s.core.cur_vars :=
      by rw [hx_get]; exact hscc_lt (k.toNat - 1) (by omega)
    have hx_eq : LitEquiv (cnfOfClauses F_cur)
        (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega)).toNat lit.toNat := by
      rw [hx_get]; exact hscc_eq (k.toNat - 1) (by omega) (by omega)
    have hk_eq_or_gt : (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega) = lit →
        (k - 1#64).toNat = k0) ∧
        (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega) ≠ lit → k0 < (k - 1#64).toNat) := by
      refine ⟨fun heq => Classical.byContradiction fun hne0 => ?_,
              fun hne => Classical.byContradiction fun hle0 => ?_⟩
      · have hgt0 : k0 < k.toNat - 1 := by omega
        exact hk0_last (k.toNat - 1) hgt0 (by omega) (by rw [← hx_get]; exact heq)
      · have heq0 : k.toNat - 1 = k0 := by omega
        exact hne (by rw [hx_get, heq0]; exact hk0_eq)
    c0_hsteps
    · exact hB (k - 1#64, s.scratch.work_stk1[(k - 1#64).toNat]'(by omega), ()) ml
        ⟨rfl, hk_eq_or_gt.1 (by assumption), hx_lt, hx_eq⟩
    · exact hL (k - 1#64).toNat
        (k - 1#64, s.scratch.work_stk1[(k - 1#64).toNat]'(by omega), ()) ml
        (by omega) ⟨rfl, rfl, hk_eq_or_gt.2 (by assumption), by omega, hx_lt, hx_eq⟩
    · exact hB (k - 1#64, min_l, ()) ml
        ⟨rfl, hk_eq_or_gt.1 (by assumption), hmin_lt, hmin_eq⟩
    · exact hL (k - 1#64).toNat (k - 1#64, min_l, ()) ml
        (by omega) ⟨rfl, rfl, hk_eq_or_gt.2 (by assumption), by omega, hmin_lt, hmin_eq⟩
  · intro B L _ hL
    c0_hsteps
    exact hL s.core.tmp_cnt (BitVec.ofNat 64 s.core.tmp_cnt, lit, ()) m
      ⟨by c0_bound, rfl, by c0_bound, by c0_bound, hlit_lt, LitEquiv.refl _ _⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute

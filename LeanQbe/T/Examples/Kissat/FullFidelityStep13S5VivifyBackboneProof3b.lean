/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof3b0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullTransLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-B — Transitive Reduction (`Proof3b`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for:
1. `full_trans_lit_m6_s5_wp` (`FullM6VivBackbone.fullTransLitM6Spec`, `15 -> 31` tick stride)
2. `full_transitive_m6_s5_wp` (`step13TransitiveSpec`, `FullM6HdrMem` + `s5bBcpM6Spec` + `probing`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.Full.FullTransHelpers
open LeanQbe.T.Examples.Kissat.FullM6Hdr FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets Kraken.Bedrock2.Test
open scoped FullArenaTactics FullM6Hdr.M6HdrTactics

/-! ## 1. `full_trans_lit_m6_s5_wp` (`fullTransLitM6Spec`) -/

section TransLitS5Proof

theorem full_trans_lit_m6_s5_wp (Γ : Env)
    (h_del_bin : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X)
    (h_add_unit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_trans_lit_m6_body a m Q X := by
  rintro ⟨h, src, stop_early, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hsrc_lt, hm, hQ⟩
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_trans_lit_m6_body
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness; have hlen0 := hsp.1.lengths
  have hsrc_vlen := s13_tl_vals_lt hlen0.core_ok hsrc_lt
  c0_hsplit
  · c0_hsteps; exact hQ true s m hsp hcl0 rfl rfl rfl (fun hf => absurd hf (by decide)) hm
  have hsrc0 : s.core.vals[src.toNat]?.getD 0#8 = 0#8 := s13_tl_vals_zero_of_domain (z := 0#32)
    (hw0.vals_domain src.toNat hsrc_lt) rfl
    (by rw [List.getElem?_eq_getElem hsrc_vlen]; exact hc)
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 32 := by have := (s13_tl_bnds hlen0.core_ok).1; omega
  have hsrc64 : (src.setWidth 64 <<< (1 : Nat)).toNat = 2 * src.toNat := by
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hsrc64_1 : ((src.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * src.toNat + 1 := by
    rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 (by rw [hsrc64]; omega), hsrc64]
  let off := fullWatchOff s src.toNat; let sz := fullWatchSize s src.toNat; let end_v := off + sz
  have hws_b : end_v ≤ s.core.wlen := by
    have hwm := hw0.watches; unfold ModeWatchesInv at hwm
    simp only [hsp.2.2.2.2, ↓reduceIte] at hwm; exact hwm.layout.bounds src.toNat hsrc_lt
  have hwv_b : 2 * src.toNat + 1 < s.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; have := hlen0.core_ok.cur_vars_le; omega
  have hw0_b2 : 2 * src.toNat < s.core.wvec.length := by omega
  have hwc_lt : c.wcap < 2 ^ 64 := by have := c.hwcap; unfold dimacsBound at *; omega
  have hoff_lt : off < 2 ^ 32 := BitVec.isLt _; have hsz_lt : sz < 2 ^ 32 := BitVec.isLt _
  have hw0_b : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat < s.core.wvec.length := by
    rw [hsrc64]; exact hw0_b2
  have hw1_b : (BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat < s.core.wvec.length := by
    rw [hsrc64_1]; exact hwv_b
  c0_hsplit
  · c0_hsteps; exact hQ true s m hsp hcl0 rfl rfl rfl (fun hf => absurd hf (by decide)) hm
  have hsz_pos : 0 < sz := by
    have hmod1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    have hsz_eq : (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
        rw [hmod1]; exact hwv_b)).toNat = sz := by
      simp only [hmod1]; exact s13_tl_getElem_toNat hwv_b
    exact Nat.pos_of_ne_zero fun hz =>
      hc (BitVec.eq_of_toNat_eq (by rw [ft_bv32_setWidth64, hsz_eq, hz]; rfl))
  have hend_lt : end_v < 2 ^ 64 := by have := (s13_tl_bnds hlen0.core_ok).2.1; omega
  have hof64 : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h_off_arg : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'
      hw0_b) = BitVec.ofNat 64 off := BitVec.eq_of_toNat_eq (by
    rw [ft_bv32_setWidth64, hof64]; simp only [hsrc64]; exact s13_tl_getElem_toNat hw0_b2)
  have h_sz_arg : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat]'
      hw1_b) = BitVec.ofNat 64 sz := BitVec.eq_of_toNat_eq (by
    rw [ft_bv32_setWidth64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [hsrc64_1]; exact s13_tl_getElem_toNat hwv_b)
  have h_end_arg :
      (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) +
       BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat]'
         hw1_b)).toNat = end_v := by
    rw [h_off_arg, h_sz_arg, BitVec.toNat_add, hof64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : sz < 2 ^ 64), Nat.mod_eq_of_lt hend_lt]
  have h_end_bv :
      BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) +
       BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat]'
         hw1_b) = BitVec.ofNat 64 end_v := BitVec.eq_of_toNat_eq (by
    rw [h_end_arg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hend_lt])
  have h_sext1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := by decide
  c0_hsteps_nogrp
  try rw [h_sext1]
  refine wp_loop_break_group (brkTs := [Ty.bool, i64, i64]) (lpTs := [Ty.bool, i64, i64])
    (BrkPost := fun xs m2 => let failed := xs.1; let reduced := xs.2.1; let p := xs.2.2.1
      ∃ st2 : FullState, off ≤ p.toNat ∧ p.toNat ≤ end_v ∧ reduced.toNat ≤ p.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st2 ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st2.core.cur_vars = s.core.cur_vars ∧ st2.core.fuel = s.core.fuel ∧
        st2.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st2 ⋆ R) m2)
    (Inv := fun n xs m1 => let failed := xs.1; let reduced := xs.2.1; let p := xs.2.2.1
      ∃ st : FullState, off ≤ p.toNat ∧ p.toNat ≤ end_v ∧ n = end_v - p.toNat ∧
        reduced.toNat ≤ p.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
        st.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st ⋆ R) m1) ?_ ?_ ?_
  · rintro B ⟨failed, reduced, p, ⟨⟩⟩ m2
      ⟨st2, hp_lo2, hp_hi2, hred_le2, hto2, hfail2, hcv2, hfuel2, hws1_2, hm2⟩
    dsimp only at hp_lo2 hp_hi2 hred_le2 hto2 hfail2
    rw [h_end_bv, h_off_arg]
    exact s13_tl_compact_wp h_add_unit hsp hw0 hsrc_lt hoff_lt hsz_lt hend_lt
      hp_lo2 hp_hi2 hred_le2 hto2 hfail2 hcv2 hfuel2 hws1_2 hm2 hQ
  · rintro B L n ⟨failed, reduced, p, ⟨⟩⟩ m1 hB hL
      ⟨st, hp_lo, hp_hi, hneq, hred_le, hto, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
    dsimp only at hp_lo hp_hi hneq hred_le hto hfail_ent
    have hlen_st := hto.base.len_ok
    have hst_cv_lt : st.core.cur_vars < 2 ^ 32 := by rw [hcv_st]; omega
    have hB_now : B (failed, reduced, p, ()) m1 :=
      hB (failed, reduced, p, ()) m1 ⟨st, hp_lo, hp_hi, hred_le, hto, hfail_ent, hcv_st, hfuel_st,
        hws1_st, hm1⟩
    c0_hsplit
    · have hp_lt : p.toNat < end_v := by
        have h1 : p.toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
          (1 : Nat)).toNat]'hw0_b) + BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
          (1 : Nat) + 1).toNat]'hw1_b)).toNat := by c0_bound
        rwa [h_end_arg] at h1
      c0_hsplit
      · c0_hsteps; exact hB_now
      · have hfail_f : failed = false := by revert hc; cases failed <;> decide
        c0_hsplit
        · have hp_len := s13_tl_wstk_lt hlen_st.core_ok hp_lt hto.base.end_le_wlen
          c0_hsplit
          · have hfl0 : (st.core.wstk[p.toNat] &&& 0x80000000#32) = 0#32 := hc
            obtain ⟨_, hto2⟩ := hto.skip_large hp_lt (List.getElem?_eq_getElem hp_len) hfl0
            c0_hsplit
            · c0_hsteps; exact hB_now
            · c0_hsteps
              have hp2_bv : (p + 2#64).toNat = p.toNat + 2 := ft_bv64_add2 (by omega)
              exact hL (end_v - (p.toNat + 2)) (failed, reduced, p + 2#64, ()) m1 (by omega) ⟨st,
                by dsimp only; rw [hp2_bv]; omega, by dsimp only; rw [hp2_bv]; omega,
                by dsimp only; rw [hp2_bv], by dsimp only; rw [hp2_bv]; omega,
                by dsimp only; rw [hp2_bv]; exact hto2, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
          · have hfl_nz : (st.core.wstk[p.toNat] &&& 0x80000000#32) ≠ 0#32 := hc
            obtain ⟨_, hdst_lt_st, _, hto_skip⟩ :=
              hto.skip_bin hp_lt (List.getElem?_eq_getElem hp_len) hfl_nz
            let w0 := st.core.wstk[p.toNat]'hp_len; let dst := w0 &&& 0x7FFFFFFF#32
            have hdst_lt0 : dst.toNat < 2 * s.core.cur_vars := by rw [← hcv_st]; exact hdst_lt_st
            c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (P := fun _ m2 => ∃ st_s : FullState,
                TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v reduced.toNat st_s ∧
                (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                st_s.core.cur_vars = s.core.cur_vars ∧ st_s.core.fuel = s.core.fuel ∧
                st_s.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st_s ⋆ R) m2) ?_ ?_
            · rintro J9 ⟨⟩ m2 ⟨st_s, hto_s, hfail_s, hcv_s, hfuel_s, hws1_s, hm2⟩; c0_hsteps
              have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega)
              exact hL (end_v - (p.toNat + 1)) (failed, reduced, p + 1#64, ()) m2 (by omega) ⟨st_s,
                by dsimp only; rw [hp1_bv]; omega, by dsimp only; rw [hp1_bv]; omega,
                by dsimp only; rw [hp1_bv], by dsimp only; rw [hp1_bv]; omega,
                by dsimp only; rw [hp1_bv]; exact hto_s, hfail_s, hcv_s, hfuel_s, hws1_s, hm2⟩
            · intro J9 hJ9
              c0_hsplit
              · c0_hsteps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
              c0_hsplit
              · c0_hsteps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
              have hdst_ne : dst.toNat ≠ src.toNat := by
                dsimp only [dst, w0]
                have hgt : ¬((st.core.wstk[p.toNat]'hp_len &&& 0x7FFFFFFF#32).toNat ≤
                    src.toNat) := by c0_bound
                omega
              have hdst_vlen :
                  (BitVec.setWidth 64 (st.core.wstk[p.toNat]'hp_len &&& 0x7FFFFFFF#32)).toNat <
                    st.core.vals.length := by
                dsimp only [dst, w0] at hdst_lt0
                rw [ft_bv32_setWidth64, hlen_st.core_ok.vals_len]
                have := hlen_st.core_ok.cur_vars_le; rw [hcv_st] at this; omega
              c0_hsplit
              · c0_hsteps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
              let not_src := src ^^^ 1#32
              have hnot_eq : not_src.toNat = src.toNat ^^^ 1 := ft_bv32_xor1 src
              have hnot_lt : not_src.toNat < 2 * st.core.cur_vars := by
                rw [hnot_eq, hcv_st]; exact litNeg_lt_two_mul hsrc_lt
              have hnot_vlen := s13_tl_vals_lt hlen_st.core_ok hnot_lt
              have hpre_vals := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.1
              have hpre_te := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              have hpre_trl := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              let saved := st.core.trail_end
              obtain ⟨hsaved_lt, hu1, _⟩ := TransUnrollInv.init (st_pre := st) hw0 hlen_st
                hpre_vals hpre_te hcv_st (by rw [hcv_st]; exact hsrc_lt)
                (by rw [hpre_vals]; exact hsrc0)
              have hte_len : saved < st.core.trl.length := by
                rw [hlen_st.core_ok.trl_len]
                exact Nat.lt_of_lt_of_le hsaved_lt hlen_st.core_ok.cur_vars_le
              have hbv_not : BitVec.ofNat 32 (src.toNat ^^^ 1) = not_src := BitVec.eq_of_toNat_eq
                (by rw [hnot_eq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
              have hsrc64_vlen : (BitVec.setWidth 64 src).toNat < st.core.vals.length := by
                rw [ft_bv32_setWidth64, hlen_st.core_ok.vals_len, ← hlen0.core_ok.vals_len]
                exact hsrc_vlen
              have hsav_lt := (s13_tl_bnds hlen_st.core_ok).2.2.2
              have hs_eq : (BitVec.ofNat 64 saved).toNat = saved := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]
              have hte64_len : (BitVec.ofNat 64 st.core.trail_end).toNat < st.core.trl.length := by
                rw [show st.core.trail_end = saved from rfl, hs_eq]; exact hte_len
              have hnot64_vlen : (BitVec.setWidth 64 not_src).toNat < st.core.vals.length := by
                rw [ft_bv32_setWidth64]; exact hnot_vlen
              have hte_p1 : (BitVec.ofNat 64 st.core.trail_end + 1).toNat = saved + 1 := by
                rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 (by rw [hs_eq]; omega),
                  hs_eq]
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [Ty.bool, i64, i64, Ty.bool])
                (Inv := fun nb xs m2 =>
                  let fb := xs.1; let _tk := xs.2.1; let prop := xs.2.2.1; let tb := xs.2.2.2.1
                  ∃ st_b : FullState, saved ≤ prop.toNat ∧ prop.toNat ≤ st_b.core.trail_end ∧
                    nb = st.core.cur_vars - prop.toNat ∧
                    TransUnrollInv c F0 F_cur s st src.toNat saved st_b ∧ ¬(fb = true ∧ tb = true) ∧
                    (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                    (tb = true → (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [src.toNat, dst.toNat])) ∧
                    (FullMem c st_b ⋆ R) m2) ?_ ?_
              · rintro L13 nb ⟨fb, tk, prop, tb, ⟨⟩⟩ m2 hL13
                  ⟨st_b, hsp_le, hpt_le, hbneq, hu_b, hntf, hfb, htb, hm2⟩
                dsimp only at hsp_le hpt_le hbneq hntf hfb htb; have hlen_b := hu_b.len_ok
                refine wp_join_group (ts := [])
                  (P := fun _ m3 => ∃ st_u : FullState,
                    TransUnrollInv c F0 F_cur s st src.toNat saved st_u ∧
                    ¬(fb = true ∧ tb = true) ∧
                    (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                    (tb = true → (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [src.toNat, dst.toNat])) ∧
                    (FullMem c st_u ⋆ R) m3) ?_ ?_
                · rintro J15 ⟨⟩ m3 ⟨st_u, hu_u, _, hfb_u, _, hm3⟩
                  exact s13_tl_unroll_wp h_del_bin hw0 hsrc_lt hdst_lt0 hdst_ne hp_lo hp_lt
                    hred_le hto hcv_st hfuel_st hws1_st hp_len rfl hfl_nz hpre_vals rfl hsav_lt
                    hu_u hfb_u hm3 fun failed' red' p' m' hdec h =>
                      hL (end_v - p'.toNat) (failed', red', p', ()) m'
                        (by dsimp only at hdec ⊢; omega) (by simpa only [end_v, true_and] using h)
                · intro J15 hJ15
                  have hJ15_now : J15 () m2 := hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
                  c0_hsplit
                  · c0_hsteps; exact hJ15_now
                  have htb_f : tb = false := by revert hc; cases tb <;> decide
                  c0_hsplit
                  · c0_hsteps; exact hJ15_now
                  have hfb_f : fb = false := by revert hc; cases fb <;> decide
                  c0_hsplit
                  · have hte_b_lt := (s13_tl_bnds hlen_b.core_ok).2.2.2
                    have hcv_b_le := hlen_b.core_ok.cur_vars_le
                    have hpt_lt : prop.toNat < st_b.core.trail_end := by
                      have h1 : prop.toNat < st_b.core.trail_end % 2 ^ 64 := by c0_bound
                      rwa [Nat.mod_eq_of_lt hte_b_lt] at h1
                    c0_hsplit
                    · have hprop_tlen : prop.toNat < st_b.core.trl.length := by
                        rw [hlen_b.core_ok.trl_len]; have := hlen_b.core_ok.trail_end_le; omega
                      have hprop1 := ft_bv64_add1 (by omega : prop.toNat + 1 < 2 ^ 64)
                      obtain ⟨lit, hlit_get, hlit_lt, _, _, _, hent_lit⟩ :=
                        hu_b.bfs_trl_inv prop.toNat hsp_le hpt_lt
                      let nl := lit ^^^ 1#32; have hnl_eq := ft_bv32_xor1 lit
                      have hnl_lt : nl.toNat < 2 * st_b.core.cur_vars := by
                        rw [hnl_eq, hu_b.same_core]; exact litNeg_lt_two_mul hlit_lt
                      have hlit_ge : st_b.core.trl[prop.toNat]'hprop_tlen = lit :=
                        Option.some.inj ((List.getElem?_eq_getElem hprop_tlen).symm.trans hlit_get)
                      have hnl_shl : (BitVec.setWidth 64 (lit ^^^ 1) <<< (1 : Nat)).toNat =
                          2 * nl.toNat := by
                        rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
                        rfl
                      have hnl_wv0 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                          1) <<< (1 : Nat)).toNat < st_b.core.wvec.length := by
                        rw [hlit_ge, hnl_shl, hlen_b.core_ok.wvec_len]; omega
                      have hnl_wv1 : ((BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                          1) <<< (1 : Nat)) + 1).toNat < st_b.core.wvec.length := by
                        rw [hlit_ge, show (1 : BitVec 64) = 1#64 from rfl,
                          ft_bv64_add1 (by rw [hnl_shl]; omega), hnl_shl, hlen_b.core_ok.wvec_len]
                        omega
                      obtain ⟨hnl_bnd, nt0, htomb0⟩ := hu_b.watch_slice hto hnl_lt
                      let loff := fullWatchOffCore st_b.core nl.toNat
                      let lsz := fullWatchSizeCore st_b.core nl.toNat; let lend := loff + lsz
                      have hloff_lt : loff < 2 ^ 64 := by
                        have := (s13_tl_bnds hlen_b.core_ok).2.2.1; omega
                      have hlo_eq : (BitVec.ofNat 64 loff).toNat = loff := by
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hloff_lt]
                      have hlo_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat)).toNat]'
                          hnl_wv0) = BitVec.ofNat 64 loff := by
                        apply BitVec.eq_of_toNat_eq; rw [ft_bv32_setWidth64, hlo_eq]
                        have hidx2 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                            1) <<< (1 : Nat)).toNat = 2 * nl.toNat := by
                          simpa [hlit_ge] using hnl_shl
                        have hnl0 : 2 * nl.toNat < st_b.core.wvec.length := by
                          rw [← hidx2]; exact hnl_wv0
                        simp only [hidx2]; exact s13_tl_getElem_toNat hnl0
                      have hls_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat) + 1).toNat]'
                          hnl_wv1) = BitVec.ofNat 64 lsz := by
                        apply BitVec.eq_of_toNat_eq
                        rw [ft_bv32_setWidth64, BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by have := (s13_tl_bnds hlen_b.core_ok).2.2.1; omega)]
                        have hidx3 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                            1) <<< (1 : Nat) + 1).toNat = 2 * nl.toNat + 1 := by
                          rw [hlit_ge, show (1 : BitVec 64) = 1#64 from rfl,
                            ft_bv64_add1 (by rw [hnl_shl]; omega), hnl_shl]
                        have hnl1 : 2 * nl.toNat + 1 < st_b.core.wvec.length := by
                          rw [← hidx3]; exact hnl_wv1
                        simp only [hidx3]; exact s13_tl_getElem_toNat hnl1
                      have hlend_bv : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat)).toNat]'
                          hnl_wv0) + BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat) + 1).toNat]'
                          hnl_wv1) = BitVec.ofNat 64 (loff + lsz) := by
                        have := (s13_tl_bnds hlen_b.core_ok).2.2.1
                        apply BitVec.eq_of_toNat_eq
                        rw [hlo_arg, hls_arg, BitVec.toNat_add, hlo_eq, BitVec.toNat_ofNat,
                          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lsz < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : loff + lsz < 2 ^ 64)]
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [Ty.bool, i64, Ty.bool, i64])
                        (P := fun xs m3 =>
                          let f2 := xs.1; let _tk2 := xs.2.1; let t2 := xs.2.2.1
                          ∃ st_w : FullState, TransUnrollInv c F0 F_cur s st src.toNat saved st_w ∧
                            st_b.core.trail_end ≤ st_w.core.trail_end ∧ ¬(f2 = true ∧ t2 = true) ∧
                            (f2 = true → (cnfOfClauses F_cur).EntailsClause
                              (cnfClause [src.toNat])) ∧
                            (t2 = true → (cnfOfClauses F_cur).EntailsClause
                              (cnfClause [src.toNat, dst.toNat])) ∧
                            (FullMem c st_w ⋆ R) m3) ?_ ?_
                      · rintro J19 ⟨f2, tk2, t2, _q, ⟨⟩⟩ m3
                          ⟨st_w, hu_w, _, hntf2, hf2, ht2, hm3⟩
                        have hpt_pre : prop.toNat < st.core.cur_vars := by
                          have := hlen_b.core_ok.trail_end_le; rw [hu_b.same_core] at this
                          exact Nat.lt_of_lt_of_le hpt_lt this
                        c0_hsteps
                        exact hL13 (st.core.cur_vars - (prop.toNat + 1))
                          (f2, tk2, prop + 1#64, t2, ()) m3 (by rw [hbneq]; omega)
                          ⟨st_w, by rw [hprop1]; omega, by rw [hprop1]; omega,
                           by rw [hprop1], hu_w, hntf2, hf2, ht2, hm3⟩
                      · intro J19 hJ19
                        have hxx : ∀ n : Nat, n ^^^ 1 ^^^ 1 = n := fun n => by
                          apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_xor]
                        rw [hlend_bv, hlo_arg, hlit_ge]
                        exact s13_tl_inner_watch_wp hw0 hcl0 hsrc_lt hcv_st hpre_vals hpre_te
                          hpre_trl hu_b hntf hfb_f htb_f hfb htb
                          (by simpa only [show (1 : BitVec 32) = 1#32 from rfl, ft_bv32_xor1,
                            hxx] using hent_lit)
                          hnl_bnd htomb0 hm2
                          (fun f2 tk2 t2 q m3 h => hJ19 (f2, tk2, t2, q, ()) m3 h)
                    · c0_hsteps; exact hJ15_now
                  · c0_hsteps; exact hJ15_now
              · intro L13 hL13
                have hnot_sw : (BitVec.setWidth 64 (src ^^^ 1)).toNat = src.toNat ^^^ 1 := by
                  rw [ft_bv32_setWidth64]; exact ft_bv32_xor1 src
                have hsrc_sw : (BitVec.setWidth 64 src).toNat = src.toNat := ft_bv32_setWidth64 src
                c0_hsteps
                let st_i : FullState := { st with core := { st.core with
                  vals := (st.core.vals.set (src.toNat ^^^ 1) 1#8).set src.toNat 0xFF#8
                  trl := st.core.trl.set saved not_src
                  trail_end := saved + 1 } }
                refine hL13 (st.core.cur_vars - saved)
                  (failed, st.scratch.ant_sz - 1#64, BitVec.ofNat 64 saved, false, ()) _
                  ⟨st_i, by dsimp only; rw [hs_eq]; exact Nat.le_refl _,
                   by dsimp only [st_i]; rw [hs_eq]; omega,
                   by dsimp only; rw [hs_eq],
                   by dsimp only [st_i]; simpa only [hbv_not] using hu1,
                   by dsimp only; simp [hfail_f],
                   fun hf => by dsimp only at hf; simp [hfail_f] at hf,
                   fun ht => False.elim (Bool.noConfusion ht), ?_⟩
                refine s13_tl_fullMem_eq ?_ (by assumption)
                dsimp only [st_i, saved, not_src] at hs_eq hte_p1 ⊢
                rw [hnot_sw, hsrc_sw, hs_eq, hte_p1]; rfl
        · c0_hsteps; exact hB_now
    · c0_hsteps; exact hB_now
  · intro B L hB hL; c0_hsteps; rw [h_off_arg]
    have hto0 := TransOuterInv.init hlen0 hw0 hsp.2.2.2.2 hcl0 hsrc_lt hsz_pos
    exact hL (end_v - off) (false, 0#64, BitVec.ofNat 64 off, ()) m ⟨s,
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      (by dsimp only; rw [hof64]; exact Nat.le_add_right off sz), (by dsimp only; rw [hof64]),
      (by dsimp only; simp), (by dsimp only; rw [hof64]; exact hto0),
      (by dsimp only; intro h; cases h), rfl, rfl, rfl, hm⟩

end TransLitS5Proof

/-! ## 2. `full_transitive_m6_s5_wp` (`step13TransitiveSpec`) -/

section TransTopS5Proof

theorem full_transitive_m6_s5_wp (Γ : Env)
    (h_backtrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (h_prio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (h_sort : ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Γ "full_trans_sort_m6" [i64, i64] [] a m Q X)
    (h_trans_lit : ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Γ "full_trans_lit_m6" [i64, i32, .bool] [.bool] a m Q X)
    (h_propagate : ∀ a m Q X, s5bBcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (h_defrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, step13TransitiveSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_transitive_m6_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, ext0, s, R, rfl, hcfg, hext0, hsp, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_transitive_m6_body
  refine wp_join_group (ts := [])
    (P := fun _ m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.probing = s.core.probing ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext0 s1 ⋆ R) m1) ?_ ?_
  · rintro J1 ⟨⟩ m1 ⟨s1, hsp1, hcl1, hpr1, hfuel1, hm1⟩
    have hlen1 := hsp1.1.lengths
    have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := (s13_tl_bnds hlen1.core_ok).1; omega
    have hcv_le1 : s1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
    have hm1_f := fullM6HdrMem_focus_full hm1
    have hret := hQ 1#64 ext0 s1 m1 ⟨hext0, fun hi => ⟨hi, M6ExtW2bPres.refl ext0⟩⟩
      hsp1 (fun _ => hcl1) hpr1 ⟨hcl1, hpr1⟩ hfuel1 (Or.inl rfl)
      (fun h => absurd h (by decide)) hm1
    c0_hsteps_nogrp
    all_goals try exact hret
    c0_hsteps_nogrp; c0_call h_prio
    have hsp_p := fullSparseInv_with_probing hsp1 1#64
    obtain ⟨F_cur1, hw1⟩ := hsp_p.1.witness
    have hsp_pW : FullSparseInvW c F0 F_cur1
        { s1 with core := { s1.core with probing := 1#64 } } :=
      ⟨hsp_p.1.lengths, hw1, hsp_p.2.1, hsp_p.2.2.1, hsp_p.2.2.2.1, hsp_p.2.2.2.2⟩
    refine ⟨c, F0, F_cur1, _, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hsp_pW, (by assumption),
      fun stop_early wstk' scr' m2 hsp2W hm2 => ?_⟩
    let s2 : FullState :=
      { s1 with
        core := { s1.core with probing := 1#64, wstk := wstk' }
        scratch := { s1.scratch with scratch_buf := scr' } }
    have hsp2 : FullSparseInv c F0 s2 := ⟨⟨hsp2W.1, ⟨F_cur1, hsp2W.2.1⟩⟩, hsp2W.2.2⟩
    have hcl2 : s2.core.cur_level = 0 := hcl1
    have hlen2 := hsp2.1.lengths
    have hcv_s2 : s2.core.cur_vars = s1.core.cur_vars := rfl
    have hfu_s2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfuel1
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64, i64])
      (fun (pn, v, ()) mc => ∃ ws1 : List (BitVec 32),
        pn.toNat ≤ v.toNat ∧ v.toNat ≤ s1.core.cur_vars ∧ ws1.length = 2 * c.max_vars ∧
        (∀ i < pn.toNat, (ws1[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1 } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mc)
      (fun (_, v, ()) _ => s1.core.cur_vars - v.toNat)
      (fun Jc hJc => by
        c0_hsteps
        exact hJc (0#64, 0#64, ()) m2 ⟨s2.scratch.work_stk1, Nat.le_refl _, Nat.zero_le _,
          hlen2.scratch_ok.work_stk1_len, (fun _ h => by cases h), hm2⟩)
      (fun Jc ⟨pn, v, ⟨⟩⟩ mc ⟨ws1, hpn_le, hv_le, hws1_len, hpn_lt, hmc⟩ ihc => ?_)
    c0_hsplit
    · have hv_lt : v.toNat < s1.core.cur_vars := by
        have h1 : v.toNat < s1.core.cur_vars % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt hcv_lt] at h1
      have hv_fl : v.toNat < s2.core.flags.length := by rw [hlen2.core_ok.flags_len]; omega
      have hv_shl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := ft_bv64_shl1 (by omega)
      have hv_vl : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
        rw [hv_shl, hlen2.core_ok.vals_len]; omega
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := ft_bv64_add1 (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (pn', ()) m' => ∃ ws1' : List (BitVec 32),
        pn'.toNat ≤ v.toNat + 1 ∧ ws1'.length = 2 * c.max_vars ∧
        (∀ i < pn'.toNat, (ws1'[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1' } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m')
        (fun _ ⟨pn', ⟨⟩⟩ m' ⟨ws1', hpn', hws1', hlt', hm'⟩ => by
          c0_hsteps
          exact ihc (pn', v + 1#64, ()) m' (by dsimp only; omega)
            ⟨ws1', by rw [hv1]; exact hpn', by rw [hv1]; omega, hws1', hlt', hm'⟩)
        (fun Jw hJw => by
          c0_hsplit
          · c0_hsplit
            · have hpn1 : (pn + 1#64).toNat = pn.toNat + 1 := ft_bv64_add1 (by omega)
              have hpn_ws1 : pn.toNat < ws1.length := by omega
              have hv32 : (v.truncate 32).toNat = v.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              c0_hsteps
              exact hJw (pn + 1#64, ()) _ ⟨ws1.set pn.toNat (v.truncate 32), by rw [hpn1]; omega,
                by simp [hws1_len], fun i hi => by
                  rw [hpn1] at hi
                  by_cases hip : i = pn.toNat
                  · subst hip; rw [List.getElem?_set_self hpn_ws1, Option.getD_some, hv32]
                    exact hv_lt
                  · rw [List.getElem?_set_ne (Ne.symm hip)]; exact hpn_lt i (by omega),
                (by assumption)⟩
            · c0_hsteps; exact hJw (pn, ()) mc ⟨ws1, by omega, hws1_len, hpn_lt, hmc⟩
          · c0_hsteps; exact hJw (pn, ()) mc ⟨ws1, by omega, hws1_len, hpn_lt, hmc⟩)
    · let s3 : FullState := { s2 with scratch := { s2.scratch with work_stk1 := ws1 } }
      have hsp3 : FullSparseInv c F0 s3 := s13_tl_sparse_with_ws1 hsp2 hws1_len
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (P := fun _ ms => ∃ ws1s : List (BitVec 32),
        ws1s.length = 2 * c.max_vars ∧
        (∀ i < pn.toNat, (ws1s[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
        FullSparseInv c F0 { s2 with scratch := { s2.scratch with work_stk1 := ws1s } } ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1s } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ms) ?_ ?_
      · rintro Js ⟨⟩ ms ⟨ws1s, hws1s_len, hpn_lts, hsp_s, hms⟩
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64])
          (BrkPost := fun xs mb => let res := xs.1
            ∃ extb sb, M6HdrExtOk extb ∧
              (M6HdrExtInitOk ext0 → M6HdrExtInitOk extb ∧ M6ExtW2bPres ext0 extb) ∧
              FullSparseInv c F0 sb ∧ sb.core.cur_level = 0 ∧
              sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (res = 1#64 ∨ res = 20#64) ∧
              (res = 20#64 → F0.Unsat) ∧
              (FullMem c sb ⋆ (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R)) mb)
          (Inv := fun rem (pi, ()) ml => ∃ extl sl,
            pi.toNat ≤ pn.toNat ∧ rem = pn.toNat - pi.toNat ∧ M6HdrExtOk extl ∧
            (M6HdrExtInitOk ext0 → M6HdrExtInitOk extl ∧ M6ExtW2bPres ext0 extl) ∧
            FullSparseInv c F0 sl ∧ sl.core.cur_level = 0 ∧ sl.core.cur_vars = s1.core.cur_vars ∧
            sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (∀ i < pn.toNat, (sl.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
            (FullMem c sl ⋆ (m6ExtMem (m6ExtAddr c.hdr) extl ⋆ R)) ml) ?_ ?_ ?_
        · rintro B ⟨res, _pi, ⟨⟩⟩ mb
            ⟨extb, sb, hextb, hwb, hspb, hclb, hfuelb, hresb, hunsatb, hmb⟩
          refine wp_join_group (ts := []) (P := fun _ m3 => ∃ sd : FullState,
            FullSparseInv c F0 sd ∧ sd.core.cur_level = 0 ∧
            sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c sd ⋆ (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R)) m3) ?_ ?_
          · rintro Jd ⟨⟩ m3 ⟨sd, hspd, hcld, hfueld, hm3⟩; c0_hsteps
            exact hQ res extb _ _ ⟨hextb, hwb⟩ (fullSparseInv_with_probing hspd s1.core.probing)
              (fun _ => hcld) hpr1 ⟨hcld, hpr1⟩ hfueld hresb hunsatb
              (fullM6HdrMem_unfocus_full (by assumption))
          · intro Jd hJd; have hlenb := hspb.1.lengths; c0_hsplit
            · c0_hsteps_nogrp; c0_call h_defrag
              obtain ⟨_, hwb_c⟩ := hspb.1.witness
              have hwm := hwb_c.watches
              simp only [ModeWatchesInv, hspb.2.2.2.2, ↓reduceIte] at hwm
              refine ⟨c, sb, m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R, rfl, hlenb, hwm.layout, hmb,
                fun _ _ _ _ m3 hlen3 hlay3 _ hpres hm3 => by
                  c0_hsteps
                  exact hJd () m3 ⟨_, fullWstackDefrag_sparse hspb rfl hlen3 hlay3 hpres, hclb,
                    hfuelb, hm3⟩⟩
            · c0_hsteps; exact hJd () mb ⟨sb, hspb, hclb, hfuelb, hmb⟩
        · rintro B L rem ⟨pi, ⟨⟩⟩ ml hB hL
            ⟨extl, sl, hpi_le, _, hextl, hwl, hspl, hcll, hcvl, hfuell, hws1l, hml⟩
          have hlenl := hspl.1.lengths
          have hB1 : B (1#64, pi, ()) ml := hB (1#64, pi, ()) ml ⟨extl, sl, hextl, hwl, hspl, hcll,
            hfuell, Or.inl rfl, fun h => by dsimp only at h; exact absurd h (by decide), hml⟩
          c0_hsplit
          · have hpi_lt : pi.toNat < pn.toNat := by c0_bound
            c0_hsplit
            · c0_hsplit
              · c0_hsplit
                · have hpi_ws1 : pi.toNat < sl.scratch.work_stk1.length := by
                    rw [hlenl.scratch_ok.work_stk1_len]; omega
                  let pv := sl.scratch.work_stk1[pi.toNat]'hpi_ws1
                  have hpv_lt : pv.toNat < s1.core.cur_vars := by
                    have h := hws1l pi.toNat hpi_lt
                    rwa [List.getElem?_eq_getElem hpi_ws1, Option.getD_some] at h
                  have hpv64 : (pv.setWidth 64).toNat = pv.toNat := ft_bv32_setWidth64 pv
                  have hpv_fl : pv.toNat < sl.core.flags.length := by
                    rw [hlenl.core_ok.flags_len]; omega
                  have hpv_shl : (pv.setWidth 64 <<< (1 : Nat)).toNat = 2 * pv.toNat := by
                    rw [ft_bv64_shl1 (by rw [hpv64]; omega), hpv64]
                  have hpv_vl : (pv.setWidth 64 <<< (1 : Nat)).toNat < sl.core.vals.length := by
                    rw [hpv_shl, hlenl.core_ok.vals_len]; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64]) (P := fun xs m_c => xs.1 = 1#64 ∧
                    ∃ extn sn, M6HdrExtOk extn ∧
                      (M6HdrExtInitOk ext0 → M6HdrExtInitOk extn ∧ M6ExtW2bPres ext0 extn) ∧
                      FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧
                      sn.core.cur_vars = s1.core.cur_vars ∧
                      sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (∀ i < pn.toNat,
                        (sn.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
                      (FullMem c sn ⋆ (m6ExtMem (m6ExtAddr c.hdr) extn ⋆ R)) m_c) ?_ ?_
                  · rintro Jc ⟨_, ⟨⟩⟩ m_c
                      ⟨rfl, extn, sn, hextn, hwn, hspn, hcln, hcvn, hfueln, hws1n, hm_c⟩
                    have hpi1 : (pi + 1#64).toNat = pi.toNat + 1 := ft_bv64_add1 (by omega)
                    c0_hsteps
                    exact hL (pn.toNat - (pi.toNat + 1)) (pi + 1#64, ()) m_c (by omega)
                      ⟨extn, sn, by rw [hpi1]; omega, by rw [hpi1], hextn, hwn, hspn, hcln,
                       hcvn, hfueln, hws1n, hm_c⟩
                  · intro Jc hJc
                    refine wp_join_group (ts := []) (P := fun _ m_e => m_e = ml)
                      (fun _ _ m_e heq => by
                        subst heq; c0_hsteps
                        have hsp_cl : FullSparseInv c F0 { sl with core := { sl.core with
                            flags := sl.core.flags.set pv.toNat
                              (sl.core.flags[pv.toNat] &&& ~~~512#32) } } :=
                          fullSparseInv_clear_fl_trans hspl
                        exact hJc (1#64, ()) _ ⟨rfl, extl, _, hextl, hwl, hsp_cl, hcll, hcvl,
                          hfuell, hws1l,
                          by refine s13_tl_fullMem_eq ?_ (by assumption)
                             dsimp only [pv] at hpv64 ⊢; simp only [hpv64]; rfl⟩)
                      (fun Jelse hJelse => ?_)
                    c0_hsplit
                    · c0_hsplit
                      · have hpv32 : 2 * pv.toNat + 1 < 2 ^ 32 := by
                          have := (s13_tl_bnds hlenl.core_ok).1; omega
                        have hlit0 : (pv <<< (1 : Nat)).toNat < 2 * sl.core.cur_vars := by
                          rw [show (pv <<< (1 : Nat)).toNat = 2 * pv.toNat by
                            simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega]
                          omega
                        c0_hsteps_nogrp; c0_call h_trans_lit
                        refine ⟨c, F0, sl, m6ExtMem (m6ExtAddr c.hdr) extl ⋆ R, rfl, hspl, hcll,
                          hlit0, hml,
                          fun ok0 st0 m3 hspt0 hclt0 hcvt0 hfuelt0 hws1t0 huns0 hm3 => ?_⟩
                        have hcv_t0 : st0.core.cur_vars = s1.core.cur_vars := hcvt0.trans hcvl
                        have hfu_t0 : st0.core.fuel.toNat ≤ s.core.fuel.toNat := by
                          rw [hfuelt0]; exact hfuell
                        have hws1_t0 : ∀ i < pn.toNat,
                            (st0.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars := by
                          rw [hws1t0]; exact hws1l
                        c0_hsplit
                        · obtain ⟨F_ct0, hwt0⟩ := hspt0.1.witness
                          c0_hsteps_nogrp; c0_call h_propagate
                          refine ⟨c, F0, F_ct0, extl, st0, R, rfl, hcfg, hextl, hspt0.1.lengths,
                            hwt0, hspt0.2.2.2.2, fullM6HdrMem_unfocus_full hm3,
                            fun r_p0 ext_p0 vals' flags' lvl' rsns' trl' tp' te' prop' unass'
                              unfl' wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom'
                              sc_p0 m4 hext_p0 hw_p0 hlen4 hw4 _ hperm4 hpr_sc4 _ _ _ _ hfu4 _ _
                              hr1 _ _ hm4 => ?_⟩
                          let st_p0 : FullState := { st0 with
                            scratch := sc_p0
                            core := { st0.core with
                              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass',
                              unflushed := unfl', wvec := wvec', arena := arena',
                              wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                              confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                              confl_lit1 := c1', oom := oom' } }
                          have hsp_p0 :=
                            s13_tl_sparse_of_bcp hspt0 hwt0 st_p0 rfl hlen4 hw4 hperm4 hpr_sc4
                          have hfu_p0 : fuel'.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu4 hfu_t0
                          have hw_ep0 := s13_ext_pres_trans_tr hwl hw_p0
                          have hm4_f := fullM6HdrMem_focus_full hm4
                          c0_hsplit
                          · c0_hsteps
                            exact hB (20#64, pi, ()) m4 ⟨ext_p0, _, hext_p0, hw_ep0, hsp_p0,
                              hclt0, hfu_p0, Or.inr rfl,
                              fun _ => level0_unsat_of_conflict_okW hw4 hclt0 (hr1 hc).2.2, hm4_f⟩
                          · c0_hsplit
                            · c0_hsteps
                              exact hB (1#64, pi, ()) m4 ⟨ext_p0, _, hext_p0, hw_ep0, hsp_p0,
                                hclt0, hfu_p0, Or.inl rfl,
                                fun h => by dsimp only at h; exact absurd h (by decide), hm4_f⟩
                            · c0_hsplit
                              · c0_hsteps
                                exact hB (1#64, pi, ()) m4 ⟨ext_p0, _, hext_p0, hw_ep0, hsp_p0,
                                  hclt0, hfu_p0, Or.inl rfl,
                                  fun h => by dsimp only at h; exact absurd h (by decide), hm4_f⟩
                              · c0_hsplit
                                · c0_hsteps
                                  exact hB (1#64, pi, ()) m4 ⟨ext_p0, _, hext_p0, hw_ep0, hsp_p0,
                                    hclt0, hfu_p0, Or.inl rfl,
                                    fun h => by dsimp only at h; exact absurd h (by decide), hm4_f⟩
                                · c0_hsplit
                                  · c0_hsteps
                                    exact hB (1#64, pi, ()) m4 ⟨ext_p0, _, hext_p0, hw_ep0, hsp_p0,
                                      hclt0, hfu_p0, Or.inl rfl,
                                      fun h => by dsimp only at h; exact absurd h (by decide),
                                        hm4_f⟩
                                  · have hws1_p0 : ∀ i < pn.toNat,
                                        (st_p0.scratch.work_stk1[i]?.getD 0#32).toNat <
                                          s1.core.cur_vars := by
                                      dsimp only [st_p0]; rw [hpr_sc4.2.1]; exact hws1_t0
                                    have hlit1 : ((pv <<< (1 : Nat)) ||| 1#32).toNat <
                                        2 * st_p0.core.cur_vars := by
                                      have hsh : (pv <<< (1 : Nat)).toNat = 2 * pv.toNat := by
                                        simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
                                      have hor : (2 * pv.toNat) ||| 1 = 2 * pv.toNat + 1 := by
                                        apply Nat.eq_of_testBit_eq; intro i
                                        rw [Nat.testBit_or]
                                        cases i with
                                        | zero => simp [Nat.testBit_zero]
                                        | succ n =>
                                          simp [Nat.testBit_succ,
                                            show (2 * pv.toNat + 1) / 2 = pv.toNat by omega]
                                      have h1 : ((pv <<< (1 : Nat)) ||| 1#32).toNat =
                                          2 * pv.toNat + 1 := by
                                        rw [BitVec.toNat_or, hsh,
                                          show (1#32 : BitVec 32).toNat = 1 from rfl, hor]
                                      rw [h1]; dsimp only [st_p0]; omega
                                    c0_hsteps_nogrp; c0_call h_trans_lit
                                    refine ⟨c, F0, st_p0, m6ExtMem (m6ExtAddr c.hdr) ext_p0 ⋆ R,
                                      rfl, hsp_p0, hclt0, hlit1, hm4_f,
                                      fun ok1 st1 m5 hspt1 hclt1 hcvt1 hfuelt1 hws1t1 huns1 hm5 =>
                                        ?_⟩
                                    have hcv_t1 : st1.core.cur_vars = s1.core.cur_vars :=
                                      hcvt1.trans hcv_t0
                                    have hfu_t1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                      rw [hfuelt1]; exact hfu_p0
                                    have hws1_t1 : ∀ i < pn.toNat,
                                        (st1.scratch.work_stk1[i]?.getD 0#32).toNat <
                                          s1.core.cur_vars := by
                                      rw [hws1t1]; exact hws1_p0
                                    c0_hsplit
                                    · obtain ⟨F_ct1, hwt1⟩ := hspt1.1.witness
                                      c0_hsteps_nogrp; c0_call h_propagate
                                      refine ⟨c, F0, F_ct1, ext_p0, st1, R, rfl, hcfg, hext_p0,
                                        hspt1.1.lengths, hwt1, hspt1.2.2.2.2,
                                        fullM6HdrMem_unfocus_full hm5,
                                        fun _ ext_p1 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2
                                          unass2 unfl2 wvec2 arena2 wstk2 wlen2 wu2 fuel2 ctype2
                                          cref2 c0_2 c1_2 oom2 sc_p1 m6 hext_p1 hw_p1 hlen6 hw6 _
                                          hperm6 hpr_sc6 _ _ _ _ hfu6 _ _ hr1_2 _ _ hm6 => ?_⟩
                                      let st_p1 : FullState := { st1 with
                                        scratch := sc_p1
                                        core := { st1.core with
                                          vals := vals2, flags := flags2, lvl := lvl2,
                                          rsns := rsns2,
                                          trl := trl2, trail_pos := tp2, trail_end := te2,
                                          propagated := prop2, unassigned := unass2,
                                          unflushed := unfl2, wvec := wvec2, arena := arena2,
                                          wstk := wstk2, wlen := wlen2, wusable := wu2,
                                          fuel := fuel2, confl_type := ctype2, confl_ref := cref2,
                                          confl_lit0 := c0_2, confl_lit1 := c1_2, oom := oom2 } }
                                      have hsp_p1 :=
                                        s13_tl_sparse_of_bcp hspt1 hwt1 st_p1 rfl hlen6 hw6 hperm6
                                          hpr_sc6
                                      have hws1_p1 : ∀ i < pn.toNat,
                                          (st_p1.scratch.work_stk1[i]?.getD 0#32).toNat <
                                            s1.core.cur_vars := by
                                        dsimp only [st_p1]; rw [hpr_sc6.2.1]; exact hws1_t1
                                      have hfu_p1 : fuel2.toNat ≤ s.core.fuel.toNat :=
                                        Nat.le_trans hfu6 hfu_t1
                                      have hw_ep1 := s13_ext_pres_trans_tr hw_ep0 hw_p1
                                      have hm6_f := fullM6HdrMem_focus_full hm6
                                      c0_hsplit
                                      · c0_hsteps
                                        exact hB (20#64, pi, ()) m6 ⟨ext_p1, _, hext_p1, hw_ep1,
                                          hsp_p1, hclt1, hfu_p1, Or.inr rfl,
                                          fun _ => level0_unsat_of_conflict_okW hw6 hclt1
                                            (hr1_2 hc).2.2, hm6_f⟩
                                      · c0_hsplit
                                        · c0_hsteps
                                          exact hB (1#64, pi, ()) m6 ⟨ext_p1, _, hext_p1, hw_ep1,
                                            hsp_p1, hclt1, hfu_p1, Or.inl rfl,
                                            fun h => by dsimp only at h; exact absurd h (by decide),
                                            hm6_f⟩
                                        · c0_hsteps_nogrp
                                          refine wp_unroll_group fun _ _ => ?_
                                          c0_hsplit
                                          · c0_hsplit
                                            · c0_hsplit
                                              · have hpv_fl2 : pv.toNat < flags2.length := by
                                                  rw [hlen6.core_ok.flags_len]; omega
                                                c0_hsteps
                                                have hsp_cl2 : FullSparseInv c F0 {
                                                  st_p1 with
                                                  core := { st_p1.core with
                                                    flags := flags2.set pv.toNat
                                                      (flags2[pv.toNat] &&& ~~~512#32) } } :=
                                                  fullSparseInv_clear_fl_trans hsp_p1
                                                exact hJc (1#64, ()) _ ⟨rfl, ext_p1, _, hext_p1,
                                                  hw_ep1, hsp_cl2, hclt1, hcv_t1, hfu_p1, hws1_p1,
                                                  by refine s13_tl_fullMem_eq ?_ (by assumption)
                                                     dsimp only [pv, st_p1] at hpv64 ⊢
                                                     simp only [hpv64]; rfl⟩
                                              · c0_hsteps; exact hJc (1#64, ()) m6 ⟨rfl, ext_p1, _,
                                                  hext_p1, hw_ep1, hsp_p1, hclt1, hcv_t1, hfu_p1,
                                                  hws1_p1, hm6_f⟩
                                            · c0_hsteps; exact hJc (1#64, ()) m6 ⟨rfl, ext_p1, _,
                                                hext_p1, hw_ep1, hsp_p1, hclt1, hcv_t1, hfu_p1,
                                                hws1_p1, hm6_f⟩
                                          · c0_hsteps; exact hJc (1#64, ()) m6 ⟨rfl, ext_p1, _,
                                              hext_p1, hw_ep1, hsp_p1, hclt1, hcv_t1, hfu_p1,
                                              hws1_p1, hm6_f⟩
                                    · c0_hsteps; exact hB (20#64, pi, ()) m5 ⟨ext_p0, st1, hext_p0,
                                        hw_ep0, hspt1, hclt1, hfu_t1, Or.inr rfl,
                                        fun _ => huns1 (by revert hc; cases ok1 <;> decide), hm5⟩
                        · c0_hsteps; exact hB (20#64, pi, ()) m3 ⟨extl, st0, hextl, hwl, hspt0,
                            hclt0, hfu_t0, Or.inr rfl,
                            fun _ => huns0 (by revert hc; cases ok0 <;> decide), hm3⟩
                      · c0_hsteps; exact hJelse () ml rfl
                    · c0_hsteps; exact hJelse () ml rfl
                · c0_hsteps; exact hB1
              · c0_hsteps; exact hB1
            · c0_hsteps; exact hB1
          · c0_hsteps; exact hB1
        · intro B L hB hL; c0_hsteps; exact hL pn.toNat (0#64, ()) _ ⟨ext0, _, Nat.zero_le _,
            by simp, hext0, fun hi => ⟨hi, M6ExtW2bPres.refl ext0⟩,
            fullSparseInv_with_ant_sz hsp_s tick_lim, hcl2, hcv_s2, hfu_s2, hpn_lts,
            (by assumption)⟩
      · intro Js hJs; c0_hsplit
        · c0_hsteps_nogrp; c0_call h_sort
          refine ⟨c, F0, s3, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hsp3,
            by dsimp only [s3]; omega, by simpa [hcv_s2] using hpn_lt, hmc,
            fun ws1s ms hws1s hsp_s hpn_lts hms => by
              c0_hsteps; exact hJs () ms ⟨ws1s, hws1s, by simpa [hcv_s2] using hpn_lts, hsp_s, hms⟩⟩
        · c0_hsteps; exact hJs () mc ⟨ws1, hws1_len, hpn_lt, hsp3, hmc⟩
  · intro J1 hJ1; have hlen := hsp.1.lengths; obtain ⟨_, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := (s13_tl_bnds hlen.core_ok).2.2.2; omega
    have hm0' := hm0; rw [fullM6HdrMem_iff] at hm0; c0_hsplit
    · c0_hsteps_nogrp; c0_call h_backtrack
      have htl0 : (0 : BitVec 64).toNat = 0 := rfl
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hlen, hcl_lt, (fun hpos => by
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [htl0] at hpos ⊢; omega), hw.trail_lits_lt,
        fullM6HdrMem_focus_full hm0',
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => by
          c0_hsteps; exact hJ1 () _ ⟨_, fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1, by simp [hcl1],
            rfl, Nat.le_refl _, fullM6HdrMem_unfocus_full hm1⟩⟩
    · c0_hsteps; have hcl0' : s.core.cur_level = 0 := by
        have h1 : s.core.cur_level % 2 ^ 64 = 0 := by c0_bound
        rwa [Nat.mod_eq_of_lt hcl_lt] at h1
      exact hJ1 () m0 ⟨s, hsp, hcl0', rfl, Nat.le_refl _, hm0'⟩

end TransTopS5Proof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end

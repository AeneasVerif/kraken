/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Src.Substitute
import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpRewriteBins0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# WP Proof for `full_subst_rewrite_bins` (`Proof.Substitute.WpRewriteBins`)

Proves `full_subst_rewrite_bins_wp` parametrically over `Γ : Env` against
`Spec.fullSubstRewriteBinsSpec`.
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

private theorem rb_bv64_one : (1#64 : BitVec 64).toNat = 1 := rfl
private theorem rb_bv64_two : (2#64 : BitVec 64).toNat = 2 := rfl

private abbrev rbEmitSt4 (st st3 : FullState) (l q : BitVec 64)
    (h1 : (l <<< 1#64).toNat < st.core.wvec.length)
    (h2 : ((l <<< 1#64) + 1#64).toNat < st.core.wvec.length) : FullState :=
  { st3 with core :=
    { st3.core with
      wvec := st3.core.wvec.set ((l <<< 1#64) + 1#64).toNat
        (BitVec.setWidth 32 (q - BitVec.setWidth 64 (st.core.wvec[(l <<< 1#64).toNat]'h1)))
      wusable := st3.core.wusable +
        (BitVec.setWidth 64 (st.core.wvec[(l <<< 1#64).toNat]'h1) +
          BitVec.setWidth 64 (st.core.wvec[((l <<< 1#64) + 1#64).toNat]'h2) - q) } }

public section

/-- `full_subst_rewrite_bins` satisfies canonical `Spec.fullSubstRewriteBinsSpec`
parametrically in `Γ`. -/
theorem full_subst_rewrite_bins_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec) :
    ∀ args m Q X, Spec.fullSubstRewriteBinsSpec args m Q X →
      Func.wp Γ full_subst_rewrite_bins_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  unfold Func.wp full_subst_rewrite_bins_body
  c0_hsplit
  · c0_hsteps; exact hQ true s0 m hsp0 hl0 rfl rfl hrepr0 (fun h => by cases h) hm
  · c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (l, ()) ml => ∃ st : FullState, RbOuterCore c F0 F_cur s0 l st ∧ (FullMem c st ⋆ R) ml)
      (fun (l, ()) _ => 2 * s0.core.cur_vars - l.toNat) ?_ ?_
    · intro J hJ; c0_hsteps
      exact hJ (0#64, ()) m ⟨s0, ⟨hsp0, rfl, hl0, rfl, hrepr0, Nat.zero_le _⟩, hm⟩
    · rintro J ⟨l, ⟨⟩⟩ ml ⟨st, ho, hml⟩ hJ
      have hcl := ho.sp.1.core_ok; have hsl := ho.sp.1.scratch_ok; have hcv := ho.cv_eq
      have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
      have hrpl := hcl.repr_len; have hlml := hcl.lit_mark_len; have hwle := hcl.wlen_le
      have hwat := rb_outer_watches ho.sp
      c0_hsplit
      · have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hl1 : (l + 1#64).toNat = l.toNat + 1 := bv64_add1_toNat (by omega)
        have hwv := rb_wvec_shl_lt ho.sp.1 hcv_le (hcv ▸ hl_lt)
        have h2l_eq := hwv.1; have h2l1_eq := hwv.2.1
        have _h2l_lt := hwv.2.2.1; have _h2l1_lt := hwv.2.2.2
        let off := fullWatchOff st l.toNat; let sz := fullWatchSize st l.toNat
        obtain ⟨hoff_eq, hsz_eq, hbound, hend_lt, hslice_orig⟩ := rb_wvec_off_sz ho hl_lt hwat
        have hwv0_eq : ∀ h, (st.core.wvec[2 * l.toNat % 2 ^ 64]'h).toNat = off := fun h => by
          have heq : 2 * l.toNat % 2 ^ 64 = (l <<< 1#64).toNat := by rw [h2l_eq]; omega
          exact (congrArg BitVec.toNat (Option.some.inj (by
            rw [← List.getElem?_eq_getElem h, ← List.getElem?_eq_getElem _h2l_lt, heq]))).trans
            hoff_eq
        have hwv1_eq : ∀ h, (st.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'h).toNat = sz := fun h => by
          have heq : (2 * l.toNat + 1) % 2 ^ 64 = ((l <<< 1#64) + 1#64).toNat := by
            rw [h2l1_eq]; omega
          exact (congrArg BitVec.toNat (Option.some.inj (by
            rw [← List.getElem?_eq_getElem h, ← List.getElem?_eq_getElem _h2l1_lt, heq]))).trans
            hsz_eq
        c0_hsplit
        · c0_hsteps
          exact hJ (l + 1#64, ()) ml (by dsimp only; omega)
            ⟨st, ⟨ho.sp, hcv, ho.hl0, ho.fuel_eq, ho.repr, by omega⟩, hml⟩
        · have _hl_rp : l.toNat < st.core.repr.length := by rw [hrpl]; omega
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (pn, ovf, p, q, ()) m1 => ∃ st1 : FullState,
              RbInner1Core c F_cur st l.toNat off sz pn p q st1 ∧ (FullMem c st1 ⋆ R) m1)
            (fun (_, _, p, _, ()) _ => off + sz - p.toNat) ?_ ?_
          · intro J1 hJ1; c0_hsteps
            exact hJ1 _ _ ⟨st, rb_inner1_init ho hl_lt hoff_eq hbound hslice_orig, hml⟩
          · rintro J1 ⟨pn, ovf, p, q, ⟨⟩⟩ m1 ⟨st1, hin, hm1⟩ hJ1
            have hcl1 := hin.len.core_ok; have hsl1 := hin.len.scratch_ok
            have hwsl1 := hcl1.wstk_len_arr; have hlml1 := hcl1.lit_mark_len
            have hrpl1 := hcl1.repr_len; have hws1l1 := hsl1.work_stk1_len
            have hws2l1 := hsl1.work_stk2_len
            have hcv1 := rbAgrees_cur_vars hin.ag; have hrp1 := rbAgrees_repr hin.ag
            c0_hsplit
            · have hp_lt : p.toNat < off + sz := by
                rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc; omega
              have hp1 : (p + 1#64).toNat = p.toNat + 1 := bv64_add1_toNat (by omega)
              have _hp_wstk : p.toNat < st1.core.wstk.length := by rw [hwsl1]; omega
              let w0 := st1.core.wstk[p.toNat]'_hp_wstk
              have hw0_eq : st.core.wstk[p.toNat]? = some w0 := by
                rw [← hin.tail_eq p.toNat (Nat.le_refl _), List.getElem?_eq_getElem _hp_wstk]
              c0_hsplit
              · have hfl0 : (w0 &&& 0x80000000#32) = 0#32 := by assumption
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64, i64])
                  (fun (p', q', ()) m2 => ∃ st2 : FullState,
                    p.toNat < p'.toNat ∧
                    RbInner1Core c F_cur st l.toNat off sz pn p' q' st2 ∧
                    (FullMem c st2 ⋆ R) m2)
                  (fun _ ⟨p', q', ⟨⟩⟩ m2 ⟨st2, hpp', hin2, hm2⟩ => by
                    c0_hsteps; exact hJ1 (pn, ovf, p', q', ()) m2 (by dsimp only; omega)
                      ⟨st2, hin2, hm2⟩)
                  (fun Jnb hNb => ?_)
                c0_hsplit
                · simp only [hwv0_eq, hwv1_eq] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                  have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
                    bv64_add1_toNat (by have := hin.qp; omega)
                  have hq2 : (q + 2#64).toNat = q.toNat + 2 := by
                    rw [BitVec.toNat_add, rb_bv64_two,
                      Nat.mod_eq_of_lt (by have := hin.qp; omega)]
                  have hp11 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                    rw [BitVec.toNat_add, hp1, rb_bv64_one, Nat.mod_eq_of_lt (by omega)]
                  obtain ⟨hcr_lt, _hcr_len1, hpp', h_nxt⟩ := rb_nonbin_step hin hp_lt hend_lt
                    hp1 hq1 hq2 hp11 hw0_eq hfl0
                  have _hq_lt : q.toNat < st1.core.wstk.length := by
                    have := hin.qp; rw [hwsl1]; omega
                  have _hq1_lt : (q + 1#64).toNat < (st1.core.wstk.set q.toNat w0).length := by
                    rw [List.length_set, hq1, hwsl1]; have := hin.qp; omega
                  c0_hsteps
                  exact hNb _ _ ⟨_, hpp', h_nxt _ rfl, by assumption⟩
                · exfalso
                  obtain ⟨_, _, hrem2, _⟩ := wsStepNonbin hin.rem (by omega)
                    (by rw [hw0_eq, Option.getD_some]; exact hfl0)
                  simp only [hwv0_eq, hwv1_eq] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                  omega
              · have hfl_ne : (w0 &&& 0x80000000#32) ≠ 0#32 := by assumption
                let ot := w0 &&& 0x7FFFFFFF#32
                obtain ⟨hfl_bin, hne_ff, hot_lt, hot_rp, hent_bin, hrem_p1, hrot_fn⟩ :=
                  rb_bin_prep ho hin hl_lt _hl_rp hp_lt hp1 hw0_eq hfl_ne
                let rot := st1.core.repr[ot.toNat]'hot_rp
                obtain ⟨hrot_lt, _hrot_lm, _hot_lm, hent_sub⟩ := hrot_fn hot_rp
                have _hot_rp_bv : (BitVec.setWidth 64 ot).toNat < st1.core.repr.length := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hot_rp
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32])
                  (fun (rot_v, ()) m_r => rot_v = rot ∧ (FullMem c st1 ⋆ R) m_r)
                  (fun _ ⟨rot_v, ⟨⟩⟩ m_r ⟨hrot_v, hm_r⟩ => ?_)
                  (fun Jrot hJrot => ?_)
                · subst hrot_v; c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, .bool, i64])
                    (fun (pn', ovf', q', ()) m2 => ∃ st2 : FullState,
                      RbInner1Core c F_cur st l.toNat off sz pn' (p + 1#64) q' st2 ∧
                      (FullMem c st2 ⋆ R) m2)
                    (fun _ ⟨pn', ovf', q', ⟨⟩⟩ m2 ⟨st2, hin2, hm2⟩ => by
                      c0_hsteps; exact hJ1 (pn', ovf', p + 1#64, q', ()) m2 (by dsimp only; omega)
                        ⟨st2, hin2, hm2⟩)
                    (fun Jbin hBin => ?_)
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := []) (fun () m_e => (FullMem c st1 ⋆ R) m_e)
                    (fun _ ⟨⟩ m_e hm_e => ?_) (fun Jelse hElse => ?_)
                  · c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64, .bool])
                      (fun (pn', ovf', ()) m2 => ∃ st2 : FullState,
                        RbInner1Core c F_cur st l.toNat off sz pn' (p + 1#64) q st2 ∧
                        (FullMem c st2 ⋆ R) m2)
                      (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 ⟨st2, hin2, hm2⟩ => by
                        c0_hsteps; exact hBin (pn', ovf', q, ()) m2 ⟨st2, hin2, hm2⟩)
                      (fun Jlc hLc => ?_)
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun () m_nb => ∃ nb' : BitVec 64,
                          (FullMem c { st1 with core := { st1.core with num_binary := nb' } } ⋆ R)
                            m_nb)
                        (fun _ ⟨⟩ m_nb ⟨nb', hnb⟩ => ?_) (fun Jnb hNb => ?_)
                      · have hin2 := rb_bin_nb_step hin hp1 hp_lt hrem_p1 (nb' := nb')
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [i64, .bool])
                          (fun (pn', ovf', ()) m2 => ∃ st2 : FullState,
                            RbInner1Core c F_cur st l.toNat off sz pn' (p + 1#64) q st2 ∧
                            (FullMem c st2 ⋆ R) m2)
                          (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 ⟨st2, hin2', hm2⟩ => by
                            c0_hsteps; exact hLc (pn', ovf', ()) m2 ⟨st2, hin2', hm2⟩)
                          (fun Jsc hSc => ?_)
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_group (ts := [i64, .bool])
                            (fun (pn', ovf', ()) m2 => ∃ st2 : FullState,
                              RbInner1Core c F_cur st l.toNat off sz pn' (p + 1#64) q st2 ∧
                              (FullMem c st2 ⋆ R) m2)
                            (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 ⟨st2, hin2', hm2⟩ => by
                              c0_hsteps; exact hSc (pn', ovf', ()) m2 ⟨st2, hin2', hm2⟩)
                            (fun Jrot2 hRot2 => ?_)
                          c0_hsplit
                          · have hrot_lm :
                                (BitVec.setWidth 64 rot).toNat < st1.core.lit_mark.length := by
                              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                              exact _hrot_lm
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [i64, .bool])
                              (fun (pn', ovf', ()) m2 => ∃ st2 : FullState,
                                RbInner1Core c F_cur st l.toNat off sz pn' (p + 1#64) q st2 ∧
                                (FullMem c st2 ⋆ R) m2)
                              (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 ⟨st2, hin2', hm2⟩ => by
                                c0_hsteps; exact hRot2 (pn', ovf', ()) m2 ⟨st2, hin2', hm2⟩)
                              (fun Jlm hLm => ?_)
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join_group (ts := [i64, .bool])
                                (fun (pn', ovf', ()) m2 => ∃ st2 : FullState,
                                  RbInner1Core c F_cur st l.toNat off sz pn' (p + 1#64) q st2 ∧
                                  (FullMem c st2 ⋆ R) m2)
                                (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 ⟨st2, hin2', hm2⟩ => by
                                  c0_hsteps; exact hLm (pn', ovf', ()) m2 ⟨st2, hin2', hm2⟩)
                                (fun Jpn hPn => ?_)
                              c0_hsplit
                              · have hpn_lt : pn.toNat < 2 * st.core.cur_vars := by
                                  rw [Nat.mod_eq_of_lt (by omega),
                                    Nat.mod_eq_of_lt (by omega)] at hc; omega
                                have hpn1 : (pn + 1#64).toNat = pn.toNat + 1 :=
                                  bv64_add1_toNat (by omega)
                                have _hpn_ws1 : pn.toNat < st1.scratch.work_stk1.length := by
                                  rw [hws1l1]; omega
                                have _hpn_ws2 : pn.toNat < st1.scratch.work_stk2.length := by
                                  rw [hws2l1]; omega
                                have hrl_lt : (st.core.repr[l.toNat]'_hl_rp).toNat <
                                    2 * st.core.cur_vars := by
                                  have := FullReprEquiv.lt ho.repr (hcv ▸ hl_lt)
                                  rwa [List.getElem?_eq_getElem _hl_rp,
                                    Option.getD_some] at this
                                c0_hsteps
                                refine hPn (pn + 1#64, ovf, ()) _
                                  ⟨_, rb_bin_push_step hin hp1 hpn1 hp_lt hpn_lt (hcv ▸ hl_lt)
                                    _hl_rp hrot_lt hent_sub hrem_p1 hrot_lm hrl_lt, by assumption⟩
                              · c0_hsteps; exact hPn (pn, true, ()) m_nb ⟨_, hin2, hnb⟩
                            · c0_hsteps; exact hLm (pn, ovf, ()) m_nb ⟨_, hin2, hnb⟩
                          · c0_hsteps; exact hRot2 (pn, true, ()) m_nb ⟨_, hin2, hnb⟩
                        · c0_hsteps; exact hSc (pn, ovf, ()) m_nb ⟨_, hin2, hnb⟩
                      · c0_hsplit
                        · c0_hsteps; exact hNb () _ ⟨st1.core.num_binary - 1#64, by assumption⟩
                        · c0_hsteps; exact hNb () m_e ⟨st1.core.num_binary, hm_e⟩
                    · c0_hsteps
                      exact hLc (pn, ovf, ()) m_e ⟨_, rb_bin_nb_step hin hp1 hp_lt hrem_p1, hm_e⟩
                  · c0_hsplit
                    · c0_hsplit
                      · have hot_lm : (BitVec.setWidth 64 ot).toNat < st1.core.lit_mark.length := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact _hot_lm
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [i64])
                          (fun (q', ()) m2 => ∃ st2 : FullState,
                            RbInner1Core c F_cur st l.toNat off sz pn (p + 1#64) q' st2 ∧
                            (FullMem c st2 ⋆ R) m2)
                          (fun _ ⟨q', ⟨⟩⟩ m2 ⟨st2, hin2, hm2⟩ => by
                            c0_hsteps; exact hBin (pn, ovf, q', ()) m2 ⟨st2, hin2, hm2⟩)
                          (fun Jth hTh => ?_)
                        c0_hsplit
                        · have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
                            bv64_add1_toNat (by have := hin.qp; omega)
                          have _hq_wstk : q.toNat < st1.core.wstk.length := by
                            have := hin.qp; rw [hwsl1]; omega
                          c0_hsteps
                          exact hTh (q + 1#64, ()) _ ⟨_, rb_bin_keep_step hin rfl hp1 hq1 hp_lt
                            hend_lt hfl_bin hne_ff hot_lt hent_bin hrem_p1 hot_lm, by assumption⟩
                        · c0_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun () m_nb => ∃ nb' : BitVec 64,
                              (FullMem c { st1 with core :=
                                { st1.core with num_binary := nb' } } ⋆ R) m_nb)
                            (fun _ ⟨⟩ m_nb ⟨nb', hnb⟩ =>
                              hTh (q, ()) m_nb ⟨_, rb_bin_nb_step hin hp1 hp_lt hrem_p1, hnb⟩)
                            (fun Jt3 hT3 => by
                              c0_hsplit
                              · c0_hsplit
                                · c0_hsteps
                                  exact hT3 () _ ⟨st1.core.num_binary - 1#64, by assumption⟩
                                · c0_hsteps; exact hT3 () m_r ⟨st1.core.num_binary, hm_r⟩
                              · c0_hsteps; exact hT3 () m_r ⟨st1.core.num_binary, hm_r⟩)
                      · c0_hsteps; exact hElse () m_r hm_r
                    · c0_hsteps; exact hElse () m_r hm_r
                · c0_hsplit
                  · c0_hsteps; exact hJrot (rot, ()) m1 ⟨rfl, hm1⟩
                  · exfalso
                    dsimp only [w0] at hot_lt
                    change ¬(st1.core.wstk[p.toNat] &&& 0x7FFFFFFF#32).toNat <
                      2 * (s0.core.cur_vars % 2 ^ 64) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
                    omega
            · simp only [hwv0_eq, hwv1_eq] at hc
              rw [Nat.mod_eq_of_lt (by omega)] at hc
              have := hin.p_hi
              have hp_end : p.toNat = off + sz := by omega
              have hq_hi : q.toNat ≤ off + sz := by have := hin.qp; omega
              have _hws1_bd : pn.toNat ≤ st1.scratch.work_stk1.length := by
                rw [hws1l1]; have := hin.pn_le; omega
              have _hws2_bd : pn.toNat ≤ st1.scratch.work_stk2.length := by
                rw [hws2l1]; have := hin.pn_le; omega
              c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (ci, ()) m2 => ∃ st2 : FullState,
                  RbClear1Core c st st1 off q.toNat pn.toNat ci st2 ∧ (FullMem c st2 ⋆ R) m2)
                (fun (ci, ()) _ => q.toNat - ci.toNat) ?_ ?_
              · intro J2 hJ2; c0_hsteps
                exact hJ2 _ m1 ⟨st1, rb_inner1_to_clear1 ho hin hl_lt rfl rfl hoff_eq, hm1⟩
              · rintro J2 ⟨ci, ⟨⟩⟩ m2 ⟨st2, hc2, hm2⟩ hJ2
                have hcl2 := hc2.len.core_ok; have hwsl2 := hcl2.wstk_len_arr
                c0_hsplit
                · have hci_lt : ci.toNat < q.toNat := hc
                  have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := bv64_add1_toNat (by omega)
                  have hci_w : ci.toNat < st2.core.wstk.length := by rw [hwsl2]; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := []) (fun () m2' => ∃ st2' : FullState,
                      RbClear1Core c st st1 off q.toNat pn.toNat (ci + 1#64) st2' ∧
                      (FullMem c st2' ⋆ R) m2')
                    (fun _ ⟨⟩ m2' ⟨st2', hc2', hm2'⟩ => by
                      c0_hsteps; exact hJ2 (ci + 1#64, ()) m2' (by dsimp only; omega)
                        ⟨st2', hc2', hm2'⟩)
                    (fun Jc hC => ?_)
                  c0_hsplit
                  · have hf_ne : (st2.core.wstk[ci.toNat]'(by
                        rw [hc2.wstk_eq, hwsl1]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
                    obtain ⟨_hbl, hc2'⟩ := rb_clear1_bin_step hin.kept hc2 rfl hci_lt hci1
                      (by rw [hwsl1]; omega) hf_ne
                    c0_hsteps; exact hC () _ ⟨_, hc2', by assumption⟩
                  · have hf_eq : (st2.core.wstk[ci.toNat]'hci_w &&& 0x80000000#32) = 0#32 := by
                      assumption
                    c0_hsteps
                    exact hC () m2 ⟨st2, rb_clear1_nonbin_step hc2 hci_lt hci1 hci_w hf_eq, hm2⟩
                · c0_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (ci2, ()) m2b => ∃ st2b : FullState,
                      RbClear2Core c st st1 pn.toNat ci2 st2b ∧ (FullMem c st2b ⋆ R) m2b)
                    (fun (ci2, ()) _ => pn.toNat - ci2.toNat) ?_ ?_
                  · intro J2b hJ2b; c0_hsteps
                    exact hJ2b (0#64, ()) m2 ⟨st2, rb_clear1_to_clear2 hc2 hc, hm2⟩
                  · rintro J2b ⟨ci2, ⟨⟩⟩ m2b ⟨st2b, hc2b, hm2b⟩ hJ2b
                    c0_hsplit
                    · have hci2_lt : ci2.toNat < pn.toNat := hc
                      have hci2_1 : (ci2 + 1#64).toNat = ci2.toNat + 1 := bv64_add1_toNat (by omega)
                      obtain ⟨_hci2_ws2, _hpb_lm, hc2b'⟩ :=
                        rb_clear2_step hin.pa hc2b hci2_lt hci2_1 _hws2_bd
                      c0_hsteps; exact hJ2b (ci2 + 1#64, ()) _ (by dsimp only; omega)
                        ⟨_, hc2b', by assumption⟩
                    · obtain ⟨hlm_zero, ht_init⟩ := rb_clear2_to_trim hc2b rfl hq_hi hc
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (ci3, ()) m3 => ∃ st3 : FullState,
                          RbTrimCore c st st1 st2b q.toNat off sz ci3 st3 ∧ (FullMem c st3 ⋆ R) m3)
                        (fun (ci3, ()) _ => off + sz - ci3.toNat) ?_ ?_
                      · intro J3 hJ3; c0_hsteps; exact hJ3 (q, ()) m2b ⟨st2b, ht_init, hm2b⟩
                      · rintro J3 ⟨ci3, ⟨⟩⟩ m3 ⟨st3, ht, hm3⟩ hJ3
                        have hcl3 := ht.len.core_ok; have hwsl3 := hcl3.wstk_len_arr
                        c0_hsplit
                        · have hci3_lt : ci3.toNat < off + sz := by
                            rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc; omega
                          have hci3_1 : (ci3 + 1#64).toNat = ci3.toNat + 1 :=
                            bv64_add1_toNat (by omega)
                          have _hci3_w : ci3.toNat < st3.core.wstk.length := by rw [hwsl3]; omega
                          c0_hsteps; exact hJ3 (ci3 + 1#64, ()) _ (by dsimp only; omega)
                            ⟨_, rb_trim_step ht hci3_lt hci3_1 (by rw [hwsl3]; omega),
                              by assumption⟩
                        · have hci3_eq : ci3.toNat = off + sz := by
                            simp only [hwv0_eq, hwv1_eq] at hc
                            rw [Nat.mod_eq_of_lt (by omega)] at hc
                            have := ht.ci3_hi; omega
                          have _h2l_lt3 : (l <<< 1#64).toNat < st3.core.wvec.length := by
                            rw [rbAgrees_wvec ht.ag]; exact _h2l_lt
                          have _h2l1_lt3 : ((l <<< 1#64) + 1#64).toNat < st3.core.wvec.length := by
                            rw [rbAgrees_wvec ht.ag]; exact _h2l1_lt
                          let st4 := rbEmitSt4 st st3 l q _h2l_lt _h2l1_lt
                          obtain ⟨_hwv_idx, hsp4, hsp_oom, hcv4, hl04, hfl4, hrepr4, hpa4,
                            he_init⟩ := rb_finish_slice ho hin ht hlm_zero hl_lt rfl rfl
                              hoff_eq hsz_eq hbound hq_hi hci3_eq
                          c0_hsplit
                          · c0_hsteps
                            exact hQ true _ _ hsp_oom hl04 hcv4 hfl4 hrepr4 (fun h => by cases h)
                              (by assumption)
                          · c0_hsteps_nogrp
                            refine wp_loop_inv
                              (fun (ci4, ()) m5 => ∃ st5 : FullState,
                                RbEmitCore c F0 F_cur s0 st4 pn.toNat ci4 st5 ∧
                                (FullMem c st5 ⋆ R) m5)
                              (fun (ci4, ()) _ => pn.toNat - ci4.toNat) ?_ ?_
                            · intro J4 hJ4; c0_hsteps
                              exact hJ4 (0#64, ()) _ ⟨_, he_init, by assumption⟩
                            · rintro J4 ⟨ci4, ⟨⟩⟩ m5 ⟨st5, he, hm5⟩ hJ4
                              have hsl5 := he.sp.1.scratch_ok
                              have hws1l5 := hsl5.work_stk1_len; have hws2l5 := hsl5.work_stk2_len
                              c0_hsplit
                              · have hci4_lt : ci4.toNat < pn.toNat := hc
                                have hci4_1 : (ci4 + 1#64).toNat = ci4.toNat + 1 :=
                                  bv64_add1_toNat (by omega)
                                have _hci4_w1 : ci4.toNat < st5.scratch.work_stk1.length := by
                                  rw [hws1l5]; have := hin.pn_le; omega
                                have _hci4_w2 : ci4.toNat < st5.scratch.work_stk2.length := by
                                  rw [hws2l5]; have := hin.pn_le; omega
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := []) (fun () m6 => ∃ st6 : FullState,
                                    RbEmitCore c F0 F_cur s0 st4 pn.toNat (ci4 + 1#64) st6 ∧
                                    (FullMem c st6 ⋆ R) m6)
                                  (fun _ ⟨⟩ m6 ⟨st6, he6, hm6⟩ => by
                                    c0_hsteps; exact hJ4 (ci4 + 1#64, ()) m6
                                      (by dsimp only; omega) ⟨st6, he6, hm6⟩)
                                  (fun J4s hJ4s => ?_)
                                c0_hsplit
                                · have heq_ab : st5.scratch.work_stk1[ci4.toNat]'_hci4_w1 =
                                      st5.scratch.work_stk2[ci4.toNat]'_hci4_w2 := by assumption
                                  obtain ⟨hpa_lt5, hab_ent5⟩ := rb_emit_unit_facts he hpa4 hcv
                                    hci4_lt _hci4_w1 _hci4_w2 heq_ab
                                  c0_hsteps; c0_hcall hAddUnit
                                  refine ⟨c, F0, F_cur, st5, R, rfl, he.sp.1, he.sp.2.1,
                                    fun _ => hab_ent5, hm5, ?_⟩
                                  intro ok1 vals1 fl1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1
                                    unfl1 inc1 ph1 ta1 ba1 pt1 pb1 hp1 ps1 hl1 qsi1 qss1 m6 _ hlen6
                                    hw6 hcl6 hfail6 _ hm6
                                  let st6 : FullState :=
                                    { core := { st5.core with
                                        vals := vals1, flags := fl1, lvl := lvl1, rsns := rsns1,
                                        trl := trl1, trail_pos := tp1, trail_end := te1,
                                        propagated := prop1, cur_level := cl1, unassigned := unass1,
                                        unflushed := unfl1, inconsistent := inc1 }
                                      scratch := { st5.scratch with
                                        phases := ph1, target_assigned := ta1, best_assigned := ba1,
                                        phases_target := pt1, phases_best := pb1, heap := hp1,
                                        pos := ps1, heap_len := hl1, q_search_idx := qsi1,
                                        q_search_stamp := qss1 } }
                                  have hsp6 := fullSparseInvW_afterAddUnit he.sp hlen6 hw6
                                  c0_hsplit
                                  · c0_hsteps
                                    exact hJ4s () m6 ⟨st6, ⟨hsp6, he.cv_eq, hcl6, he.fuel_eq,
                                      he.repr, he.ws1_eq, he.ws2_eq, by omega⟩, hm6⟩
                                  · c0_hsteps
                                    exact hQ false st6 m6 hsp6 hcl6 he.cv_eq he.fuel_eq he.repr
                                      (fun _ => (hfail6 hpa_lt5 (by
                                        cases ok1 <;> first | rfl | exact absurd hc (by decide))).1)
                                      hm6
                                · c0_hsteps; c0_hcall hAddBin
                                  refine ⟨c, F0, F_cur, st5, R, rfl, he.sp.1, he.sp.2.1, he.hl0,
                                    fun _ _ => rb_emit_bin_facts he hpa4 hci4_lt _hci4_w1 _hci4_w2,
                                    hm5, ?_⟩
                                  intro r vals1 fl1 lvl1 rsns1 trl1 tp1 te1 unass1 unfl1 wv1 ws1
                                    wl1 wu1 nb1 oom1 inc1 ph1 wsort1 m6 _ hlen6 hw6 _ hr20 _ hm6
                                  let st6 : FullState :=
                                    { core := { st5.core with
                                        vals := vals1, flags := fl1, lvl := lvl1, rsns := rsns1,
                                        trl := trl1, trail_pos := tp1, trail_end := te1,
                                        unassigned := unass1, num_binary := nb1,
                                        unflushed := unfl1, wvec := wv1, wstk := ws1, wlen := wl1,
                                        wusable := wu1, oom := oom1, inconsistent := inc1 }
                                      scratch := { st5.scratch with
                                        phases := ph1, wsort := wsort1 } }
                                  have hsp6 := fullSparseInvW_afterAddBin he.sp hlen6 hw6
                                  c0_hsplit
                                  · c0_hsteps
                                    exact hQ false st6 m6 hsp6 he.hl0 he.cv_eq he.fuel_eq he.repr
                                      (fun _ => (hr20 hc).1) hm6
                                  · c0_hsteps_nogrp
                                    refine wp_join_group (ts := [])
                                      (fun () m6' => (FullMem c st6 ⋆ R) m6')
                                      (fun _ ⟨⟩ m6' hm6' => by
                                        c0_hsteps
                                        exact hQ true
                                          { st6 with core := { st6.core with oom := 1#64 } }
                                          _ (fullSparseInvW_with_oom hsp6 1#64) he.hl0 he.cv_eq
                                          he.fuel_eq he.repr (fun h => by cases h) (by assumption))
                                      (fun Joom hOom => ?_)
                                    c0_hsplit
                                    · c0_hsteps; exact hOom () m6 hm6
                                    · c0_hsplit
                                      · c0_hsteps; exact hOom () m6 hm6
                                      · c0_hsteps
                                        exact hJ4s () m6 ⟨st6, ⟨hsp6, he.cv_eq, he.hl0, he.fuel_eq,
                                          he.repr, he.ws1_eq, he.ws2_eq, by omega⟩, hm6⟩
                              · c0_hsteps
                                exact hJ (l + 1#64, ()) m5 (by dsimp only; omega)
                                  ⟨st5, ⟨he.sp, he.cv_eq, he.hl0, he.fuel_eq, he.repr, by omega⟩,
                                    hm5⟩
      · c0_hsteps
        exact hQ true st ml ho.sp ho.hl0 hcv ho.fuel_eq ho.repr (fun h => by cases h) hml

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute

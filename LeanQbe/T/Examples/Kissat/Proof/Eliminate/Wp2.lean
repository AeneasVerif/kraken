/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp2b
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp2c
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BVE `Func.wp` Proofs — Part 2 (`Wp2`: `full_bve_var_m7_wp`)

Canonical `Func.wp` proof for `full_bve_var_m7` against `Spec.fullBveVarM7Spec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Eliminate
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Eliminate.EliminateTactics

open scoped FullArenaTactics
open scoped EliminateTactics

public theorem full_bve_var_m7_wp (Γ : Env)
    (hCollect : Γ.Has "full_bve_collect_m7" Spec.fullBveCollectM7Spec)
    (hExtNeed : Γ.Has "full_bve_ext_need" Spec.fullBveExtNeedSpec)
    (hWeakenUnit : Γ.Has "full_bve_weaken_unit_fid" Spec.fullBveWeakenTmkSpec)
    (hInactive : Γ.Has "full_set_inactive" Internal.Spec.fullSetInactiveSpec)
    (hGatesFid : Γ.Has "full_bve_gates_fid" Definition.Spec.m8BveGatesSpec)
    (hGatesM7 : Γ.Has "full_bve_gates_m7" Definition.Spec.fullBveGatesM7Spec)
    (hResolve : Γ.Has "full_bve_resolve_pair" Spec.fullBveResolvePairSpec)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (hWeaken : Γ.Has "full_bve_weaken" Spec.fullBveWeakenTmkSpec)
    (hCommit : Γ.Has "full_bve_commit_res" Spec.fullBveCommitResTmkSpec)
    (hFlush : Γ.Has "full_dense_flush_units_m7" Dense.Spec.fullDenseFlushUnitsSpec) :
    ∀ a m Q X, Spec.fullBveVarM7Spec a m Q X → Func.wp Γ full_bve_var_m7_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hdi0, htmk0, hv0, hm0, hQ⟩
  obtain ⟨F_cur, hdw0⟩ := hdi0.exists_witness
  unfold Func.wp full_bve_var_m7_body
  elim_steps_nogrp
  · exact bve_ret_q hQ ⟨hdw0.toDense, htmk0, Nat.le_refl _, Nat.le_refl _, Or.inl rfl,
      fun h20 => by simp at h20⟩ hm0
  · have hsc := bve_scratch_cap_lt32 (c := c)
    have h2048 : 2048 ≤ c.scratch_cap := by simp at hc; omega
    let m8 : Bool := decide (16384 ≤ c.scratch_cap)
    have hm8 : m8 = decide (16384 ≤ c.scratch_cap) := rfl
    have hm8_eq : BitVec.ule 16384 (BitVec.ofNat 64 c.scratch_cap) = m8 := by
      simp [m8, BitVec.ule, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)]
    have hbm := bveMode_bounds h2048 hm8
    refine wp_mux32 fun _ occ_lim h_occ => ?_
    refine wp_mux32 fun _ neg_off h_neg => ?_
    refine wp_mux32 fun _ pos_mask h_pm => ?_
    refine wp_mux32 fun _ neg_mask h_nm => ?_
    refine wp_mux32 fun _ gf_idx h_gf => ?_
    refine wp_mux32 fun _ rg_idx h_rg => ?_
    dsimp only at h_occ h_neg h_pm h_nm h_gf h_rg
    simp only [hm8_eq] at h_occ h_neg h_pm h_nm h_gf h_rg
    refine wp_join_fwd (fun xs m' => xs.1.toNat = bveROff m8 ∧ m = m') ?_ ?_
    · intro J hJ; elim_steps_nogrp
      · have h16 : 16384 ≤ c.scratch_cap := by simp at hc; omega
        apply hJ; simp [m8, h16, bveROff]
      · have h16 : ¬ 16384 ≤ c.scratch_cap := by simp at hc; omega
        apply hJ; simp [m8, h16, bveROff]
    rintro _ ⟨r_off, ⟨⟩⟩ m' hm_eq; cases hm_eq.2
    have h_roff := hm_eq.1
    elim_steps_nogrp
    have hcv31 : s0.core.cur_vars < 2 ^ 31 := bve_cur_vars_lt31 hdw0.1
    have hpl : (v <<< 1#32).toNat < 2 * s0.core.cur_vars := by rw [bve_bv32_shl1 (by omega)]; omega
    have hnl : ((v <<< 1#32) ||| 1#32).toNat < 2 * s0.core.cur_vars := by
      rw [bve_bv32_shl1_or1 (by omega)]; omega
    have hneg_off_eq : neg_off.toNat = bveOccLim m8 := by rw [h_neg]; cases m8 <;> simp [bveOccLim]
    have hocc_eq : occ_lim.toNat = bveOccLim m8 := by rw [h_occ]; cases m8 <;> simp [bveOccLim]
    dsimp only
    have h2lim : bveOccLim m8 + bveOccLim m8 ≤ c.scratch_cap := by
      have := hbm.2.1; have := hbm.2.2.1; have := hbm.2.2.2.1
      have := hbm.2.2.2.2.1; have := hbm.2.2.2.2.2.1; have := hbm.2.2.2.2.2.2.1; omega
    refine wp_call_of_spec _ _ (hCollect _ _ _ _ ?_)
    refine ⟨c, F0, F_cur, s0, 0, R, rfl, hdw0, (by dsimp only [Arg.val]; exact hpl), by simp,
      (by dsimp only [Arg.val]; rw [hocc_eq]; omega), hm0, ?_⟩
    intro np scr1 m1 s1_spec hlen1 hhold1 hpost1 hm1; dsimp only
    let s1 : FullState := { core := s0.core, scratch := { s0.scratch with scratch_buf := scr1 } }
    have hdw1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_scratch_buf hdw0 hlen1
    have htmk1 : TmkZero s1 := htmk0; elim_steps_nogrp
    refine wp_call_of_spec _ _ (hCollect _ _ _ _ ?_)
    refine ⟨c, F0, F_cur, s1, bveOccLim m8, R, rfl, hdw1, (by dsimp only [Arg.val]; exact hnl),
      (by dsimp only [Arg.val]
          have hset : neg_off.setWidth 64 = BitVec.ofNat 64 (bveOccLim m8) := by
            apply BitVec.eq_of_toNat_eq
            have hlim : bveOccLim m8 < 2 ^ 32 := by cases m8 <;> simp [bveOccLim]
            simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hneg_off_eq,
              Nat.mod_eq_of_lt (by omega : bveOccLim m8 < 2 ^ 64)]
          simp [BitVec.ofNat_mul, hset]; cases m8 <;> simp [bveOccLim] <;> rfl),
      (by dsimp only [Arg.val]; rw [hocc_eq]; omega), hm1, ?_⟩
    intro nn scr2 m2 s2_spec hlen2 hhold2 hpost2 hm2; dsimp only
    let s2 : FullState := { core := s1.core, scratch := { s1.scratch with scratch_buf := scr2 } }
    have hdw2 : FullDenseInvW c F0 F_cur s2 := fullDenseInvW_with_scratch_buf hdw1 hlen2
    have htmk2 : TmkZero s2 := htmk1; elim_steps_nogrp
    · exact bve_ret_q hQ ⟨hdw2.toDense, htmk2, Nat.le_refl _, Nat.le_refl _, Or.inl rfl,
        fun h20 => by simp at h20⟩ hm2
    · exact bve_ret_q hQ ⟨hdw2.toDense, htmk2, Nat.le_refl _, Nat.le_refl _, Or.inl rfl,
        fun h20 => by simp at h20⟩ hm2
    simp only [Arg.val_var, Nat.zero_add] at hpost1 hpost2
    have hsh1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by simpa using bve_bv32_shl1 (by omega)
    have hsh1o : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
      simpa using bve_bv32_shl1_or1 (by omega)
    have hnp_le : np.toNat ≤ bveOccLim m8 := by
      rcases hpost1 with h_eq | h1
      · exact absurd h_eq ‹np ≠ 4294967295#32›
      · rw [hocc_eq] at h1; exact h1.1
    have hnn_le : nn.toNat ≤ bveOccLim m8 := by
      rcases hpost2 with h_eq | h2
      · exact absurd h_eq ‹nn ≠ 4294967295#32›
      · rw [hocc_eq] at h2; exact h2.1
    have hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
        (s2.scratch.scratch_buf[i]?.getD 0#32) := by
      rcases hpost1 with h_eq | h1
      · exact absurd h_eq ‹np ≠ 4294967295#32›
      · exact bve_collect2_congr (c := c) hnp_le hbm.2.2.2.2.2.2.1
          (by simpa [Arg.val_var, hocc_eq] using hhold2) (fun i hi => by
            have h1' := h1.2 i hi; rw [hsh1] at h1'
            exact bveEntry_congr_core (s := s1_spec) (s' := s1) h1' rfl rfl rfl)
    have hent_n2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
        (s2.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32) := by
      rcases hpost2 with h_eq | h2
      · exact absurd h_eq ‹nn ≠ 4294967295#32›
      · intro j hj
        exact bveEntry_congr_core (s := s2_spec) (s' := s2)
          (by simpa [hsh1o] using h2.2 j hj) rfl rfl rfl
    have hcv2 : s2.core.cur_vars = s0.core.cur_vars := rfl
    have hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_refl _
    have hm2' : (FullMem c s2 ⋆ R) m2 := hm2
    clear hpost1 hpost2 hhold1 hhold2 hlen1 hlen2 s2_spec s1_spec hdw1 htmk1 hm1 hm2
    generalize s2 = s2g at hdw2 htmk2 hent_p2 hent_n2 hcv2 hfl2 hm2'
    clear s2 s1
    revert s2g hdw2 htmk2 hent_p2 hent_n2 hcv2 hfl2 hm2'
    intro s2 hdw2 htmk2 hent_p2 hent_n2 hcv2 hfl2 hm2
    refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
    · intro J hJ; elim_steps_nogrp
      · exact bve_ret_q hQ ⟨hdw2.toDense, htmk2, by omega, hfl2, Or.inl rfl,
          fun h20 => by simp at h20⟩ hm2
      all_goals exact hJ () m2 rfl
    rintro _ _ m' hm_eq; subst hm_eq
    refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
    · intro J hJ; elim_steps_nogrp
      · refine wp_call_of_spec _ _ (hExtNeed _ _ _ _ ?_)
        refine ⟨c, s2, R, rfl, hdw2.1, (by dsimp only [Arg.val]; omega), ?_, hm2,
          fun r => hJ (r, ()) m2 rfl⟩
        exact bve_extNeed_pre_of_entries hdw2 (off := 0) (fun i hi => by simpa using hent_p2 i hi)
      · exact hJ (0#64, ()) m2 rfl
    rintro _ ⟨ext_p, ⟨⟩⟩ m' hm_eq; subst hm_eq
    refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
    · intro J hJ; elim_steps_nogrp
      · refine wp_call_of_spec _ _ (hExtNeed _ _ _ _ ?_)
        refine ⟨c, s2, R, rfl, hdw2.1, (by dsimp only [Arg.val]; omega), ?_, hm2,
          fun r => hJ (r, ()) m2 rfl⟩
        simpa [hneg_off_eq] using bve_extNeed_pre_of_entries hdw2 (off := bveOccLim m8) hent_n2
      · exact hJ (0#64, ()) m2 rfl
    rintro _ ⟨ext_n, ⟨⟩⟩ m' hm_eq; subst hm_eq
    elim_steps_nogrp
    refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
    · intro J hJ; elim_steps_nogrp
      refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
      · intro Jho hJho; elim_steps_nogrp
        · exact hJho () m2 rfl
        · exact hJho () m2 rfl
        · refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
          · intro Jmx hJmx; elim_steps_nogrp <;> exact hJmx _ m2 rfl
          · rintro _ ⟨mx, ⟨⟩⟩ m' hm_eq; subst hm_eq; elim_steps_nogrp
            exact hJ _ m2 rfl
      · rintro _ _ m' hm_eq; subst hm_eq; elim_steps_nogrp
        refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
        · intro Jbo hJbo; elim_steps_nogrp <;> exact hJbo _ m2 rfl
        · rintro _ ⟨bo, ⟨⟩⟩ m' hm_eq; subst hm_eq; elim_steps_nogrp
          exact hJ _ m2 rfl
    rintro _ ⟨_ext_m, ⟨⟩⟩ m' hm_eq; subst hm_eq
    refine wp_join_fwd (fun _ m' => m2 = m') ?_ ?_
    · intro J hJ; elim_steps_nogrp <;> exact hJ _ m2 rfl
    rintro _ ⟨ext_ok, ⟨⟩⟩ m' hm_eq; subst hm_eq
    elim_steps_nogrp
    refine wp_join_group (fun _ m' =>
        (ext_ok = false ∨ (np ≠ 0#32 ∧ nn ≠ 0#32)) ∧ m2 = m') ?_ ?_
    · rintro _ _ m' ⟨hext_pure, hm_eq⟩; subst hm_eq
      elim_steps_nogrp
      refine wp_join_group (fun (xs : Tup Val [i64, i64, i64, Ty.bool]) m' =>
          ∃ rp r_cnt w_est fit res_sz s,
          xs = (rp, r_cnt, w_est, fit, ()) ∧
          BveVarLoopsInv c F0 F_cur s0 m8 v np nn rp r_cnt w_est fit res_sz s m' R) ?_ ?_
      · rintro _ ⟨rp, r_cnt, w_est, fit, ⟨⟩⟩ m' ⟨rp', r_cnt', w_est', fit', res_sz', s, heq, hinv⟩
        cases heq
        obtain ⟨hdw, htmk, hcv, hfl, hent_p, hent_n, hro, hsc, hrb, hm⟩ := hinv
        elim_steps_nogrp
        refine wp_join_fwd (fun xs mf => ∃ fit2 sf, xs = (fit2, ()) ∧
            FullDenseInvW c F0 F_cur sf ∧ TmkZero sf ∧
            sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            (∀ i < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
              (sf.scratch.scratch_buf[i]?.getD 0#32)) ∧
            (∀ j < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
              (sf.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
            FullResBufOkW F_cur sf rp.toNat (bveROff m8) ∧ (FullMem c sf ⋆ R) mf) ?_ ?_
        · intro J_fit hJ_fit; elim_steps_nogrp
          · refine wp_fit_defrag hDefrag rfl hdw htmk hcv hfl hro hm rfl rfl hent_p hent_n hrb ?_
            intro _ fit2 sf mf hdwf htmkf hcvf hflf hpf hnf hrbf hmf
            elim_steps_nogrp
            exact hJ_fit (fit2, ()) mf
              ⟨fit2, sf, rfl, hdwf, htmkf, hcvf, hflf, hpf, hnf, hrbf, hmf⟩
          · exact hJ_fit (fit, ()) m'
              ⟨fit, s, rfl, hdw, htmk, hcv, hfl, hent_p, hent_n, hrb, hm⟩
        rintro _ ⟨fit2, ⟨⟩⟩ mf ⟨fit2', sf, heqf, hdwf, htmkf, hcvf, hflf, hpf, hnf, hrbf, hmf⟩
        cases heqf
        elim_steps_nogrp
        · have hwk_p : ∀ i < np.toNat, FullBveWeakItemOk sf.core
              (sf.scratch.scratch_buf[i]?.getD 0#32) :=
            fun i hi => by
              simpa using bve_weak_items_of_entries (off := 0)
                (fun i' hi' => by simpa using hpf i' hi') i hi
          have hwk_n : ∀ j < nn.toNat, FullBveWeakItemOk sf.core
              (sf.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32) :=
            bve_weak_items_of_entries (off := bveOccLim m8) hnf
          refine wp_join_fwd (fun xs m'' => ∃ sw wok, xs = (wok, ()) ∧
              FullDenseInvW c F0 F_cur sw ∧ TmkZero sw ∧
              sw.core.cur_vars = s0.core.cur_vars ∧ sw.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
              FullResBufOkW F_cur sw rp.toNat (bveROff m8) ∧ (FullMem c sw ⋆ R) m'') ?_ ?_
          · intro J_w hJ_w; elim_steps_nogrp
            · refine wp_weaken_seq (aoff1 := Arg.imm 0) (aoff2 := Arg.var neg_off)
                (off1 := 0) (off2 := bveOccLim m8) (cnt1 := np) (cnt2 := nn)
                hWeaken hWeakenUnit rfl hdwf htmkf hcvf hflf hro hmf hrbf
                (by rw [hcvf]; exact hpl) (by decide) (by omega)
                (fun i hi => by simpa using hwk_p i hi)
                (by rw [hcvf]; exact hnl) hneg_off_eq (by omega) hwk_n ?_
              intro _ ok sw mw hdw_w htmk_w hcv_w hfl_w hrb_w hm_w
              exact hJ_w (ok, ()) mw ⟨sw, ok, rfl, hdw_w, htmk_w, hcv_w, hfl_w, hrb_w, hm_w⟩
            · refine wp_weaken_seq (aoff1 := Arg.var neg_off) (aoff2 := Arg.imm 0)
                (off1 := bveOccLim m8) (off2 := 0) (cnt1 := nn) (cnt2 := np)
                hWeaken hWeakenUnit rfl hdwf htmkf hcvf hflf hro hmf hrbf
                (by rw [hcvf]; exact hnl) hneg_off_eq (by omega) hwk_n
                (by rw [hcvf]; exact hpl) (by decide) (by omega)
                (fun i hi => by simpa using hwk_p i hi) ?_
              intro _ ok sw mw hdw_w htmk_w hcv_w hfl_w hrb_w hm_w
              exact hJ_w (ok, ()) mw ⟨sw, ok, rfl, hdw_w, htmk_w, hcv_w, hfl_w, hrb_w, hm_w⟩
          rintro _ ⟨wok, ⟨⟩⟩ m_w ⟨sw, wok', heqw, hdww, htmkw, hcvw, hflw, hrbw, hmw⟩
          cases heqw; elim_steps_nogrp
          · exact wp_bve_var_commit hInactive hCommit hFlush rfl h_roff hv0
              hdww htmkw hcvw hflw hro hsc hrbw hmw hQ
          · have hoom := bve_oom_post hdww htmkw hcvw hflw
            exact bve_ret_q hQ ⟨hoom.1, hoom.2.1, hoom.2.2.1, hoom.2.2.2, Or.inr (Or.inl rfl),
              fun h20 => by simp at h20⟩ ‹_›
        · exact bve_ret_q hQ ⟨hdwf.toDense, htmkf, by omega, hflf, Or.inl rfl,
            fun h20 => by simp at h20⟩ hmf
      · intro J_post hJ_post
        elim_steps_nogrp
        · refine wp_bve_var_gates hGatesFid hGatesM7 rfl hm8 hm8_eq h2048 hv0 h_roff
              hbm.2.2.2.2.2.2.1 hdw2 htmk2 hcv2 hfl2 hnp_le hnn_le hent_p2 hent_n2
              hm2 ?_
          intro _ sg mg hinvg
          have hdwg := hinvg.1; have hcvg := hinvg.2.2.1; have hmg := hinvg.2.2.2.2.2.2.2.2.2
          have hro_le := hbm.2.2.2.2.2.2.1
          have hgf_lt : gf_idx.toNat < sg.scratch.scratch_buf.length := by
            rw [hdwg.1.scratch_ok.scratch_buf_len, h_gf]
            cases hm8c : m8 <;> simp [hm8c, bveROff] at hro_le ⊢ <;> omega
          have hrg_lt : rg_idx.toNat < sg.scratch.scratch_buf.length := by
            rw [hdwg.1.scratch_ok.scratch_buf_len, h_rg]
            cases hm8c : m8 <;> simp [hm8c, bveROff] at hro_le ⊢ <;> omega
          have hpl_g : (v <<< 1#32).toNat < sg.core.vals.length := by
            rw [hdwg.1.core_ok.vals_len, bve_bv32_shl1 (by omega)]
            have := hdwg.1.core_ok.cur_vars_le; omega
          elim_steps_nogrp
          · have hin := bve_loops_incon_unsat hinvg ‹_›
            exact bve_ret_q hQ ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2.1, Or.inr (Or.inr rfl),
              fun _ => hin.2.2.2.2⟩ hmg
          · exact bve_ret_q hQ ⟨hdwg.toDense, hinvg.2.1, by omega,
              hinvg.2.2.2.1, Or.inl rfl, fun h20 => by simp at h20⟩ hmg
          · refine wp_loop_fwd
              (fun μ (xs : Tup Val [i64, i64, i64, Ty.bool, i64, i32]) m' => ∃ s,
                xs.2.2.2.2.2.1.toNat ≤ np.toNat ∧
                μ = 2 * (np.toNat - xs.2.2.2.2.2.1.toNat) + (if xs.2.2.2.1 then 1 else 0) ∧
                BveVarLoopsInv c F0 F_cur s0 m8 v np nn xs.1 xs.2.1 xs.2.2.1 xs.2.2.2.1
                  xs.2.2.2.2.1 s m' R) ?_ ?_
            · intro J_o hJ_o; elim_steps_nogrp
              exact hJ_o _ _ _ ⟨sg, Nat.zero_le _, rfl, hinvg⟩
            rintro J_o μ ⟨rp, r_cnt, w_est, fit, res_sz, i, ⟨⟩⟩ m_o
              ⟨so, hi_le, rfl, hinv_o⟩ hJ_o
            have hdw_o := hinv_o.1; have hm_o := hinv_o.2.2.2.2.2.2.2.2.2
            refine wp_join_group (fun _ m' => ∃ s,
                BveVarLoopsInv c F0 F_cur s0 m8 v np nn rp r_cnt w_est fit res_sz s m' R) ?_ ?_
            · rintro _ _ m_ex ⟨s_ex, hinv_ex⟩
              have hdw_ex := hinv_ex.1; have hm_ex := hinv_ex.2.2.2.2.2.2.2.2.2
              elim_steps_nogrp
              exact hJ_post (rp, r_cnt, w_est, fit, ()) _
                ⟨rp, r_cnt, w_est, fit, res_sz, _, rfl, bve_loops_resSz_store hinv_ex ‹_›⟩
            intro J_exit hJ_exit; elim_steps_nogrp
            · have hi_lt : i.toNat < np.toNat := ‹_›
              have hfit_true : fit = true := ‹_›
              have hpm_lt : (pos_mask + (i >>> 5#32)).toNat < so.scratch.scratch_buf.length := by
                have hpm_bv : pos_mask = BitVec.ofNat 32 (bvePosMask m8) := by
                  cases hm8c : m8 <;> simp [h_pm, hm8c, bvePosMask]
                have hmw := bve_u32_mask_word_idx hnp_le hi_lt hm8
                rw [hdw_o.1.scratch_ok.scratch_buf_len, hpm_bv, hmw.2.2.1]; omega
              elim_steps_nogrp
              refine wp_join_fwd
                (fun (xs : Tup Val [i64, i64, i64, Ty.bool, i64, i32]) m' => ∃ s,
                  BveVarLoopsInv c F0 F_cur s0 m8 v np nn xs.1 xs.2.1 xs.2.2.1 xs.2.2.2.1
                    xs.2.2.2.2.1 s m' R) ?_ ?_
              · intro J17 hJ17; elim_steps_nogrp
                refine wp_loop_fwd
                  (fun μj (xs : Tup Val [i64, i64, i64, i64, i32]) m' => ∃ s,
                    xs.2.2.2.2.1.toNat ≤ nn.toNat ∧ μj = nn.toNat - xs.2.2.2.2.1.toNat ∧
                    BveVarLoopsInv c F0 F_cur s0 m8 v np nn xs.1 xs.2.1 xs.2.2.1 true
                      xs.2.2.2.1 s m' R) ?_ ?_
                · intro J_in hJ_in; elim_steps_nogrp
                  exact hJ_in _ _ _ ⟨so, Nat.zero_le _, rfl, by simpa [hfit_true] using hinv_o⟩
                rintro J_in μj ⟨rpj, r_cntj, w_estj, res_szj, j, ⟨⟩⟩ mj
                  ⟨sj, hj_le, rfl, hinv_j⟩ hJ_in
                have hdw_j := hinv_j.1; have hm_j := hinv_j.2.2.2.2.2.2.2.2.2
                elim_steps_nogrp
                · have hj_lt : j.toNat < nn.toNat := ‹_›
                  have hnm_lt :
                      (neg_mask + (j >>> 5#32)).toNat < sj.scratch.scratch_buf.length := by
                    have hnm_bv : neg_mask = BitVec.ofNat 32 (bveNegMask m8) := by
                      cases hm8c : m8 <;> simp [h_nm, hm8c, bveNegMask]
                    have hmw := bve_u32_mask_word_idx hnn_le hj_lt hm8
                    rw [hdw_j.1.scratch_ok.scratch_buf_len, hnm_bv, hmw.2.2.2]; omega
                  elim_steps_nogrp
                  refine wp_join_fwd (fun (_ : Tup Val [Ty.bool]) m' => mj = m') ?_ ?_
                  · intro J_np hJ_np; elim_steps_nogrp
                    · refine wp_join_fwd (fun (_ : Tup Val [i32]) m' => mj = m') ?_ ?_
                      · intro J_np1 hJ_np1; elim_steps_nogrp
                        · refine wp_join_fwd (fun (_ : Tup Val [Ty.bool]) m' => mj = m') ?_ ?_
                          · intro J_np2 hJ_np2; elim_steps_nogrp <;> exact hJ_np2 _ mj rfl
                          · rintro _ ⟨_, ⟨⟩⟩ m' hm_eq; subst hm_eq; elim_steps_nogrp
                            exact hJ_np1 _ mj rfl
                        · exact hJ_np1 _ mj rfl
                      · rintro _ ⟨_, ⟨⟩⟩ m' hm_eq; subst hm_eq; elim_steps_nogrp <;>
                          exact hJ_np _ mj rfl
                    · exact hJ_np _ mj rfl
                  rintro _ ⟨need_p, ⟨⟩⟩ m' hm_eq; subst hm_eq
                  refine wp_join_fwd
                    (fun (xs : Tup Val [i64, i64, i64, Ty.bool, i64, i32]) m' => ∃ s,
                      xs.2.2.2.2.2.1 = j ∧ xs.2.2.2.1 = true ∧
                      BveVarLoopsInv c F0 F_cur s0 m8 v np nn xs.1 xs.2.1 xs.2.2.1 true
                        xs.2.2.2.2.1 s m' R) ?_ ?_
                  · intro J20 hJ20; elim_steps_nogrp
                    · refine wp_join_fwd
                        (fun (xs : Tup Val [i64, i64, i64, Ty.bool, i32]) m' => ∃ s,
                          xs.2.2.2.2.1 = j ∧ xs.2.2.2.1 = true ∧
                          BveVarLoopsInv c F0 F_cur s0 m8 v np nn xs.1 xs.2.1 xs.2.2.1 true
                            (res_szj + 1#64) s m' R) ?_ ?_
                      · intro J_a hJ_a
                        have hi_buf : i.toNat < sj.scratch.scratch_buf.length := by
                          rw [hdw_j.1.scratch_ok.scratch_buf_len]; omega
                        have hj_add : (neg_off + j).toNat = bveOccLim m8 + j.toNat := by
                          rw [BitVec.toNat_add, hneg_off_eq]
                          exact Nat.mod_eq_of_lt (by omega)
                        have hj_buf : (neg_off + j).toNat < sj.scratch.scratch_buf.length := by
                          rw [hdw_j.1.scratch_ok.scratch_buf_len, hj_add]; omega
                        have hj_buf' : bveOccLim m8 + j.toNat < sj.scratch.scratch_buf.length := by
                          rw [← hj_add]; exact hj_buf
                        elim_steps_nogrp
                        exact wp_bve_var_resolve hResolve hAssign rfl rfl rfl rfl rfl rfl hfit_true
                          hv0 hnp_le hnn_le hinv_j
                          (by simpa [Nat.mod_eq_of_lt (show i.toNat < 2 ^ 64 by omega),
                                List.getElem?_eq_getElem hi_buf] using
                              hinv_j.2.2.2.2.1 i.toNat hi_lt)
                          (by simpa [hj_add,
                                Nat.mod_eq_of_lt (show bveOccLim m8 + j.toNat < 2 ^ 64 by omega),
                                List.getElem?_eq_getElem hj_buf'] using
                              hinv_j.2.2.2.2.2.1 j.toNat hj_lt)
                          hQ
                          (fun sa ma ha => hJ_in _ (rpj, r_cntj, w_estj, res_szj + 1#64,
                            j + 1#32, ()) ma
                            (by have := bve_cur_vars_lt31 hdw2.1; simp [BitVec.toNat_add]; omega)
                            ⟨sa, by simp [BitVec.toNat_add]; omega, rfl, ha⟩)
                          (fun sr mr hrf => hJ17 _ mr ⟨sr, hrf⟩)
                          (fun _ _ _ sr mr hra => hJ_a _ mr ⟨sr, rfl, rfl, hra⟩)
                      · rintro _ ⟨rpa, r_cnta, w_esta, fita, ja, ⟨⟩⟩ ma ⟨sa, hjeq, hfeq, hinv_a⟩
                        elim_steps_nogrp
                        exact hJ20 (rpa, r_cnta, w_esta, fita, res_szj + 1#64, ja, ()) ma
                          ⟨sa, hjeq, hfeq, hinv_a⟩
                    · rw [hfit_true]
                      exact hJ20 (rpj, r_cntj, w_estj, true, res_szj, j, ()) mj
                        ⟨sj, rfl, rfl, hinv_j⟩
                  · rintro _ ⟨rpn, r_cntn, w_estn, fitn, res_szn, jn, ⟨⟩⟩ mn
                      ⟨sn, hjeq, _, hinv_n⟩
                    dsimp only at hjeq; subst hjeq
                    elim_steps_nogrp
                    exact hJ_in _ (rpn, r_cntn, w_estn, res_szn, jn + 1#32, ()) mn
                      (by have := bve_cur_vars_lt31 hdw2.1; simp [BitVec.toNat_add]; omega)
                      ⟨sn, by simp [BitVec.toNat_add]; omega, rfl, hinv_n⟩
                · exact hJ17 (rpj, r_cntj, w_estj, fit, res_szj, j, ()) mj
                    ⟨sj, by simpa [hfit_true] using hinv_j⟩
                · exact hJ17 (rpj, r_cntj, w_estj, fit, res_szj, j, ()) mj
                    ⟨sj, by simpa [hfit_true] using hinv_j⟩
              · rintro _ ⟨rp17, r_cnt17, w_est17, fit17, res_sz17, j17, ⟨⟩⟩ m17 ⟨s17, hinv17⟩
                elim_steps_nogrp
                exact hJ_o _ (rp17, r_cnt17, w_est17, fit17, res_sz17, i + 1#32, ()) m17
                  (by have := bve_cur_vars_lt31 hdw2.1
                      simp [BitVec.toNat_add]; cases fit17 <;> simp [hfit_true] <;> omega)
                  ⟨s17, by simp [BitVec.toNat_add]; omega, rfl, hinv17⟩
            · exact hJ_exit () m_o ⟨so, hinv_o⟩
            · exact hJ_exit () m_o ⟨so, hinv_o⟩
        · have hextf : ext_ok = false := by cases ext_ok <;> first | rfl | contradiction
          exact hJ_post (r_off, 0#64, 0#64, ext_ok, ()) m2
            ⟨r_off, 0#64, 0#64, ext_ok, s2.scratch.res_sz, s2, rfl, by
              rw [hextf]
              exact bve_loops_init hdw2 htmk2 hcv2 hfl2 hent_p2 hent_n2 h_roff
                (by rw [h_roff]; exact hbm.2.2.2.2.2.2.1) hm2⟩
    · intro J_bf hJ_bf; elim_steps_nogrp
      · refine wp_join_group (fun _ m' => (np = 0#32 ∨ nn = 0#32) ∧ m2 = m') ?_ ?_
        · rintro _ _ _ ⟨_, hm_eq⟩; subst hm_eq
          exact wp_bve_var_pure hWeakenUnit hInactive rfl hv0 hpl hnl hneg_off_eq hnp_le hnn_le
            h2lim hdw2 htmk2 hcv2 hfl2 hent_p2 hent_n2 hm2 hQ
        intro J_pure hJ_pure; elim_steps_nogrp
        · exact hJ_pure () m2 ⟨Or.inl (by assumption), rfl⟩
        · exact hJ_pure () m2 ⟨Or.inr (by assumption), rfl⟩
        · exact hJ_bf () m2 ⟨Or.inr ⟨by assumption, by assumption⟩, rfl⟩
      · exact hJ_bf () m2 ⟨Or.inl (by cases ext_ok <;> first | rfl | contradiction), rfl⟩

end LeanQbe.T.Examples.Kissat.Proof.Eliminate

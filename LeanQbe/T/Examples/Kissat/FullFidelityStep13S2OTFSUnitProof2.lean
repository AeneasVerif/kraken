/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof2d
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 13 `full_propagate_beyond_m7` WP Proof (`FullFidelityStep13S2OTFSUnitProof2`)

Plain `public section` (`0` `@[expose]`, `0` `import all`, `<= 100` cols, theorem `<= 320` lines):
proves `full_propagate_beyond_m7_step13_wp` against `step13PropagateBeyondM6Spec`, reusing
`S13OuterInv`, `s13_outer_init_inv`, `s13_outer_sz0_step`, `s13_sz_nz_init_facts`, and
`s13_ovf_loop_wp` (`isBeyond := true`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "s13_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

private theorem s13_perm_refl_b (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem s13_trail_refl_b (k : FullCoreState) : FullTrailExt k k :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Parametric Step-13 WP proof for `full_propagate_beyond_m7` (`step13PropagateBeyondM6Spec`). -/
theorem full_propagate_beyond_m7_step13_wp (Γ : Env)
    (hWm4Get : ∀ args m Q X, step13Wm4GetSpec args m Q X →
      Γ "m6_wm4_get" [i64] [i64] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, step13PropagateBeyondM6Spec args m Q X →
      Func.wp Γ full_propagate_beyond_m7_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hcfg, hext0, hlen0, hw0,
    hdense0, hm0, hQ⟩
  have hQ' : S13HQ true c F0 F_cur ext0 s 0xFFFFFFFF#64 R Q := fun r ext' v' f' l' rs' tr' tp'
      te' pr' un' uf' wv' ar' ws' wl' wu' fl' ct' cr' c0' c1' om' sc' m' hx hw2 hl hwf htr hpm
      hpr hrr hdl hnp hd0 hfl hr hbcf hr0 hr1 h2 hno hm => by
    rcases hbcf rfl with ⟨rfl, rfl, rfl, rfl⟩
    refine hQ r ext' v' f' l' rs' tr' tp' te' pr' un' uf' wv' ar' ws' wl' wu' fl' om' sc' m'
      hx hw2 hl hwf htr hpm hpr hrr hdl hnp hd0 hfl ?_ (fun h0 => let x := hr0 h0; ⟨x.1, x.2.2⟩)
      h2 ?_ hm
    · rcases hr with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hpe; rcases hno hpe with ⟨h0, h1, h2'⟩; exact ⟨h0, h1, h2'⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have har := c.harena; unfold dimacsBound at har
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hdelc := c.hdel; unfold dimacsBound at hdelc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
    (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.trail_end_le hcv_lt64
  have hpr0_lt64 : s.core.propagated < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.propagated_le hte0_lt64
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hclv_lt64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hclv_lt32 (by decide)
  have hdelc_lt64 : c.delayed_cap < 2 ^ 64 := Nat.lt_trans hdelc (by decide)
  have hdlim_toNat : (BitVec.ofNat 64 c.delayed_cap * 3#64).toNat = 3 * c.delayed_cap := by
    rw [BitVec.toNat_mul, m7_bv64_ofNat_toNat_lt hdelc_lt64,
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  unfold Func.wp full_propagate_beyond_m7_body
  have _hm0_f := fullM6HdrMem_focus_full hm0
  s13_hsplit
  · have hge : s.core.trail_end ≤ s.core.propagated := by
      have hh : s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64] at hh
    have hpe : s.core.propagated = s.core.trail_end :=
      Nat.le_antisymm hlen0.core_ok.propagated_le hge
    exact s13_exit_hQ hQ' hext0 (fun h => ⟨h, .refl _⟩) (.refl _ _)
      (s13_probePres_of_S13Scr rfl) rfl rfl (fun _ => rfl) hlen0 hw0
      (s13_trail_refl_b s.core) (s13_perm_refl_b s.core)
      (fun _ => rfl) (Nat.le_refl _) (Or.inl rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
      (fun _ => ⟨hpe, fun _ => rfl, fun h => h, fun hlt => absurd hlt (by omega)⟩)
      (fun _ h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩)
      hm0
  · have hpr_lt : s.core.propagated < s.core.trail_end := by
      have hh : ¬ s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64, Nat.not_le] at hh
    s13_hsplit
    · exact s13_exit_hQ hQ' hext0 (fun h => ⟨h, .refl _⟩) (.refl _ _)
        (s13_probePres_of_S13Scr rfl) rfl rfl (fun _ => rfl) hlen0 hw0
        (s13_trail_refl_b s.core) (s13_perm_refl_b s.core)
        (fun _ => rfl) (Nat.le_refl _) (Or.inr rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
        (fun h => absurd h (by decide)) (fun _ h => absurd h (by decide)) (fun _ => Or.inl hc)
        (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm0
    · have hoom0 : s.core.oom = 0#64 := hc
      clear _hm0_f
      have _hm0_f := fullM6HdrMem_focus_full hm0
      s13_hsteps_nogrp
      refine wp_call_of_spec _ _ (hWm4Get _ _ _ _ ?_)
      refine ⟨c, ext0, s, R, rfl, hcfg, hext0, hlen0, hm0, fun wm4 hm_wm4 => ?_⟩
      clear _hm0_f
      have _hm_wm4_f := fullM6HdrMem_focus_full hm_wm4
      s13_hsteps_nogrp
      refine wp_loop_group
        (fun rem (prop_v, tend_v, fuel_v, unass_v, unfl_v, ticks_v, ()) ml =>
          S13OuterInv true c F0 F_cur ext0 s R rem prop_v tend_v fuel_v unass_v unfl_v ticks_v
            ml) ?_ ?_
      · rintro J rem ⟨prop_v, tend_v, fuel_v, unass_v, unfl_v, ticks_v, ⟨⟩⟩ ml ih hinv_o
        obtain ⟨ext1, sem, te_mem, rfl, hext1, hw2b1, hlen_o, hw_o, htr_o, hperm_o, hag_o, hprop_eq,
            htend_eq, hfuel_eq, hunass_eq, hunfl_eq, hoom_o, hct_o, hbcf_o, hdm_o, hcv_o, hcl_o,
            hprob_o, halen_o, hfuel_le, hfuel_lt, hpr_ge, htem_le, hpr_tem, hsc_o, hd0_sem, hml⟩ :=
          s13OuterInv_elim hinv_o
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let sem_d : FullState := { sem with core :=
          { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
        have hsd_len : s_disk.LengthsOk c := ⟨{ hlen0.core_ok with
          trail_end_le := Nat.le_trans htem_le (hcv_o ▸ hlen_o.core_ok.trail_end_le)
          propagated_le := hpr_tem }, hlen0.scratch_ok⟩
        have hsemd_len : sem_d.LengthsOk c := ⟨{ hlen_o.core_ok with
          propagated_le := Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
          hlen_o.scratch_ok⟩
        have hmem_len := fastPropMem_lengthsOk hsd_len hsemd_len (by simp [s_disk, sem_d, hcv_o])
          rfl rfl
        have hte_lt64 : sem.core.trail_end < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.trail_end_le (hcv_o ▸ hcv_lt64)
        have hpr_o_lt64 : sem.core.propagated < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.propagated_le hte_lt64
        have _hml_f := fullM6HdrMem_focus_full hml
        s13_hsplit
        · have hp_lt_o : prop_v.toNat < tend_v.toNat := hc
          have hp_lt_sem : sem.core.propagated < sem.core.trail_end := by
            rw [hprop_eq, htend_eq]; exact hp_lt_o
          s13_hsplit
          · have hfl0 : sem.core.fuel = 0#64 := hfuel_eq.trans hc
            clear ih; s13_hsteps_nogrp; (try dsimp only)
            exact s13_outer_flush_ret
              (sem := { sem with scratch := { sem.scratch with
                search_ticks := s.scratch.search_ticks } })
              hAddTicks hQ' hcfg hext1 hw2b1
              ⟨hlen_o.core_ok,
                { hlen_o.scratch_ok with phases_len := hlen_o.scratch_ok.phases_len }⟩
              hw_o htr_o hperm_o
              hag_o (by dsimp only; rw [hsc_o]) hd0_sem hprop_eq htend_eq hfl0 hunass_eq hunfl_eq
              hfuel_le hpr_lt (Or.inr rfl) hbcf_o (fun h => absurd h (by decide))
              (fun _ => by decide) (fun _ => Or.inr hfl0)
              (fullM6HdrMem_unfocus_full (by simpa only [fastPropMem, s_disk, sem_d, hprop_eq,
                htend_eq, hunass_eq, hunfl_eq, hfl0, BitVec.ofNat_eq_ofNat] using hm))
          · have hfl_ne : sem.core.fuel ≠ 0#64 := fun h => hc (hfuel_eq ▸ h)
            have hfl_pos : 0 < sem.core.fuel.toNat := by
              by_cases h0 : sem.core.fuel.toNat = 0
              · exact absurd (BitVec.eq_of_toNat_eq h0) hfl_ne
              · omega
            have hfl_dec : (sem.core.fuel - 1#64).toNat = sem.core.fuel.toNat - 1 :=
              m7_bv64_sub_toNat (by simp; omega)
            have hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by omega
            have hp_lt_trl : prop_v.toNat < (fastPropMem s_disk sem_d).core.trl.length := by
              rw [fastPropMem_trl, hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            have hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length := by
              rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
              have := hcv_o; omega
            let lit := sem.core.trl[prop_v.toNat]'hp_sem_lt_trl
            have hlit_eq : lit = sem.core.trl[sem.core.propagated]'(by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega) := by
              simp only [lit]; exact (fc_getElem_eq_of_idx hprop_eq _ _).symm
            have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
              have := hw_o.trail_lits_lt sem.core.propagated hp_lt_sem
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              rwa [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq] at this
            let not_lit := lit ^^^ 1#32
            have hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars := by
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [fc_nat_xor_one]; split <;> omega
            have hnot_f0 : sem.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              refine (hw_o.vals_false_iff not_lit.toNat hnot_lt).mpr
                ⟨sem.core.propagated, hp_lt_sem, ?_⟩
              rw [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq]
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rcases Nat.mod_two_eq_zero_or_one lit.toNat with h | h
              · have h2 : (lit.toNat + 1) % 2 = 1 := by omega
                simp only [fc_nat_xor_one, h, ↓reduceIte, h2, Nat.one_ne_zero]; omega
              · have h2 : (lit.toNat - 1) % 2 = 0 := by omega
                simp only [fc_nat_xor_one, h, Nat.one_ne_zero, ↓reduceIte, h2]; omega
            have hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
              m7_bv64_shl1_u32_nat not_lit
            have hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                2 * not_lit.toNat + 1 := m7_bv64_shl1_add1_nat not_lit
            have hwv_o_len := hlen_o.core_ok.wvec_len
            have hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1 :=
              m7_bv64_add1_toNat (by omega)
            have hnl64_lt_wv0 :
                (not_lit.setWidth 64 <<< (1 : Nat)).toNat < sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_1_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_lt_wv : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_lt_wv0
            have hnl64_1_lt_wv : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_1_lt_wv0
            have hnl64_lt_wv_fp :
                (((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^
                  1#32).setWidth 64 <<< (1 : Nat)).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              simpa only [fastPropMem_trl] using hnl64_lt_wv
            have hnl64_1_lt_wv_fp :
                ((((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^
                  1#32).setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              simpa only [fastPropMem_trl] using hnl64_1_lt_wv
            let _ := hnl64_lt_wv_fp; let _ := hnl64_1_lt_wv_fp
            have hsz_hc_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                (2 * ((sem.core.trl[prop_v.toNat]'hp_sem_lt_trl).toNat ^^^ 1) + 1) % 2 ^ 64 := by
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := rfl
              have hnot_toNat : not_lit.toNat = lit.toNat ^^^ 1 := by
                dsimp only [not_lit]; rw [BitVec.toNat_xor]
                simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [hnl64_1_idx, hlit_trl, ← hnot_toNat,
                Nat.mod_eq_of_lt (by have := hlen_o.core_ok.cur_vars_le; omega)]
            s13_hsplit
            · s13_hsteps
              exact ih _ _ ml hfl_rem_dec (s13_outer_sz0_step hext1 hw2b1 hlen_o hw_o htr_o hperm_o
                hag_o hprop_eq htend_eq hfuel_eq hunass_eq hunfl_eq hoom_o hct_o hbcf_o hdm_o hcv_o
                hcl_o hprob_o halen_o hsc_o hd0_sem hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge
                htem_le hpr_tem hml)
            · have hsz_ne : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 ≠ 0#64 := by
                have hc' := hc; simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]; exact hc'
              let s_base : FullState := { sem with core :=
                { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := rfl
              obtain ⟨hoff0_nat, hsz0_nat, hend0_lt64, hpi0, hnl_idx_lt, hnl_sbase⟩ :=
                s13_sz_nz_init_facts hwc hlen_o hw_o hcv_o hdm_o hprop_eq hp_lt_sem hpr_ge rfl
                  hnot_lt hnot_f0 hnl64_idx hnl64_1_idx (fastPropMem_trl s_disk sem_d)
                  (fastPropMem_lvl s_disk sem_d) hp_sem_lt_trl hlit_trl rfl hsz_ne
              have hend0_eq :
                  (sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64 +
                    (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'
                      hnl64_1_lt_wv0).setWidth 64 =
                  (sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64 +
                    BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat) :=
                congrArg _ (BitVec.eq_of_toNat_eq (by
                  have hsz_lt64 : fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 := by
                    rw [← hsz0_nat]; exact BitVec.isLt _
                  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt64]
                  simpa only [BitVec.toNat_setWidth] using hsz0_nat))
              have hend0_nat :
                  ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64 +
                    (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'
                      hnl64_1_lt_wv0).setWidth 64).toNat =
                  fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat := by
                have hof : ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                    hnl64_lt_wv0).setWidth 64).toNat = fullWatchOffCore s_base.core not_lit.toNat :=
                  hoff0_nat
                have hsz : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                    1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat =
                    fullWatchSizeCore s_base.core not_lit.toNat := hsz0_nat
                rw [BitVec.toNat_add, hof, hsz, Nat.mod_eq_of_lt (by omega)]
              s13_hsteps_nogrp
              have hm_base := fullM6HdrMem_focus_full hml
              simp only [fastPropMem_wvec, fastPropMem_trl, fastPropMem_lvl]
              have hnl_sbase' := hnl_sbase
              simp only [fastPropMem_lvl, fastPropMem_trl] at hnl_sbase'
              have hpi0' : PropLitInv c F0 F_cur s_base s_base not_lit.toNat
                  ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64).toNat
                  ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64).toNat
                  ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64).toNat
                  ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                      hnl64_lt_wv0).setWidth 64 +
                    (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                      1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat := by
                have hp := hpi0
                rw [← hend0_nat, ← hoff0_nat] at hp
                exact hp
              refine s13_ovf_loop_wp (ignore_ref := .imm 0xFFFFFFFF) hOvf hFlush hAddTicks hQ'
                (fun rem_n xs_n mc0 hrem_n hinv_n => by
                  s13_hsteps
                  exact ih rem_n (xs_n.1.val, xs_n.2.1.val, xs_n.2.2.1.val, xs_n.2.2.2.1.val,
                    xs_n.2.2.2.2.1.val, xs_n.2.2.2.2.2.1.val, ()) mc0 hrem_n hinv_n)
                hcfg hext1 hw2b1 hlen0 hpr_lt rfl hfuel_eq rfl hprop_eq htend_eq
                hunass_eq hunfl_eq ⟨te_mem, rfl, htem_le, hpr_tem⟩ hlen_o hw_o htr_o hperm_o hag_o
                hoom_o hct_o hbcf_o hdm_o hcv_o hcl_o hprob_o halen_o hsc_o hd0_sem hfl_rem_dec
                hfuel_le hp1_prop hp_lt_o hpr_ge rfl hnot_lt ?_ ?_ (hcl_o ▸ hclv_lt32) rfl hnl64_idx
                hnl_sbase' hdlim_toNat hoff0_nat hend0_eq hend0_nat hpi0' hm_base
              · simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
                rw [Nat.mod_eq_of_lt hcv_lt64, show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                  Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm s.core.cur_vars 2,
                  Nat.mod_eq_of_lt h2cv_lt64, hcv_o]
              · apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hclv_lt32, Nat.mod_eq_of_lt hclv_lt64, hcl_o]
        · have hpe_o : sem.core.propagated = sem.core.trail_end := by
            have hh : tend_v.toNat ≤ prop_v.toNat := Nat.le_of_not_lt hc
            rw [← htend_eq, ← hprop_eq] at hh; exact Nat.le_antisymm hlen_o.core_ok.propagated_le hh
          have hprop_gt : s.core.propagated < prop_v.toNat := by
            rw [← hprop_eq, hpe_o]; exact Nat.lt_of_lt_of_le hpr_lt htr_o.1
          have hfuel_dec := hfuel_lt hprop_gt
          clear ih; s13_hsteps_nogrp; (try dsimp only)
          exact s13_outer_flush_ret
            (sem := { sem with scratch := { sem.scratch with
              search_ticks := s.scratch.search_ticks } })
            hAddTicks hQ' hcfg hext1 hw2b1
            ⟨hlen_o.core_ok,
              { hlen_o.scratch_ok with phases_len := hlen_o.scratch_ok.phases_len }⟩
            hw_o htr_o hperm_o
            hag_o (by dsimp only; rw [hsc_o]) hd0_sem hprop_eq htend_eq hfuel_eq hunass_eq hunfl_eq
            hfuel_le hpr_lt (Or.inl rfl) hbcf_o
            (fun _ => ⟨hprop_eq ▸ htend_eq ▸ hpe_o, hct_o, fun _ => hoom_o, fun _ => hfuel_dec⟩)
            (fun _ => by decide) (fun h => absurd h (by decide))
            (fullM6HdrMem_unfocus_full (by simpa only [fastPropMem, s_disk, sem_d, hprop_eq,
              htend_eq, hunass_eq, hunfl_eq, hfuel_eq] using hm))
      · intro J hJ; s13_hsteps
        exact hJ s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated,
            BitVec.ofNat 64 s.core.trail_end, s.core.fuel, s.core.unassigned, s.core.unflushed,
            0#64, ()) m
          (s13_outer_init_inv hlen0 hext0 hw0 hdense0 hoom0 hpr0_lt64 hte0_lt64 hm_wm4)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end

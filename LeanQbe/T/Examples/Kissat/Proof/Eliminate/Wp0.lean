/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
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
# Kissat BVE `Func.wp` Proofs — Part 0a (`Wp0`: Collect, ExtNeed, Weaken, WeakenUnit)

Clean `CanonicalEnv` `Func.wp` proofs (`0` legacy `Full*` imports, `<= 100` cols,
every decl `<= 450`L):
1. `full_bve_collect_m7_wp` (`Spec.fullBveCollectM7Spec`)
2. `full_bve_ext_need_wp` (`Spec.fullBveExtNeedSpec`)
3. `full_bve_weaken_wp` (`Spec.fullBveWeakenTmkSpec`)
4. `full_bve_weaken_unit_fid_wp` (`Spec.fullBveWeakenTmkSpec`)
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
open Kraken.Bedrock2.Test

open scoped FullArenaTactics
open scoped EliminateTactics

/-! ## 1. Pure Helpers -/

private theorem fullDenseInvW_of_extendPush1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {estk' : List (BitVec 32)} {elen' : Nat}
    (hlen : estk'.length = c.extend_cap) (hel : elen' ≤ c.extend_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with extend_stk := estk', extend_len := elen' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with extend_stk_len := hlen }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, ⟨h.2.2.2.2.1.1, hel⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem fullDenseInvW_of_extPush {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len ≤ c.extend_cap) : FullDenseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2.1, heq ▸ h.2.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · refine ⟨fun i hi => ?_, hel⟩
    change s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      _ ∈ fullArenaClauseRefsCore s'.core
    rw [hll, heq]; exact h.2.2.2.2.1.1 i hi

private theorem elim_garb_zero_of_garb_red {x : BitVec 32}
    (h : (x &&& (524288#32 ||| 4194304#32)) = 0#32) :
    (x &&& 0x00080000#32) = 0#32 := by
  ext i hi
  have hi_eq := congrArg (·[i]) h
  have h2 : (524288#32 ||| 4194304#32 : BitVec 32)[i] =
      (4718592#32 : BitVec 32)[i] := rfl
  rw [BitVec.getElem_and, BitVec.getElem_zero] at hi_eq ⊢
  cases hb : (0x00080000#32 : BitVec 32)[i]
  · simp
  · simp only [Bool.and_true]
    have ht : (4718592#32 : BitVec 32)[i] = true := by
      clear hi_eq h2; revert i hi; decide
    rwa [h2, ht, Bool.and_true] at hi_eq

/-! ## 2. `full_bve_collect_m7_wp` -/

public theorem full_bve_collect_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullBveCollectM7Spec a m Q X →
      Func.wp Γ full_bve_collect_m7_body a m Q X := by
  rintro ⟨h, lit, out_ptr, cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, out_off, R, rfl, hdw0, hlit_lt, hout_ptr, hcap_le, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx hwc harc hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hwlen_le := hdw0.1.core_ok.wlen_le
  have hdw_s0 := denseWatchesInv_of_w hdw0
  have hbd := hdw_s0.layout.bounds lit.toNat hlit_lt
  have hlv0 : (lit.setWidth 64 <<< (1 : Nat)).toNat < s0.core.wvec.length := by
    rw [hdw0.1.core_ok.wvec_len]; c0_bound
  have hlv1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < s0.core.wvec.length := by
    rw [hdw0.1.core_ok.wvec_len]; c0_bound
  let off_l := (s0.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlv0).setWidth 64
  let sz_l := (s0.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlv1).setWidth 64
  let end_l := off_l + sz_l
  have hoff_eq : off_l.toNat = fullWatchOffCore s0.core lit.toNat := by
    unfold off_l fullWatchOffCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
      elim_zext32_toNat]
    exact congrArg BitVec.toNat (elim_getElem_congr (by c0_bound) _ _)
  have hsz_eq : sz_l.toNat = fullWatchSizeCore s0.core lit.toNat := by
    unfold sz_l fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
      elim_zext32_toNat]
    exact congrArg BitVec.toNat (elim_getElem_congr (by c0_bound) _ _)
  have hend_eq : end_l.toNat = off_l.toNat + sz_l.toNat := by
    dsimp only [end_l]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hend_c0 :
      ((s0.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
          rw [hdw0.1.core_ok.wvec_len]; omega)).toNat +
        (s0.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'(by
          rw [hdw0.1.core_ok.wvec_len]; omega)).toNat) % 2 ^ 64 = end_l.toNat := by
    have h1 : (s0.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
        rw [hdw0.1.core_ok.wvec_len]; omega)).toNat = off_l.toNat := by
      rw [hoff_eq]; unfold fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (elim_getElem_congr (by omega) _ _)
    have h2 : (s0.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'(by
        rw [hdw0.1.core_ok.wvec_len]; omega)).toNat = sz_l.toNat := by
      rw [hsz_eq]; unfold fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (elim_getElem_congr (by omega) _ _)
    rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
  unfold Func.wp full_bve_collect_m7_body
  elim_steps_nogrp
  refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
    (fun (_pb, cnt, ()) mp => ∃ scr_p : List (BitVec 32),
      scr_p.length = c.scratch_cap ∧ cnt.toNat ≤ cap.toNat ∧
      (∀ i < c.scratch_cap, i < out_off ∨ out_off + cap.toNat ≤ i →
        scr_p[i]? = s0.scratch.scratch_buf[i]?) ∧
      (∀ i < cnt.toNat, FullBveEntryOkW F_cur
        { s0 with scratch := { s0.scratch with scratch_buf := scr_p } }
        lit.toNat (scr_p[out_off + i]?.getD 0#32)) ∧
      (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mp)
    (fun rem (p, cnt, ()) mp => ∃ scr_p : List (BitVec 32),
      scr_p.length = c.scratch_cap ∧ off_l.toNat ≤ p.toNat ∧ p.toNat ≤ end_l.toNat ∧
      rem = end_l.toNat - p.toNat ∧ cnt.toNat ≤ cap.toNat ∧
      DenseWatchSliceOk F_cur s0.core lit.toNat p.toNat rem ∧
      (∀ i < c.scratch_cap, i < out_off ∨ out_off + cap.toNat ≤ i →
        scr_p[i]? = s0.scratch.scratch_buf[i]?) ∧
      (∀ i < cnt.toNat, FullBveEntryOkW F_cur
        { s0 with scratch := { s0.scratch with scratch_buf := scr_p } }
        lit.toNat (scr_p[out_off + i]?.getD 0#32)) ∧
      (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mp)
    ?_ ?_ ?_
  · rintro _ ⟨_pb, cnt, ⟨⟩⟩ mp ⟨scr_p, hlen_p, hcnt_le, hout_p, hent_p, hmp⟩
    elim_steps!
    exact hQ cnt scr_p mp hlen_p hout_p (Or.inr ⟨hcnt_le, hent_p⟩) hmp
  · rintro B L rem ⟨p, cnt, ⟨⟩⟩ mp hB hL
      ⟨scr_p, hlen_p, hp_ge, hp_le, hrem, hcnt_le, hslice, hout_p, hent_p, hmp⟩
    elim_steps_nogrp
    · have hp_lt : p.toNat < end_l.toNat := by
        simpa only [BitVec.toNat_ofNat] using (hend_c0 ▸ hc)
      have hpw : p.toNat < s0.core.wstk.length := by
        rw [hdw0.1.core_ok.wstk_len_arr]; omega
      have hp1 : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      cases hslice with
      | empty => omega
      | @bin _ r1 w0 hwp0 hflag hne hot_lt hent_b hrest =>
        have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
          rw [List.getElem?_eq_getElem hpw] at hwp0; exact Option.some.inj hwp0
        cases hw0_eq
        have hfl_b : ((s0.core.wstk[p.toNat]'hpw) &&& 0x80000000#32) ≠ 0#32 := hflag
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
        have hrest' : DenseWatchSliceOk F_cur s0.core lit.toNat (p + 1#64).toNat
            (end_l.toNat - (p + 1#64).toNat) := by
          rw [hp1_nat, show end_l.toNat - (p.toNat + 1) = r1 by omega]; exact hrest
        have hot_lt' : ((s0.core.wstk[p.toNat]'hpw) &&& 0x7FFFFFFF#32).toNat <
            2 * s0.core.cur_vars := hot_lt
        have hot_val : (((s0.core.wstk[p.toNat]'hpw &&& 0x7FFFFFFF#32).setWidth 64)).toNat <
            s0.core.vals.length := by
          rw [hdw0.1.core_ok.vals_len, elim_zext32_toNat]; omega
        elim_steps_nogrp
        · elim_steps!
          exact hL (end_l.toNat - (p + 1#64).toNat) (p + 1#64, cnt, ()) mp (by omega)
            ⟨scr_p, hlen_p, by omega, by omega, rfl, hcnt_le, hrest', hout_p, hent_p, hmp⟩
        · elim_steps!; exact hQ 0xFFFFFFFF#32 scr_p mp hlen_p hout_p (Or.inl rfl) hmp
        · have hcnt_lt : cnt.toNat < cap.toNat := by
            have := Nat.lt_of_not_le hc; exact this
          have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by c0_bound
          have hidx_sc : out_off + cnt.toNat < scr_p.length := by omega
          rw [hout_ptr]
          elim_steps!
          let scr' := scr_p.set (out_off + cnt.toNat) (s0.core.wstk[p.toNat]'hpw)
          have hw0_ok : FullBveEntryOkW F_cur
              { s0 with scratch := { s0.scratch with scratch_buf := scr' } }
              lit.toNat (s0.core.wstk[p.toNat]'hpw) := by
            unfold FullBveEntryOkW; rw [ite_eq_left hfl_b]
            exact ⟨hot_lt, hent_b⟩
          exact hL (end_l.toNat - (p + 1#64).toNat) (p + 1#64, cnt + 1#32, ()) _ (by omega)
            ⟨scr', by simp [scr', hlen_p], by omega, by omega, rfl, by omega, hrest',
             fun i hi hor => by
               dsimp only [scr']; rw [List.getElem?_set_ne (by omega)]; exact hout_p i hi hor,
             fun i hi => by
               dsimp only [scr']
               rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hcnt1 ▸ hi)) with h | h
               · rw [List.getElem?_set_ne (by omega)]; exact hent_p i h
               · subst h; rw [List.getElem?_set_self hidx_sc, Option.getD_some]
                 exact hw0_ok, hm⟩
      | @occ _ r1 w0 cr hwp0 hnp1 hflag _ hcr_lt31 href_cr hrest =>
        have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
          rw [List.getElem?_eq_getElem hpw] at hwp0; exact Option.some.inj hwp0
        cases hw0_eq
        have hfl_z : (s0.core.wstk[p.toNat]'hpw &&& 0x80000000#32) = 0#32 := hflag
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
        have hp1_lt : (p + 1#64).toNat < s0.core.wstk.length := by
          rw [hdw0.1.core_ok.wstk_len_arr]; omega
        have hp1_c0 : (p.toNat + 1) % 2 ^ 64 = (p + 1#64).toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        have hcr_eq : s0.core.wstk[(p + 1#64).toNat]'hp1_lt = cr := by
          have hp1_lt' : p.toNat + 1 < s0.core.wstk.length := hp1_nat ▸ hp1_lt
          rw [List.getElem?_eq_getElem hp1_lt'] at hnp1
          exact (elim_getElem_congr hp1_nat hp1_lt hp1_lt').trans (Option.some.inj hnp1)
        cases hcr_eq
        have href_cr' : (s0.core.wstk[(p + 1#64).toNat]'hp1_lt).toNat ∈
            fullArenaClauseRefs s0 := href_cr
        have hwf_cr := hdw0.2.1.arena.refs_wf _ href_cr'
        have hal_le := hdw0.1.core_ok.arena_len_le
        have hcr_ar0 : ((s0.core.wstk[(p + 1#64).toNat]'hp1_lt).setWidth 64).toNat <
            s0.core.arena.length := by
          rw [hdw0.1.core_ok.arena_len_arr, elim_zext32_toNat]; omega
        have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
        have hrest' : DenseWatchSliceOk F_cur s0.core lit.toNat (p + 1#64 + 1#64).toNat
            (end_l.toNat - (p + 1#64 + 1#64).toNat) := by
          rw [hp2_nat, show end_l.toNat - (p.toNat + 2) = r1 by omega]; exact hrest
        have hcr_c0 :
            ((s0.core.wstk[(p.toNat + 1) % 2 ^ 64]'(by
                rw [hp1_c0]; exact hp1_lt)).setWidth 64).toNat < s0.core.arena.length := by
          rw [elim_getElem_congr hp1_c0 _ hp1_lt]; exact hcr_ar0
        elim_steps_nogrp
        · elim_steps!
          exact hL (end_l.toNat - (p + 1#64 + 1#64).toNat) (p + 1#64 + 1#64, cnt, ()) mp
            (by omega)
            ⟨scr_p, hlen_p, by omega, by omega, rfl, hcnt_le, hrest', hout_p, hent_p, hmp⟩
        · have hcr_ar2 : ((s0.core.wstk[(p + 1#64).toNat]'hp1_lt).setWidth 64 + 2#64).toNat <
              s0.core.arena.length := by
            rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
          have hng_cr' : fullArenaClauseGarb s0
              (s0.core.wstk[(p + 1#64).toNat]'hp1_lt).toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            have h0 : s0.core.arena[(s0.core.wstk[(p + 1#64).toNat]'hp1_lt).toNat]?.getD 0#32 =
                s0.core.arena[((s0.core.wstk[(p + 1#64).toNat]'hp1_lt).setWidth
                  64).toNat]'hcr_ar0 := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                Option.getD_some]
              exact elim_getElem_congr (elim_zext32_toNat _).symm _ hcr_ar0
            have hcr_idx := congrArg BitVec.toNat (elim_getElem_congr hp1_c0
              (by rw [hp1_c0]; exact hp1_lt) hp1_lt)
            have hget_ar : s0.core.arena[((s0.core.wstk[(p + 1#64).toNat]'hp1_lt).setWidth
                  64).toNat]'hcr_ar0 =
                s0.core.arena[(s0.core.wstk[(p.toNat + 1) % 2 ^ 64]'(by
                  rw [hp1_c0]; exact hp1_lt)).toNat]'(by
                  rw [elim_zext32_toNat] at hcr_c0; exact hcr_c0) :=
              elim_getElem_congr (by rw [elim_zext32_toNat, hcr_idx]) _ _
            have hz : (s0.core.arena[((s0.core.wstk[(p + 1#64).toNat]'hp1_lt).setWidth
                  64).toNat]'hcr_ar0 &&& (524288#32 ||| 4194304#32)) = 0#32 := by
              rw [hget_ar]; exact hc
            rw [h0, elim_garb_zero_of_garb_red hz]; decide
          elim_steps_nogrp
          · elim_steps!; exact hQ 0xFFFFFFFF#32 scr_p mp hlen_p hout_p (Or.inl rfl) hmp
          · elim_steps!; exact hQ 0xFFFFFFFF#32 scr_p mp hlen_p hout_p (Or.inl rfl) hmp
          · have hcnt_lt : cnt.toNat < cap.toNat := by
              have := Nat.lt_of_not_le hc; exact this
            have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by c0_bound
            have hidx_sc : out_off + cnt.toNat < scr_p.length := by omega
            have hcr_nobin : (s0.core.wstk[(p + 1#64).toNat]'hp1_lt &&& 0x80000000#32) =
                0#32 :=
              elim_bv32_and_msb_zero_of_lt hcr_lt31
            rw [hout_ptr]
            elim_steps!
            let cr' := s0.core.wstk[(p + 1#64).toNat]'hp1_lt
            let scr' := scr_p.set (out_off + cnt.toNat) cr'
            have hcr_ok : FullBveEntryOkW F_cur
                { s0 with scratch := { s0.scratch with scratch_buf := scr' } }
                lit.toNat cr' := by
              unfold FullBveEntryOkW; rw [ite_eq_right (fun h => h hcr_nobin)]
              exact ⟨href_cr', hng_cr'⟩
            exact hL (end_l.toNat - (p + 1#64 + 1#64).toNat)
              (p + 1#64 + 1#64, cnt + 1#32, ()) _ (by omega)
              ⟨scr', by simp [scr', hlen_p], by omega, by omega, rfl, by omega, hrest',
               fun i hi hor => by
                 dsimp only [scr']; rw [List.getElem?_set_ne (by omega)]
                 exact hout_p i hi hor,
               fun i hi => by
                 dsimp only [scr']
                 rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hcnt1 ▸ hi)) with h | h
                 · rw [List.getElem?_set_ne (by omega)]; exact hent_p i h
                 · subst h; rw [List.getElem?_set_self hidx_sc, Option.getD_some]
                   exact hcr_ok, hm⟩
    · elim_steps!; exact hB (p, cnt, ()) mp ⟨scr_p, hlen_p, hcnt_le, hout_p, hent_p, hmp⟩
  · intro _ L _ hL; elim_steps!
    exact hL sz_l.toNat (off_l, 0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.le_refl _,
       by omega, show sz_l.toNat = end_l.toNat - off_l.toNat by omega,
       Nat.zero_le _, by rw [hoff_eq, hsz_eq]; exact hdw_s0.slices lit.toNat hlit_lt,
       fun _ _ _ => rfl, fun _ h => by simp at h, hm0⟩

/-! ## 3. `full_bve_ext_need_wp` -/

public theorem full_bve_ext_need_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullBveExtNeedSpec a m Q X →
      Func.wp Γ full_bve_ext_need_body a m Q X := by
  rintro ⟨h, off, cnt, ⟨⟩⟩ m0 Q X ⟨c, s0, R, rfl, hlen0, hoff_cnt, hent_i, hm0, hQ⟩
  have harc := c.harena; have hsc := c.hscr; unfold dimacsBound at harc hsc
  unfold Func.wp full_bve_ext_need_body
  elim_steps_nogrp
  refine wp_loop_group (ts := [i64, i32])
    (fun rem (need, i, ()) mi => mi = m0 ∧ i.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - i.toNat)
    ?_ ?_
  · rintro L rem ⟨need, i, ⟨⟩⟩ mi hL ⟨hmi, hi_le, hrem⟩
    rw [hmi]
    elim_steps_nogrp
    · have hi_lt : i.toNat < cnt.toNat := hc
      have hoff_i : ((off + i).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hlen0.scratch_ok.scratch_buf_len, elim_zext32_toNat]; c0_bound
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      have hi32 : (off.toNat + i.toNat) % 2 ^ 32 = off.toNat + i.toNat :=
        Nat.mod_eq_of_lt (by omega)
      elim_steps_nogrp
      refine wp_join_state (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ mj => mj = m0)
        (fun _ new_need mj hmj => by
          rw [hmj]
          elim_steps!
          exact hL (cnt.toNat - (i + 1#32).toNat) (new_need, i + 1#32, ()) m0 (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun J hJ => by
          elim_steps_nogrp
          · elim_steps!; exact hJ _ _ rfl
          · have hlt_ar : ((s0.scratch.scratch_buf[(off.toNat + i.toNat) % 2 ^ 32]'(by
                rw [hlen0.scratch_ok.scratch_buf_len, hi32]; omega)).setWidth 64 + 2#64).toNat <
                s0.core.arena.length := by
              have hw_eq : s0.scratch.scratch_buf[(off.toNat + i.toNat) % 2 ^ 32]'(by
                  rw [hlen0.scratch_ok.scratch_buf_len, hi32]; omega) =
                  s0.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem (by rw [hlen0.scratch_ok.scratch_buf_len]; omega),
                  Option.getD_some]
                exact elim_getElem_congr hi32 _ _
              have hent := hent_i i.toNat hi_lt
              rw [← hw_eq] at hent
              rcases hent with hbin | har
              · exfalso; exact hbin (by simpa [hi32] using hc)
              · rw [hlen0.core_ok.arena_len_arr]; c0_bound
            elim_steps!; exact hJ _ _ rfl)
    · elim_steps!; exact hQ need
  · intro L hL; elim_steps!
    exact hL cnt.toNat (0#64, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩

/-! ## 4. `full_bve_weaken_wp` -/

public theorem full_bve_weaken_wp (Γ : Env)
    (hExt2 : ∀ a m Q X, Extend.Spec.fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hExtCl : ∀ a m Q X, Extend.Spec.fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, Watch.Spec.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, Spec.fullBveWeakenTmkSpec a m Q X →
      Func.wp Γ full_bve_weaken_body a m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hblk_lt, hoff_cnt, hent_i, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx harc hsc
  unfold Func.wp full_bve_weaken_body
  elim_steps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (i, ()) mi => ∃ si : FullState,
      i.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - i.toNat ∧
      FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
      si.core.cur_vars = s0.core.cur_vars ∧ si.core.fuel = s0.core.fuel ∧
      si.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      fullArenaClauseRefs si = fullArenaClauseRefs s0 ∧ (FullMem c si ⋆ R) mi)
    ?_ ?_
  · rintro L rem ⟨i, ⟨⟩⟩ mi hL ⟨si, hi_le, rfl, hdwi, htmki, hcvi, hfli, hscri, hrefsi, hmi⟩
    elim_steps_nogrp
    · have hi_lt : i.toNat < cnt.toNat := hc
      have hcv_le := hdwi.1.core_ok.cur_vars_le
      have hoff_i : ((off + i).setWidth 64).toNat < si.scratch.scratch_buf.length := by
        rw [hdwi.1.scratch_ok.scratch_buf_len, elim_zext32_toNat]; c0_bound
      let w := si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hoff_i
      have hw_orig : w = s0.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
        have hget := congrArg (·[off.toNat + i.toNat]?.getD 0#32) hscri
        rw [← hget]; dsimp only [w]
        rw [List.getElem?_eq_getElem (by rw [hdwi.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact elim_getElem_congr (by rw [elim_zext32_toNat]; c0_bound) _ _
      have hw_ok : FullBveWeakItemOk si.core w := by
        have hk := hent_i i.toNat hi_lt; rw [← hw_orig] at hk
        unfold FullBveWeakItemOk at hk ⊢
        split at hk
        · next hb => rw [ite_eq_left hb, hcvi]; exact hk
        · next hb =>
          rw [ite_eq_right hb]; change w.toNat ∈ fullArenaClauseRefs si; rw [hrefsi]; exact hk
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      elim_steps_nogrp
      refine wp_join0 (P := fun mj => ∃ sj : FullState,
        FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
        sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.fuel = s0.core.fuel ∧
        sj.scratch.scratch_buf = s0.scratch.scratch_buf ∧
        fullArenaClauseRefs sj = fullArenaClauseRefs s0 ∧ (FullMem c sj ⋆ R) mj)
        (fun _ mj ⟨sj, hdwj, htmkj, hcvj, hflj, hscrj, hrefsj, hmj⟩ => by
          elim_steps!
          exact hL (cnt.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj (by omega)
            ⟨sj, by omega, rfl, hdwj, htmkj, hcvj, hflj, hscrj, hrefsj, hmj⟩)
        ?_
      intro J hJ
      elim_steps_nogrp
      · have hbin : (w &&& 0x80000000#32) ≠ 0#32 := hc
        unfold FullBveWeakItemOk at hw_ok; rw [ite_eq_left hbin] at hw_ok
        let ot := w &&& 0x7FFFFFFF#32
        elim_call hExt2
        refine ⟨c, si, R, ⟨rfl, hdwi.2.2.2.2.1.2⟩, hdwi.1, hmi,
          fun ok1 s1 m1 hpres1 hlen1 ⟨hll1, hel1, hscr1, htmk1⟩ hm1 => ?_⟩
        change (FullMem c s1 ⋆ R) m1 at hm1
        have hdw1 := fullDenseInvW_of_extPush hdwi hlen1 hpres1 hll1 hel1
        have hcore1 : s1.core = si.core := fullCoreState_agrees_with_scratch hpres1
        have hcv1 : s1.core.cur_vars = s0.core.cur_vars := by rw [hcore1]; exact hcvi
        have hfl1 : s1.core.fuel = s0.core.fuel := by rw [hcore1]; exact hfli
        have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s0 := by
          change fullArenaClauseRefsCore s1.core = _; rw [hcore1]; exact hrefsi
        have htmk1' : TmkZero s1 := tmkZero_congr htmki (by rw [hcore1]) htmk1
        have hscr1' : s1.scratch.scratch_buf = s0.scratch.scratch_buf := hscr1.trans hscri
        have hblk_max : blk_lit.toNat < 2 * c.max_vars := by
          have := hdw1.1.core_ok.cur_vars_le; omega
        have hot_max : (w &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
          have hcw := hdw1.1.core_ok.cur_vars_le; rw [← hcore1] at hw_ok; omega
        elim_steps_nogrp
        · elim_call hDelBin
          refine ⟨c, s1, R, rfl, hlen1, (denseWatchesInv_of_w hdw1).layout,
            hblk_max, hot_max, hm1,
            fun flags2 wvec2 wstk2 wu2 nb2 m2 hlen2 _ hmw2 hm2 => ?_⟩
          let s2 : FullState := { s1 with core := { s1.core with
            flags := flags2, wvec := wvec2, wstk := wstk2, wusable := wu2, num_binary := nb2 } }
          have hdw2 := fullDenseInvW_of_deleteBinary hdw1 hlen2 (hmw2 F_cur hdw1.2.1.watches)
          have htmk2 : TmkZero s2 := tmkZero_congr htmk1' rfl rfl
          have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0 := by
            unfold fullArenaClauseRefs fullArenaClauseRefsCore; exact hrefs1
          elim_steps!; exact hJ _ ⟨s2, hdw2, htmk2, hcv1, hfl1, hscr1', hrefs2, hm2⟩
        · elim_steps!; exact hQ false s1 m1 hdw1 htmk1' hcv1 hfl1 hscr1' hrefs1 hm1
      · have hi32 : (off.toNat + i.toNat) % 2 ^ 32 = off.toNat + i.toNat :=
          Nat.mod_eq_of_lt (by omega)
        have hw_eq_si : w = si.scratch.scratch_buf[off.toNat + i.toNat]'(by
            rw [hdwi.1.scratch_ok.scratch_buf_len]; omega) := by
          have hget := List.getElem?_eq_getElem (by
            rw [hdwi.1.scratch_ok.scratch_buf_len]; omega :
              off.toNat + i.toNat < si.scratch.scratch_buf.length)
          have hs := congrArg (fun l : List (BitVec 32) => l[off.toNat + i.toNat]?.getD 0#32) hscri
          rw [← hw_orig] at hs
          rw [hget, Option.getD_some] at hs; exact hs.symm
        have hnobin : (w &&& 0x80000000#32) = 0#32 := by
          rw [hw_eq_si]; simpa [hi32] using hc
        unfold FullBveWeakItemOk at hw_ok; rw [ite_eq_right (fun hn => hn hnobin)] at hw_ok
        have href_w : w.toNat ∈ fullArenaClauseRefs si := hw_ok
        have hwf_w := hdwi.2.1.arena.refs_wf w.toNat href_w
        have hal_le := hdwi.1.core_ok.arena_len_le
        elim_call hExtCl
        refine ⟨c, si, R, ⟨rfl, hdwi.2.2.2.2.1.2⟩, hdwi.1, hmi,
          fun ok1 s1 m1 hpres1 hlen1 ⟨hll1, hel1, hscr1, htmk1⟩ hm1 => ?_⟩
        change (FullMem c s1 ⋆ R) m1 at hm1
        have hdw1 := fullDenseInvW_of_extPush hdwi hlen1 hpres1 hll1 hel1
        have hcore1 : s1.core = si.core := fullCoreState_agrees_with_scratch hpres1
        have hcv1 : s1.core.cur_vars = s0.core.cur_vars := by rw [hcore1]; exact hcvi
        have hfl1 : s1.core.fuel = s0.core.fuel := by rw [hcore1]; exact hfli
        have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s0 := by
          change fullArenaClauseRefsCore s1.core = _; rw [hcore1]; exact hrefsi
        have href_w1 : w.toNat ∈ fullArenaClauseRefs s1 := by
          change w.toNat ∈ fullArenaClauseRefsCore s1.core; rw [hcore1]; exact href_w
        have htmk1' : TmkZero s1 := tmkZero_congr htmki (by rw [hcore1]) htmk1
        have hscr1' : s1.scratch.scratch_buf = s0.scratch.scratch_buf := hscr1.trans hscri
        have hal1 : s1.core.arena_len ≤ c.arena_cap := by rw [hcore1]; exact hal_le
        have hw_ar0 : (w.setWidth 64).toNat < s1.core.arena.length := by
          rw [hlen1.core_ok.arena_len_arr, elim_zext32_toNat]; omega
        have hw_ar2 : (w.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
          rw [hlen1.core_ok.arena_len_arr]; c0_bound
        elim_steps_nogrp
        · have h_ar_len : (s1.core.arena.set (w.setWidth 64).toNat
              (s1.core.arena[(w.setWidth 64).toNat]'hw_ar0 ||| 524288#32)).length =
              s1.core.arena.length := List.length_set
          have hw_ar2' := hw_ar2
          dsimp only [w] at hw_ar0 hw_ar2' h_ar_len
          elim_steps!
          let ar2 := s1.core.arena.set w.toNat (fullArenaHdr s1 w.toNat ||| 0x00080000#32)
          let ag2 := s1.core.arena_garbage + 3#64 +
            (s1.core.arena[(w.setWidth 64 + 2#64).toNat]'hw_ar2).setWidth 64
          let s2 : FullState :=
            { s1 with core := { s1.core with arena := ar2, arena_garbage := ag2 } }
          have hdw2 := fullDenseInvW_of_markGarb_zero hdw1 href_w1 ag2
          have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0 := by
            have hmg := hdw1.2.1.arena.markGarb hdw1.1.core_ok href_w1 ag2
            exact hmg.1.trans hrefs1
          have htmk2 : TmkZero s2 := tmkZero_congr htmk1' rfl rfl
          have hw_ar_eq : s1.core.arena[(w.setWidth 64).toNat]'hw_ar0 =
              fullArenaHdr s1 w.toNat := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by rw [hlen1.core_ok.arena_len_arr]; omega),
              Option.getD_some]
            exact elim_getElem_congr (elim_zext32_toNat w) _ _
          have hm2 : (FullMem c s2 ⋆ R) m :=
            (fun {st : FullState} (hx : (FullMem c st ⋆ R) m) (heq : st = s2) => heq ▸ hx) hm
              (by
                have hne : (w.setWidth 64).toNat ≠ (w.setWidth 64 + 2).toNat := by
                  rw [elim_zext32_toNat]; c0_bound
                have hwa : (w.setWidth 64).toNat = w.toNat := elim_zext32_toNat w
                dsimp only [w] at hne hw_ar_eq hwa
                dsimp only [s2, ar2, ag2, w]
                rw [List.getElem_set_ne hne, ← hw_ar_eq, ← hwa]; rfl)
          exact hJ _ ⟨s2, hdw2, htmk2, hcv1, hfl1, hscr1', hrefs2, hm2⟩
        · elim_steps!; exact hQ false s1 m1 hdw1 htmk1' hcv1 hfl1 hscr1' hrefs1 hm1
    · elim_steps!; exact hQ true si mi hdwi htmki hcvi hfli hscri hrefsi hmi
  · intro L hL; elim_steps!
    exact hL cnt.toNat (0#32, ()) m0
      ⟨s0, Nat.zero_le _, by simp, hdw0, htmk0, rfl, rfl, rfl, rfl, hm0⟩

/-! ## 5. `full_bve_weaken_unit_fid_wp` -/

public theorem full_bve_weaken_unit_fid_wp (Γ : Env)
    (hDelBin : ∀ a m Q X, Watch.Spec.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, Spec.fullBveWeakenTmkSpec a m Q X →
      Func.wp Γ full_bve_weaken_unit_fid_body a m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hblk_lt, hoff_cnt, hent_i, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr; have hext := c.hext
  unfold dimacsBound at hmx harc hsc hext
  unfold Func.wp full_bve_weaken_unit_fid_body
  elim_steps_nogrp
  · elim_steps!; exact hQ true s0 m0 hdw0 htmk0 rfl rfl rfl rfl hm0
  · elim_steps!; exact hQ false s0 m0 hdw0 htmk0 rfl rfl rfl rfl hm0
  · have hel_le0 := hdw0.2.2.2.2.1.2
    have hel_lt : s0.scratch.extend_len < c.extend_cap := by
      have hc' : ¬ c.extend_cap ≤ s0.scratch.extend_len := by
        simpa only [Nat.mod_eq_of_lt (by omega : s0.scratch.extend_len < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : c.extend_cap < 2 ^ 64)] using hc
      omega
    refine wp_loop_group (ts := [i32])
      (fun rem (i, ()) mi => ∃ si : FullState,
        i.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - i.toNat ∧
        FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
        si.core.cur_vars = s0.core.cur_vars ∧ si.core.fuel = s0.core.fuel ∧
        si.scratch.scratch_buf = s0.scratch.scratch_buf ∧
        si.scratch.extend_len = s0.scratch.extend_len ∧
        si.scratch.extend_stk = s0.scratch.extend_stk ∧
        fullArenaClauseRefs si = fullArenaClauseRefs s0 ∧ (FullMem c si ⋆ R) mi)
      ?_ ?_
    · rintro L rem ⟨i, ⟨⟩⟩ mi hL
        ⟨si, hi_le, rfl, hdwi, htmki, hcvi, hfli, hscri, heli, hestki, hrefsi, hmi⟩
      elim_steps_nogrp
      · have hi_lt : i.toNat < cnt.toNat := hc
        have hcv_le := hdwi.1.core_ok.cur_vars_le
        have hoff_i : ((off + i).setWidth 64).toNat < si.scratch.scratch_buf.length := by
          rw [hdwi.1.scratch_ok.scratch_buf_len, elim_zext32_toNat]; c0_bound
        let w := si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hoff_i
        have hw_orig : w = s0.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
          have hget := congrArg (·[off.toNat + i.toNat]?.getD 0#32) hscri
          rw [← hget]; dsimp only [w]
          rw [List.getElem?_eq_getElem (by rw [hdwi.1.scratch_ok.scratch_buf_len]; omega),
            Option.getD_some]
          exact elim_getElem_congr (by rw [elim_zext32_toNat]; c0_bound) _ _
        have hw_ok : FullBveWeakItemOk si.core w := by
          have hk := hent_i i.toNat hi_lt; rw [← hw_orig] at hk
          unfold FullBveWeakItemOk at hk ⊢
          split at hk
          · next hb => rw [ite_eq_left hb, hcvi]; exact hk
          · next hb =>
            rw [ite_eq_right hb]; change w.toNat ∈ fullArenaClauseRefs si; rw [hrefsi]; exact hk
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
        elim_steps_nogrp
        refine wp_join0 (P := fun mj => ∃ sj : FullState,
          FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
          sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.fuel = s0.core.fuel ∧
          sj.scratch.scratch_buf = s0.scratch.scratch_buf ∧
          sj.scratch.extend_len = s0.scratch.extend_len ∧
          sj.scratch.extend_stk = s0.scratch.extend_stk ∧
          fullArenaClauseRefs sj = fullArenaClauseRefs s0 ∧ (FullMem c sj ⋆ R) mj)
          (fun _ mj ⟨sj, hdwj, htmkj, hcvj, hflj, hscrj, helj, hestkj, hrefsj, hmj⟩ => by
            elim_steps!
            exact hL (cnt.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj (by omega)
              ⟨sj, by omega, rfl, hdwj, htmkj, hcvj, hflj, hscrj, helj, hestkj, hrefsj, hmj⟩)
          ?_
        intro J hJ
        elim_steps_nogrp
        · have hbin : (w &&& 0x80000000#32) ≠ 0#32 := hc
          unfold FullBveWeakItemOk at hw_ok; rw [ite_eq_left hbin] at hw_ok
          let ot := w &&& 0x7FFFFFFF#32
          have hblk_max : blk_lit.toNat < 2 * c.max_vars := by
            have := hdwi.1.core_ok.cur_vars_le; omega
          have hot_max : (w &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
            have := hdwi.1.core_ok.cur_vars_le; omega
          elim_call hDelBin
          refine ⟨c, si, R, rfl, hdwi.1, (denseWatchesInv_of_w hdwi).layout,
            hblk_max, hot_max, hmi,
            fun flags1 wvec1 wstk1 wu1 nb1 m1 hlen1 _ hmw1 hm1 => ?_⟩
          let s1 : FullState := { si with core := { si.core with
            flags := flags1, wvec := wvec1, wstk := wstk1, wusable := wu1, num_binary := nb1 } }
          have hdw1 := fullDenseInvW_of_deleteBinary hdwi hlen1 (hmw1 F_cur hdwi.2.1.watches)
          have htmk1 : TmkZero s1 := tmkZero_congr htmki rfl rfl
          have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s0 := by
            unfold fullArenaClauseRefs fullArenaClauseRefsCore; exact hrefsi
          elim_steps!
          exact hJ _ ⟨s1, hdw1, htmk1, hcvi, hfli, hscri, heli, hestki, hrefs1, hm1⟩
        · have hi32 : (off.toNat + i.toNat) % 2 ^ 32 = off.toNat + i.toNat :=
            Nat.mod_eq_of_lt (by omega)
          have hw_eq_si : w = si.scratch.scratch_buf[off.toNat + i.toNat]'(by
              rw [hdwi.1.scratch_ok.scratch_buf_len]; omega) := by
            have hget := List.getElem?_eq_getElem (by
              rw [hdwi.1.scratch_ok.scratch_buf_len]; omega :
                off.toNat + i.toNat < si.scratch.scratch_buf.length)
            have hs := congrArg (fun l : List (BitVec 32) => l[off.toNat + i.toNat]?.getD 0#32)
              hscri
            rw [← hw_orig] at hs
            rw [hget, Option.getD_some] at hs; exact hs.symm
          have hnobin : (w &&& 0x80000000#32) = 0#32 := by
            rw [hw_eq_si]; simpa [hi32] using hc
          unfold FullBveWeakItemOk at hw_ok; rw [ite_eq_right (fun hn => hn hnobin)] at hw_ok
          have href_w : w.toNat ∈ fullArenaClauseRefs si := hw_ok
          have hwf_w := hdwi.2.1.arena.refs_wf w.toNat href_w
          have hal_le := hdwi.1.core_ok.arena_len_le
          have hw_ar0 : (w.setWidth 64).toNat < si.core.arena.length := by
            rw [hdwi.1.core_ok.arena_len_arr, elim_zext32_toNat]; omega
          have hw_ar2 : (w.setWidth 64 + 2#64).toNat < si.core.arena.length := by
            rw [hdwi.1.core_ok.arena_len_arr]; c0_bound
          have h_ar_len : (si.core.arena.set (w.setWidth 64).toNat
              (si.core.arena[(w.setWidth 64).toNat]'hw_ar0 ||| 524288#32)).length =
              si.core.arena.length := List.length_set
          have hw_ar2' := hw_ar2
          dsimp only [w] at hw_ar0 hw_ar2' h_ar_len
          elim_steps!
          let ar1 := si.core.arena.set w.toNat (fullArenaHdr si w.toNat ||| 0x00080000#32)
          let ag1 := si.core.arena_garbage + 3#64 +
            (si.core.arena[(w.setWidth 64 + 2#64).toNat]'hw_ar2).setWidth 64
          let s1 : FullState :=
            { si with core := { si.core with arena := ar1, arena_garbage := ag1 } }
          have hdw1 := fullDenseInvW_of_markGarb_zero hdwi href_w ag1
          have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s0 := by
            have hmg := hdwi.2.1.arena.markGarb hdwi.1.core_ok href_w ag1
            exact hmg.1.trans hrefsi
          have htmk1 : TmkZero s1 := tmkZero_congr htmki rfl rfl
          have hw_ar_eq : si.core.arena[(w.setWidth 64).toNat]'hw_ar0 =
              fullArenaHdr si w.toNat := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by rw [hdwi.1.core_ok.arena_len_arr]; omega),
              Option.getD_some]
            exact elim_getElem_congr (elim_zext32_toNat w) _ _
          have hm1 : (FullMem c s1 ⋆ R) m :=
            (fun {st : FullState} (hx : (FullMem c st ⋆ R) m) (heq : st = s1) => heq ▸ hx) hm
              (by
                have hne : (w.setWidth 64).toNat ≠ (w.setWidth 64 + 2).toNat := by
                  rw [elim_zext32_toNat]; c0_bound
                have hwa : (w.setWidth 64).toNat = w.toNat := elim_zext32_toNat w
                dsimp only [w] at hne hw_ar_eq hwa
                dsimp only [s1, ar1, ag1, w]
                rw [List.getElem_set_ne hne, ← hw_ar_eq, ← hwa]; rfl)
          exact hJ _ ⟨s1, hdw1, htmk1, hcvi, hfli, hscri, heli, hestki, hrefs1, hm1⟩
      · have heli_lt : si.scratch.extend_len < si.scratch.extend_stk.length := by
          rw [hdwi.1.scratch_ok.extend_stk_len, heli]; exact hel_lt
        elim_steps!
        let val := (blk_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
        let s' : FullState := { si with scratch := { si.scratch with
          extend_stk := si.scratch.extend_stk.set si.scratch.extend_len val,
          extend_len := (BitVec.ofNat 64 si.scratch.extend_len + 1#64).toNat } }
        have hel_i_le := hdwi.2.2.2.2.1.2
        have hel_eq : (BitVec.ofNat 64 si.scratch.extend_len + 1#64).toNat =
            si.scratch.extend_len + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : si.scratch.extend_len < 2 ^ 64),
            show (1#64 : BitVec 64).toNat = 1 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have h_idx_eq : (BitVec.ofNat 64 si.scratch.extend_len).toNat =
            si.scratch.extend_len := Nat.mod_eq_of_lt (by omega)
        rw [h_idx_eq] at hm
        have hdw' := fullDenseInvW_of_extendPush1 hdwi
          (estk' := s'.scratch.extend_stk) (elen' := s'.scratch.extend_len)
          (by dsimp only [s']; rw [List.length_set, hdwi.1.scratch_ok.extend_stk_len])
          (by dsimp only [s']; rw [hel_eq, heli]; exact hel_lt)
        have htmk' : TmkZero s' := tmkZero_congr htmki rfl rfl
        have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s0 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; exact hrefsi
        exact hQ true s' _ hdw' htmk' hcvi hfli hscri hrefs' hm
    · intro L hL; elim_steps!
      exact hL cnt.toNat (0#32, ()) m0
        ⟨s0, Nat.zero_le _, by simp, hdw0, htmk0, rfl, rfl, rfl, rfl, rfl, rfl, hm0⟩

end LeanQbe.T.Examples.Kissat.Proof.Eliminate

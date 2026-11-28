/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveEnd
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# End-of-Collection Move-Redundant Entry WP (`Proof.Collect.WpMoveRed2`)

Canonical `Func.wp` proof for `full_move_red_end_m6` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Classical
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open scoped FullArenaTactics M6Tactics2a

public section

private def endState (s : FullState) (ar rsns : List (BitVec 32))
    (fred : BitVec 64) (sc : FullScratch) : FullState :=
  let c1 := { s.core with first_reducible := fred }
  let c2 := { c1 with rsns := rsns }
  { core := { c2 with arena := ar }, scratch := sc }

theorem full_move_red_end_m6_wp (Γ : Env)
    (hEndBuf : ∀ a m Q X, fullMoveRedEndBufSpec a m Q X →
      Γ "full_move_red_end_buf_m6" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullMoveRedEndSpec a m Q X →
      Func.wp Γ full_move_red_end_m6_body a m Q X := by
  rintro ⟨h, first_red, dst, ⟨⟩⟩ m Q X
    ⟨c, s, rw0, R, rfl, hlen, hfr_dst, hdst_cap, hrw0_pos, hmv_orig, hvals_tri, huniq, hm, hQ⟩
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have har_cap : c.arena_cap < 2 * dimacsBound := c.harena
  have har_len : s.core.arena.length = c.arena_cap := hlen.core_ok.arena_len_arr
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap :=
    hlen.scratch_ok.scratch_buf_len
  have hscr_bd : c.scratch_cap < 2 * dimacsBound := Nat.lt_trans c.hscr (by omega)
  have hrs_len : s.core.rsns.length = c.max_vars := hlen.core_ok.rsns_len
  have hrw0_le : rw0 ≤ dst.toNat - first_red.toNat := moveRangeChain_rw_le hmv_orig
  have h0_64 : (0#64).toNat = 0 := rfl
  have h2_64 : (2#64).toNat = 2 := rfl
  have h3_64 : (3#64).toNat = 3 := rfl
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun ⟨r, rwc, ⟨⟩⟩ mC => mC = m ∧ first_red.toNat ≤ r.toNat ∧ r.toNat ≤ dst.toNat ∧
      rwc.toNat ≤ rw0 ∧
      MoveRangeChain s.core.arena first_red.toNat r.toNat rwc.toNat ∧
      MoveRangeChain s.core.arena r.toNat dst.toNat (rw0 - rwc.toNat))
    (fun ⟨r, _, ⟨⟩⟩ _ => dst.toNat - r.toNat)
    (fun JL hLoop => by
      c0_hsteps
      exact hLoop ⟨first_red, 0#64, ⟨⟩⟩ m ⟨rfl, Nat.le_refl _, by omega, Nat.zero_le _,
        MoveRangeChain.empty, by rw [h0_64, Nat.sub_zero]; exact hmv_orig⟩)
    (fun JL ⟨r, rwc, ⟨⟩⟩ mL ⟨hmL_eq, hfr_r, hr_dst, hrwc_le, hmv_pre, hmv_rem⟩ hLoop => ?_)
  have hmeq : m = mL := hmL_eq.symm
  subst hmeq
  c0_hsplit
  · have hr_lt : r.toNat < dst.toNat := hc
    obtain ⟨rwRem, hclean_r, hsz3_r, hfit_r, hrw_step, hmv_rem'⟩ :=
      moveRangeChain_uncons hmv_rem hr_lt
    have hr0_lt : r.toNat < s.core.arena.length := by rw [har_len]; omega
    have hr2_eq : (r + 2#64).toNat = r.toNat + 2 := by
      rw [BitVec.toNat_add, h2_64, Nat.mod_eq_of_lt (by omega)]
    have hr2_lt : (r + 2#64).toNat < s.core.arena.length := by rw [hr2_eq, har_len]; omega
    let hdr := s.core.arena[r.toNat]'hr0_lt
    let sz := s.core.arena[(r + 2#64).toNat]'hr2_lt
    have hhdr_ar : s.core.arena[r.toNat]? = some hdr := List.getElem?_eq_getElem hr0_lt
    have hsz_ar : s.core.arena[r.toNat + 2]? = some sz := by
      rw [← hr2_eq]; exact List.getElem?_eq_getElem hr2_lt
    have hsz3 : 3 ≤ sz.toNat := by rwa [hsz_ar, Option.getD_some] at hsz3_r
    have hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat := by
      rwa [hsz_ar, Option.getD_some] at hfit_r
    have hclen_eq : (3 + sz.setWidth 64).toNat = 3 + sz.toNat := bv64_add3_zext_toNat sz
    have hr_next_eq : (r + (3 + sz.setWidth 64)).toNat = r.toNat + 3 + sz.toNat := by
      rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun ⟨rwc', ⟨⟩⟩ mJ => mJ = m ∧
        rwc'.toNat = rwc.toNat +
          (if (hdr &&& 0x00400000#32) ≠ 0#32 then 3 + sz.toNat else 0) ∧
        rwc'.toNat ≤ rw0) ?_ ?_
    · rintro _ ⟨rwc', ⟨⟩⟩ mJ ⟨hmJ, hrwc', hrwc'_le⟩
      c0_hsteps
      refine hLoop ⟨r + (3 + sz.setWidth 64), rwc', ⟨⟩⟩ mJ
        (by dsimp only; rw [hr_next_eq]; omega)
        ⟨hmJ, by rw [hr_next_eq]; omega, by rw [hr_next_eq]; omega, hrwc'_le, ?_, ?_⟩
      · rw [hr_next_eq]
        exact moveRangeChain_snoc_rw hmv_pre (by omega) hclean_r hsz3_r
          (by rw [hsz_ar, Option.getD_some])
          (by rw [hhdr_ar, hsz_ar, Option.getD_some, Option.getD_some]; exact hrwc'.symm)
      · have hrem_eq : rw0 - rwc'.toNat = rwRem := by
          rw [hhdr_ar, hsz_ar, Option.getD_some, Option.getD_some] at hrw_step; omega
        rw [hr_next_eq, hrem_eq]
        rw [hsz_ar, Option.getD_some] at hmv_rem'
        simpa only [Nat.add_assoc] using hmv_rem'
    · intro Js_w hJs_w
      c0_hsplit
      · have hred : (hdr &&& 0x00400000#32) ≠ 0#32 := hc
        have hadd_le : rwc.toNat + (3 + sz.toNat) ≤ rw0 := by
          rw [hhdr_ar, hsz_ar, Option.getD_some, Option.getD_some, ite_eq_left hred] at hrw_step
          omega
        c0_hsteps
        exact hJs_w ⟨rwc + (3 + sz.setWidth 64), ⟨⟩⟩ m ⟨rfl, by
          rw [ite_eq_left hred, BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega)],
          by rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega)]; exact hadd_le⟩
      · have hirr : (hdr &&& 0x00400000#32) = 0#32 := hc
        c0_hsteps
        exact hJs_w ⟨rwc, ⟨⟩⟩ m ⟨rfl, by rw [ite_eq_right (fun h => h hirr), Nat.add_zero], hrwc_le⟩
  · have hr_eq : r.toNat = dst.toNat := by have := hc; omega
    rw [hr_eq] at hmv_pre hmv_rem
    have hrw_rem : rw0 - rwc.toNat = 0 := moveRangeChain_empty_rw hmv_rem
    have hrwc_eq : rwc.toNat = rw0 := by omega
    have hhm_split : (array (t := i32) c.pArena (s.core.arena.take dst.toNat) ⋆
        (array (t := i32) (c.pArena + BitVec.ofNat 64 (4 * dst.toNat))
          (s.core.arena.drop dst.toNat) ⋆
        (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        (FullMemArenaOut c s ⋆ R)))) m := by
      have hm1 := hm
      rw [fullMem_eq_arenaOut, array32_split_at (by rw [har_len]; exact hdst_cap)] at hm1
      simpa only [sep_assoc] using hm1
    have harPre_eq : ∀ i, i < dst.toNat →
        (s.core.arena.take dst.toNat)[i]? = s.core.arena[i]? :=
      fun i hi => List.getElem?_take_of_lt hi
    have hmv_take : MoveRangeChain (s.core.arena.take dst.toNat)
        first_red.toNat dst.toNat rw0 := by
      rw [← hrwc_eq]
      exact moveRangeChain_congr_out (lo := first_red.toNat) (fun i _ hi => harPre_eq i hi)
        hmv_pre
    have huniq_take : MoveRedRsnUnique (s.core.arena.take dst.toNat) s.core.vals s.core.rsns
        s.core.cur_vars first_red.toNat dst.toNat := huniq
    c0_hsteps_nogrp
    · have hrw_scr : rw0 ≤ c.scratch_cap := by
        have := Nat.le_trans hc (Nat.mod_le _ _); omega
      c0_hsteps_nogrp; c0_call hEndBuf
      have hm_call : (array (t := i32) c.pArena (s.core.arena.take dst.toNat) ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
          FullMemArenaOut c s ⋆
          (array (t := i32) (c.pArena + BitVec.ofNat 64 (4 * dst.toNat))
            (s.core.arena.drop dst.toNat) ⋆ R)) m := by
        have hm1 := hhm_split
        simp only [sep_assoc] at hm1 ⊢
        rw [sep_right5_swap24] at hm1
        exact hm1
      refine ⟨c, s, s.core.arena.take dst.toNat, s.scratch.scratch_buf, rw0,
        array (t := i32) (c.pArena + BitVec.ofNat 64 (4 * dst.toNat))
          (s.core.arena.drop dst.toNat) ⋆ R,
        rfl, hlen, Nat.le_of_lt hfr_dst, hdst_cap,
        by rw [List.length_take, har_len]; exact Nat.min_eq_left hdst_cap,
        by rw [hscr_len]; exact hrw_scr, by rw [hscr_len]; exact hscr_bd,
        hmv_take, hvals_tri, huniq_take, hm_call,
        fun arOut bufOut rsns' fred' mid m' harOut hbufOut hrsnsOut
          hfr_mid hmid_dst hpre_out hmv_irred hmv_red hblk hrsn _ hm' => ?_⟩
      c0_hsteps
      let tail := s.core.arena.drop dst.toNat
      have htail_len : tail.length = c.arena_cap - dst.toNat := by simp [tail, har_len]
      have hsc'_ok : FullScratch.LengthsOk c { s.scratch with scratch_buf := bufOut } :=
        { hlen.scratch_ok with scratch_buf_len := by rw [hbufOut, hscr_len] }
      let ar' := arOut ++ tail
      have har'_len : ar'.length = c.arena_cap := by
        rw [List.length_append, harOut, htail_len]; omega
      have hm_end : (FullMem c (endState s ar' rsns' fred'
          { s.scratch with scratch_buf := bufOut }) ⋆ R) m' := by
        dsimp only [endState, ar']
        rw [fullMem_eq_arenaOut,
          array32_split_at (k := dst.toNat)
            (by rw [List.length_append, harOut, htail_len]; omega),
          List.take_left' harOut, List.drop_left' harOut,
          fullMemArenaOut_congr_arena_buf c s ar' rsns' fred' bufOut]
        have hm1 := hm'
        simp only [sep_assoc] at hm1 ⊢
        rw [sep_right5_rot4_2] at hm1
        exact hm1
      obtain ⟨_, hpre', hmv', hblk', hrsn'⟩ := end_buf_post_to_end_post hfr_dst hdst_cap rfl
        htail_len harOut hmid_dst hpre_out hmv_irred hmv_red hblk hrsn hmv_orig
      exact hQ ar' rsns' fred' { s.scratch with scratch_buf := bufOut } (dst.toNat - mid) m'
        har'_len hrsnsOut hsc'_ok rfl rfl rfl hpre' hmv' hblk' hrsn' hm_end
    · have hrw_ar : dst.toNat + rw0 ≤ c.arena_cap := by
        have hle := hc
        rw [hrwc_eq, Nat.mod_eq_of_lt (by omega : dst.toNat + rw0 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : c.arena_cap < 2 ^ 64)] at hle
        exact hle
      c0_hsteps_nogrp; c0_call hEndBuf
      let tail := s.core.arena.drop dst.toNat
      have htail_len : tail.length = c.arena_cap - dst.toNat := by simp [tail, har_len]
      have hp_eq : c.pArena + BitVec.ofNat 64 (4 * dst.toNat) = c.pArena + dst * 4#64 := by
        rw [bv64_mul4_eq_ofNat]
      have hm_call : (array (t := i32) c.pArena (s.core.arena.take dst.toNat) ⋆
          array (t := i32) (c.pArena + dst * 4#64) tail ⋆
          FullMemArenaOut c s ⋆
          (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R)) m := by
        rw [← hp_eq]
        have hm1 := hhm_split
        simp only [sep_assoc] at hm1 ⊢
        rw [sep_right5_swap34] at hm1
        exact hm1
      refine ⟨c, s, s.core.arena.take dst.toNat, tail, rw0,
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R,
        rfl, hlen, Nat.le_of_lt hfr_dst, hdst_cap,
        by rw [List.length_take, har_len]; exact Nat.min_eq_left hdst_cap,
        by rw [htail_len]; omega, by rw [htail_len]; omega, hmv_take, hvals_tri, huniq_take,
        hm_call, fun arOut bufOut rsns' fred' mid m' harOut hbufOut hrsnsOut
          hfr_mid hmid_dst hpre_out hmv_irred hmv_red hblk hrsn _ hm' => ?_⟩
      c0_hsteps
      have hbufOut_len : bufOut.length = c.arena_cap - dst.toNat := by rw [hbufOut, htail_len]
      let ar' := arOut ++ bufOut
      have har'_len : ar'.length = c.arena_cap := by
        rw [List.length_append, harOut, hbufOut_len]; omega
      have hm_end : (FullMem c (endState s ar' rsns' fred' s.scratch) ⋆ R) m' := by
        dsimp only [endState, ar']
        rw [fullMem_eq_arenaOut,
          array32_split_at (k := dst.toNat)
            (by rw [List.length_append, harOut, hbufOut_len]; omega),
          List.take_left' harOut, List.drop_left' harOut, hp_eq,
          fullMemArenaOut_congr_arena_buf c s ar' rsns' fred' s.scratch.scratch_buf]
        have hm1 := hm'
        simp only [sep_assoc] at hm1 ⊢
        rw [sep_right5_swap34] at hm1
        exact hm1
      obtain ⟨_, hpre', hmv', hblk', hrsn'⟩ := end_buf_post_to_end_post hfr_dst hdst_cap rfl
        hbufOut_len harOut hmid_dst hpre_out hmv_irred hmv_red hblk hrsn hmv_orig
      exact hQ ar' rsns' fred' s.scratch (dst.toNat - mid) m' har'_len hrsnsOut
        hlen.scratch_ok rfl rfl rfl hpre' hmv' hblk' hrsn' hm_end
    ·   c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun ⟨p, ⟨⟩⟩ mF => first_red.toNat ≤ p.toNat ∧ p.toNat ≤ dst.toNat ∧
            ∃ arCurr : List (BitVec 32), arCurr.length = c.arena_cap ∧
              (∀ i < first_red.toNat, arCurr[i]? = s.core.arena[i]?) ∧
              (∀ i, p.toNat ≤ i → i < c.arena_cap → arCurr[i]? = s.core.arena[i]?) ∧
              ∃ rwPre rwRem, rwPre + rwRem = rw0 ∧
                MoveRangeChain s.core.arena first_red.toNat p.toNat rwPre ∧
                MoveRangeChain s.core.arena p.toNat dst.toNat rwRem ∧
                MoveRangeChain arCurr first_red.toNat p.toNat rwPre ∧
              (∀ r, RefInChain s.core.arena first_red.toNat p.toNat r →
                RefInChain arCurr first_red.toNat p.toNat r) ∧
              (∀ r, RefInChain arCurr first_red.toNat p.toNat r →
                (arCurr[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
                RefInChain s.core.arena first_red.toNat dst.toNat r ∧
                (arCurr[r + 2]?.getD 0#32).toNat = (s.core.arena[r + 2]?.getD 0#32).toNat ∧
                ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat,
                  arCurr[r + 3 + j]? = s.core.arena[r + 3 + j]?) ∧
              (FullMem c { s with core := { s.core with arena := arCurr } } ⋆ R) mF)
          (fun ⟨p, ⟨⟩⟩ _ => dst.toNat - p.toNat)
          (fun Jf hFb => by
            c0_hsteps
            exact hFb ⟨first_red, ⟨⟩⟩ m ⟨Nat.le_refl _, by omega, s.core.arena, har_len,
              fun _ _ => rfl, fun _ _ _ => rfl, 0, rw0, Nat.zero_add _,
              MoveRangeChain.empty, hmv_orig, MoveRangeChain.empty,
              fun _ h => absurd (refInChain_bounds h).2 (Nat.not_lt_of_ge (refInChain_bounds h).1),
              fun _ h => absurd (refInChain_bounds h).2 (Nat.not_lt_of_ge (refInChain_bounds h).1),
              hm⟩)
          (fun Jf ⟨p, ⟨⟩⟩ mF ⟨hfr_p, hp_dst, arCurr, harC_len, harC_pre, harC_suf,
              rwPre, rwRem, hrw_sum, hmv_p, hmv_r, hmvC_p, hrc_fwd, hblkC, hmF⟩ hFb => ?_)
        c0_hsplit
        · have hp_lt : p.toNat < dst.toNat := hc
          obtain ⟨rwRem', hclean_p, hsz3_p, hfit_p, hrw_step, hmv_r'⟩ :=
            moveRangeChain_uncons hmv_r hp_lt
          have hp0_lt : p.toNat < arCurr.length := by rw [harC_len]; omega
          have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
            rw [BitVec.toNat_add, h2_64, Nat.mod_eq_of_lt (by omega)]
          have hp2_lt : (p + 2#64).toNat < arCurr.length := by rw [hp2_eq, harC_len]; omega
          let hdr := arCurr[p.toNat]'hp0_lt
          let sz := arCurr[(p + 2#64).toNat]'hp2_lt
          have hhdr_ar : s.core.arena[p.toNat]? = some hdr := by
            dsimp [hdr]; rw [← harC_suf p.toNat (Nat.le_refl _) (by omega)]
            exact List.getElem?_eq_getElem hp0_lt
          have hsz_ar : s.core.arena[p.toNat + 2]? = some sz := by
            have h1 : arCurr[(p + 2#64).toNat]? = some sz := List.getElem?_eq_getElem hp2_lt
            rw [hp2_eq, harC_suf (p.toNat + 2) (by omega) (by omega)] at h1; exact h1
          have hclean : (hdr &&& 0x00880000#32) = 0#32 := by
            rwa [hhdr_ar, Option.getD_some] at hclean_p
          have hsz3 : 3 ≤ sz.toNat := by rwa [hsz_ar, Option.getD_some] at hsz3_p
          have hfit : p.toNat + 3 + sz.toNat ≤ dst.toNat := by
            rwa [hsz_ar, Option.getD_some] at hfit_p
          have hclen_eq : (3 + sz.setWidth 64).toNat = 3 + sz.toNat := bv64_add3_zext_toNat sz
          have hp_next_eq : (p + 3 + sz.setWidth 64).toNat = p.toNat + 3 + sz.toNat := by
            rw [BitVec.add_assoc, BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega),
              Nat.add_assoc]
          c0_hsteps
          let arCurr' := arCurr.set p.toNat (hdr &&& ~~~0x00200000#32)
          have hcl_p := bv32_clear_0020_props hclean
          have hmF' : (FullMem c
              { s with core := { s.core with arena := arCurr' } } ⋆ R) m := hm
          have harC'_pre_m : MoveRangeChain arCurr' first_red.toNat p.toNat rwPre :=
            moveRangeChain_congr_out (fun i _ hi => by
              dsimp [arCurr']; exact List.getElem?_set_ne (by omega)) hmvC_p
          have harC'_0 : arCurr'[p.toNat]? = some (hdr &&& ~~~0x00200000#32) := by
            dsimp [arCurr']; exact List.getElem?_set_self hp0_lt
          have harC'_2 : arCurr'[p.toNat + 2]? = some sz := by
            dsimp [arCurr']; rw [List.getElem?_set_ne (by omega), ← hsz_ar]
            exact harC_suf (p.toNat + 2) (by omega) (by omega)
          have hmvC'_next : MoveRangeChain arCurr' first_red.toNat (p.toNat + 3 + sz.toNat)
              (rwPre + if (hdr &&& 0x00400000#32) ≠ 0#32 then 3 + sz.toNat else 0) :=
            moveRangeChain_snoc_rw harC'_pre_m (by omega)
              (by rw [harC'_0, Option.getD_some]; exact hcl_p.1)
              (by rw [harC'_2, Option.getD_some]; exact hsz3)
              (by rw [harC'_2, Option.getD_some])
              (by rw [harC'_0, harC'_2, Option.getD_some, Option.getD_some, hcl_p.2.1])
          have hmv_next : MoveRangeChain s.core.arena first_red.toNat (p.toNat + 3 + sz.toNat)
              (rwPre + if (hdr &&& 0x00400000#32) ≠ 0#32 then 3 + sz.toNat else 0) :=
            moveRangeChain_snoc_rw hmv_p (by omega) hclean_p hsz3_p
              (by rw [hsz_ar, Option.getD_some])
              (by rw [hhdr_ar, hsz_ar, Option.getD_some, Option.getD_some])
          refine hFb ⟨p + 3 + sz.setWidth 64, ⟨⟩⟩ m
            (by dsimp only; rw [hp_next_eq]; omega)
            ⟨by rw [hp_next_eq]; omega, by rw [hp_next_eq]; omega, arCurr',
              by simp [arCurr', harC_len],
              fun i hi => by
                dsimp [arCurr']; rw [List.getElem?_set_ne (by omega)]; exact harC_pre i hi,
              fun i hi1 hi2 => by
                rw [hp_next_eq] at hi1; dsimp [arCurr']
                rw [List.getElem?_set_ne (by omega)]; exact harC_suf i (by omega) hi2,
              rwPre + if (hdr &&& 0x00400000#32) ≠ 0#32 then 3 + sz.toNat else 0, rwRem',
              by rw [hhdr_ar, hsz_ar, Option.getD_some, Option.getD_some] at hrw_step; omega,
              by rw [hp_next_eq]; exact hmv_next,
              by rw [hp_next_eq]
                 rw [hsz_ar, Option.getD_some] at hmv_r'
                 simpa only [Nat.add_assoc] using hmv_r',
              by rw [hp_next_eq]; exact hmvC'_next,
              fun ir hir => ?_, fun ir hir => ?_, hmF'⟩
          · rw [hp_next_eq] at hir
            rcases refInChain_split hmv_p hir with hir_pre | hir_new
            · have hir_old := hrc_fwd ir hir_pre
              exact refInChain_append_left (by omega)
                (refInChain_congr_out (fun i _ hi => by
                  dsimp [arCurr']; exact List.getElem?_set_ne (by omega)) hir_old)
            · have hir_eq : ir = p.toNat := refInChain_single (by
                  rw [hsz_ar, Option.getD_some]) hir_new
              subst hir_eq
              exact refInChain_append_right harC'_pre_m
                (RefInChain.head (by omega) (by rw [harC'_0, Option.getD_some]; exact hcl_p.1)
                  (by rw [harC'_2, Option.getD_some]; exact hsz3)
                  (by rw [harC'_2, Option.getD_some]; omega))
          · rw [hp_next_eq] at hir
            rcases refInChain_split harC'_pre_m hir with hir_pre | hir_new
            · have hir_b := refInChain_bounds hir_pre
              have hir_old : RefInChain arCurr first_red.toNat p.toNat ir :=
                refInChain_congr_out (fun i _ hi => by
                  dsimp [arCurr']; exact (List.getElem?_set_ne (by omega)).symm) hir_pre
              have hir_fit := (refInChain_of_moveRangeChain hmvC_p hir_old).2.2.2
              obtain ⟨h0, hrc, hsz_i, hcp_i⟩ := hblkC ir hir_old
              refine ⟨by dsimp [arCurr']; rw [List.getElem?_set_ne (by omega)]; exact h0,
                hrc, by dsimp [arCurr']; rw [List.getElem?_set_ne (by omega)]; exact hsz_i,
                fun j hj => ?_⟩
              dsimp [arCurr']
              rw [List.getElem?_set_ne (by omega)]
              exact hcp_i j hj
            · have hir_eq : ir = p.toNat := refInChain_single (by
                  rw [harC'_2, Option.getD_some]) hir_new
              subst hir_eq
              refine ⟨by rw [harC'_0, Option.getD_some]; exact hcl_p.2.2,
                refInChain_append_left (by omega) (refInChain_append_right hmv_p
                  (RefInChain.head (by omega) hclean_p hsz3_p
                    (by rw [hsz_ar, Option.getD_some]; omega))),
                by rw [harC'_2, hsz_ar], fun j hj => ?_⟩
              dsimp [arCurr']
              rw [List.getElem?_set_ne (by omega), ← harC_suf (p.toNat + 3 + j) (by omega)
                (by rw [hsz_ar, Option.getD_some] at hj; omega)]
        · have hp_eq : p.toNat = dst.toNat := by have := hc; omega
          rw [hp_eq] at hmv_r hmvC_p hrc_fwd hblkC
          have hrw_rem0 : rwRem = 0 := moveRangeChain_empty_rw hmv_r
          have hrw_pre_eq : rwPre = rw0 := by omega
          rw [hrw_pre_eq] at hmvC_p
          c0_hsteps
          have hm_ret : (FullMem c (endState s arCurr s.core.rsns first_red s.scratch) ⋆ R)
              m := hm
          refine hQ arCurr s.core.rsns first_red s.scratch rw0 m harC_len hrs_len
            hlen.scratch_ok rfl rfl rfl harC_pre hmvC_p (fun r hr => ?_) (fun v hv => ?_) hm_ret
          · obtain ⟨h0, hsrc, hsz_r, hcp_r⟩ := hblkC r hr
            exact ⟨h0, r, hsrc, hsz_r, hcp_r⟩
          · dsimp only
            by_cases hcond : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                RefInChain s.core.arena first_red.toNat dst.toNat
                  (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                  0x00200000#32) ≠ 0#32 ∧
                ∃ j, j < (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                    0#32).toNat ∧
                  let lit := (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                    j]?.getD 0#32).toNat
                  lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
            · rw [ite_eq_left hcond]
              have hr0_fit := (refInChain_of_moveRangeChain hmv_orig hcond.2.2.1).2.2.2
              have hrc_curr := hrc_fwd _ hcond.2.2.1
              have h1 := hblkC _ hrc_curr
              refine ⟨hcond.1, hcond.2.1, by omega, hrc_curr, h1.2.2.1, h1.2.2.2⟩
            · rw [ite_eq_right hcond]

end

end LeanQbe.T.Examples.Kissat.Proof.Collect

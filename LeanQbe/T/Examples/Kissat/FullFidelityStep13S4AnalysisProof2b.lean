/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Analysis
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofMin2
public import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-B Proof 2b (`full_shrink_blk_bool_m8`)

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for Step-13 `fidStep13S4ShrinkBlkBoolM8Fn`
(`full_shrink_blk_bool_m8`, with `L6a` hoisted `u64 alen = h->arena_len;`) against
`FullM8CoreParity.m8ShrinkBlkBoolSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. Block-Shrink Invariants & Helper Lemmas -/

structure S13ShrinkBaseInv (c : FullCfg) (s : FullState)
    (mrk : List (BitVec 8)) (mclr sstk wsort : List (BitVec 32))
    (mcl : Nat) (mcf : BitVec 64) (slen : Nat) (keep0 : List Nat) : Prop where
  mrk_len : mrk.length = c.max_vars
  mclr_len : mclr.length = c.max_vars
  mcl_le : mcl ≤ c.max_vars
  sstk_len : sstk.length = c.max_vars
  wsort_len : wsort.length = 2 * c.max_vars
  slen_le : slen ≤ s.core.cur_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv
    { s.core with mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf } keep0
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8_sstk : ∀ w < s.core.cur_vars, (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    ∃ j < slen, (sstk[j]?.getD 0#32).toNat = w
  sstk_lt : ∀ j < slen, (sstk[j]?.getD 0#32).toNat < s.core.cur_vars

theorem s13ShrinkBaseInv_core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk : List (BitVec 8)}
    {mclr sstk wsort : List (BitVec 32)} {mcl : Nat} {mcf ticks : BitVec 64} {slen : Nat}
    {keep0 : List Nat} (hb : S13ShrinkBaseInv c s mrk mclr sstk wsort mcl mcf slen keep0) :
    FullOtfsCoreInv c F0 (m8BlkState s s.core.tmp mrk mclr sstk wsort mcl mcf ticks) :=
  m8CoreInv_blk hcore hcore.1.core_ok.tmp_len_arr hb.mrk_len hb.mclr_len hb.mcl_le
    hb.sstk_len hb.wsort_len

abbrev S13ShrinkBlk8 (s : FullState) (mrk : List (BitVec 8)) (beg end_b : Nat) : Prop :=
  ∀ j, beg ≤ j → j < end_b → (mrk[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8

abbrev S13ShrinkStk8 (mrk : List (BitVec 8)) (sstk : List (BitVec 32))
    (slen : Nat) : Prop :=
  ∀ j < slen, (mrk[(sstk[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8

abbrev S13ShrinkAll8 (s : FullState) (blvl : BitVec 32) (mrk : List (BitVec 8))
    (t_lim idx_uip : Nat) : Prop :=
  ∀ w < s.core.cur_vars, (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    (s.core.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
    ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧
      (idx ≤ t_lim ∨ ShrinkResolved s.core mrk idx ∨ idx = idx_uip)

abbrev s13ShrinkRsnLit (s : FullState) (rsn : BitVec 32) (is_bin : Bool) (k : Nat) : Nat :=
  if is_bin = true then (rsn &&& 0x7FFFFFFF#32).toNat
  else (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat

abbrev S13ShrinkCovAt (s : FullState) (mrk : List (BitVec 8)) (t_in : Nat) (rsn : BitVec 32)
    (is_bin : Bool) (k : Nat) : Prop :=
  let q := s13ShrinkRsnLit s rsn is_bin k
  q = (s.core.trl[t_in]?.getD 0#32).toNat ∨ ∃ m < t_in,
    (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
    ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
      (mrk[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)

private theorem s13ShrinkOkInv_lvl_lt_no8 {s : FullState} {blvl : BitVec 32}
    {mrk1 : List (BitVec 8)}
    (h8 : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.core.lvl[w]?.getD 0#32).toNat = blvl.toNat)
    {ov : Nat} (hlov : (s.core.lvl[ov]?.getD 0#32).toNat < blvl.toNat) :
    ∀ w < s.core.cur_vars, (s.core.lvl[w]?.getD 0#32).toNat ≤ (s.core.lvl[ov]?.getD 0#32).toNat →
      (mrk1[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw hle =>
  Classical.byContradiction fun hnz => by have := h8 w hw hnz; omega

theorem s13Shrink_set_bit8_monos {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ov : Nat} (hcv : s.core.cur_vars ≤ c.max_vars) (hmrk_len : mrk.length = c.max_vars)
    (hov : ov < s.core.cur_vars) :
    let mrk2 := mrk.set ov (mrk[ov]?.getD 0#8 ||| 8#8)
    (∀ w, s.core.cur_vars ≤ w → mrk2[w]? = mrk[w]?) ∧
    (∀ w < s.core.cur_vars, (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ w < s.core.cur_vars, (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8) :=
  ⟨fun _ hw => List.getElem?_set_ne (by omega), fun w _ h => by
    by_cases hwe : w = ov
    · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some, bv8_and2_pres_or8]; exact h
    · rwa [List.getElem?_set_ne (Ne.symm hwe)], fun w _ h => by
    by_cases hwe : w = ov
    · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv8_and8_of_or8 _
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]⟩

private theorem s13Shrink_cov_lift {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)} {t_in i_lim : Nat}
    {rsn : BitVec 32} {is_bin_b : Bool} (ht_te : t_in < s.core.trail_end)
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hcov : ∀ k < i_lim, S13ShrinkCovAt s mrk1 t_in rsn is_bin_b k)
    {ot : BitVec 32} (hot_eq : ot.toNat = s13ShrinkRsnLit s rsn is_bin_b i_lim)
    (hstep : ot.toNat = (s.core.trl[t_in]?.getD 0#32).toNat ∨ ∃ m < t_in,
      (s.core.trl[m]?.getD 0#32).toNat = ot.toNat ^^^ 1 ∧
      ((s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 ∨
        (mrk2[ot.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
        (mrk2[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)) :
    ∀ k < i_lim + 1, S13ShrinkCovAt s mrk2 t_in rsn is_bin_b k := by
  obtain ⟨_, hw0⟩ := hcore.2
  intro k hk; by_cases hki : k < i_lim
  · rcases hcov k hki with heq | ⟨m', hm', hmeq, hdep⟩
    · exact Or.inl heq
    · have hqlt : s13ShrinkRsnLit s rsn is_bin_b k / 2 < s.core.cur_vars := by
        have := hw0.trail_lits_lt m' (Nat.lt_trans hm' ht_te)
        have hln := litVar_litNeg (s13ShrinkRsnLit s rsn is_bin_b k)
        unfold litVar litNeg at hln; rw [← hln, ← hmeq]; omega
      refine Or.inr ⟨m', hm', hmeq, ?_⟩
      rcases hdep with h0 | h2 | h8
      · exact Or.inl h0
      · exact Or.inr (Or.inl (hm2 _ hqlt h2))
      · exact Or.inr (Or.inr (hm8 _ hqlt h8))
  · have hke : k = i_lim := by omega
    subst k; simpa only [S13ShrinkCovAt, ← hot_eq] using hstep

private theorem s13Shrink_step_pre_push8 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {blvl : BitVec 32} {beg end_b : Nat}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)}
    {mcl1 open_cnt slen t_lim idx_uip k_ot : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb : S13ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen keep0)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hblk_8 : S13ShrinkBlk8 s mrk1 beg end_b) (hsstk_8 : S13ShrinkStk8 mrk1 sstk1 slen)
    (h8_pre : S13ShrinkAll8 s blvl mrk1 t_lim idx_uip)
    (hcnt_pre : trailCount8 s.core.trl mrk1 (min (t_lim + 1) s.core.trail_end) ≤ open_cnt - 1)
    (hop_ge : 2 ≤ open_cnt) (hop_le : open_cnt ≤ (end_b - beg) + slen)
    (hslen : slen < s.core.cur_vars) {ot : BitVec 32} (hot : ot.toNat < 2 * s.core.cur_vars)
    (huip_te : idx_uip < s.core.trail_end) (hk_lt : k_ot < idx_uip)
    (hk_eq : (s.core.trl[k_ot]?.getD 0#32).toNat = ot.toNat ^^^ 1) (hk_tlim : k_ot ≤ t_lim)
    (hlov_eq : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = blvl.toNat) :
    let ov := ot >>> 1
    let mrk2 := mrk1.set ov.toNat (mrk1[ov.toNat]?.getD 0#8 ||| 8#8)
    let sstk2 := sstk1.set slen ov
    S13ShrinkBaseInv c s mrk2 mclr1 sstk2 wsort1 mcl1 mcf1 (slen + 1) keep0 ∧
    S13ShrinkBlk8 s mrk2 beg end_b ∧ S13ShrinkStk8 mrk2 sstk2 (slen + 1) ∧
    S13ShrinkAll8 s blvl mrk2 t_lim idx_uip ∧
    trailCount8 s.core.trl mrk2 (min (t_lim + 1) s.core.trail_end) ≤ (open_cnt + 1) - 1 ∧
    2 ≤ open_cnt + 1 ∧ open_cnt + 1 ≤ (end_b - beg) + (slen + 1) ∧
    (mrk2[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
  intro ov mrk2 sstk2
  obtain ⟨_, hw⟩ := hcore.2
  have hcv := hcore.1.core_ok.cur_vars_le
  have hov_nat : ov.toNat = ot.toNat / 2 := bv32_lshr_1 ot
  have hov_lt : ov.toNat < s.core.cur_vars := by rw [hov_nat]; omega
  obtain ⟨hab2, hmono2, hmono8⟩ := s13Shrink_set_bit8_monos hcv hb.mrk_len hov_lt
  have hmin2 := fullMinMarkInv_set_bit8 (s13ShrinkBaseInv_core hcore hb (ticks := 0#64))
    hb.min_inv hov_lt
  have hb2 : S13ShrinkBaseInv c s mrk2 mclr1 sstk2 wsort1 mcl1 mcf1 (slen + 1) keep0 := by
    refine ⟨by simp [mrk2, hb.mrk_len], hb.mclr_len, hb.mcl_le, by simp [sstk2, hb.sstk_len],
      hb.wsort_len, by omega, fun w hw' => (hab2 w hw').trans (hb.mrk_above w hw'),
      ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩,
      fun w hw' h2 => hmono2 w hw' (hb.mono2 w hw' h2), fun w hw' h8 => ?_, fun j hj => ?_⟩
    · by_cases hwe : w = ov.toNat
      · subst w; refine ⟨slen, by omega, ?_⟩
        dsimp only [sstk2]
        rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
      · dsimp only [mrk2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
        obtain ⟨j, hj, hje⟩ := hb.bit8_sstk w hw' h8
        exact ⟨j, by omega, by dsimp only [sstk2]; rwa [List.getElem?_set_ne (by omega)]⟩
    · dsimp only [sstk2]; by_cases hjs : j = slen
      · subst j; rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
        exact hov_lt
      · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hb.sstk_lt j (by omega)
  have hm8' : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 := hmono8
  refine ⟨hb2, fun j hj1 hj2 => hm8' _ (hblk_lt j hj1 hj2) (hblk_8 j hj1 hj2), fun j hj => ?_,
    fun w hw' h8 => ?_, ?_, by omega, by omega, ?_⟩
  · dsimp only [sstk2]; by_cases hjs : j = slen
    · subst j; rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
      dsimp only [mrk2]; rw [List.getElem?_set_self (by rw [hb.mrk_len]; omega), Option.getD_some]
      exact bv8_and8_of_or8 _
    · rw [List.getElem?_set_ne (Ne.symm hjs)]
      exact hm8' _ (hb.sstk_lt j (by omega)) (hsstk_8 j (by omega))
  · by_cases hwe : w = ov.toNat
    · subst w; refine ⟨by rw [hov_nat]; exact hlov_eq, k_ot, Nat.lt_trans hk_lt huip_te, ?_,
        Or.inl hk_tlim⟩
      have hln := litVar_litNeg ot.toNat; unfold litVar litNeg at hln
      rw [hk_eq, hln, hov_nat]
    · dsimp only [mrk2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
      obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_pre w hw' h8
      exact ⟨hl, idx, hidx_te, hidx_v, hdisj.elim Or.inl fun h => h.elim
        (fun h2 => Or.inr (Or.inl (shrinkResolved_mono hcore hmono2 hm8' h2))) (Or.inr ∘ Or.inr)⟩
  · have htc := trailCount8_set_bit8_le (trl := s.core.trl) (mrk := mrk1)
      (fun i j hi hj heq => hw.trail_vars_nodup i j (by omega) (by omega) heq)
      ov.toNat (min (t_lim + 1) s.core.trail_end) (Nat.min_le_right _ _)
    dsimp only [mrk2]; omega
  · rw [← hov_nat]; dsimp only [mrk2]
    rw [List.getElem?_set_self (by rw [hb.mrk_len]; omega), Option.getD_some]
    exact bv8_and8_of_or8 _

private theorem s13Shrink_step_pre_mark2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {blvl : BitVec 32} {beg end_b : Nat}
    {mrk1 mrk2 : List (BitVec 8)} {mclr2 sstk1 wsort2 : List (BitVec 32)}
    {mcl2 open_cnt slen t_lim idx_uip : Nat} {mcf2 : BitVec 64} {keep0 : List Nat}
    (hb : S13ShrinkBaseInv c s mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 slen keep0)
    (hmono2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ w < s.core.cur_vars, (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8))
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hblk_8 : S13ShrinkBlk8 s mrk1 beg end_b) (hsstk_8 : S13ShrinkStk8 mrk1 sstk1 slen)
    (h8_pre : S13ShrinkAll8 s blvl mrk1 t_lim idx_uip)
    (hcnt_pre : trailCount8 s.core.trl mrk1 (min (t_lim + 1) s.core.trail_end) ≤ open_cnt - 1) :
    S13ShrinkBlk8 s mrk2 beg end_b ∧ S13ShrinkStk8 mrk2 sstk1 slen ∧
    S13ShrinkAll8 s blvl mrk2 t_lim idx_uip ∧
    trailCount8 s.core.trl mrk2 (min (t_lim + 1) s.core.trail_end) ≤ open_cnt - 1 := by
  obtain ⟨_, hw⟩ := hcore.2
  have hm8 : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 := fun w hw' h => by rwa [hbit8 w hw']
  refine ⟨fun j hj1 hj2 => by rw [hbit8 _ (hblk_lt j hj1 hj2)]; exact hblk_8 j hj1 hj2,
    fun j hj => by rw [hbit8 _ (hb.sstk_lt j hj)]; exact hsstk_8 j hj, fun w hw' h8 => ?_, ?_⟩
  · rw [hbit8 w hw'] at h8
    obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_pre w hw' h8
    exact ⟨hl, idx, hidx_te, hidx_v, hdisj.elim Or.inl fun h => h.elim
      (fun h2 => Or.inr (Or.inl (shrinkResolved_mono hcore hmono2 hm8 h2))) (Or.inr ∘ Or.inr)⟩
  · have htc := trailCount8_eq_of_bit8_eq (trl := s.core.trl) (mrk1 := mrk1) (mrk2 := mrk2)
      (n := min (t_lim + 1) s.core.trail_end) (fun j hj => by
        have := hw.trail_lits_lt j (Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)); omega) hbit8
    rw [htc]; exact hcnt_pre

private theorem s13Shrink_blk_success_finish {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {beg end_b keepLen : Nat} {blvl : BitVec 32}
    (hbe : beg < end_b) (hek : end_b ≤ keepLen) (hkc : keepLen ≤ s.core.cur_vars)
    (hkeep_spec : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {mrk1 mrkf : List (BitVec 8)} {mclr1 mclrf sstk1 wsort1 tmp' : List (BitVec 32)}
    {mcl1 mclf slen idx_uip : Nat} {mcf1 mcff ticks1 : BitVec 64} {uip : BitVec 32}
    (hb : S13ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hmrkf_len : mrkf.length = c.max_vars) (hmclrf_len : mclrf.length = c.max_vars)
    (htmp_len : tmp'.length = c.max_vars)
    (hdomf : ∀ w < s.core.cur_vars, (mrkf[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcovf : mcff = 0#64 → ∀ w < s.core.cur_vars, (mrkf[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < mclf, (mclrf[k]?.getD 0#32).toNat = w)
    (hmono1f : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrkf[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (h8_to_2f : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrkf[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hnew2_only : ∀ w < s.core.cur_vars, (mrkf[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (huip_te : idx_uip < s.core.trail_end)
    (huip_eq : (s.core.trl[idx_uip]?.getD 0#32).toNat = uip.toNat)
    (huip_8 : (mrk1[uip.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (huip_lvl : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hres : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      w = uip.toNat / 2 ∨ ∃ idx < s.core.trail_end, idx_uip < idx ∧
        (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧ ShrinkResolved s.core mrk1 idx)
    (hblk1 : S13ShrinkBlk8 s mrk1 beg end_b)
    (htmp_out : ∀ k < keepLen, (k < beg ∨ end_b ≤ k) → tmp'[k]? = s.core.tmp[k]?)
    (htmp_beg : tmp'[beg]? = some (uip ^^^ 1#32))
    (htmp_rest : ∀ k, beg < k → k < end_b → tmp'[k]? = some 0xFFFFFFFF#32) :
    let keep' := ((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    let sf := m8BlkState s tmp' mrkf mclrf sstk1 wsort1 mclf mcff ticks1
    FullMinMarkInv sf.core keep' ∧
    (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur sf.core ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause keep')) ∧
    (∀ k, beg ≤ k → k < end_b → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) ∧
    (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (tmp'[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ sf.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (mrkf[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro keep' sf; obtain ⟨_, hw0⟩ := hcore.2
  have hcv := hcore.1.core_ok.cur_vars_le; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have huip_lt : uip.toNat < 2 * s.core.cur_vars := by
    rw [← huip_eq]; exact hw0.trail_lits_lt _ huip_te
  obtain ⟨hnuip_xor, hnuip_lt⟩ := bv32_xor1_toNat_lt huip_lt
  have hnuip_ne : (uip ^^^ 1#32) ≠ 0xFFFFFFFF#32 := by
    intro heq; have := congrArg BitVec.toNat heq
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; rw [hff] at this; omega
  have hmin_f : FullMinMarkInv sf.core keep' := by
    refine ⟨hdomf, hcovf, fun idx hi h2f => ?_⟩
    have hv_lt : (s.core.trl[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      have := hw0.trail_lits_lt idx hi; omega
    by_cases hv8 : (mrk1[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8
    · rcases hres _ hv_lt hv8 with hvu | ⟨idx2, hi2, _, hv2, hr2⟩
      · have hidx := hw0.trail_vars_nodup idx idx_uip hi huip_te (by rw [huip_eq]; exact hvu)
        subst hidx; left; rw [huip_eq, ← hnuip_xor, mem_filter_map_toNat_take]
        exact ⟨beg, by rw [htmp_len]; omega, uip ^^^ 1#32, htmp_beg, hnuip_ne, rfl⟩
      · have hidx := hw0.trail_vars_nodup idx idx2 hi hi2 hv2.symm; subst hidx
        exact Or.inr (by
          simpa [RsnCov, fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
            fullArenaHdrCore, fullArenaClauseSizeCore] using
              shrinkResolved_to_rem hcore hmono1f h8_to_2f hr2)
    · rcases hb.min_inv.rem_sound idx hi ((hnew2_only _ hv_lt h2f).resolve_right hv8) with hin | hok
      · rw [mem_filter_map_toNat_take] at hin; obtain ⟨k, hk, b, hkb, hne, hbn⟩ := hin
        have hkbnd : k < beg ∨ end_b ≤ k := by
          by_cases hlt_b : k < beg; · exact Or.inl hlt_b
          by_cases hge_e : end_b ≤ k; · exact Or.inr hge_e
          exfalso; have h8k := hblk1 k (by omega) (by omega)
          have htmp_b : (s.core.tmp[k]?.getD 0#32).toNat / 2 =
              (s.core.trl[idx]?.getD 0#32).toNat / 2 := by
            rw [hkb, Option.getD_some, hbn]; exact xor1_div2 _
          rw [htmp_b] at h8k; exact hv8 h8k
        left; rw [mem_filter_map_toNat_take]
        exact ⟨k, by rw [htmp_len]; omega, b, (htmp_out k (by omega) hkbnd).trans hkb, hne, hbn⟩
      · exact Or.inr (by
          simpa [RsnCov, fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
            fullArenaHdrCore, fullArenaClauseSizeCore] using remSound_lift_mrk2 hcore hmono1f hok)
  have hEnt_f : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur sf.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause keep') := by
    intro F_cur hw hEnt0
    have hwf := m8Witness_shrinkBlk hw (tmp1 := tmp') (mrk1 := mrkf) (mclr1 := mclrf)
      (sstk1 := sstk1) (wsort1 := wsort1) (mcl1 := mclf) (mcf1 := mcff) (ticks1 := ticks1)
    refine ⟨hwf, fullMinMark_entails hwf hmin_f hEnt0 fun l hl => ?_⟩
    rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
    obtain ⟨hlt, hfals, hm2⟩ := hkeep_spec k (by omega) (by rwa [hkb, Option.getD_some])
    have hlb : (s.core.tmp[k]?.getD 0#32).toNat = b.toNat := by rw [hkb, Option.getD_some]
    rw [hlb] at hlt hfals hm2
    exact ⟨hlt, hfals, Or.inr (hmono1f _ (by omega) (hb.mono2 _ (by omega) hm2))⟩
  have hlvl_f : ∀ k, beg ≤ k → k < end_b → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
    intro k hk1 hk2 hne; by_cases hkb : k = beg
    · subst k; rw [show tmp'[beg]?.getD 0#32 = uip ^^^ 1#32 by rw [htmp_beg, Option.getD_some],
        hnuip_xor, xor1_div2 uip.toNat, huip_lvl]
    · exfalso; rw [htmp_rest k (by omega) hk2, Option.getD_some] at hne; exact hne rfl
  refine ⟨hmin_f, hEnt_f, hlvl_f, fun k hk hne => ?_⟩
  by_cases hkbnd : k < beg ∨ end_b ≤ k
  · rw [htmp_out k hk hkbnd] at hne ⊢
    obtain ⟨hlt, hfals, hm2⟩ := hkeep_spec k hk hne
    exact ⟨hlt, hfals, hmono1f _ (by omega) (hb.mono2 _ (by omega) hm2)⟩
  · have hk1 : k = beg := by
      by_cases hke : k = beg; · exact hke
      exfalso; rw [htmp_rest k (by omega) (by omega), Option.getD_some] at hne; exact hne rfl
    subst k; rw [show tmp'[beg]?.getD 0#32 = uip ^^^ 1#32 by rw [htmp_beg, Option.getD_some]]
    exact ⟨hnuip_lt,
      (hw0.vals_false_iff _ hnuip_lt).mpr ⟨idx_uip, huip_te, by rw [huip_eq, hnuip_xor, xor1_xor1]⟩,
      h8_to_2f _ (by omega) (by rwa [hnuip_xor, xor1_div2 uip.toNat])⟩

/-! ## 2. Block-Shrink Sub-Expressions & Inner Resolution Loop -/

@[expose] def S13ShrinkAfterInv (c : FullCfg) (s : FullState) (blvl : BitVec 32) (beg end_b : Nat)
    (keep0 : List Nat) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, .bool, i32, i64] → Mem 64 → Prop :=
  fun (_, slen_a, failed_a, uip_a, _) m_a =>
    ∃ (mrk_a : List (BitVec 8)) (mclr_a sstk_a wsort_a : List (BitVec 32))
      (mcl_a : Nat) (mcf_a ticks_a : BitVec 64),
      S13ShrinkBaseInv c s mrk_a mclr_a sstk_a wsort_a mcl_a mcf_a slen_a.toNat keep0 ∧
      S13ShrinkStk8 mrk_a sstk_a slen_a.toNat ∧
      (FullMem c (m8BlkState s s.core.tmp mrk_a mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a) ⋆ R)
        m_a ∧
      (failed_a = false → uip_a ≠ 0xFFFFFFFF#32 →
        ∃ idx_uip < s.core.trail_end, (s.core.trl[idx_uip]?.getD 0#32).toNat = uip_a.toNat ∧
          (mrk_a[uip_a.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
          (s.core.lvl[uip_a.toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
          S13ShrinkBlk8 s mrk_a beg end_b ∧
          ∀ w < s.core.cur_vars, (mrk_a[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
            w = uip_a.toNat / 2 ∨ ∃ idx < s.core.trail_end, idx_uip < idx ∧
              (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧ ShrinkResolved s.core mrk_a idx)

@[expose] def S13ShrinkMainInv (c : FullCfg) (s : FullState) (blvl : BitVec 32) (beg end_b : Nat)
    (keep0 : List Nat) (R : Mem 64 → Prop) :
    Nat → Tup Val [i64, i64, .bool, i32, i64] → Mem 64 → Prop :=
  fun n (open_c, slen_c, failed_c, _, t_c, ()) m_c =>
    ∃ (mrk_c : List (BitVec 8)) (mclr_c sstk_c wsort_c : List (BitVec 32))
      (mcl_c : Nat) (mcf_c ticks_c : BitVec 64),
      n = (if failed_c = true then 0 else min t_c.toNat s.core.trail_end + 1) ∧
      S13ShrinkBaseInv c s mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c slen_c.toNat keep0 ∧
      S13ShrinkBlk8 s mrk_c beg end_b ∧ S13ShrinkStk8 mrk_c sstk_c slen_c.toNat ∧
      (FullMem c (m8BlkState s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c) ⋆ R)
        m_c ∧
      (failed_c = false →
        1 ≤ open_c.toNat ∧ open_c.toNat ≤ (end_b - beg) + slen_c.toNat ∧
        (∀ w < s.core.cur_vars, (mrk_c[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          (s.core.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
          ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧
            (idx ≤ t_c.toNat ∨ ShrinkResolved s.core mrk_c idx)) ∧
        trailCount8 s.core.trl mrk_c (min (t_c.toNat + 1) s.core.trail_end) ≤ open_c.toNat)

private def S13ShrinkClInv (c : FullCfg) (s : FullState) (blvl : BitVec 32) (beg end_b : Nat)
    (keep0 : List Nat) (t_next t_in csz : Nat) (rsn : BitVec 32) (is_bin : Bool)
    (R : Mem 64 → Prop) : Nat → Tup Val [i64, i64, .bool, i32] → Mem 64 → Prop :=
  fun n (open_i, slen_i, failed_i, i_bv, ()) m_i =>
    n = (if failed_i = true then 0 else csz - i_bv.toNat + 1) ∧ i_bv.toNat ≤ csz ∧
    ∃ (mrk_i : List (BitVec 8)) (mclr_i sstk_i wsort_i : List (BitVec 32))
      (mcl_i : Nat) (mcf_i ticks_i : BitVec 64),
      S13ShrinkBaseInv c s mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i slen_i.toNat keep0 ∧
      S13ShrinkBlk8 s mrk_i beg end_b ∧ S13ShrinkStk8 mrk_i sstk_i slen_i.toNat ∧
      (FullMem c (m8BlkState s s.core.tmp mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i) ⋆ R)
        m_i ∧
      (failed_i = false →
        2 ≤ open_i.toNat ∧ open_i.toNat ≤ (end_b - beg) + slen_i.toNat ∧
        S13ShrinkAll8 s blvl mrk_i t_next t_in ∧
        trailCount8 s.core.trl mrk_i (min (t_next + 1) s.core.trail_end) ≤ open_i.toNat - 1 ∧
        ∀ k < i_bv.toNat, S13ShrinkCovAt s mrk_i t_in rsn is_bin k)

@[expose] def s13ShrinkBlkBoolClearExpr (pMark pShrinkStk slen : Val i64) : Expr Val Cont [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js => .cons (fun p =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var slen, ())) fun p_12 =>
    .jnz (.var p_12.fst)
      (.let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p_13 =>
       .let_ (op64 (.add i64) (.var pShrinkStk) (.var p_13.fst)) fun p_14 =>
       .load i32 (.var p_14.fst) fun ld =>
       .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_15 =>
       .let_ (op64 (.add i64) (.var pMark) (.var p_15.fst)) fun p_16 =>
       .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_17 =>
       .let_ (op64 (.add i64) (.var pMark) (.var p_17.fst)) fun p_18 =>
       .load i8 (.var p_18.fst) fun ld =>
       .let_ (Op.mk (.trunc 32 8) (.imm 247, ())) fun p_19 =>
       .let_ (Op.mk (.zext 8 32) (.var ld, ())) fun p_20 =>
       .let_ (Op.mk (.zext 8 32) (.var p_19.fst, ())) fun p_21 =>
       .let_ (Op.mk (.and i32) (.var p_20.fst, .var p_21.fst, ())) fun p_22 =>
       .let_ (Op.mk (.trunc 32 8) (.var p_22.fst, ())) fun p_23 =>
       .store (.var p_23.fst) (.var p_16.fst)
         (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun p =>
          .jump Js.fst (.var p.fst, ())))
      (.ret (.imm false, ()))) .nil)
    (fun Js => .jump Js.fst (.imm 0, ()))

private theorem s13_shrink_blk_bool_clear_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep0 : List Nat} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) {mrk_a : List (BitVec 8)}
    {mclr_a sstk_a wsort_a : List (BitVec 32)} {mcl_a : Nat}
    {mcf_a ticks_a slen_a : Val i64} {m_a : Mem 64}
    (hb_a : S13ShrinkBaseInv c s mrk_a mclr_a sstk_a wsort_a mcl_a mcf_a slen_a.toNat keep0)
    (hm_a : (FullMem c (m8BlkState s s.core.tmp mrk_a mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a)
      ⋆ R) m_a)
    (hpost : ∀ mrk_f m_f,
      let sf := m8BlkState s s.core.tmp mrk_f mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a
      FullOtfsCoreInv c F0 sf → FullMinMarkInv sf.core keep0 →
      (∀ w, s.core.cur_vars ≤ w → mrk_f[w]? = s.core.mrk[w]?) →
      (∀ v < s.core.cur_vars, (mrk_f[v]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ w < s.core.cur_vars,
        (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_f[w]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c sf ⋆ R) m_f → Q (false, ()) m_f) :
    wp Γ Q X (s13ShrinkBlkBoolClearExpr c.pMark c.pShrinkStk slen_a) m_a := by
  dsimp only [s13ShrinkBlkBoolClearExpr]
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_f =>
      ∃ (mrk_f : List (BitVec 8)),
        n = slen_a.toNat - i_bv.toNat ∧ i_bv.toNat ≤ slen_a.toNat ∧ mrk_f.length = c.max_vars ∧
        (∀ w, s.core.cur_vars ≤ w → mrk_f[w]? = s.core.mrk[w]?) ∧
        FullMinMarkInv
          (m8BlkState s s.core.tmp mrk_f mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a).core keep0 ∧
        (∀ w < s.core.cur_vars,
          (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_f[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ w < s.core.cur_vars, (mrk_f[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          ∃ j, i_bv.toNat ≤ j ∧ j < slen_a.toNat ∧ (sstk_a[j]?.getD 0#32).toNat = w) ∧
        (FullMem c (m8BlkState s s.core.tmp mrk_f mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a) ⋆
          R) m_f)
    ?_ (fun Jf hJf => by
      ml_lets; exact hJf slen_a.toNat (0#64, ()) m_a ⟨mrk_a, rfl, Nat.zero_le _, hb_a.mrk_len,
        hb_a.mrk_above, hb_a.min_inv, hb_a.mono2, fun w hw h8 =>
          let ⟨j, hj, hjw⟩ := hb_a.bit8_sstk w hw h8; ⟨j, Nat.zero_le _, hj, hjw⟩, hm_a⟩)
  rintro Jf n ⟨i_bv, ⟨⟩⟩ m_f hJf ⟨mrk_f, rfl, hilen, hmrf_len, hab_f, hmin_f, hmono_f, h8_f, hm_f⟩
  let st_f := m8BlkState s s.core.tmp mrk_f mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hilt => ?_, fun hdone_f => ?_⟩
  · c0_cond hilt
    have hi_sstk : i_bv.toNat < st_f.scratch.shrink_stk.length := by
      dsimp only [st_f, m8BlkState, m8ShrinkBlkBoolState]; rw [hb_a.sstk_len]
      have := hb_a.slen_le; omega
    have hi_stk' : i_bv.toNat < sstk_a.length := by
      dsimp only [st_f, m8BlkState, m8ShrinkBlkBoolState] at hi_sstk; exact hi_sstk
    ml_ld c0_load_full_shrink_stk (s := st_f) (i := i_bv) hi_sstk hm_f
    let sv := sstk_a[i_bv.toNat]'hi_sstk
    have hsv_lt : sv.toNat < s.core.cur_vars := by
      have := hb_a.sstk_lt i_bv.toNat hilt
      rwa [List.getElem?_eq_getElem hi_stk', Option.getD_some] at this
    have hsv64 : (sv.setWidth 64).toNat = sv.toNat := bv_c0_zext32_64 sv
    have hmrk_sv : sv.toNat < mrk_f.length := by rw [hmrf_len]; omega
    have hmrk_sv' : (sv.setWidth 64).toNat < st_f.core.mrk.length := by
      dsimp only [st_f, m8BlkState, m8ShrinkBlkBoolState]; rw [hmrf_len, hsv64]; omega
    ml_ld c0_load_full_mrk (s := st_f) (i := sv.setWidth 64) hmrk_sv' hm_f
    ml_st m_f2, hm_s := c0_store_full_mrk (s := st_f) (i := sv.setWidth 64) _ hmrk_sv' hm_f
    let mrk_f2 := mrk_f.set sv.toNat (mrk_f[sv.toNat]?.getD 0#8 &&& 0xF7#8)
    have hm_f2 : (FullMem c (m8BlkState s s.core.tmp mrk_f2 mclr_a sstk_a wsort_a
        mcl_a mcf_a ticks_a) ⋆ R) m_f2 := by
      dsimp only [st_f, m8BlkState, m8ShrinkBlkBoolState, mrk_f2, sv] at hm_s ⊢
      simp only [bv_c0_zext32_64, Arg.val_var, bv8_and247_c0] at hm_s
      rw [List.getElem?_eq_getElem hmrk_sv, Option.getD_some]; exact hm_s
    have hcb_f := m8CoreInv_blk hcore hlen0.tmp_len_arr hmrf_len hb_a.mclr_len hb_a.mcl_le
      hb_a.sstk_len hb_a.wsort_len (mcf1 := mcf_a) (ticks1 := ticks_a)
    have hmin_f2 := fullMinMarkInv_clear_bit8 hcb_f hmin_f hsv_lt
    change FullMinMarkInv (m8BlkState s s.core.tmp mrk_f2 mclr_a sstk_a wsort_a
      mcl_a mcf_a ticks_a).core keep0 at hmin_f2
    have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := min_bv64_add1 (by have := hb_a.slen_le; omega)
    refine hJf (slen_a.toNat - (i_bv + 1).toNat) (i_bv + 1, ()) _ (by omega)
      ⟨mrk_f2, rfl, by omega, by simp [mrk_f2, hmrf_len],
        fun w hw => by dsimp only [mrk_f2]; rw [List.getElem?_set_ne (by omega)]; exact hab_f w hw,
        hmin_f2, fun w hw h2 => ?_, fun w hw h8 => ?_, hm_f2⟩
    · dsimp only [mrk_f2]; by_cases hwe : w = sv.toNat
      · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some, bv8_and2_pres_clear8]
        exact hmono_f _ hw h2
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hmono_f w hw h2
    · rw [hi1]; dsimp only [mrk_f2] at h8; by_cases hwe : w = sv.toNat
      · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some] at h8
        exact absurd (bv8_and8_clear _) h8
      · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
        obtain ⟨j, hj1, hj2, hjw⟩ := h8_f w hw h8; refine ⟨j, ?_, hj2, hjw⟩
        by_cases hji : j = i_bv.toNat
        · subst j; exfalso; apply hwe
          rw [← hjw, List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some]
        · omega
  · ml_lets; rw [wp]; c0_cond hdone_f
    have hno8_f : ∀ w < s.core.cur_vars, (mrk_f[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw => by
      by_cases hnz : (mrk_f[w]?.getD 0#8 &&& 8#8) = 0#8; · exact hnz
      obtain ⟨j, hj1, hj2, _⟩ := h8_f w hw hnz; omega
    exact hpost mrk_f m_f (m8CoreInv_blk hcore hlen0.tmp_len_arr hmrf_len hb_a.mclr_len hb_a.mcl_le
      hb_a.sstk_len hb_a.wsort_len) hmin_f hab_f hno8_f hmono_f hm_f

@[expose] def s13ShrinkBlkBoolAfterExpr (hdr beg end_b pTmp pMark pShrinkStk : Val i64)
    (xs : Tup Val [i64, i64, .bool, i32, i64]) : Expr Val Cont [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ =>
    s13ShrinkBlkBoolClearExpr pMark pShrinkStk xs.snd.fst) .nil)
    fun Js => .jnz (.var xs.snd.snd.fst) (.jump Js.fst ())
      (.let_ (Op.mk (.cmp .eq i32 .bool rfl)
          (.var xs.snd.snd.snd.fst, .imm 4294967295, ())) fun p_12 =>
       .jnz (.var p_12.fst) (.jump Js.fst ())
         (.group (sig := [[i64]]) (fun Js => .cons (fun p_14 =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_14.fst, .var end_b, ())) fun p_15 =>
           .jnz (.var p_15.fst)
             (.let_ (op64 (.mul i64) (.var p_14.fst) (.imm 4)) fun p =>
              .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
              .store (t := i32) (.imm 4294967295) (.var p.fst)
                (.let_ (op64 (.add i64) (.var p_14.fst) (.imm 1)) fun p =>
                 .jump Js.fst (.var p.fst, ())))
             (.let_ (op64 (.mul i64) (.var beg) (.imm 4)) fun p_16 =>
              .let_ (op64 (.add i64) (.var pTmp) (.var p_16.fst)) fun p_17 =>
              .let_ (Op.mk (.xor i32) (.var xs.snd.snd.snd.fst, .imm 1, ())) fun p_18 =>
              .store (.var p_18.fst) (.var p_17.fst)
                (.group (sig := [[i64]]) (fun Js => .cons (fun p_19 =>
                  .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                      (.var p_19.fst, .var xs.snd.fst, ())) fun p_20 =>
                  .jnz (.var p_20.fst)
                    (.let_ (op64 (.mul i64) (.var p_19.fst) (.imm 4)) fun p_21 =>
                     .let_ (op64 (.add i64) (.var pShrinkStk) (.var p_21.fst)) fun p_22 =>
                     .load i32 (.var p_22.fst) fun ld =>
                     .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_23 =>
                     .let_ (op64 (.add i64) (.var pMark) (.var p_23.fst)) fun p_24 =>
                     .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_25 =>
                     .let_ (op64 (.add i64) (.var pMark) (.var p_25.fst)) fun p_26 =>
                     .load i8 (.var p_26.fst) fun ld_8 =>
                     .let_ (Op.mk (.trunc 32 8) (.imm 247, ())) fun p_27 =>
                     .let_ (Op.mk (.zext 8 32) (.var ld_8, ())) fun p_28 =>
                     .let_ (Op.mk (.zext 8 32) (.var p_27.fst, ())) fun p_29 =>
                     .let_ (Op.mk (.and i32) (.var p_28.fst, .var p_29.fst, ())) fun p_30 =>
                     .let_ (Op.mk (.trunc 32 8) (.var p_30.fst, ())) fun p_31 =>
                     .store (.var p_31.fst) (.var p_24.fst)
                       (.let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p_32 =>
                        .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                          (.var hdr, .var ld, .var p_32.fst, ()) fun _ =>
                        .let_ (op64 (.add i64) (.var p_19.fst) (.imm 1)) fun p =>
                        .jump Js.fst (.var p.fst, ())))
                    (.ret (.imm true, ()))) .nil)
                  (fun Js => .jump Js.fst (.imm 0, ()))))) .nil)
           fun Js => .jump Js.fst (.var beg, ())))

theorem s13_shrink_blk_bool_after_wp {Γ : Env}
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {beg end_b : Val i64} {blvl : Val i32}
    {keepLen : Nat} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hbeg_end : beg.toNat < end_b.toNat)
    (hend_kl : end_b.toNat ≤ keepLen) (hkl_cv : keepLen ≤ s.core.cur_vars)
    (hblk_spec : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hkeep_spec : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hQ : ∀ (ok : Bool) tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m',
      let s' : FullState := m8BlkState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks'
      FullOtfsCoreInv c F0 s' →
      FullMinMarkInv s'.core
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (ok = false → tmp' = s.core.tmp) →
      (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
      (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
      ((((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup →
        (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
          s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
      (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (tmp'[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    {xs : Tup Val [i64, i64, .bool, i32, i64]} {m_a : Mem 64}
    (ha : S13ShrinkAfterInv c s blvl beg.toNat end_b.toNat
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) R xs m_a) :
    wp Γ Q X (s13ShrinkBlkBoolAfterExpr c.hdr beg end_b c.pTmp c.pMark c.pShrinkStk xs) m_a := by
  dsimp only [s13ShrinkBlkBoolAfterExpr]
  rcases xs with ⟨open_a, slen_a, failed_a, uip_a, t_a, ⟨⟩⟩
  rcases ha with ⟨mrk_a, mclr_a, sstk_a, wsort_a, mcl_a, mcf_a, ticks_a,
    hb_a, hsstk_a, hm_a, hsucc_a⟩
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  refine wp_join_group (ts := []) (fun () m_f => m_f = m_a) ?_ ?_
  · rintro J_fl ⟨⟩ m_f hm_f_eq; subst m_f; rw [Blocks.get_here]
    exact s13_shrink_blk_bool_clear_wp hcore hb_a hm_a fun mrk_f m_f hc hm ha h8 hm2 hmf =>
      hQ false s.core.tmp mrk_f mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a m_f hc hm ha h8 hm2
        (fun _ => rfl) (fun _ _ _ => rfl) (fun k hk1 hk2 _ => hblk_spec k hk1 hk2)
        (fun hnd _ => hnd) (fun _ hw hent => ⟨m8Witness_shrinkBlk hw, hent⟩)
        (fun k hk hne => let sp := hkeep_spec k hk hne; ⟨sp.1, sp.2.1, hm2 _ (by omega) sp.2.2⟩)
        hmf
  rintro J_fl hJ_fl
  ml_jnz; refine ⟨fun _ => by ml_lets; exact hJ_fl () m_a rfl, ?_⟩; intro hnfail
  ml_lets; ml_jnz; refine ⟨fun _ => by ml_lets; exact hJ_fl () m_a rfl, ?_⟩; intro huip_ne
  c0_cond huip_ne
  obtain ⟨idx_uip, huip_te, huip_eq, huip_8, huip_lvl, hblk_a, hres_a⟩ := hsucc_a hnfail huip_ne
  ml_lets
  refine wp_loop_group (ts := [i64]) (fun n (k_bv, ()) m_k =>
      ∃ (tmp_k : List (BitVec 32)),
        n = end_b.toNat - k_bv.toNat ∧ beg.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ end_b.toNat ∧
        tmp_k.length = c.max_vars ∧
        (∀ j < keepLen, (j < beg.toNat ∨ k_bv.toNat ≤ j) → tmp_k[j]? = s.core.tmp[j]?) ∧
        (∀ j, beg.toNat ≤ j → j < k_bv.toNat → tmp_k[j]? = some 0xFFFFFFFF#32) ∧
        (FullMem c (m8BlkState s tmp_k mrk_a mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a) ⋆ R)
          m_k)
    ?_ (fun Jk hJk => by
      ml_lets; exact hJk (end_b.toNat - beg.toNat) (beg, ()) m_a ⟨s.core.tmp, rfl, le_refl _,
        le_of_lt hbeg_end, hlen0.tmp_len_arr, fun _ _ _ => rfl, fun _ h1 h2 => by omega, hm_a⟩)
  rintro Jk n ⟨k_bv, ⟨⟩⟩ m_k hJk ⟨tmp_k, rfl, hbk, hke, htk_len, htk_out, htk_set, hm_k⟩
  let st_k := m8BlkState s tmp_k mrk_a mclr_a sstk_a wsort_a mcl_a mcf_a ticks_a
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hklt => ?_, ?_⟩
  · c0_cond hklt
    have hkt : k_bv.toNat < st_k.core.tmp.length := by
      dsimp only [st_k, m8BlkState, m8ShrinkBlkBoolState]; rw [htk_len]; omega
    ml_st m_k2, hm_s := c0_store_full_tmp (s := st_k) (i := k_bv) 0xFFFFFFFF#32 hkt hm_k
    ml_lets; let tmp_k2 := tmp_k.set k_bv.toNat 0xFFFFFFFF#32
    have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := min_bv64_add1 (by omega)
    refine hJk (end_b.toNat - (k_bv + 1).toNat) (k_bv + 1, ()) m_k2 (by omega)
      ⟨tmp_k2, rfl, by rw [hk1]; omega, by rw [hk1]; omega, by simp [tmp_k2, htk_len],
        fun j hj hjb => ?_, fun j hj1 hj2 => ?_,
        by dsimp only [st_k, m8BlkState, m8ShrinkBlkBoolState, tmp_k2] at hm_s ⊢; exact hm_s⟩
    · rw [hk1] at hjb; by_cases hjk : j = k_bv.toNat
      · omega
      · dsimp only [tmp_k2]; rw [List.getElem?_set_ne (Ne.symm hjk)]
        exact htk_out j hj (hjb.elim Or.inl fun h => Or.inr (by omega))
    · rw [hk1] at hj2; dsimp only [tmp_k2]; by_cases hjk : j = k_bv.toNat
      · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega)]
      · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact htk_set j hj1 (by omega)
  intro hkge; ml_lets; c0_cond hkge
  have hkb_end : k_bv = end_b := BitVec.eq_of_toNat_eq (by omega); subst k_bv
  have hbt : beg.toNat < st_k.core.tmp.length := by
    dsimp only [st_k, m8BlkState, m8ShrinkBlkBoolState]; rw [htk_len]; omega
  ml_st m_sf, hm_sf := c0_store_full_tmp (s := st_k) (i := beg) (uip_a ^^^ 1#32) hbt hm_k
  let tmp_f := tmp_k.set beg.toNat (uip_a ^^^ 1#32)
  have htf_len : tmp_f.length = c.max_vars := by simp [tmp_f, htk_len]
  have htf_out : ∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
      tmp_f[k]? = s.core.tmp[k]? := fun k hk hkb => by
    dsimp only [tmp_f]; rw [List.getElem?_set_ne (by omega)]; exact htk_out k hk hkb
  have htf_beg : tmp_f[beg.toNat]? = some (uip_a ^^^ 1#32) := by
    dsimp only [tmp_f]; rw [List.getElem?_set_self (by rw [htk_len]; omega)]
  have htf_rest : ∀ k, beg.toNat < k → k < end_b.toNat → tmp_f[k]? = some 0xFFFFFFFF#32 :=
    fun k hk1 hk2 => by
      dsimp only [tmp_f]; rw [List.getElem?_set_ne (by omega)]; exact htk_set k (by omega) hk2
  ml_lets
  refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_i =>
      ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32)) (mcl_i : Nat) (mcf_i : BitVec 64),
        n = slen_a.toNat - i_bv.toNat ∧ i_bv.toNat ≤ slen_a.toNat ∧
        mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
        (∀ w, s.core.cur_vars ≤ w → mrk_i[w]? = s.core.mrk[w]?) ∧
        (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
        (mcf_i = 0#64 → ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
          ∃ k < mcl_i, (mclr_i[k]?.getD 0#32).toNat = w) ∧
        (∀ w < s.core.cur_vars,
          (mrk_a[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ j < slen_a.toNat, j < i_bv.toNat →
          (mrk_i[(sstk_a[j]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
          (mrk_a[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk_a[w]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
        (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          ∃ j, i_bv.toNat ≤ j ∧ j < slen_a.toNat ∧ (sstk_a[j]?.getD 0#32).toNat = w) ∧
        (FullMem c (m8BlkState s tmp_f mrk_i mclr_i sstk_a wsort_a mcl_i mcf_i ticks_a) ⋆ R)
          m_i)
    ?_ (fun Ji hJi => by
      ml_lets; exact hJi slen_a.toNat (0#64, ()) m_sf ⟨mrk_a, mclr_a, mcl_a, mcf_a, rfl,
        Nat.zero_le _, hb_a.mrk_len, hb_a.mclr_len, hb_a.mcl_le, hb_a.mrk_above,
        hb_a.min_inv.mrk_dom, hb_a.min_inv.clr_cov, fun _ _ h => h, fun _ _ h => by simp at h,
        fun _ _ h => Or.inl h, fun w hw h8 =>
          let ⟨j, hj, hjw⟩ := hb_a.bit8_sstk w hw h8; ⟨j, Nat.zero_le _, hj, hjw⟩,
        by dsimp only [st_k, m8BlkState, m8ShrinkBlkBoolState, tmp_f] at hm_sf ⊢; exact hm_sf⟩)
  rintro Ji n ⟨i_bv, ⟨⟩⟩ m_i hJi ⟨mrk_i, mclr_i, mcl_i, mcf_i, rfl, hilen, hmri_len, hmclri_len,
    hmcli_le, hab_i, hdom_i, hcov_i, hmono_i, h2_sstk, hnew2_i, h8_i, hm_i⟩
  let st_i := m8BlkState s tmp_f mrk_i mclr_i sstk_a wsort_a mcl_i mcf_i ticks_a
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hilt => ?_, fun hidone => ?_⟩
  · c0_cond hilt
    have hi_stk : i_bv.toNat < st_i.scratch.shrink_stk.length := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState]; rw [hb_a.sstk_len]
      have := hb_a.slen_le; omega
    have hi_stk' : i_bv.toNat < sstk_a.length := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState] at hi_stk; exact hi_stk
    ml_ld c0_load_full_shrink_stk (s := st_i) (i := i_bv) hi_stk hm_i
    let sv := sstk_a[i_bv.toNat]'hi_stk'
    have hsv_lt : sv.toNat < s.core.cur_vars := by
      have := hb_a.sstk_lt i_bv.toNat hilt
      rwa [List.getElem?_eq_getElem hi_stk', Option.getD_some] at this
    have hsv64 : (sv.setWidth 64).toNat = sv.toNat := bv_c0_zext32_64 sv
    have hmrk_sv : sv.toNat < mrk_i.length := by rw [hmri_len]; omega
    have hmrk_sv' : (sv.setWidth 64).toNat < st_i.core.mrk.length := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState]; rw [hmri_len, hsv64]; omega
    ml_ld c0_load_full_mrk (s := st_i) (i := sv.setWidth 64) hmrk_sv' hm_i
    ml_st m_i2, hm_s := c0_store_full_mrk (s := st_i) (i := sv.setWidth 64) _ hmrk_sv' hm_i
    let mrk_i2 := mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8)
    have hm_i2 : (FullMem c (m8BlkState s tmp_f mrk_i2 mclr_i sstk_a wsort_a
        mcl_i mcf_i ticks_a) ⋆ R) m_i2 := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState, mrk_i2, sv] at hm_s ⊢
      simp only [bv_c0_zext32_64, Arg.val_var, bv8_and247_c0] at hm_s
      rw [List.getElem?_eq_getElem hmrk_sv, Option.getD_some]; exact hm_s
    let sb_i2 := m8BlkState s tmp_f mrk_i2 mclr_i sstk_a wsort_a mcl_i mcf_i ticks_a
    have hln_i2 : sb_i2.LengthsOk c :=
      (m8CoreInv_blk hcore htf_len (by simp [mrk_i2, hmri_len]) hmclri_len hmcli_le
        hb_a.sstk_len hb_a.wsort_len).1
    have hno8_sv : (sb_i2.core.mrk[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
      dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2]
      rw [List.getElem?_set_self (by rw [hmri_len]; omega), Option.getD_some]
      exact bv8_and8_clear _
    ml_lets; apply wp_call_of_spec; apply hMm
    refine fullMinMarkSpec_step hln_i2 hm_i2 sv hsv_lt ((2 : BitVec 32).setWidth 8)
      fun m_m hm_m => ?_
    have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl; rw [h2_eq] at hm_m
    let sb_i3 := fullMinMarkStepState sb_i2 sv.toNat 2#8
    have hln_i3 := fullMinMarkStepState_lengths hln_i2 sv.toNat 2#8
    have hab_i3 : ∀ w, s.core.cur_vars ≤ w → sb_i3.core.mrk[w]? = s.core.mrk[w]? := fun w hw =>
      (fullMinMarkStepState_mrk_above (s := sb_i2) hsv_lt 2#8 w hw).trans (by
        dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2]
        rw [List.getElem?_set_ne (by omega)]; exact hab_i w hw)
    obtain ⟨hdom_i3, hcov_i3⟩ := fullMinMarkStepState_dom_clr hln_i2 (fun w hw => by
      dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2] at hw ⊢
      by_cases hwe : w = sv.toNat
      · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; omega), Option.getD_some]
        exact bv8_and_dom_clear8 (hdom_i _ hsv_lt)
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hdom_i w hw)
      (fun hmcf w hw h6 => by
        dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2] at hmcf hw h6 ⊢
        by_cases hwe : w = sv.toNat
        · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; omega), Option.getD_some,
            bv8_and6_pres_clear8] at h6; exact hcov_i hmcf _ hsv_lt h6
        · rw [List.getElem?_set_ne (Ne.symm hwe)] at h6; exact hcov_i hmcf w hw h6)
      hsv_lt (Or.inl rfl) hno8_sv
    obtain ⟨hbit8_i3, hmono2_i3⟩ :=
      fullMinMarkStepState_bit8_mono2 hln_i2 hsv_lt (Or.inl rfl) hno8_sv
    have hm_i3 : (FullMem c (m8BlkState s tmp_f sb_i3.core.mrk sb_i3.core.min_clr sstk_a wsort_a
        sb_i3.core.min_clr_len sb_i3.core.min_clr_full ticks_a) ⋆ R) m_m := by
      dsimp only [sb_i3, sb_i2] at hm_m ⊢; rw [m8Blk_step]; exact hm_m
    have hmono_i2 : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (sb_i2.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w _ h2 => by
      dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2]; by_cases hwe : w = sv.toNat
      · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; omega), Option.getD_some,
          bv8_and2_pres_clear8]; exact h2
      · rwa [List.getElem?_set_ne (Ne.symm hwe)]
    have hsv_2 : (sb_i3.core.mrk[sv.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
      dsimp only [sb_i3, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]; split
      · rename_i hc; exact hc.resolve_left (Nat.not_le.mpr hsv_lt)
      · dsimp only; rw [List.getElem?_set_self (by rw [hln_i2.core_ok.mrk_len]; omega),
          Option.getD_some]; exact bv8_and2_of_or2 _
    have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := min_bv64_add1 (by have := hb_a.slen_le; omega)
    ml_lets
    refine hJi (slen_a.toNat - (i_bv + 1).toNat) (i_bv + 1, ()) m_m (by omega)
      ⟨sb_i3.core.mrk, sb_i3.core.min_clr, sb_i3.core.min_clr_len, sb_i3.core.min_clr_full, rfl,
        by omega, hln_i3.core_ok.mrk_len, hln_i3.core_ok.min_clr_len_arr,
        hln_i3.core_ok.min_clr_len_le, hab_i3, hdom_i3, hcov_i3,
        fun w hw h2 => hmono2_i3 w hw (hmono_i2 w hw (hmono_i w hw h2)),
        fun j hj hji1 => ?_, fun w hw h2 => ?_, fun w hw h8 => ?_, hm_i3⟩
    · rw [hi1] at hji1; by_cases hji : j = i_bv.toNat
      · subst j; dsimp only [sv] at hsv_2
        rw [List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some]; exact hsv_2
      · exact hmono2_i3 _ (hb_a.sstk_lt j hj)
          (hmono_i2 _ (hb_a.sstk_lt j hj) (h2_sstk j hj (by omega)))
    · by_cases hwe : w = sv.toNat
      · subst w; right; have h1 := hsstk_a i_bv.toNat hilt
        rwa [List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some] at h1
      · have h2_i2 : (sb_i2.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
          dsimp only [sb_i3, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore] at h2
          split at h2
          · exact h2
          · dsimp only at h2; rwa [List.getElem?_set_ne (Ne.symm hwe)] at h2
        dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2] at h2_i2
        exact hnew2_i w hw (by rwa [List.getElem?_set_ne (Ne.symm hwe)] at h2_i2)
    · rw [hi1]; rw [hbit8_i3 w hw] at h8
      dsimp only [sb_i2, m8BlkState, m8ShrinkBlkBoolState, mrk_i2] at h8
      by_cases hwe : w = sv.toNat
      · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; omega), Option.getD_some] at h8
        exact absurd (bv8_and8_clear _) h8
      · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
        obtain ⟨j, hj1, hj2, hjw⟩ := h8_i w hw h8; refine ⟨j, ?_, hj2, hjw⟩
        by_cases hji : j = i_bv.toNat
        · subst j; exfalso; apply hwe
          rw [← hjw, List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some]
        · omega
  · ml_lets; rw [wp]; c0_cond hidone
    have hno8_f : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw => by
      by_cases hnz : (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8; · exact hnz
      obtain ⟨j, hj1, hj2, _⟩ := h8_i w hw hnz; omega
    have h8_to_2f : ∀ w < s.core.cur_vars, (mrk_a[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
        (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w hw h8 => by
      obtain ⟨j, hj, hjw⟩ := hb_a.bit8_sstk w hw h8
      have := h2_sstk j hj (by omega); rwa [hjw] at this
    have hcore_f := m8CoreInv_blk hcore htf_len hmri_len hmclri_len hmcli_le
      hb_a.sstk_len hb_a.wsort_len (mcf1 := mcf_i) (ticks1 := ticks_a)
    obtain ⟨hmin_f, hEnt_f, hlvl_f, htmp_f⟩ := s13Shrink_blk_success_finish
      hcore hbeg_end hend_kl hkl_cv hkeep_spec hb_a hmri_len hmclri_len htf_len hdom_i
      hcov_i hmono_i h8_to_2f hnew2_i huip_te huip_eq huip_8 huip_lvl hres_a hblk_a htf_out
      htf_beg htf_rest
    exact hQ true tmp_f mrk_i mclr_i sstk_a wsort_a mcl_i mcf_i ticks_a m_i hcore_f hmin_f hab_i
      hno8_f (fun w hw h2 => hmono_i w hw (hb_a.mono2 w hw h2)) (fun h => by cases h)
      htf_out hlvl_f
      (fun hnd hother => nodup_filter_shrink_blk (by rw [hlen0.tmp_len_arr]; omega)
        (by rw [htf_len]; omega) hnd htf_out hlvl_f
        (fun _ j _ hij hj _ hnj => hnj (by rw [htf_rest j (by omega) hj]; rfl)) hother)
      hEnt_f htmp_f hm_i

@[expose] def s13ShrinkBlkClExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMark pLvl pSstk pAr cv : V i64) (blvl uip_in rsn csz_bv : V i32)
    (is_bin_b f_sz : V .bool) (open_c slen_c t_next : V i64)
    (Jm : C [i64, i64, .bool, i32, i64]) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64, .bool, i32]]) (fun Jcl =>
    .cons (fun (xs : Tup V [i64, i64, .bool, i32]) =>
    let op_i := xs.fst; let sl_i := xs.snd.fst; let fl_i := xs.snd.snd.fst
    let i_bv := xs.snd.snd.snd.fst
    .group (sig := [[]]) (fun _ => .cons (fun _ =>
      .group (sig := [[i64]]) (fun _ => .cons (fun (opf : Tup V [i64]) =>
        .jump Jm (.var opf.fst, .var sl_i, .var fl_i, .var uip_in, .var t_next, ())) .nil)
        fun Jop =>
          .jnz (.var fl_i) (.jump Jop.fst (.var op_i, ()))
            (.let_ (op64 (.sub i64) (.var op_i) (.imm 1)) fun op1 =>
             .jump Jop.fst (.var op1.fst, ()))) .nil)
      fun Jce =>
        .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var i_bv, .var csz_bv, ())) fun p1 =>
        .jnz (.var p1.fst)
          (.jnz (.var fl_i) (.jump Jce.fst ())
            (.group (sig := [[i32]]) (fun _ => .cons (fun (ot_t : Tup V [i32]) =>
              let ot := ot_t.fst
              .let_ (Op.mk (.lshr i32) (.var ot, .imm 1, ())) fun ov =>
              .group (sig := [[i64, i64, .bool]]) (fun _ =>
                .cons (fun (ys : Tup V [i64, i64, .bool]) =>
                .let_ (Op.mk (.add i32) (.var i_bv, .imm 1, ())) fun i1 =>
                .jump Jcl.fst (.var ys.fst, .var ys.snd.fst, .var ys.snd.snd.fst, .var i1.fst, ()))
                .nil)
                fun Jit =>
                  .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ot, .var uip_in, ())) fun p2 =>
                  .jnz (.var p2.fst)
                    (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun p3 =>
                     .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p3.fst, .var cv, ())) fun p4 =>
                     .jnz (.var p4.fst)
                       (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun p5 =>
                        .let_ (op64 (.mul i64) (.var p5.fst) (.imm 4)) fun p6 =>
                        .let_ (op64 (.add i64) (.var pLvl) (.var p6.fst)) fun p7 =>
                        .load i32 (.var p7.fst) fun lov =>
                        .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (.var lov, .imm 0, ())) fun p8 =>
                        .jnz (.var p8.fst)
                          (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun p9 =>
                           .let_ (op64 (.add i64) (.var pMark) (.var p9.fst)) fun p10 =>
                           .load i8 (.var p10.fst) fun mov =>
                           .let_ (Op.mk (.trunc 32 8) (.imm 8, ())) fun p11 =>
                           .let_ (Op.mk (.zext 8 32) (.var mov, ())) fun p12 =>
                           .let_ (Op.mk (.zext 8 32) (.var p11.fst, ())) fun p13 =>
                           .let_ (Op.mk (.and i32) (.var p12.fst, .var p13.fst, ())) fun p14 =>
                           .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p15 =>
                           .let_ (Op.mk (.zext 8 32) (.var p15.fst, ())) fun p16 =>
                           .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var p14.fst, .var p16.fst, ()))
                             fun p17 =>
                           .jnz (.var p17.fst)
                             (.group (sig := [[i64, i64, .bool]]) (fun _ =>
                               .cons (fun (zb : Tup V [i64, i64, .bool]) =>
                               .jump Jit.fst (.var zb.fst, .var zb.snd.fst,
                                 .var zb.snd.snd.fst, ()))
                               .nil)
                               fun Jb =>
                                 .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun q1 =>
                                 .let_ (op64 (.mul i64) (.var q1.fst) (.imm 4)) fun q2 =>
                                 .let_ (op64 (.add i64) (.var pLvl) (.var q2.fst)) fun q3 =>
                                 .load i32 (.var q3.fst) fun lov2 =>
                                 .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var lov2, .var blvl, ()))
                                   fun q4 =>
                                 .jnz (.var q4.fst)
                                   (.group (sig := [[.bool]]) (fun _ =>
                                     .cons (fun (fb : Tup V [.bool]) =>
                                     .jump Jb.fst (.var op_i, .var sl_i, .var fb.fst, ())) .nil)
                                     fun Jl =>
                                       .call "full_shrink_lower_m8" (as := [i64, i32, i32])
                                         (bs := [.bool]) (.var h, .var ot, .var ov.fst, ()) fun r =>
                                       .jnz (.var r.fst) (.jump Jl.fst (.var fl_i, ()))
                                         (.jump Jl.fst (.imm true, ())))
                                   (.group (sig := [[i64, i64, .bool]]) (fun _ =>
                                     .cons (fun (ze : Tup V [i64, i64, .bool]) =>
                                     .jump Jb.fst (.var ze.fst, .var ze.snd.fst,
                                       .var ze.snd.snd.fst, ())) .nil)
                                     fun Je =>
                                       .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun r1 =>
                                       .let_ (op64 (.mul i64) (.var r1.fst) (.imm 4)) fun r2 =>
                                       .let_ (op64 (.add i64) (.var pLvl) (.var r2.fst)) fun r3 =>
                                       .load i32 (.var r3.fst) fun lov3 =>
                                       .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                         (.var lov3, .var blvl, ())) fun r4 =>
                                       .jnz (.var r4.fst)
                                         (.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                           (.var sl_i, .var cv, ())) fun r5 =>
                                          .jnz (.var r5.fst)
                                            (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun r6 =>
                                             .let_ (op64 (.add i64) (.var pMark) (.var r6.fst))
                                               fun r7 =>
                                             .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun r8 =>
                                             .let_ (op64 (.add i64) (.var pMark) (.var r8.fst))
                                               fun r9 =>
                                             .load i8 (.var r9.fst) fun mov2 =>
                                             .let_ (Op.mk (.trunc 32 8) (.imm 8, ())) fun r10 =>
                                             .let_ (Op.mk (.zext 8 32) (.var mov2, ())) fun r11 =>
                                             .let_ (Op.mk (.zext 8 32) (.var r10.fst, ()))
                                               fun r12 =>
                                             .let_ (Op.mk (.or i32)
                                                 (.var r11.fst, .var r12.fst, ()))
                                               fun r13 =>
                                             .let_ (Op.mk (.trunc 32 8) (.var r13.fst, ()))
                                               fun r14 =>
                                             .store (.var r14.fst) (.var r7.fst)
                                               (.let_ (op64 (.mul i64) (.var sl_i) (.imm 4))
                                                 fun r15 =>
                                                .let_ (op64 (.add i64) (.var pSstk) (.var r15.fst))
                                                  fun r16 =>
                                                .store (.var ov.fst) (.var r16.fst)
                                                  (.let_ (op64 (.add i64) (.var sl_i) (.imm 1))
                                                    fun sl1 =>
                                                   .let_ (op64 (.add i64) (.var op_i) (.imm 1))
                                                     fun op1 =>
                                                   .jump Je.fst (.var op1.fst, .var sl1.fst,
                                                     .var fl_i, ()))))
                                            (.jump Je.fst (.var op_i, .var sl_i, .imm true, ())))
                                         (.jump Je.fst (.var op_i, .var sl_i, .imm true, ()))))
                             (.jump Jit.fst (.var op_i, .var sl_i, .var fl_i, ())))
                          (.jump Jit.fst (.var op_i, .var sl_i, .var fl_i, ())))
                       (.jump Jit.fst (.var op_i, .var sl_i, .var fl_i, ())))
                    (.jump Jit.fst (.var op_i, .var sl_i, .var fl_i, ()))) .nil)
              fun Jot =>
                .jnz (.var is_bin_b)
                  (.let_ (Op.mk (.and i32) (.var rsn, .imm 2147483647, ())) fun lb =>
                   .jump Jot.fst (.var lb.fst, ()))
                  (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun a1 =>
                   .let_ (op64 (.add i64) (.var a1.fst) (.imm 3)) fun a2 =>
                   .let_ (Op.mk (.zext 32 64) (.var i_bv, ())) fun a3 =>
                   .let_ (op64 (.add i64) (.var a2.fst) (.var a3.fst)) fun a4 =>
                   .let_ (op64 (.mul i64) (.var a4.fst) (.imm 4)) fun a5 =>
                   .let_ (op64 (.add i64) (.var pAr) (.var a5.fst)) fun a6 =>
                   .load i32 (.var a6.fst) fun al =>
                   .jump Jot.fst (.var al, ()))))
          (.jump Jce.fst ())) .nil)
    fun Jcl => .jump Jcl.fst (.var open_c, .var slen_c, .var f_sz, .imm 0, ())

theorem s13_shrink_blk_cl_wp {Γ : Env}
    (hSl : ∀ args m Q X, m8ShrinkLowerSpec args m Q X →
      Γ "full_shrink_lower_m8" [i64, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur0 : List (List Nat)} {s : FullState}
    {beg end_b open_c slen_c t_c t_in t_next : Val i64} {blvl uip_in rsn csz_bv : Val i32}
    {is_bin_b f_sz : Val .bool} {keep0 : List Nat} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {X : XPost}
    {mrk_c : List (BitVec 8)} {mclr_c sstk_c wsort_c : List (BitVec 32)} {mcl_c : Nat}
    {mcf_c ticks_sz : BitVec 64} {m_sz : Mem 64}
    {Jm : Cont [i64, i64, .bool, i32, i64]}
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hblvl_lt : blvl.toNat < s.core.cur_level) (hend_cv : end_b.toNat ≤ s.core.cur_vars)
    (hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (ht_te : t_in.toNat < s.core.trail_end) (ht_tc : t_in.toNat ≤ t_c.toNat)
    (ht_pos : 1 ≤ t_in.toNat) (ht_next : t_next.toNat = t_in.toNat - 1)
    (huip_in_eq' : (s.core.trl[t_in.toNat]?.getD 0#32).toNat = uip_in.toNat)
    (ht_in_lvl : (s.core.lvl[(s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hrsn_ne' : s.core.rsns[(s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32)
    (his_bin : is_bin_b = (rsn &&& 0x80000000#32 != 0#32)) (hf_sz : f_sz = false)
    (hcsz_eq : csz_bv.toNat =
      (if is_bin_b = true then 1 else fullArenaClauseSizeCore s.core rsn.toNat))
    (hbig_ok : is_bin_b = false → rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      rsn.toNat + 3 + csz_bv.toNat ≤ s.core.arena.length)
    (hop_ge2 : 2 ≤ open_c.toNat) (hop_le : open_c.toNat ≤ (end_b.toNat - beg.toNat) + slen_c.toNat)
    (hb_c : S13ShrinkBaseInv c s mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c slen_c.toNat keep0)
    (hblk_c : S13ShrinkBlk8 s mrk_c beg.toNat end_b.toNat)
    (hsstk_c : S13ShrinkStk8 mrk_c sstk_c slen_c.toNat)
    (h8_pre : S13ShrinkAll8 s blvl mrk_c t_next.toNat t_in.toNat)
    (hcnt_pre : trailCount8 s.core.trl mrk_c (min (t_next.toNat + 1) s.core.trail_end) ≤
      open_c.toNat - 1)
    (hm_sz : (FullMem c (m8BlkState s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_sz)
      ⋆ R) m_sz)
    (hJm : ∀ n' ys m', n' < min t_c.toNat s.core.trail_end + 1 →
      S13ShrinkMainInv c s blvl beg.toNat end_b.toNat keep0 R n' ys m' → Jm ys m') :
    wp Γ Q X (s13ShrinkBlkClExpr c.hdr c.pMark c.pLevel c.pShrinkStk c.pArena
      (BitVec.ofNat 64 s.core.cur_vars) blvl uip_in rsn csz_bv
      is_bin_b f_sz open_c slen_c t_next Jm) m_sz := by
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hrs := hw0.reason_inv_below t_in.toNat ht_te ht_in_lvl hrsn_ne'
  dsimp only [s13ShrinkBlkClExpr]
  refine wp_loop_group (ts := [i64, i64, .bool, i32])
    (S13ShrinkClInv c s blvl beg.toNat end_b.toNat keep0 t_next.toNat t_in.toNat csz_bv.toNat
      rsn is_bin_b R) ?_ (fun Jcl hJcl => by
      subst f_sz; ml_lets; exact hJcl (csz_bv.toNat - 0 + 1) (open_c, slen_c, false, 0#32, ()) m_sz
        ⟨rfl, Nat.zero_le _, mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_sz,
          hb_c, hblk_c, hsstk_c, hm_sz, fun _ =>
            ⟨hop_ge2, hop_le, h8_pre, hcnt_pre, fun _ h => by simp at h⟩⟩)
  rintro Jcl n_cl ⟨open_i, slen_i, failed_i, i_bv, ⟨⟩⟩ m_i hJcl
    ⟨rfl, hi_le, mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i,
      hb_i, hblk_i, hsstk_i, hm_i, hok_i⟩
  let st_i := m8BlkState s s.core.tmp mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i
  rw [Blocks.get_here]
  refine wp_join_group (ts := [])
    (fun () m_ex => m_ex = m_i ∧ (failed_i = false → i_bv.toNat = csz_bv.toNat)) ?_ ?_
  · rintro J_ce ⟨⟩ m_ex ⟨hm_ex_eq, hce_done⟩; subst m_ex; rw [Blocks.get_here]
    refine wp_join_group (ts := [i64])
      (fun (open_f, ()) m_o => m_o = m_i ∧ (failed_i = false → open_f.toNat = open_i.toNat - 1)) ?_
      (fun J_op hJ_op => by
        ml_jnz; refine ⟨fun hfi => hJ_op (open_i, ()) m_i ⟨rfl, fun h => by cases hfi.symm.trans h⟩,
          fun hnfi => by
            ml_lets; have hop2 := (hok_i hnfi).1
            exact hJ_op (open_i - 1, ()) m_i ⟨rfl, fun _ => min_bv64_sub1 (by omega)⟩⟩)
    rintro J_op ⟨open_f, ⟨⟩⟩ m_o ⟨hm_o_eq, hop_f⟩; subst m_o; rw [Blocks.get_here]; ml_lets
    by_cases hfi : failed_i = true
    · subst failed_i
      exact hJm 0 (open_f, slen_i, true, uip_in, t_next, ()) m_i (by omega)
        ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, rfl, hb_i, hblk_i, hsstk_i,
          hm_i, fun h => by cases h⟩
    · have hnfi : failed_i = false := Bool.eq_false_iff.mpr hfi; subst failed_i
      obtain ⟨hop2_i, hopl_i, h8_i, hcnt_i, hcov_i⟩ := hok_i rfl
      have hi_eq := hce_done rfl
      have hrc_i : ShrinkResolved s.core mrk_i t_in.toNat := by
        refine shrink_rsn_loop_done hcore ht_te ht_in_lvl hrsn_ne' ?_
        dsimp only; intro j hj
        have hbin_iff : ((rsn &&& 0x80000000#32) ≠ 0#32) ↔ is_bin_b = true := by
          rw [his_bin]; simp only [bne_iff_ne, ne_eq]
        rw [← hrsn_eq] at hj ⊢
        by_cases hb' : is_bin_b = true
        · simp only [eq_true (hbin_iff.mpr hb'), hb', ↓reduceIte] at hj hcsz_eq ⊢
          simpa only [S13ShrinkCovAt, s13ShrinkRsnLit, hb', ↓reduceIte] using hcov_i j (by omega)
        · have hbf := Bool.eq_false_iff.mpr hb'
          have hbn : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := fun h => hb' (hbin_iff.mp h)
          simp only [eq_false hbn, hbf, Bool.false_eq_true, ↓reduceIte] at hj hcsz_eq ⊢
          simpa only [S13ShrinkCovAt, s13ShrinkRsnLit, hbf, Bool.false_eq_true, ↓reduceIte] using
            hcov_i j (by omega)
      have hop_f' := hop_f rfl
      refine hJm (if (false : Bool) = true then 0 else min t_next.toNat s.core.trail_end + 1)
        (open_f, slen_i, false, uip_in, t_next, ()) m_i
        (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
        ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, rfl, hb_i, hblk_i, hsstk_i,
          hm_i, fun _ => ⟨by omega, by omega, fun w hw hw8 => ?_, by omega⟩⟩
      obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_i w hw hw8
      exact ⟨hl, idx, hidx_te, hidx_v,
        hdisj.elim Or.inl fun h => h.elim Or.inr (fun h3 => h3 ▸ Or.inr hrc_i)⟩
  rintro J_ce hJ_ce; ml_lets; ml_jnz
  refine ⟨?_, fun hige => by c0_cond hige; exact hJ_ce () m_i ⟨rfl, fun _ => by omega⟩⟩
  intro hilt; ml_jnz
  refine ⟨fun hfi => hJ_ce () m_i ⟨rfl, fun h => by cases hfi.symm.trans h⟩, ?_⟩
  intro hnfi; c0_cond hilt
  obtain ⟨hop2_i, hopl_i, h8_i, hcnt_i, hcov_i⟩ := hok_i hnfi
  subst failed_i
  let OtJoin : Tup Val [i32] → Mem 64 → Prop := fun (ot, ()) m_o =>
    m_o = m_i ∧ ot.toNat = s13ShrinkRsnLit s rsn is_bin_b i_bv.toNat
  refine wp_join_group (ts := [i32]) OtJoin ?_ (fun J_ot hJ_ot => by
    ml_jnz; refine ⟨fun hbt => by
      ml_lets
      exact hJ_ot _ _ ⟨rfl, by simp only [s13ShrinkRsnLit, hbt, ↓reduceIte]; rfl⟩, fun hbf => ?_⟩
    obtain ⟨_, _, har_bd⟩ := hbig_ok hbf
    have hi_ar : (rsn.setWidth 64 + 3 + i_bv.setWidth 64).toNat < st_i.core.arena.length := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState]; rw [bv64_zext32_add3_add]; omega
    ml_ld c0_load_full_arena (s := st_i) (i := rsn.setWidth 64 + 3 + i_bv.setWidth 64) hi_ar hm_i
    ml_lets; apply hJ_ot; refine ⟨rfl, ?_⟩
    simp only [s13ShrinkRsnLit, hbf, Bool.false_eq_true, ↓reduceIte]
    dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState, Arg.val_var]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 2; exact bv64_zext32_add3_add rsn i_bv)
  rintro J_ot ⟨ot, ⟨⟩⟩ m_o ⟨hm_o_eq, hot_eq⟩; subst m_o; rw [Blocks.get_here]; ml_lets
  let IterInv : Tup Val [i64, i64, .bool] → Mem 64 → Prop := fun (op', sl', f', ()) m' =>
    ∃ mrk' mclr' sstk' wsort' mcl' mcf' ticks',
      S13ShrinkBaseInv c s mrk' mclr' sstk' wsort' mcl' mcf' sl'.toNat keep0 ∧
      S13ShrinkBlk8 s mrk' beg.toNat end_b.toNat ∧ S13ShrinkStk8 mrk' sstk' sl'.toNat ∧
      (FullMem c (m8BlkState s s.core.tmp mrk' mclr' sstk' wsort' mcl' mcf' ticks') ⋆ R) m' ∧
      (f' = false →
        2 ≤ op'.toNat ∧ op'.toNat ≤ (end_b.toNat - beg.toNat) + sl'.toNat ∧
        S13ShrinkAll8 s blvl mrk' t_next.toNat t_in.toNat ∧
        trailCount8 s.core.trl mrk' (min (t_next.toNat + 1) s.core.trail_end) ≤ op'.toNat - 1 ∧
        ∀ k < i_bv.toNat + 1, S13ShrinkCovAt s mrk' t_in.toNat rsn is_bin_b k)
  have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := bv32_add1_toNat (by have := csz_bv.isLt; omega)
  refine wp_join_group (ts := [i64, i64, .bool]) IterInv
    (fun _ ⟨op', sl', f', ⟨⟩⟩ m' ⟨mrk', mclr', sstk', wsort', mcl', mcf', ticks',
        hb', hblk', hsstk', hm', hok'⟩ => by
      rw [Blocks.get_here]; ml_lets
      refine hJcl (if f' = true then 0 else csz_bv.toNat - (i_bv + 1).toNat + 1)
        (op', sl', f', i_bv + 1, ()) m' ?_
        ⟨rfl, by omega, mrk', mclr', sstk', wsort', mcl', mcf', ticks',
          hb', hblk', hsstk', hm',
          fun hf' => let ⟨h1, h2, h3, h4, h5⟩ := hok' hf'; ⟨h1, h2, h3, h4, by rw [hi1]; exact h5⟩⟩
      cases f' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega) ?_
  rintro J_it hJ_it
  have hot_info : ot.toNat < 2 * s.core.cur_vars ∧
      (ot = uip_in ∨ ∃ k_ot < t_in.toNat,
        (s.core.trl[k_ot]?.getD 0#32).toNat = ot.toNat ^^^ 1) := by
    have hbin_iff : ((rsn &&& 0x80000000#32) ≠ 0#32) ↔ is_bin_b = true := by
      rw [his_bin]; simp only [bne_iff_ne, ne_eq]
    by_cases hb' : is_bin_b = true
    · rw [← hrsn_eq] at hrs; simp only [eq_true (hbin_iff.mpr hb'), ↓reduceIte] at hrs
      simp only [s13ShrinkRsnLit, hb', ↓reduceIte] at hot_eq
      obtain ⟨k_ot, hk_lt, hk_eq, _⟩ := hrs.2.2
      exact ⟨by rw [hot_eq]; exact hrs.1, Or.inr ⟨k_ot, hk_lt, by rw [hot_eq]; exact hk_eq⟩⟩
    · have hbf := Bool.eq_false_iff.mpr hb'; rw [← hrsn_eq] at hrs
      simp only [eq_false (fun h => hb' (hbin_iff.mp h) : ¬ (rsn &&& 0x80000000#32) ≠ 0#32),
        ↓reduceIte] at hrs
      simp only [s13ShrinkRsnLit, hbf, Bool.false_eq_true, ↓reduceIte] at hot_eq hcsz_eq
      have hmem := shrink_arena_lits_mem hcore hrs.1 (pos := i_bv.toNat) (by omega)
      refine ⟨by rw [hot_eq]; exact hw0.arena.lits_lt _ hrs.1 hrs.2.1 _ hmem, ?_⟩
      rcases hrs.2.2 _ hmem with heq | ⟨k_ot, hk_lt, hk_eq, _⟩
      · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [hot_eq, heq, huip_in_eq']))
      · exact Or.inr ⟨k_ot, hk_lt, by rw [hot_eq]; exact hk_eq⟩
  have hov_lt : (ot >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
  have hskip : ∀ (hstep : ot.toNat = (s.core.trl[t_in.toNat]?.getD 0#32).toNat ∨ ∃ m < t_in.toNat,
      (s.core.trl[m]?.getD 0#32).toNat = ot.toNat ^^^ 1 ∧
      ((s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 ∨
        (mrk_i[ot.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
        (mrk_i[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)),
      IterInv (open_i, slen_i, false, ()) m_i := fun hstep =>
    ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, hb_i, hblk_i, hsstk_i, hm_i, fun _ =>
      ⟨hop2_i, hopl_i, h8_i, hcnt_i,
        s13Shrink_cov_lift hcore ht_te (fun _ _ h => h) (fun _ _ h => h) hcov_i hot_eq hstep⟩⟩
  ml_lets; ml_jnz
  refine ⟨?_, fun heq_uip => by
    c0_cond heq_uip; exact hJ_it _ m_i (hskip (Or.inl (by rw [heq_uip, huip_in_eq'])))⟩
  intro hne_uip; c0_cond hne_uip
  obtain ⟨k_ot, hk_lt, hk_eq⟩ := hot_info.2.resolve_left hne_uip
  ml_lets; ml_jnz; refine ⟨?_, fun hov_ge => by exfalso; c0_cond hov_ge; bv_omega⟩; intro _
  have hov_lvl_l : ((ot >>> 1).setWidth 64).toNat < st_i.core.lvl.length := by
    dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState]; rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
  ml_ld c0_load_full_lvl (s := st_i) (i := (ot >>> 1).setWidth 64) hov_lvl_l hm_i
  ml_lets; ml_jnz
  refine ⟨?_, fun hlvl0 => by
    have hl0 : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 := by
      c0_cond hlvl0; dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState] at hlvl0
      rw [List.getElem?_eq_getElem (by rw [hlen0.lvl_len]; omega), Option.getD_some]; bv_omega
    exact hJ_it _ m_i (hskip (Or.inr ⟨k_ot, hk_lt, hk_eq, Or.inl hl0⟩))⟩
  intro hlvl_pos
  have hov_mrk_l : ((ot >>> 1).setWidth 64).toNat < st_i.core.mrk.length := by
    dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState]; rw [hb_i.mrk_len, bv_c0_zext32_64]; omega
  ml_ld c0_load_full_mrk (s := st_i) (i := (ot >>> 1).setWidth 64) hov_mrk_l hm_i
  ml_lets; ml_jnz
  refine ⟨?_, fun has8_ov => by
    have h8_ov : (mrk_i[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
      have h8 := bv8_c0_and8_ne0 has8_ov
      rw [List.getElem?_eq_getElem (by rw [hb_i.mrk_len]; omega), Option.getD_some]
      simpa only [st_i, m8BlkState, m8ShrinkBlkBoolState, bv_c0_zext32_64, bv32_lshr_1] using h8
    exact hJ_it _ m_i (hskip (Or.inr ⟨k_ot, hk_lt, hk_eq, Or.inr (Or.inr h8_ov)⟩))⟩
  intro hno8_ov
  refine wp_join_group (ts := [i64, i64, .bool]) IterInv
    (fun _ xs m_b hb_b => by rw [Blocks.get_here]; exact hJ_it xs m_b hb_b) ?_
  rintro J_b hJ_b
  ml_ld c0_load_full_lvl (s := st_i) (i := (ot >>> 1).setWidth 64) hov_lvl_l hm_i
  ml_lets; ml_jnz; refine ⟨fun hlt_blvl => ?_, fun _ => ?_⟩
  · have hlov_lt : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat < blvl.toNat := by
      c0_cond hlt_blvl
      rw [List.getElem?_eq_getElem (by rw [hlen0.lvl_len]; omega), Option.getD_some]; exact hlt_blvl
    refine wp_join_group (ts := [.bool]) (fun (f', ()) m' => IterInv (open_i, slen_i, f', ()) m')
      (fun _ ⟨f', ⟨⟩⟩ m' hf' => by rw [Blocks.get_here]; exact hJ_b _ m' hf') ?_
    rintro J_l hJ_l; apply wp_call_of_spec; apply hSl
    dsimp only [vals, Arg.val]
    have hval_ot : st_i.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 :=
      (hw0.vals_false_iff _ hot_info.1).mpr ⟨k_ot, Nat.lt_trans hk_lt ht_te, hk_eq⟩
    refine m8ShrinkLowerSpec_of (s13ShrinkBaseInv_core hcore hb_i) (m8_toFullMinInv hb_i.min_inv)
      (bv32_lshr_1 ot) hot_info.1 hval_ot
      (by rw [bv32_lshr_1]; exact Nat.lt_trans hlov_lt hblvl_lt)
      (by rw [bv32_lshr_1]
          exact s13ShrinkOkInv_lvl_lt_no8 (fun w hw h8 => (h8_i w hw h8).1) hlov_lt)
      hm_i (fun ok_l mrk_l wsort_l mclr_l mcl_l mcf_l ticks_l m_l hlen_l hab_l hmono_l hbit8_l
        hmin_lf hok_l hm_l => by
    have hmin_l := m8_toSpecsMinInv hmin_lf
    have hbit8_l' : ∀ w < s.core.cur_vars,
        (mrk_l[w]?.getD 0#8 &&& 8#8) = (mrk_i[w]?.getD 0#8 &&& 8#8) := fun w hw => by
      simpa only [st_i, m8BlkState, m8ShrinkBlkBoolState] using hbit8_l w hw
    have hb_l : S13ShrinkBaseInv c s mrk_l mclr_l sstk_i wsort_l mcl_l mcf_l slen_i.toNat keep0 :=
      ⟨hlen_l.core_ok.mrk_len, hlen_l.core_ok.min_clr_len_arr, hlen_l.core_ok.min_clr_len_le,
        hb_i.sstk_len, hlen_l.scratch_ok.wsort_len, hb_i.slen_le,
        fun w hw => (hab_l w hw).trans (hb_i.mrk_above w hw), hmin_l,
        fun w hw h2 => hmono_l w hw (hb_i.mono2 w hw h2),
        fun w hw h8 => hb_i.bit8_sstk w hw (by rwa [← hbit8_l' w hw]), hb_i.sstk_lt⟩
    obtain ⟨hblk_l, hsstk_l, h8_l, hcnt_l⟩ :=
      s13Shrink_step_pre_mark2 hcore hb_l hmono_l hbit8_l' hblk_lt hblk_i hsstk_i h8_i hcnt_i
    have hm_l' : (FullMem c (m8BlkState s s.core.tmp mrk_l mclr_l sstk_i wsort_l
        mcl_l mcf_l ticks_l) ⋆ R) m_l := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState, m8MinLitDfsState] at hm_l ⊢; exact hm_l
    ml_lets; ml_jnz
    refine ⟨fun hok_t => ?_, fun _ => hJ_l (true, ()) m_l
      ⟨mrk_l, mclr_l, sstk_i, wsort_l, mcl_l, mcf_l, ticks_l, hb_l, hblk_l, hsstk_l, hm_l',
        fun h => by cases h⟩⟩
    have h2 := hok_l hok_t; rw [bv32_lshr_1] at h2
    exact hJ_l (false, ()) m_l ⟨mrk_l, mclr_l, sstk_i, wsort_l, mcl_l, mcf_l, ticks_l,
      hb_l, hblk_l, hsstk_l, hm_l', fun _ => ⟨hop2_i, hopl_i, h8_l, hcnt_l,
        s13Shrink_cov_lift hcore ht_te hmono_l (fun w hw h8 => by rwa [hbit8_l' w hw]) hcov_i hot_eq
          (Or.inr ⟨k_ot, hk_lt, hk_eq, Or.inr (Or.inl h2)⟩)⟩⟩)
  · refine wp_join_group (ts := [i64, i64, .bool]) IterInv
      (fun _ xs m_e he => by rw [Blocks.get_here]; exact hJ_b xs m_e he) ?_
    rintro J_e hJ_e
    ml_ld c0_load_full_lvl (s := st_i) (i := (ot >>> 1).setWidth 64) hov_lvl_l hm_i
    ml_lets; ml_jnz
    refine ⟨?_, fun _ => hJ_e (open_i, slen_i, true, ()) m_i
      ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, hb_i, hblk_i, hsstk_i, hm_i,
        fun h => by cases h⟩⟩
    intro hlvl_eq; ml_lets; ml_jnz
    refine ⟨?_, fun _ => hJ_e (open_i, slen_i, true, ()) m_i
      ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, hb_i, hblk_i, hsstk_i, hm_i,
        fun h => by cases h⟩⟩
    intro hsl_lt; c0_cond hlvl_eq; c0_cond hsl_lt
    have hlov_eq : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
      rw [List.getElem?_eq_getElem (by rw [hlen0.lvl_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat hlvl_eq
    have hsl_lt' : slen_i.toNat < s.core.cur_vars := by bv_omega
    ml_ld c0_load_full_mrk (s := st_i) (i := (ot >>> 1).setWidth 64) hov_mrk_l hm_i
    ml_lets
    ml_st m_p1, hm_p1 :=
      c0_store_full_mrk (s := st_i) (i := (ot >>> 1).setWidth 64) _ hov_mrk_l hm_i
    let ov := ot >>> 1; let mrk2 := mrk_i.set ov.toNat (mrk_i[ov.toNat]?.getD 0#8 ||| 8#8)
    have hm_p1' : (FullMem c (m8BlkState s s.core.tmp mrk2 mclr_i sstk_i wsort_i
        mcl_i mcf_i ticks_i) ⋆ R) m_p1 := by
      dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState, mrk2, ov] at hm_p1 ⊢
      simp only [bv_c0_zext32_64, bv32_lshr_1, Arg.val_var, bv8_or8_c0] at hm_p1
      rw [bv32_lshr_1, List.getElem?_eq_getElem (by rw [hb_i.mrk_len]; omega), Option.getD_some]
      exact hm_p1
    ml_st m_p2, hm_p2 := c0_store_full_shrink_stk (s := m8BlkState s s.core.tmp mrk2
        mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i) (i := slen_i) ov
      (by dsimp only [m8BlkState, m8ShrinkBlkBoolState]; rw [hb_i.sstk_len]; omega) hm_p1'
    let sstk2 := sstk_i.set slen_i.toNat ov
    obtain ⟨hb2, hblk2, hsstk2, h8_2, hcnt2, hop2_2, hopl2, hot8_2⟩ :=
      s13Shrink_step_pre_push8 hcore hb_i hblk_lt hblk_i hsstk_i h8_i hcnt_i hop2_i hopl_i hsl_lt'
        hot_info.1 ht_te hk_lt hk_eq (by omega) hlov_eq
    obtain ⟨_, hm2_p, hm8_p⟩ := s13Shrink_set_bit8_monos hcv hb_i.mrk_len hov_lt
    have hsl1 : (slen_i + 1).toNat = slen_i.toNat + 1 := min_bv64_add1 (by omega)
    have hop1 : (open_i + 1).toNat = open_i.toNat + 1 := min_bv64_add1 (by omega)
    ml_lets
    exact hJ_e (open_i + 1, slen_i + 1, false, ()) m_p2
      ⟨mrk2, mclr_i, sstk2, wsort_i, mcl_i, mcf_i, ticks_i, by rw [hsl1]; exact hb2, hblk2,
        by rw [hsl1]; exact hsstk2,
        by dsimp only [m8BlkState, m8ShrinkBlkBoolState, sstk2] at hm_p2 ⊢; exact hm_p2,
        fun _ => ⟨by omega, by omega, h8_2, by dsimp only [mrk2, ov]; omega,
          s13Shrink_cov_lift hcore ht_te hm2_p hm8_p hcov_i hot_eq
            (Or.inr ⟨k_ot, hk_lt, hk_eq, Or.inr (Or.inr hot8_2)⟩)⟩⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

end

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-!
# Shared Invariants & State Helpers for `full_shrink_blk_bool_m8`

Purely structural helpers (`M8ShrinkBaseInv`, `M8ShrinkBlk8`, `M8ShrinkStk8`, `M8ShrinkAll8`,
`M8ShrinkCovAt`, `m8Shrink_step_pre_*`, and `m8Shrink_blk_success_finish`) over `Proof.Spec` and
`Minimize.Spec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

public section

open Std Std.Sat
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
open scoped FullArenaTactics FullMinTactics

abbrev m8BlkState := Spec.m8ShrinkBlkBoolState

theorem m8CoreInv_blk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 ticks1 : BitVec 64}
    (htmp : tmp1.length = c.max_vars) (hmrk : mrk1.length = c.max_vars)
    (hmclr : mclr1.length = c.max_vars) (hmcl : mcl1 ≤ c.max_vars)
    (hsstk : sstk1.length = c.max_vars) (hw : wsort1.length = 2 * c.max_vars) :
    FullOtfsCoreInv c F0 (m8BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) :=
  fullOtfsCoreInv_with_min_tmp hcore htmp hcore.1.core_ok.tmp_len_le hmrk
    hcore.1.core_ok.min_stk_len hmclr hmcl
    { hcore.1.scratch_ok with shrink_stk_len := hsstk, wsort_len := hw }

theorem m8Blk_step {s : FullState} {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 ticks1 : BitVec 64}
    (v : Nat) (tag : BitVec 8) :
    let st := m8BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1
    let st' := fullMinMarkStepState st v tag
    st' = m8BlkState s tmp1 st'.core.mrk st'.core.min_clr sstk1 wsort1
      st'.core.min_clr_len st'.core.min_clr_full ticks1 := by
  intro st st'
  dsimp only [st', fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, st, m8BlkState,
    Spec.m8ShrinkBlkBoolState]
  split <;> rfl

theorem m8Witness_shrinkBlk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 ticks1 : BitVec 64}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core) :
    FullOtfsWitnessInv c F0 F_cur
      (m8BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

abbrev M8ShrinkBlk8 (s : FullState) (mrk : List (BitVec 8)) (beg end_b : Nat) : Prop :=
  ∀ j, beg ≤ j → j < end_b → (mrk[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8

abbrev M8ShrinkStk8 (mrk : List (BitVec 8)) (sstk : List (BitVec 32)) (slen : Nat) : Prop :=
  ∀ j < slen, (mrk[(sstk[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8

abbrev M8ShrinkAll8 (s : FullState) (blvl : BitVec 32) (mrk : List (BitVec 8))
    (t_next t_in : Nat) : Prop :=
  ∀ w < s.core.cur_vars, (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    (s.core.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
    ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧
      (idx ≤ t_next ∨ ShrinkResolved s.core mrk idx ∨ idx = t_in)

abbrev m8ShrinkRsnLit (s : FullState) (rsn : BitVec 32) (is_bin : Bool) (i : Nat) : Nat :=
  if is_bin then (rsn &&& 0x7FFFFFFF#32).toNat
  else (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat

abbrev M8ShrinkCovAt (s : FullState) (mrk : List (BitVec 8)) (t_in : Nat)
    (rsn : BitVec 32) (is_bin : Bool) (k : Nat) : Prop :=
  let q := m8ShrinkRsnLit s rsn is_bin k
  q = (s.core.trl[t_in]?.getD 0#32).toNat ∨
  ∃ m < t_in, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
    ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
      (mrk[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)

structure M8ShrinkBaseInv (c : FullCfg) (s : FullState)
    (mrk1 : List (BitVec 8)) (mclr1 sstk1 wsort1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 : BitVec 64) (slen : Nat) (keep0 : List Nat) : Prop where
  mrk_len : mrk1.length = c.max_vars
  mclr_len : mclr1.length = c.max_vars
  mcl_le : mcl1 ≤ c.max_vars
  sstk_len : sstk1.length = c.max_vars
  wsort_len : wsort1.length = 2 * c.max_vars
  slen_le : slen ≤ s.core.cur_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv (m8BlkState s s.core.tmp mrk1 mclr1 sstk1 wsort1
    mcl1 mcf1 s.scratch.search_ticks).core keep0
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8_sstk : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    ∃ j < slen, (sstk1[j]?.getD 0#32).toNat = w
  sstk_lt : ∀ j < slen, (sstk1[j]?.getD 0#32).toNat < s.core.cur_vars

theorem m8ShrinkBaseInv_core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 slen : Nat} {mcf1 ticks : BitVec 64}
    {keep0 : List Nat}
    (hb : M8ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen keep0) :
    FullOtfsCoreInv c F0 (m8BlkState s s.core.tmp mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks) :=
  m8CoreInv_blk hcore hcore.1.core_ok.tmp_len_arr hb.mrk_len hb.mclr_len hb.mcl_le
    hb.sstk_len hb.wsort_len

theorem m8Shrink_set_bit8_monos {cv mv v : Nat} {mrk1 : List (BitVec 8)}
    (hcv : cv ≤ mv) (hmrk : mrk1.length = mv) (hv : v < cv) :
    let mrk2 := mrk1.set v (mrk1[v]?.getD 0#8 ||| 8#8)
    (∀ w, cv ≤ w → mrk2[w]? = mrk1[w]?) ∧
    (∀ w < cv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ w < cv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8) := by
  intro mrk2
  refine ⟨fun w hw => List.getElem?_set_ne (by omega), fun w hw h2 => ?_, fun w hw h8 => ?_⟩
  · dsimp only [mrk2]; by_cases hwe : w = v
    · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some, bv8_and2_pres_or8]; exact h2
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  · dsimp only [mrk2]; by_cases hwe : w = v
    · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv8_and8_of_or8 _
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]

theorem m8ShrinkOkInv_lvl_lt_no8 {s : FullState} {mrk : List (BitVec 8)} {blvl : BitVec 32}
    {ov : Nat} (hlvl_bl : ∀ w < s.core.cur_vars, (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.core.lvl[w]?.getD 0#32).toNat = blvl.toNat)
    (hlov : (s.core.lvl[ov]?.getD 0#32).toNat < blvl.toNat) :
    ∀ w < s.core.cur_vars,
      (s.core.lvl[w]?.getD 0#32).toNat ≤ (s.core.lvl[ov]?.getD 0#32).toNat →
      (mrk[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw hle => by
  by_cases hnz : (mrk[w]?.getD 0#8 &&& 8#8) = 0#8
  · exact hnz
  · exfalso; have := hlvl_bl w hw hnz; omega

theorem m8Shrink_cov_lift {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)} {t_in i_nat : Nat}
    {rsn ot : BitVec 32} {is_bin : Bool} (ht : t_in < s.core.trail_end)
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hprev : ∀ k < i_nat, M8ShrinkCovAt s mrk1 t_in rsn is_bin k)
    (hot_eq : ot.toNat = m8ShrinkRsnLit s rsn is_bin i_nat)
    (hstep : ot.toNat = (s.core.trl[t_in]?.getD 0#32).toNat ∨ ∃ m < t_in,
      (s.core.trl[m]?.getD 0#32).toNat = ot.toNat ^^^ 1 ∧
      ((s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 ∨
        (mrk2[ot.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
        (mrk2[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)) :
    ∀ k < i_nat + 1, M8ShrinkCovAt s mrk2 t_in rsn is_bin k := by
  obtain ⟨_, hw0⟩ := hcore.2
  intro k hk
  by_cases hki : k = i_nat
  · subst k; dsimp only [M8ShrinkCovAt]; rw [← hot_eq]; exact hstep
  · dsimp only [M8ShrinkCovAt]
    rcases hprev k (by omega) with heq | ⟨m, hm, hmeq, hdep⟩
    · exact Or.inl heq
    · refine Or.inr ⟨m, hm, hmeq, ?_⟩
      have hqm : m8ShrinkRsnLit s rsn is_bin k / 2 < s.core.cur_vars := by
        have hm_lt := hw0.trail_lits_lt m (Nat.lt_trans hm ht)
        have hln := litVar_litNeg (m8ShrinkRsnLit s rsn is_bin k)
        unfold litVar litNeg at hln; rw [← hmeq] at hln; omega
      rcases hdep with h0 | h2 | h8
      · exact Or.inl h0
      · exact Or.inr (Or.inl (hm2 _ hqm h2))
      · exact Or.inr (Or.inr (hm8 _ hqm h8))

theorem m8Shrink_step_pre_push8 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {blvl ot : BitVec 32}
    {beg end_b mcl1 open_i slen t_lim huip k_ot : Nat} {mcf1 ticks1 : BitVec 64}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)} {keep0 : List Nat}
    (hb : M8ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen keep0)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hblk_8 : M8ShrinkBlk8 s mrk1 beg end_b) (hsstk_8 : M8ShrinkStk8 mrk1 sstk1 slen)
    (h8_pre : M8ShrinkAll8 s blvl mrk1 t_lim huip)
    (hcnt_pre : trailCount8 s.core.trl mrk1 (min (t_lim + 1) s.core.trail_end) ≤ open_i - 1)
    (hop2 : 2 ≤ open_i) (hopl : open_i ≤ (end_b - beg) + slen)
    (hsl_lt : slen < s.core.cur_vars) (hot_bd : ot.toNat < 2 * s.core.cur_vars)
    (huip_te : huip < s.core.trail_end) (hk_lt : k_ot < huip)
    (hk_eq : (s.core.trl[k_ot]?.getD 0#32).toNat = ot.toNat ^^^ 1) (hk_tlim : k_ot ≤ t_lim)
    (hlov_eq : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = blvl.toNat) :
    let ov := ot >>> 1
    let mrk2 := mrk1.set ov.toNat (mrk1[ov.toNat]?.getD 0#8 ||| 8#8)
    let sstk2 := sstk1.set slen ov
    M8ShrinkBaseInv c s mrk2 mclr1 sstk2 wsort1 mcl1 mcf1 (slen + 1) keep0 ∧
    M8ShrinkBlk8 s mrk2 beg end_b ∧ M8ShrinkStk8 mrk2 sstk2 (slen + 1) ∧
    M8ShrinkAll8 s blvl mrk2 t_lim huip ∧
    trailCount8 s.core.trl mrk2 (min (t_lim + 1) s.core.trail_end) ≤ open_i + 1 - 1 ∧
    2 ≤ open_i + 1 ∧ open_i + 1 ≤ (end_b - beg) + (slen + 1) ∧
    (mrk2[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
  intro ov mrk2 sstk2
  obtain ⟨_, hw⟩ := hcore.2
  have hcv := hcore.1.core_ok.cur_vars_le
  have hov_nat : ov.toNat = ot.toNat / 2 := bv32_lshr_1 ot
  have hov_lt : ov.toNat < s.core.cur_vars := by rw [hov_nat]; omega
  obtain ⟨hab2, hmono2, hmono8⟩ := m8Shrink_set_bit8_monos hcv hb.mrk_len hov_lt
  have hmin2 := fullMinMarkInv_set_bit8 (m8ShrinkBaseInv_core hcore hb) hb.min_inv hov_lt
  change FullMinMarkInv (m8BlkState s s.core.tmp mrk2 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core
    keep0 at hmin2
  have hb2 : M8ShrinkBaseInv c s mrk2 mclr1 sstk2 wsort1 mcl1 mcf1 (slen + 1) keep0 := by
    refine ⟨by simp [mrk2, hb.mrk_len], hb.mclr_len, hb.mcl_le, by simp [sstk2, hb.sstk_len],
      hb.wsort_len, by omega, fun w hw' => (hab2 w hw').trans (hb.mrk_above w hw'),
      ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩,
      fun w hw' h2 => hmono2 w hw' (hb.mono2 w hw' h2), fun w hw' h8 => ?_, fun j hj => ?_⟩
    · by_cases hwe : w = ov.toNat
      · subst w; exact ⟨slen, by omega, by
          dsimp only [sstk2]; rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega),
            Option.getD_some]⟩
      · dsimp only [mrk2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
        obtain ⟨j, hj, hje⟩ := hb.bit8_sstk w hw' h8
        exact ⟨j, by omega, by dsimp only [sstk2]; rwa [List.getElem?_set_ne (by omega)]⟩
    · dsimp only [sstk2]; by_cases hjs : j = slen
      · subst j; rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
        exact hov_lt
      · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hb.sstk_lt j (by omega)
  refine ⟨hb2, fun j hj1 hj2 => hmono8 _ (hblk_lt j hj1 hj2) (hblk_8 j hj1 hj2), fun j hj => ?_,
    fun w hw' h8 => ?_, ?_, by omega, by omega, ?_⟩
  · dsimp only [sstk2]; by_cases hjs : j = slen
    · subst j; rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
      dsimp only [mrk2]; rw [List.getElem?_set_self (by rw [hb.mrk_len]; omega), Option.getD_some]
      exact bv8_and8_of_or8 _
    · rw [List.getElem?_set_ne (Ne.symm hjs)]
      exact hmono8 _ (hb.sstk_lt j (by omega)) (hsstk_8 j (by omega))
  · by_cases hwe : w = ov.toNat
    · subst w; refine ⟨by rw [hov_nat]; exact hlov_eq, k_ot, Nat.lt_trans hk_lt huip_te, ?_,
        Or.inl hk_tlim⟩
      have hln := litVar_litNeg ot.toNat; unfold litVar litNeg at hln; rw [hk_eq, hln, hov_nat]
    · dsimp only [mrk2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
      obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_pre w hw' h8
      exact ⟨hl, idx, hidx_te, hidx_v, hdisj.elim Or.inl fun h => h.elim
        (fun h2 => Or.inr (Or.inl (shrinkResolved_mono hcore hmono2 hmono8 h2))) (Or.inr ∘ Or.inr)⟩
  · have htc := trailCount8_set_bit8_le (trl := s.core.trl) (mrk := mrk1)
      (fun i j hi hj heq => hw.trail_vars_nodup i j (by omega) (by omega) heq)
      ov.toNat (min (t_lim + 1) s.core.trail_end) (Nat.min_le_right _ _)
    dsimp only [mrk2]; omega
  · rw [← hov_nat]; dsimp only [mrk2]
    rw [List.getElem?_set_self (by rw [hb.mrk_len]; omega), Option.getD_some]
    exact bv8_and8_of_or8 _

theorem m8Shrink_step_pre_mark2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {blvl : BitVec 32} {beg end_b : Nat}
    {mrk1 mrk2 : List (BitVec 8)} {mclr2 sstk1 wsort2 : List (BitVec 32)}
    {mcl2 open_cnt slen t_lim idx_uip : Nat} {mcf2 : BitVec 64} {keep0 : List Nat}
    (hb : M8ShrinkBaseInv c s mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 slen keep0)
    (hmono2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ w < s.core.cur_vars, (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8))
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hblk_8 : M8ShrinkBlk8 s mrk1 beg end_b) (hsstk_8 : M8ShrinkStk8 mrk1 sstk1 slen)
    (h8_pre : M8ShrinkAll8 s blvl mrk1 t_lim idx_uip)
    (hcnt_pre : trailCount8 s.core.trl mrk1 (min (t_lim + 1) s.core.trail_end) ≤ open_cnt - 1) :
    M8ShrinkBlk8 s mrk2 beg end_b ∧ M8ShrinkStk8 mrk2 sstk1 slen ∧
    M8ShrinkAll8 s blvl mrk2 t_lim idx_uip ∧
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

theorem m8Shrink_blk_success_finish {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {beg end_b keepLen : Nat} {blvl : BitVec 32}
    (hbe : beg < end_b) (hek : end_b ≤ keepLen) (hkc : keepLen ≤ s.core.cur_vars)
    (hkeep_spec : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {mrk1 mrkf : List (BitVec 8)} {mclr1 mclrf sstk1 wsort1 tmp' : List (BitVec 32)}
    {mcl1 mclf slen idx_uip : Nat} {mcf1 mcff ticks1 : BitVec 64} {uip : BitVec 32}
    (hb : M8ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen
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
    (hblk1 : M8ShrinkBlk8 s mrk1 beg end_b)
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
  have hcv := hcore.1.core_ok.cur_vars_le; have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have huip_lt : uip.toNat < 2 * s.core.cur_vars := by
    rw [← huip_eq]; exact hw0.trail_lits_lt _ huip_te
  obtain ⟨hnuip_xor, hnuip_lt⟩ := bv32_xor1_toNat_lt huip_lt
  have hnuip_ne : (uip ^^^ 1#32) ≠ 0xFFFFFFFF#32 := by
    intro heq; have := congrArg BitVec.toNat heq
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; rw [hff] at this; omega
  have hnuip_mem : (uip ^^^ 1#32).toNat ∈ keep' := by
    rw [mem_filter_map_toNat_take]
    exact ⟨beg, by rw [htmp_len]; omega, uip ^^^ 1#32, htmp_beg, hnuip_ne, rfl⟩
  have hmin_f : FullMinMarkInv sf.core keep' := by
    refine ⟨hdomf, hcovf, fun idx hi h2f => ?_⟩
    have hv_lt : (s.core.trl[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      have := hw0.trail_lits_lt idx hi; omega
    by_cases hv8 : (mrk1[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8
    · rcases hres _ hv_lt hv8 with hvu | ⟨idx2, hi2, _, hv2, hr2⟩
      · have hidx := hw0.trail_vars_nodup idx idx_uip hi huip_te (by rw [huip_eq]; exact hvu)
        subst hidx; left; rwa [huip_eq, ← hnuip_xor]
      · have hidx := hw0.trail_vars_nodup idx idx2 hi hi2 hv2.symm; subst hidx
        exact Or.inr (by
          simpa [RsnCov, fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
            fullArenaHdrCore, fullArenaClauseSizeCore] using
              shrinkResolved_to_rem hcore hmono1f h8_to_2f hr2)
    · rcases hb.min_inv.rem_sound idx hi ((hnew2_only _ hv_lt h2f).resolve_right hv8) with
        hin | hok
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
    have hwf := m8Witness_shrinkBlk (s := s) hw (tmp1 := tmp') (mrk1 := mrkf)
      (mclr1 := mclrf) (sstk1 := sstk1) (wsort1 := wsort1) (mcl1 := mclf) (mcf1 := mcff)
      (ticks1 := ticks1)
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

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize

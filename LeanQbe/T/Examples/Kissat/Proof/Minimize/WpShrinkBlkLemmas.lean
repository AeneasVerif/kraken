/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkBlkHelpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-!
# Structural Loop & Step Lemmas for `full_shrink_blk_bool_m8`

Purely structural loop invariants (`M8ShrinkClInv`) and store/step preservation lemmas supporting
`WpShrinkBlk`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open FullMinTactics
open scoped FullArenaTactics FullMinTactics

public section

abbrev m8SBlkSt := m8ShrinkBlkBoolState

theorem m8Shrink_init_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {beg end_b keepLen slen k : Nat} {blvl : BitVec 32}
    {max_tr : BitVec 64} {mrk1 : List (BitVec 8)} {sstk1 : List (BitVec 32)}
    (hbeg_k : beg ≤ k) (hk_lt : k < end_b) (hend_kl : end_b ≤ keepLen)
    (hkl_cv : keepLen ≤ s.core.cur_vars)
    (hblk : ∀ j, beg ≤ j → j < end_b →
      let l := (s.core.tmp[j]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
      (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat)
    (hb : M8ShrinkBaseInv c s mrk1 s.core.min_clr sstk1 s.scratch.wsort s.core.min_clr_len
      s.core.min_clr_full slen
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hsstk_8 : M8ShrinkStk8 mrk1 sstk1 slen)
    (hblk_prev : ∀ j, beg ≤ j → j < k →
      (mrk1[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hcnt_le : trailCount8 s.core.trl mrk1 (min (max_tr.toNat + 1) s.core.trail_end) ≤ slen)
    (hno8_other : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, beg ≤ j ∧ j < k ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w)
    (hslen_k : slen = k - beg) (hk_arr : k < s.core.tmp.length) :
    let v := s.core.tmp[k]'hk_arr >>> 1
    let mrk2 := mrk1.set v.toNat (mrk1[v.toNat]?.getD 0#8 ||| 8#8)
    let sstk2 := sstk1.set slen v
    v.toNat < s.core.cur_vars ∧ slen < sstk1.length ∧
    M8ShrinkBaseInv c s mrk2 s.core.min_clr sstk2 s.scratch.wsort s.core.min_clr_len
      s.core.min_clr_full (slen + 1)
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
    M8ShrinkStk8 mrk2 sstk2 (slen + 1) ∧
    (∀ j, beg ≤ j → j < k + 1 →
      (mrk2[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    trailCount8 s.core.trl mrk2 (min (max_tr.toNat + 1) s.core.trail_end) ≤ slen + 1 ∧
    (∀ w < s.core.cur_vars, (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, beg ≤ j ∧ j < k + 1 ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w) := by
  intro v mrk2 sstk2
  obtain ⟨_, hw⟩ := hcore.2
  have hcv := hcore.1.core_ok.cur_vars_le
  have hv_nat : v.toNat = (s.core.tmp[k]?.getD 0#32).toNat / 2 := by
    dsimp only [v]; rw [bv32_lshr_1, List.getElem?_eq_getElem hk_arr, Option.getD_some]
  have hv_lt : v.toNat < s.core.cur_vars := by
    rw [hv_nat]; have := (hblk k hbeg_k hk_lt).1; omega
  have hsl_lt : slen < s.core.cur_vars := by omega
  have hsl_arr : slen < sstk1.length := by rw [hb.sstk_len]; omega
  obtain ⟨hab2, hmono2, hmono8⟩ := m8Shrink_set_bit8_monos hcv hb.mrk_len hv_lt
  have hmin2 := fullMinMarkInv_set_bit8 (m8ShrinkBaseInv_core hcore hb) hb.min_inv hv_lt
  change FullMinMarkInv (m8BlkState s s.core.tmp mrk2 s.core.min_clr sstk1 s.scratch.wsort
    s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks).core _ at hmin2
  have hb2 : M8ShrinkBaseInv c s mrk2 s.core.min_clr sstk2 s.scratch.wsort s.core.min_clr_len
      s.core.min_clr_full (slen + 1)
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
    refine ⟨by simp [mrk2, hb.mrk_len], hb.mclr_len, hb.mcl_le, by simp [sstk2, hb.sstk_len],
      hb.wsort_len, by omega, fun w hw' => (hab2 w hw').trans (hb.mrk_above w hw'), hmin2,
      fun w hw' h2 => hmono2 w hw' (hb.mono2 w hw' h2), fun w hw' h8 => ?_, fun j hj => ?_⟩
    · by_cases hwe : w = v.toNat
      · subst w; exact ⟨slen, by omega, by
          dsimp only [sstk2]; rw [List.getElem?_set_self hsl_arr, Option.getD_some]⟩
      · dsimp only [mrk2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
        obtain ⟨j, hj, hje⟩ := hb.bit8_sstk w hw' h8
        exact ⟨j, by omega, by dsimp only [sstk2]; rwa [List.getElem?_set_ne (by omega)]⟩
    · dsimp only [sstk2]; by_cases hjs : j = slen
      · subst j; rw [List.getElem?_set_self hsl_arr, Option.getD_some]; exact hv_lt
      · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hb.sstk_lt j (by omega)
  have htc := trailCount8_set_bit8_le (trl := s.core.trl) (mrk := mrk1)
    (fun i j hi hj heq => hw.trail_vars_nodup i j (by omega) (by omega) heq)
    v.toNat (min (max_tr.toNat + 1) s.core.trail_end) (Nat.min_le_right _ _)
  refine ⟨hv_lt, hsl_arr, hb2, fun j hj => ?_, fun j hj1 hj2 => ?_, by dsimp only [mrk2]; omega,
    fun w hw' h8 => ?_⟩
  · dsimp only [sstk2]; by_cases hjs : j = slen
    · subst j; rw [List.getElem?_set_self hsl_arr, Option.getD_some]
      dsimp only [mrk2]; rw [List.getElem?_set_self (by rw [hb.mrk_len]; omega), Option.getD_some]
      exact bv8_and8_of_or8 _
    · rw [List.getElem?_set_ne (Ne.symm hjs)]
      exact hmono8 _ (hb.sstk_lt j (by omega)) (hsstk_8 j (by omega))
  · by_cases hjk : j = k
    · subst j; rw [← hv_nat]; dsimp only [mrk2]
      rw [List.getElem?_set_self (by rw [hb.mrk_len]; omega), Option.getD_some]
      exact bv8_and8_of_or8 _
    · have hjl : (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
        have := (hblk j hj1 (by omega)).1; omega
      exact hmono8 _ hjl (hblk_prev j hj1 (by omega))
  · by_cases hwe : w = v.toNat
    · subst w; exact ⟨k, hbeg_k, by omega, hv_nat.symm⟩
    · dsimp only [mrk2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
      obtain ⟨j, hj1, hj2, hje⟩ := hno8_other w hw' h8
      exact ⟨j, hj1, by omega, hje⟩

theorem m8Shrink_init_all8 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {beg end_b : Nat} {blvl : BitVec 32} {max_tr : BitVec 64}
    {mrk1 : List (BitVec 8)}
    (hblk : ∀ j, beg ≤ j → j < end_b →
      let l := (s.core.tmp[j]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
      (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat)
    (hno8_other : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, beg ≤ j ∧ j < end_b ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w) :
    M8ShrinkAll8 s blvl mrk1 max_tr.toNat s.core.trail_end := by
  obtain ⟨_, hw⟩ := hcore.2
  intro w hwv h8
  obtain ⟨j, hj1, hj2, hjeq⟩ := hno8_other w hwv h8
  have hbj := hblk j hj1 hj2
  obtain ⟨idx, hi, hieq⟩ := (hw.vals_false_iff _ hbj.1).mp hbj.2.1
  have hidx_v : (s.core.trl[idx]?.getD 0#32).toNat / 2 = w := by
    have hln := litVar_litNeg (s.core.tmp[j]?.getD 0#32).toNat
    unfold litVar litNeg at hln; rw [hieq, hln, hjeq]
  have htp := hw.trail_pos_inv idx hi
  have htp_eq : (s.core.trail_pos[w]?.getD 0#32).toNat = idx := by rw [← hidx_v]; exact htp
  refine ⟨by rw [← hjeq]; exact hbj.2.2.1, idx, hi, hidx_v, Or.inl ?_⟩
  rw [← htp_eq, ← hjeq]; exact hbj.2.2.2

theorem m8Shrink_trail_found {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {blvl lit : BitVec 32} {mrk1 : List (BitVec 8)}
    {open_i t_in t_cur : Nat}
    (h8_in : M8ShrinkAll8 s blvl mrk1 t_in s.core.trail_end)
    (hcnt_in : trailCount8 s.core.trl mrk1 (min (t_in + 1) s.core.trail_end) ≤ open_i)
    (ht_le : t_cur ≤ t_in) (ht_te : t_cur < s.core.trail_end)
    (hlit_eq : lit = s.core.trl[t_cur]?.getD 0#32)
    (h8_above : ∀ j, t_cur < j → j ≤ min t_in (s.core.trail_end - 1) →
      (mrk1[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8)
    (h8_lit : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) :
    trailCount8 s.core.trl mrk1 t_cur ≤ open_i - 1 ∧
    M8ShrinkAll8 s blvl mrk1 (t_cur - 1) t_cur ∧
    (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
    (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
  obtain ⟨_, hw⟩ := hcore.2
  have hlt2v := hw.trail_lits_lt t_cur ht_te
  have hdiv : (lit >>> 1).toNat = (s.core.trl[t_cur]?.getD 0#32).toNat / 2 := by
    rw [bv32_lshr_1, ← hlit_eq]
  have h8_tc : (mrk1[(s.core.trl[t_cur]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
    rwa [← hdiv]
  have hmn_eq : min (t_in + 1) s.core.trail_end = min t_in (s.core.trail_end - 1) + 1 := by omega
  have htc_zero := trailCount8_eq_of_zero_range (trl := s.core.trl) (mrk := mrk1)
    (a := t_cur + 1) (b := min (t_in + 1) s.core.trail_end) (by omega)
    (fun j hj1 hj2 => h8_above j (by omega) (by omega))
  rw [trailCount8_step_nz h8_tc] at htc_zero
  have hcnt' : trailCount8 s.core.trl mrk1 t_cur ≤ open_i - 1 := by omega
  have h8' : M8ShrinkAll8 s blvl mrk1 (t_cur - 1) t_cur := by
    intro w hwv hw8
    obtain ⟨hl, idx, hi, hv, hdisj⟩ := h8_in w hwv hw8
    refine ⟨hl, idx, hi, hv, ?_⟩
    rcases hdisj with hle | hres | heq_te
    · by_cases hit : idx = t_cur
      · exact Or.inr (Or.inr hit)
      · have hnot : ¬ t_cur < idx := by
          intro hgt
          have hz := h8_above idx hgt (by omega)
          rw [hv] at hz; exact hw8 hz
        exact Or.inl (by omega)
    · exact Or.inr (Or.inl hres)
    · exfalso; omega
  have hbl := (h8' (lit.toNat / 2) (by rw [hlit_eq]; omega)
    (by rwa [← hlit_eq] at h8_tc)).1
  exact ⟨hcnt', h8', h8_lit, hbl⟩

theorem m8Shrink_open1_done {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (_hcore : FullOtfsCoreInv c F0 s) {blvl uip : BitVec 32} {mrk1 : List (BitVec 8)}
    {t_uip : Nat} (ht_te : t_uip < s.core.trail_end)
    (huip_eq : (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat)
    (h8_all : M8ShrinkAll8 s blvl mrk1 (t_uip - 1) t_uip)
    (hcnt : trailCount8 s.core.trl mrk1 t_uip = 0) :
    ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      w = uip.toNat / 2 ∨ ∃ idx < s.core.trail_end, t_uip < idx ∧
        (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧ ShrinkResolved s.core mrk1 idx := by
  intro w hwv hw8
  obtain ⟨_, idx, hi, hv, hdisj⟩ := h8_all w hwv hw8
  rcases hdisj with hlt | hres | heq
  · by_cases ht0 : t_uip = 0
    · rw [ht0] at hlt; have : idx = 0 := by omega
      subst this; left; rw [← hv, ← huip_eq, ht0]
    · exfalso; have hz := trailCount8_eq_zero_mem hcnt (by omega : idx < t_uip)
      rw [hv] at hz; exact hw8 hz
  · by_cases hi_le : t_uip < idx
    · exact Or.inr ⟨idx, hi, hi_le, hv, hres⟩
    · by_cases heq : idx = t_uip
      · subst heq; left; rw [← hv, huip_eq]
      · exfalso; have hz := trailCount8_eq_zero_mem hcnt (by omega : idx < t_uip)
        rw [hv] at hz; exact hw8 hz
  · subst heq; left; rw [← hv, huip_eq]

structure M8ShrinkClInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) (blvl : BitVec 32)
    (beg end_b keepLen : Nat) (mrk0 : List (BitVec 8)) (slen0 t_uip : Nat)
    (uip rsn : BitVec 32) (is_bin : Bool) (open_i slen i_nat : Nat) (failed : Bool)
    (mrk1 : List (BitVec 8)) (mclr1 sstk1 wsort1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 ticks1 : BitVec 64) : Prop where
  base : M8ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen
    (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  mono2_prev : ∀ w < s.core.cur_vars,
    (mrk0[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  ok : failed = false →
    M8ShrinkBlk8 s mrk1 beg end_b ∧ M8ShrinkStk8 mrk1 sstk1 slen ∧
    M8ShrinkAll8 s blvl mrk1 (t_uip - 1) t_uip ∧
    trailCount8 s.core.trl mrk1 t_uip ≤ open_i - 1 ∧
    2 ≤ open_i ∧ open_i ≤ (end_b - beg) + slen ∧
    (∀ k < i_nat, M8ShrinkCovAt s mrk1 t_uip rsn is_bin k)

theorem m8Shrink_cl_after_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn : BitVec 32} {t_uip open_i : Nat} {is_bin : Bool} {mrk1 : List (BitVec 8)}
    (hcore : FullOtfsCoreInv c F0 s) (ht_te : t_uip < s.core.trail_end) (ht_pos : 0 < t_uip)
    (huip_eq : (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat)
    (huip_lvl : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hblvl_lt : blvl.toNat < s.core.cur_level)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[t_uip]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (his_bin : (is_bin = true) ↔ (rsn &&& 0x80000000#32) ≠ 0#32)
    (hcsz_cov : ∀ j < (if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat),
      M8ShrinkCovAt s mrk1 t_uip rsn is_bin j)
    (h8_all : M8ShrinkAll8 s blvl mrk1 (t_uip - 1) t_uip)
    (hcnt : trailCount8 s.core.trl mrk1 t_uip ≤ open_i - 1) :
    M8ShrinkAll8 s blvl mrk1 (t_uip - 1) s.core.trail_end ∧
    trailCount8 s.core.trl mrk1 (min ((t_uip - 1) + 1) s.core.trail_end) ≤ open_i - 1 := by
  have hres : ShrinkResolved s.core mrk1 t_uip := by
    apply shrink_rsn_loop_done hcore ht_te (by rw [huip_eq, huip_lvl]; exact hblvl_lt)
      (by rwa [← hrsn_eq])
    dsimp only; rw [← hrsn_eq]; intro j hj
    by_cases hbn : (rsn &&& 0x80000000#32) ≠ 0#32
    · have hibt : is_bin = true := his_bin.mpr hbn
      have hj' := hcsz_cov j (by
        simp only [eq_true hbn, ↓reduceIte] at hj; simp only [eq_true hibt, ↓reduceIte]; exact hj)
      simpa only [M8ShrinkCovAt, m8ShrinkRsnLit, eq_true hibt, eq_true hbn, ↓reduceIte] using hj'
    · have hibf : is_bin = false := Bool.eq_false_iff.mpr fun ht => hbn (his_bin.mp ht)
      have hf' : (is_bin = true) = False := by rw [hibf]; exact Bool.false_eq_true
      have hj' := hcsz_cov j (by
        simp only [eq_false hbn, ↓reduceIte] at hj; simp only [hf', ↓reduceIte]; exact hj)
      simpa only [M8ShrinkCovAt, m8ShrinkRsnLit, hf', eq_false hbn, ↓reduceIte] using hj'
  refine ⟨fun w hwv hw8 => ?_, ?_⟩
  · obtain ⟨hl, idx, hi, hv, hdisj⟩ := h8_all w hwv hw8
    refine ⟨hl, idx, hi, hv, ?_⟩
    rcases hdisj with hle | hsr | hit
    · exact Or.inl hle
    · exact Or.inr (Or.inl hsr)
    · subst hit; exact Or.inr (Or.inl hres)
  · rw [show t_uip - 1 + 1 = t_uip by omega, Nat.min_eq_left (le_of_lt ht_te)]; exact hcnt

theorem m8SBlk_store_mrk {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 8)
    (hi : i.toNat < (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core.mrk.length)
    (hm : (FullMem c (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R) m) :
    storeOk m i8 (c.pMark + i) ∧
      (FullMem c (m8SBlkSt s tmp1 (mrk1.set i.toNat v) mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆
        R) (storeMem m i8 (c.pMark + i) v) := by
  dsimp only [m8SBlkSt, m8ShrinkBlkBoolState] at hi hm ⊢
  exact c0_store_full_mrk v hi hm

theorem m8SBlk_store_sstk {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 32)
    (hi : i.toNat <
      (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).scratch.shrink_stk.length)
    (hm : (FullMem c (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R) m) :
    storeOk m i32 (c.pShrinkStk + i * 4) ∧
      (FullMem c (m8SBlkSt s tmp1 mrk1 mclr1 (sstk1.set i.toNat v) wsort1 mcl1 mcf1 ticks1) ⋆
        R) (storeMem m i32 (c.pShrinkStk + i * 4) v) := by
  dsimp only [m8SBlkSt, m8ShrinkBlkBoolState] at hi hm ⊢
  exact c0_store_full_shrink_stk v hi hm

theorem m8SBlk_store_tmp {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 32)
    (hi : i.toNat < (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core.tmp.length)
    (hm : (FullMem c (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧
      (FullMem c (m8SBlkSt s (tmp1.set i.toNat v) mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆
        R) (storeMem m i32 (c.pTmp + i * 4) v) := by
  dsimp only [m8SBlkSt, m8ShrinkBlkBoolState] at hi hm ⊢
  exact c0_store_full_tmp v hi hm

theorem m8SBlk_reason_facts {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {t_uip : Nat} {uip blvl rsn : BitVec 32} {is_bin : Bool}
    (ht_te : t_uip < s.core.trail_end)
    (huip_eq : (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat)
    (huip_lvl : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hblvl_lt : blvl.toNat < s.core.cur_level)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[t_uip]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (his_bin : (is_bin = true) ↔ (rsn &&& 0x80000000#32) ≠ 0#32) :
    (is_bin = false →
      rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      rsn.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core rsn.toNat ∧
      rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤ s.core.arena_len) ∧
    (∀ k < (if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat),
      let q := m8ShrinkRsnLit s rsn is_bin k
      q < 2 * s.core.cur_vars ∧
      (q = uip.toNat ∨ ∃ m < t_uip, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ blvl.toNat)) := by
  obtain ⟨_, hw⟩ := hcore.2
  have hr := hw.reason_inv_below t_uip ht_te (by rw [huip_eq, huip_lvl]; exact hblvl_lt)
    (by rwa [← hrsn_eq])
  rw [← hrsn_eq] at hr
  refine ⟨fun hbf => ?_, fun k hk => ?_⟩
  · have hb : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := fun ht => by
      have := his_bin.mpr ht; rw [hbf] at this; cases this
    simp only [eq_false hb, ↓reduceIte] at hr
    have hwf := hw.arena.refs_wf _ hr.1
    exact ⟨hr.1, hr.2.1, hwf.1, hwf.2.1,
      Nat.le_trans (by have := hwf.2.2.1; omega) hwf.2.2.2.1⟩
  · by_cases hbt : (rsn &&& 0x80000000#32) ≠ 0#32
    · have hibt : is_bin = true := his_bin.mpr hbt
      simp only [eq_true hbt, ↓reduceIte] at hr
      have hq : m8ShrinkRsnLit s rsn is_bin k = (rsn &&& 0x7FFFFFFF#32).toNat := by
        simp [m8ShrinkRsnLit, hibt]
      rw [hq]; obtain ⟨hlt, _, m, hm, hmeq, hml⟩ := hr
      exact ⟨hlt, Or.inr ⟨m, hm, hmeq, by rw [huip_eq, huip_lvl] at hml; exact hml⟩⟩
    · have hibf : is_bin = false := Bool.eq_false_iff.mpr fun ht => hbt (his_bin.mp ht)
      simp only [hibf] at hk
      simp only [eq_false hbt, ↓reduceIte] at hr
      have hq : m8ShrinkRsnLit s rsn is_bin k =
          (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat := by simp [m8ShrinkRsnLit, hibf]
      have hmem := shrink_arena_lits_mem hcore hr.1 hk
      have hq_lt := hw.arena.lits_lt _ hr.1 hr.2.1 _ hmem
      rw [hq]
      rcases hr.2.2 _ hmem with heq | ⟨m, hm, hmeq, hml⟩
      · exact ⟨hq_lt, Or.inl (by rw [heq, huip_eq])⟩
      · exact ⟨hq_lt, Or.inr ⟨m, hm, hmeq, by rw [huip_eq, huip_lvl] at hml; exact hml⟩⟩

theorem m8Shrink_cl_step_skip {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn ot : BitVec 32} {beg end_b keepLen slen0 t_uip open_i slen i_nat mcl1 : Nat}
    {mrk0 mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcf1 ticks1 : BitVec 64}
    {is_bin : Bool} (hcore : FullOtfsCoreInv c F0 s) (ht_te : t_uip < s.core.trail_end)
    (hinv : M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen i_nat false mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1)
    (hot_eq : ot.toNat = m8ShrinkRsnLit s rsn is_bin i_nat)
    (hstep : ot.toNat = uip.toNat ∨ ∃ m < t_uip, (s.core.trl[m]?.getD 0#32).toNat = ot.toNat ^^^ 1 ∧
      ((s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 ∨
        (mrk1[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8))
    (huip_eq : (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat) :
    M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen (i_nat + 1) false mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 := by
  obtain ⟨hblk, hstk, h8, hcnt, hop2, hopl, hcov⟩ := hinv.ok rfl
  refine ⟨hinv.base, hinv.mono2_prev, fun _ => ⟨hblk, hstk, h8, hcnt, hop2, hopl, ?_⟩⟩
  refine m8Shrink_cov_lift hcore ht_te (fun _ _ h => h) (fun _ _ h => h) hcov hot_eq ?_
  rcases hstep with heq | ⟨m, hm, hmeq, hdep⟩
  · exact Or.inl (heq.trans huip_eq.symm)
  · exact Or.inr ⟨m, hm, hmeq, hdep.elim Or.inl (Or.inr ∘ Or.inr)⟩

theorem m8Shrink_cl_step_lower_ok {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn ot : BitVec 32} {beg end_b keepLen slen0 t_uip open_i slen i_nat mcl1 mcl2 : Nat}
    {mrk0 mrk1 mrk2 : List (BitVec 8)} {mclr1 mclr2 sstk1 wsort1 wsort2 : List (BitVec 32)}
    {mcf1 mcf2 ticks1 ticks2 : BitVec 64} {is_bin : Bool}
    (hcore : FullOtfsCoreInv c F0 s) (ht_te : t_uip < s.core.trail_end)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hinv : M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen i_nat false mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1)
    (hot_eq : ot.toNat = m8ShrinkRsnLit s rsn is_bin i_nat)
    (hot_src : ∃ m < t_uip, (s.core.trl[m]?.getD 0#32).toNat = ot.toNat ^^^ 1)
    (hlok : (m8SBlkSt s s.core.tmp mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 ticks2).LengthsOk c)
    (hab : ∀ w, s.core.cur_vars ≤ w → mrk2[w]? = mrk1[w]?)
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8))
    (hmin2 : FullMinMarkInv
      (m8SBlkSt s s.core.tmp mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 ticks2).core
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hgot2 : (mrk2[(ot >>> 1).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen (i_nat + 1) false mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 ticks2 := by
  have hb := hinv.base
  obtain ⟨hblk, hstk, h8, hcnt, hop2, hopl, hcov⟩ := hinv.ok rfl
  have hb2 : M8ShrinkBaseInv c s mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 slen
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
    refine ⟨hlok.core_ok.mrk_len, hlok.core_ok.min_clr_len_arr, hlok.core_ok.min_clr_len_le,
      hb.sstk_len, hlok.scratch_ok.wsort_len, hb.slen_le,
      fun w hw => (hab w hw).trans (hb.mrk_above w hw),
      ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩,
      fun w hw h2 => hm2 w hw (hb.mono2 w hw h2), fun w hw h8w => ?_, hb.sstk_lt⟩
    rw [hm8 w hw] at h8w; exact hb.bit8_sstk w hw h8w
  obtain ⟨m, hm, hmeq⟩ := hot_src
  obtain ⟨hblk2, hstk2, h8_2, hcnt2⟩ := m8Shrink_step_pre_mark2 hcore hb2 hm2 hm8 hblk_lt
    hblk hstk h8 (by rw [show t_uip - 1 + 1 = t_uip by omega,
      Nat.min_eq_left (le_of_lt ht_te)]; exact hcnt)
  rw [show t_uip - 1 + 1 = t_uip by omega, Nat.min_eq_left (le_of_lt ht_te)] at hcnt2
  refine ⟨hb2, fun w hw h0 => hm2 w hw (hinv.mono2_prev w hw h0),
    fun _ => ⟨hblk2, hstk2, h8_2, hcnt2, hop2, hopl, ?_⟩⟩
  refine m8Shrink_cov_lift hcore ht_te hm2 (fun w hw h8w => by rw [hm8 w hw]; exact h8w) hcov
    hot_eq (Or.inr ?_)
  exact ⟨m, hm, hmeq, Or.inr (Or.inl (by rwa [← bv32_lshr_1 ot]))⟩

theorem m8Shrink_cl_step_fail {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn : BitVec 32} {beg end_b keepLen slen0 t_uip open_i slen i_nat mcl1 mcl2 : Nat}
    {mrk0 mrk1 mrk2 : List (BitVec 8)} {mclr1 mclr2 sstk1 wsort1 wsort2 : List (BitVec 32)}
    {mcf1 mcf2 ticks1 ticks2 : BitVec 64} {is_bin : Bool}
    (hinv : M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen i_nat false mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1)
    (hlok : (m8SBlkSt s s.core.tmp mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 ticks2).LengthsOk c)
    (hab : ∀ w, s.core.cur_vars ≤ w → mrk2[w]? = mrk1[w]?)
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8))
    (hmin2 : FullMinMarkInv
      (m8SBlkSt s s.core.tmp mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 ticks2).core
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen (i_nat + 1) true mrk2 mclr2 sstk1 wsort2 mcl2 mcf2 ticks2 := by
  have hb := hinv.base
  refine ⟨⟨hlok.core_ok.mrk_len, hlok.core_ok.min_clr_len_arr, hlok.core_ok.min_clr_len_le,
      hb.sstk_len, hlok.scratch_ok.wsort_len, hb.slen_le,
      fun w hw => (hab w hw).trans (hb.mrk_above w hw),
      ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩,
      fun w hw h2 => hm2 w hw (hb.mono2 w hw h2),
      fun w hw h8w => by rw [hm8 w hw] at h8w; exact hb.bit8_sstk w hw h8w, hb.sstk_lt⟩,
    fun w hw h0 => hm2 w hw (hinv.mono2_prev w hw h0), fun h => by cases h⟩

theorem m8Shrink_cl_step_push {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn ot : BitVec 32} {beg end_b keepLen slen0 t_uip open_i slen i_nat mcl1 : Nat}
    {mrk0 mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)} {mcf1 ticks1 : BitVec 64}
    {is_bin : Bool} (hcore : FullOtfsCoreInv c F0 s) (ht_te : t_uip < s.core.trail_end)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hinv : M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      open_i slen i_nat false mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1)
    (hot_eq : ot.toNat = m8ShrinkRsnLit s rsn is_bin i_nat)
    (hot_bd : ot.toNat < 2 * s.core.cur_vars)
    (hot_src : ∃ m < t_uip, (s.core.trl[m]?.getD 0#32).toNat = ot.toNat ^^^ 1)
    (hlov : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hsl_lt : slen < s.core.cur_vars) :
    let ov := ot >>> 1
    let mrk2 := mrk1.set ov.toNat (mrk1[ov.toNat]?.getD 0#8 ||| 8#8)
    let sstk2 := sstk1.set slen ov
    M8ShrinkClInv c F0 s blvl beg end_b keepLen mrk0 slen0 t_uip uip rsn is_bin
      (open_i + 1) (slen + 1) (i_nat + 1) false mrk2 mclr1 sstk2 wsort1 mcl1 mcf1 ticks1 := by
  intro ov mrk2 sstk2
  have hb := hinv.base
  obtain ⟨hblk, hstk, h8, hcnt, hop2, hopl, hcov⟩ := hinv.ok rfl
  obtain ⟨m, hm, hmeq⟩ := hot_src
  have hcv := hcore.1.core_ok.cur_vars_le
  have hov_lt : ov.toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
  obtain ⟨_, hmono2, hmono8⟩ := m8Shrink_set_bit8_monos hcv hb.mrk_len hov_lt
  obtain ⟨hb2, hblk2, hstk2, h8_2, hcnt2, hop2', hopl', h8ov⟩ := m8Shrink_step_pre_push8
    (ticks1 := ticks1) hcore hb
    hblk_lt hblk hstk h8 (by rw [show t_uip - 1 + 1 = t_uip by omega,
      Nat.min_eq_left (le_of_lt ht_te)]; exact hcnt) hop2 hopl hsl_lt hot_bd ht_te hm hmeq
    (by omega) hlov
  rw [show t_uip - 1 + 1 = t_uip by omega, Nat.min_eq_left (le_of_lt ht_te)] at hcnt2
  refine ⟨hb2, fun w hw h0 => hmono2 w hw (hinv.mono2_prev w hw h0),
    fun _ => ⟨hblk2, hstk2, h8_2, hcnt2, hop2', hopl', ?_⟩⟩
  exact m8Shrink_cov_lift hcore ht_te hmono2 hmono8 hcov hot_eq
    (Or.inr ⟨m, hm, hmeq, Or.inr (Or.inr h8ov)⟩)

theorem m8Shrink_clear_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)}
    {mcl1 slen i : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hcore : FullOtfsCoreInv c F0 s) (hb : M8ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1
      slen keep0) (hi : i < slen)
    (hrem8 : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, i ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w) :
    let sv := sstk1[i]'(by
      rw [hb.sstk_len]; have := hb.slen_le; have := hcore.1.core_ok.cur_vars_le; omega)
    let mrk2 := mrk1.set sv.toNat (mrk1[sv.toNat]?.getD 0#8 &&& 0xF7#8)
    sv.toNat < s.core.cur_vars ∧ sv.toNat < mrk1.length ∧
    M8ShrinkBaseInv c s mrk2 mclr1 sstk1 wsort1 mcl1 mcf1 slen keep0 ∧
    (∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ w < s.core.cur_vars, (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, i + 1 ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w) := by
  intro sv mrk2
  have hcv := hcore.1.core_ok.cur_vars_le; have := hb.slen_le
  have hsv_lt : sv.toNat < s.core.cur_vars := by
    have := hb.sstk_lt i hi
    rwa [List.getElem?_eq_getElem (by rw [hb.sstk_len]; omega), Option.getD_some] at this
  have hsv_arr : sv.toNat < mrk1.length := by rw [hb.mrk_len]; omega
  have hm2 : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w _ h2 => by
    dsimp only [mrk2]; by_cases hwe : w = sv.toNat
    · subst w; rwa [List.getElem?_set_self hsv_arr, Option.getD_some, bv8_and2_pres_clear8]
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  have hrem' : ∀ w < s.core.cur_vars, (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, i + 1 ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w := fun w hw h8 => by
    dsimp only [mrk2] at h8; by_cases hwe : w = sv.toNat
    · subst w; rw [List.getElem?_set_self hsv_arr, Option.getD_some] at h8
      exact absurd (bv8_and8_clear _) h8
    · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
      obtain ⟨j, hj1, hj2, hjeq⟩ := hrem8 w hw h8
      refine ⟨j, ?_, hj2, hjeq⟩
      by_cases hji : j = i
      · subst j; exfalso; apply hwe
        rw [← hjeq, List.getElem?_eq_getElem (by rw [hb.sstk_len]; omega), Option.getD_some]
      · omega
  have hmin2 := fullMinMarkInv_clear_bit8 (m8ShrinkBaseInv_core hcore hb) hb.min_inv hsv_lt
  change FullMinMarkInv (m8BlkState s s.core.tmp mrk2 mclr1 sstk1 wsort1
    mcl1 mcf1 s.scratch.search_ticks).core keep0 at hmin2
  have hb2 : M8ShrinkBaseInv c s mrk2 mclr1 sstk1 wsort1 mcl1 mcf1 slen keep0 := by
    refine ⟨by simp [mrk2, hb.mrk_len], hb.mclr_len, hb.mcl_le, hb.sstk_len, hb.wsort_len,
      hb.slen_le, fun w hw => by
        dsimp only [mrk2]; rw [List.getElem?_set_ne (by omega)]; exact hb.mrk_above w hw,
      ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩,
      fun w hw h2 => hm2 w hw (hb.mono2 w hw h2), fun w hw h8 => ?_, hb.sstk_lt⟩
    obtain ⟨j, _, hj2, hjeq⟩ := hrem' w hw h8; exact ⟨j, hj2, hjeq⟩
  exact ⟨hsv_lt, hsv_arr, hb2, hm2, hrem'⟩

theorem m8Shrink_succ_tmp_step {tmp1 : List (BitVec 32)} {beg k len mv : Nat}
    (hlen : tmp1.length = mv) (hk_lt : k < len) (_hb_k : beg ≤ k) (hkl : len ≤ mv)
    (hff : ∀ j, beg ≤ j → j < k → tmp1[j]? = some 0xFFFFFFFF#32) :
    let tmp2 := tmp1.set k 0xFFFFFFFF#32
    k < tmp1.length ∧ tmp2.length = mv ∧
    (∀ j, beg ≤ j → j < k + 1 → tmp2[j]? = some 0xFFFFFFFF#32) := by
  intro tmp2
  have hk_arr : k < tmp1.length := by rw [hlen]; omega
  refine ⟨hk_arr, by simp [tmp2, hlen], fun j hj1 hj2 => ?_⟩
  by_cases hjk : j = k
  · subst j; exact List.getElem?_set_self hk_arr
  · dsimp only [tmp2]; rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hff j hj1 (by omega)

theorem m8Shrink_succ_mark_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {mrk1 mrk_i mrk_fin : List (BitVec 8)}
    {mclr_i mclr_fin sstk1 wsort1 tmp2 : List (BitVec 32)}
    {mcl_i mcl_fin slen i : Nat} {mcf_i mcf_fin ticks1 : BitVec 64}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsstk : sstk1.length = c.max_vars) (hslen : slen ≤ s.core.cur_vars)
    (hsstk_lt : ∀ j < slen, (sstk1[j]?.getD 0#32).toNat < s.core.cur_vars)
    (hsstk_8 : M8ShrinkStk8 mrk1 sstk1 slen) (hi : i < slen)
    (hmrki : mrk_i.length = c.max_vars) (hmclri : mclr_i.length = c.max_vars)
    (hmcli : mcl_i ≤ c.max_vars)
    (hdom_i : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcov_i : mcf_i = 0#64 → ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < mcl_i, (mclr_i[k]?.getD 0#32).toNat = w)
    (hm_above : ∀ w, s.core.cur_vars ≤ w → mrk_i[w]? = mrk1[w]?)
    (hm2_i : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hdone_2 : ∀ k < i, (mrk_i[(sstk1[k]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hrem8 : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, i ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w)
    (hnew2_i : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (h8_orig : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (htmp_len : tmp2.length = c.max_vars) (hw_len : wsort1.length = 2 * c.max_vars)
    (hstep :
      let sv := sstk1[i]'(by rw [hsstk]; have := hcore.1.core_ok.cur_vars_le; omega)
      let mrk_mid := mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8)
      let st_mid := m8BlkState s tmp2 mrk_mid mclr_i sstk1 wsort1 mcl_i mcf_i ticks1
      let st_fin := fullMinMarkStepState st_mid sv.toNat 2#8
      st_fin = m8BlkState s tmp2 mrk_fin mclr_fin sstk1 wsort1 mcl_fin mcf_fin ticks1) :
    let sv := sstk1[i]'(by rw [hsstk]; have := hcore.1.core_ok.cur_vars_le; omega)
    let mrk_mid := mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8)
    let st_mid := m8BlkState s tmp2 mrk_mid mclr_i sstk1 wsort1 mcl_i mcf_i ticks1
    sv.toNat < s.core.cur_vars ∧ sv.toNat < mrk_i.length ∧
    st_mid.LengthsOk c ∧ (mrk_mid[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8 ∧
    (∀ w < s.core.cur_vars, (mrk_mid[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
    (mcf_i = 0#64 → ∀ w < s.core.cur_vars, (mrk_mid[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < mcl_i, (mclr_i[k]?.getD 0#32).toNat = w) ∧
    (mrk_fin.length = c.max_vars ∧ mclr_fin.length = c.max_vars ∧ mcl_fin ≤ c.max_vars ∧
      (∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
      (mcf_fin = 0#64 → ∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
        ∃ k < mcl_fin, (mclr_fin[k]?.getD 0#32).toNat = w) ∧
      (∀ w, s.core.cur_vars ≤ w → mrk_fin[w]? = mrk1[w]?) ∧
      (∀ w < s.core.cur_vars,
        (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_fin[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (∀ k < i + 1, (mrk_fin[(sstk1[k]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
        ∃ j, i + 1 ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w) ∧
      (∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
        (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8)) := by
  intro sv mrk_mid st_mid
  have hcv := hcore.1.core_ok.cur_vars_le
  have hsi : (sstk1[i]?.getD 0#32) = sv := by
    rw [List.getElem?_eq_getElem (by rw [hsstk]; omega), Option.getD_some]
  have hsv_lt : sv.toNat < s.core.cur_vars := by have := hsstk_lt i hi; rwa [hsi] at this
  have hsv_arr : sv.toNat < mrk_i.length := by rw [hmrki]; omega
  have hsv_8 : (mrk1[sv.toNat]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
    have := hsstk_8 i hi; rwa [hsi] at this
  have hm_mid_8 : (mrk_mid[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
    dsimp only [mrk_mid]; rw [List.getElem?_set_self hsv_arr, Option.getD_some]
    exact bv8_and8_clear _
  have hdom_mid : ∀ w < s.core.cur_vars, (mrk_mid[w]?.getD 0#8 &&& 0xF1#8) = 0#8 := fun w hw => by
    dsimp only [mrk_mid]; by_cases hwe : w = sv.toNat
    · subst w; rw [List.getElem?_set_self hsv_arr, Option.getD_some]
      exact bv8_and_dom_clear8 (hdom_i _ hw)
    · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hdom_i w hw
  have hcov_mid : mcf_i = 0#64 → ∀ w < s.core.cur_vars, (mrk_mid[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < mcl_i, (mclr_i[k]?.getD 0#32).toNat = w := fun hmcf w hw hnz => by
    refine hcov_i hmcf w hw ?_
    dsimp only [mrk_mid] at hnz; by_cases hwe : w = sv.toNat
    · subst w; rwa [List.getElem?_set_self hsv_arr, Option.getD_some, bv8_and6_pres_clear8] at hnz
    · rwa [List.getElem?_set_ne (Ne.symm hwe)] at hnz
  have hm2_mid : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk_mid[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w _ h2 => by
    dsimp only [mrk_mid]; by_cases hwe : w = sv.toNat
    · subst w; rwa [List.getElem?_set_self hsv_arr, Option.getD_some, bv8_and2_pres_clear8]
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  have hst_mid_ok : st_mid.LengthsOk c :=
    (m8CoreInv_blk hcore htmp_len (by simp [mrk_mid, hmrki]) hmclri hmcli hsstk hw_len).1
  have hlen_fin := fullMinMarkStepState_lengths hst_mid_ok sv.toNat 2#8
  have hab_fin := fullMinMarkStepState_mrk_above (s := st_mid) hsv_lt 2#8
  obtain ⟨hbit8_fin, hm2_fin⟩ := fullMinMarkStepState_bit8_mono2 hst_mid_ok hsv_lt
    (Or.inl rfl) hm_mid_8
  obtain ⟨hdom_fin, hcov_fin⟩ := fullMinMarkStepState_dom_clr hst_mid_ok hdom_mid hcov_mid
    hsv_lt (Or.inl rfl) hm_mid_8
  have hm_e : (fullMinMarkStepState st_mid sv.toNat 2#8).core.mrk = mrk_fin :=
    congrArg (fun x => x.core.mrk) hstep
  have hmc_e : (fullMinMarkStepState st_mid sv.toNat 2#8).core.min_clr = mclr_fin :=
    congrArg (fun x => x.core.min_clr) hstep
  have hmcl_e : (fullMinMarkStepState st_mid sv.toNat 2#8).core.min_clr_len = mcl_fin :=
    congrArg (fun x => x.core.min_clr_len) hstep
  have hmcf_e : (fullMinMarkStepState st_mid sv.toNat 2#8).core.min_clr_full = mcf_fin :=
    congrArg (fun x => x.core.min_clr_full) hstep
  have hstep_sv2 : (mrk_fin[sv.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    rw [← hm_e]; dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
    split
    · rename_i hor; rcases hor with hge | hne
      · exfalso; change s.core.cur_vars ≤ sv.toNat at hge; exact absurd hge (by omega)
      · exact hne
    · dsimp only [fullMinMarkCore]
      rw [List.getElem?_set_self (by
          change sv.toNat < mrk_mid.length; simp [mrk_mid, hmrki]; omega),
        Option.getD_some]
      exact bv8_and2_of_or2 _
  have hbit8_mid : ∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 8#8) =
      (mrk_mid[w]?.getD 0#8 &&& 8#8) := fun w hw => by rw [← hm_e]; exact hbit8_fin w hw
  have hrem_fin : ∀ w < s.core.cur_vars, (mrk_fin[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, i + 1 ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w := fun w hw h8w => by
    rw [hbit8_mid w hw] at h8w; dsimp only [mrk_mid] at h8w
    by_cases hwe : w = sv.toNat
    · subst w; rw [List.getElem?_set_self hsv_arr, Option.getD_some] at h8w
      exact absurd (bv8_and8_clear _) h8w
    · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
      obtain ⟨j, hj1, hj2, hjeq⟩ := hrem8 w hw h8w
      refine ⟨j, ?_, hj2, hjeq⟩
      by_cases hji : j = i
      · subst j; exfalso; apply hwe; rw [← hjeq, hsi]
      · omega
  refine ⟨hsv_lt, hsv_arr, hst_mid_ok, hm_mid_8, hdom_mid, hcov_mid,
    by rw [← hm_e]; exact hlen_fin.core_ok.mrk_len,
    by rw [← hmc_e]; exact hlen_fin.core_ok.min_clr_len_arr,
    by rw [← hmcl_e]; exact hlen_fin.core_ok.min_clr_len_le,
    fun w hw => by rw [← hm_e]; exact hdom_fin w hw,
    fun hmcf w hw hnz => by
      rw [← hm_e] at hnz; rw [← hmc_e, ← hmcl_e]
      exact hcov_fin (by rwa [hmcf_e]) w hw hnz,
    fun w hw => by
      rw [← hm_e, hab_fin w hw]
      dsimp only [st_mid, m8BlkState, m8ShrinkBlkBoolState, mrk_mid]
      rw [List.getElem?_set_ne (by omega)]; exact hm_above w hw,
    fun w hw h2 => by
      rw [← hm_e]; exact hm2_fin w hw (hm2_mid w hw (hm2_i w hw h2)),
    fun k hk => by
      by_cases hki : k = i
      · subst k; rwa [hsi]
      · have hk' : k < i := by omega
        have hlt_k := hsstk_lt k (by omega)
        rw [← hm_e]; exact hm2_fin _ hlt_k (hm2_mid _ hlt_k (hdone_2 k hk')),
    hrem_fin, fun w hw h2 => ?_, fun w hw h8w => ?_⟩
  · by_cases hwe : w = sv.toNat
    · subst w; exact Or.inr hsv_8
    · have h2_mid : (mrk_mid[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        rw [← hm_e] at h2; dsimp only [fullMinMarkStepState, fullMinMarkStepCore] at h2
        split at h2
        · exact h2
        · dsimp only [fullMinMarkCore] at h2; rwa [List.getElem?_set_ne (Ne.symm hwe)] at h2
      dsimp only [mrk_mid] at h2_mid; rw [List.getElem?_set_ne (Ne.symm hwe)] at h2_mid
      exact hnew2_i w hw h2_mid
  · rw [hbit8_mid w hw] at h8w; dsimp only [mrk_mid] at h8w
    by_cases hwe : w = sv.toNat
    · subst w; rw [List.getElem?_set_self hsv_arr, Option.getD_some] at h8w
      exact absurd (bv8_and8_clear _) h8w
    · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w; exact h8_orig w hw h8w

theorem m8Shrink_tmp_nodup {s : FullState} {beg end_b keepLen : Nat} {blvl uip : BitVec 32}
    {tmp' : List (BitVec 32)} (htmp_le : keepLen ≤ s.core.tmp.length)
    (htmp'_le : keepLen ≤ tmp'.length)
    (huip_lvl : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (htmp_out : ∀ k < keepLen, (k < beg ∨ end_b ≤ k) → tmp'[k]? = s.core.tmp[k]?)
    (htmp_beg : tmp'[beg]? = some (uip ^^^ 1#32))
    (htmp_rest : ∀ k, beg < k → k < end_b → tmp'[k]? = some 0xFFFFFFFF#32)
    (hnd0 : (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
      fun x => x.toNat / 2).Nodup)
    (hout_lvl : ∀ k < keepLen, (k < beg ∨ end_b ≤ k) →
      s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) :
    (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup := by
  rw [nodup_filter_map_div2_iff htmp'_le]
  intro i j hij hj hni hnj heq
  have hnone_mid : ∀ k, beg < k → k < end_b → tmp'[k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun k h1 h2 => by rw [htmp_rest k h1 h2, Option.getD_some]
  by_cases hi_in : beg ≤ i ∧ i < end_b
  · have hib : i = beg := by
      by_cases he : i = beg; · exact he
      exfalso; exact hni (hnone_mid i (by omega) hi_in.2)
    subst i
    have hj_out : j < beg ∨ end_b ≤ j := by
      by_cases hjb : j < end_b
      · exfalso; exact hnj (hnone_mid j hij hjb)
      · exact Or.inr (by omega)
    have hlv_i : (s.core.lvl[(tmp'[beg]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
      rw [htmp_beg, Option.getD_some, (bv32_xor1_toNat_lt (by omega : uip.toNat < 2 * 2^31)).1,
        xor1_div2, huip_lvl]
    have hnj_orig : s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rwa [← htmp_out j hj hj_out]
    have hlv_j := hout_lvl j hj hj_out hnj_orig
    have hteq : tmp'[j]? = s.core.tmp[j]? := htmp_out j hj hj_out
    have hgj : (tmp'[j]?.getD 0#32).toNat / 2 = (s.core.tmp[j]?.getD 0#32).toNat / 2 := by
      rw [hteq]
    rw [← heq] at hgj; rw [← hgj] at hlv_j; exact hlv_j hlv_i
  · have hi_out : i < beg ∨ end_b ≤ i := by omega
    by_cases hj_in : beg ≤ j ∧ j < end_b
    · have hjb : j = beg := by
        by_cases he : j = beg; · exact he
        exfalso; exact hnj (hnone_mid j (by omega) hj_in.2)
      subst j
      have hlv_j : (s.core.lvl[(tmp'[beg]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          blvl.toNat := by
        rw [htmp_beg, Option.getD_some, (bv32_xor1_toNat_lt (by omega : uip.toNat < 2 * 2^31)).1,
          xor1_div2, huip_lvl]
      have hni_orig : s.core.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rwa [← htmp_out i (by omega) hi_out]
      have hlv_i := hout_lvl i (by omega) hi_out hni_orig
      have htei : tmp'[i]? = s.core.tmp[i]? := htmp_out i (by omega) hi_out
      have hgi : (tmp'[i]?.getD 0#32).toNat / 2 = (s.core.tmp[i]?.getD 0#32).toNat / 2 := by
        rw [htei]
      rw [heq] at hgi; rw [← hgi] at hlv_i; exact hlv_i hlv_j
    · have hj_out : j < beg ∨ end_b ≤ j := by omega
      have hall := (nodup_filter_map_div2_iff htmp_le).mp hnd0 i j hij hj
      rw [htmp_out i (by omega) hi_out] at hni heq
      rw [htmp_out j hj hj_out] at hnj heq
      exact hall hni hnj heq

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize

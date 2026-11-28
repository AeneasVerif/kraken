/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Feature-ID Extraction WP Proofs (`WpExtractFid`)

Canonical `Func.wp` proofs for `full_cong_extract_and_clause_fid` and
`full_cong_extract_from_fid`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

private theorem andExtract_litNeg_invol (x : Nat) : litNeg (litNeg x) = x := by
  unfold litNeg; rw [Nat.xor_assoc, show 1 ^^^ 1 = 0 from rfl, Nat.xor_zero]

private theorem andExtract_not_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hx

private theorem idx_get_eq {α : Type _} {l : List α} {i1 i2 : Nat}
    (h1 : i1 < l.length) (h2 : i2 < l.length) (hi : i1 = i2) : l[i1] = l[i2] := by
  subst hi; rfl

private abbrev aeMem (c : FullCfg) (s : FullState) (lm : List (BitVec 8))
    (scr : List (BitVec 32)) (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  (FullMem c { s with
    core := { s.core with lit_mark := lm },
    scratch := { s.scratch with scratch_buf := scr } } ⋆ R) m

private abbrev aeMarkInv (c : FullCfg) (ws2 : List (BitVec 32)) (usz : Nat)
    (lm : List (BitVec 8)) : Prop :=
  ∀ l, l < 2 * c.max_vars → lm[l]?.getD 0#8 ≠ 0#8 →
    ∃ k, k < usz ∧ l = litNeg (ws2[k]?.getD 0#32).toNat

private abbrev aeBit2Clr (c : FullCfg) (lm : List (BitVec 8)) : Prop :=
  ∀ l, l < 2 * c.max_vars → (lm[l]?.getD 0#8 &&& 2#8) = 0#8

private abbrev aeStateInv (maxA : Nat) (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (usz : Nat) (g_len g_cap : BitVec 64) (R : Mem 64 → Prop) (g_cur : BitVec 64)
    (lm : List (BitVec 8)) (scr : List (BitVec 32)) (m : Mem 64) : Prop :=
  g_len.toNat ≤ g_cur.toNat ∧ g_cur.toNat ≤ g_cap.toNat ∧
  lm.length = 2 * c.max_vars ∧ scr.length = c.scratch_cap ∧
  (∀ idx, idx < g_len.toNat → scr[idx]? = s.scratch.scratch_buf[idx]?) ∧
  CongGateSeqOk maxA F_cur s.core.cur_vars scr g_cur.toNat 0 ∧
  aeMarkInv c s.scratch.work_stk2 usz lm ∧ aeBit2Clr c lm ∧ aeMem c s lm scr R m

private def andExtractMarkGood (lm : List (BitVec 8)) (ws2 : List (BitVec 32)) (k : Nat) :
    Bool :=
  (lm[litNeg (ws2[k]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) != 0#8

private abbrev aeScanInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (usz isel : Nat)
    (lhs : BitVec 32) (scr2 : List (BitVec 32)) (R : Mem 64 → Prop) (mcnt : BitVec 32)
    (lmw : List (BitVec 8)) (mw : Mem 64) : Prop :=
  lmw.length = 2 * c.max_vars ∧ aeMarkInv c s.scratch.work_stk2 usz lmw ∧
  mcnt.toNat = (List.range usz).countP (fun k =>
    decide (k ≠ isel) && andExtractMarkGood lmw s.scratch.work_stk2 k) ∧
  (∀ k, k < usz → k ≠ isel → andExtractMarkGood lmw s.scratch.work_stk2 k = true →
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lhs.toNat, litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat])) ∧
  aeMem c s lmw scr2 R mw

private abbrev aeGateWriteInv (c : FullCfg) (s : FullState) (usz isel : Nat)
    (g_cur : BitVec 64) (csel mword : BitVec 32) (scr2 : List (BitVec 32))
    (lmw : List (BitVec 8)) (R : Mem 64 → Prop) (oi k : BitVec 32) (mk : Mem 64) : Prop :=
  k.toNat ≤ usz ∧ oi.toNat = (if k.toNat ≤ isel then k.toNat else k.toNat - 1) ∧
  ∃ scrk : List (BitVec 32), scrk.length = c.scratch_cap ∧
    (∀ idx, idx < g_cur.toNat → scrk[idx]? = scr2[idx]?) ∧
    scrk[g_cur.toNat]? = some csel ∧ scrk[g_cur.toNat + 1]? = some mword ∧
    (∀ j, j < k.toNat → j ≠ isel → litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat ∈
      List.map BitVec.toNat (List.take oi.toNat (List.drop (g_cur.toNat + 2) scrk))) ∧
    (∀ t, t < oi.toNat → ∃ j, j < k.toNat ∧ j ≠ isel ∧
      scrk[g_cur.toNat + 2 + t]? = some (s.scratch.work_stk2[j]?.getD 0#32 ^^^ 1#32)) ∧
    aeMem c s lmw scrk R mk

private theorem andExtract_fullDenseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hd : FullDenseInvW c F0 F_cur s) {lm' : List (BitVec 8)} {scr' : List (BitVec 32)}
    (rsz' : BitVec 64) (hlm : lm'.length = 2 * c.max_vars)
    (hscr : scr'.length = c.scratch_cap)
    (hclr : ∀ l, l < 2 * c.max_vars → lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with lit_mark := lm' },
        scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } } := by
  have hd1 := fullDenseInvW_with_scr (fullDenseInvW_with_rsz hd rsz') hscr
  rcases hd1 with ⟨hl1, hw1, hm1, hn1, he1, hc1, hd_mode⟩
  refine ⟨⟨⟨hl1.core_ok.vals_len, hlm, hl1.core_ok.mrk_len, hl1.core_ok.flags_len,
    hl1.core_ok.lvl_len, hl1.core_ok.rsns_len, hl1.core_ok.trl_len,
    hl1.core_ok.trail_pos_len, hl1.core_ok.tmp_len_arr, hl1.core_ok.min_clr_len_arr,
    hl1.core_ok.frame_trail_len, hl1.core_ok.frame_dec_len, hl1.core_ok.wvec_len,
    hl1.core_ok.repr_len, hl1.core_ok.min_stk_len, hl1.core_ok.arena_len_arr,
    hl1.core_ok.wstk_len_arr, hl1.core_ok.cur_vars_ge, hl1.core_ok.cur_vars_le,
    hl1.core_ok.arena_len_le, hl1.core_ok.wlen_le, hl1.core_ok.trail_end_le,
    hl1.core_ok.propagated_le, hl1.core_ok.tmp_len_le, hl1.core_ok.min_clr_len_le⟩,
    hl1.scratch_ok⟩, ?_, ⟨hm1.1, hclr⟩, ?_, ?_, hc1, hd_mode⟩
  · simpa using fullWitnessInv_with_tmp_lm hw1 s.core.tmp lm'
  · exact fullArenaVarsNodup_of_eq hn1 rfl rfl
  · exact fullExtScratchOk_of_eq he1 rfl rfl rfl rfl

private theorem andExtract_countP_inc {n i k : Nat} {f g : Nat → Bool}
    (hk : k < n) (hki : k ≠ i) (hf : f k = false) (hg : g k = true)
    (hother : ∀ j, j < n → j ≠ k → g j = f j) :
    (List.range n).countP (fun j => decide (j ≠ i) && g j) =
      (List.range n).countP (fun j => decide (j ≠ i) && f j) + 1 := by
  induction n with
  | zero => simp at hk
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_append, List.countP_cons,
      List.countP_cons, List.countP_nil, List.countP_nil]
    by_cases hkm : k = m
    · subst hkm
      have heq : List.countP (fun j => decide (j ≠ i) && g j) (List.range k) =
          List.countP (fun j => decide (j ≠ i) && f j) (List.range k) := by
        apply List.countP_congr; intro j hj
        have hjk : j ≠ k := Nat.ne_of_lt (List.mem_range.mp hj)
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [hother j (Nat.lt_succ_of_lt (List.mem_range.mp hj)) hjk]
      rw [heq]; simp [hki, hf, hg]
    · have hk' : k < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkm
      have ih' := ih hk' (fun j hj hjk => hother j (Nat.lt_succ_of_lt hj) hjk)
      have hmn := hother m (Nat.lt_succ_self m) (Ne.symm hkm)
      simp only [hmn]; rw [ih']; omega

private theorem andExtract_countP_le_excl (n i : Nat) (f : Nat → Bool) :
    (List.range n).countP (fun j => decide (j ≠ i) && f j) ≤ if i < n then n - 1 else n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
    by_cases hmi : m = i
    · subst hmi
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.lt_irrefl m))] at ih
      have hc0 : (if (decide (m ≠ m) && f m) = true then 1 else 0) = 0 := by simp
      rw [hc0, Nat.add_zero]
      rw [ite_eq_left_iff.mpr (fun h => absurd (Nat.lt_succ_self m) h), Nat.add_sub_cancel]
      exact ih
    · by_cases him : i < m
      · have hlt : i < m + 1 := Nat.lt_succ_of_lt him
        rw [ite_eq_left_iff.mpr (fun h => absurd him h)] at ih
        rw [ite_eq_left_iff.mpr (fun h => absurd hlt h)]
        have hc1 : (if (decide (m ≠ i) && f m) = true then 1 else 0) ≤ 1 := by
          split <;> omega
        omega
      · have hn : ¬ i < m + 1 := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h him)] at ih
        rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
        have hc1 : (if (decide (m ≠ i) && f m) = true then 1 else 0) ≤ 1 := by
          split <;> omega
        omega

private theorem andExtract_countP_full {n i : Nat} {f : Nat → Bool}
    (hi : i < n) (hcnt : (List.range n).countP (fun j => decide (j ≠ i) && f j) = n - 1) :
    ∀ k, k < n → k ≠ i → f k = true := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil] at hcnt
    have hle := andExtract_countP_le_excl m i f
    intro k hk hki
    by_cases hmi : m = i
    · subst hmi
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.lt_irrefl m))] at hle
      have hc0 : (if (decide (m ≠ m) && f m) = true then 1 else 0) = 0 := by simp
      rw [hc0, Nat.add_zero] at hcnt
      have hkm : k < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hki
      have hall : (List.range m).countP (fun j => decide (j ≠ m) && f j) =
          (List.range m).length := by simpa [List.length_range] using hcnt
      have hmem := (List.countP_eq_length.mp hall) k (List.mem_range.mpr hkm)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
      exact hmem.2
    · have him : i < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) (Ne.symm hmi)
      rw [ite_eq_left_iff.mpr (fun h => absurd him h)] at hle
      have hfm : f m = true := by
        cases hfv : f m
        · exfalso
          have hc0 : (if (decide (m ≠ i) && f m) = true then 1 else 0) = 0 := by simp [hfv]
          rw [hc0] at hcnt; omega
        · rfl
      have hc1 : (if (decide (m ≠ i) && f m) = true then 1 else 0) = 1 := by simp [hmi, hfm]
      have hsub : (List.range m).countP (fun j => decide (j ≠ i) && f j) = m - 1 := by
        rw [hc1] at hcnt; omega
      by_cases hkm : k = m
      · subst hkm; exact hfm
      · exact ih him hsub k (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkm) hki

private theorem andExtract_dense_slice_ok {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hd : FullDenseInvW c F0 F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    (if s.core.dense_mode = 0#64 then
      WatchSliceOk F_cur s.core l (fullWatchOffCore s.core l) (fullWatchSizeCore s.core l)
    else
      DenseWatchSliceOk F_cur s.core l (fullWatchOffCore s.core l)
        (fullWatchSizeCore s.core l)) := by
  have hw := hd.2.1.watches
  unfold ModeWatchesInv at hw
  have hdm : s.core.dense_mode ≠ 0#64 := hd.2.2.2.2.2.2
  rw [ite_eq_right_iff.mpr (fun h => absurd h hdm)] at hw ⊢
  exact hw.slices l hl

private theorem andExtract_mword_ok {usz : BitVec 32} (h3 : 3 ≤ usz.toNat)
    (hmax : usz.toNat - 1 ≤ congAndArityMax) :
    let rhs := usz - 1#32
    let mword := if rhs.ule 64#32 then rhs else (3#32 <<< 28) ||| rhs
    congGateArity mword = usz.toNat - 1 ∧
      ((mword >>> 28).toNat = 0 ∧ 2 ≤ congGateArity mword ∧ congGateArity mword ≤ 64 ∨
       (mword >>> 28).toNat = 3 ∧ 65 ≤ congGateArity mword) := by
  intro rhs mword
  have h1 : rhs.toNat = usz.toNat - 1 := by dsimp only [rhs]; bv_omega
  have hbd : rhs.toNat ≤ 1000000 := by
    have : congAndArityMax = 1000000 := rfl
    omega
  by_cases h64 : rhs.ule 64#32 = true
  · have hle : rhs.toNat ≤ 64 := by simpa [BitVec.ule] using h64
    have hm : mword = rhs := by simp [mword, h64]
    have hs : rhs >>> 28 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]; rfl
    have hand : rhs &&& 255#32 = rhs := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (255#32).toNat = 2 ^ 8 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have har : congGateArity mword = usz.toNat - 1 := by
      rw [hm, congGateArity_of_ne3 (by rw [hs]; decide), hand, h1]
    exact ⟨har, Or.inl ⟨by rw [hm, hs]; rfl, by omega, by omega⟩⟩
  · have hgt : 64 < rhs.toNat := by
      have hf : rhs.ule 64#32 = false := Bool.eq_false_iff.mpr h64
      simpa [BitVec.ule] using hf
    have hm : mword = (3#32 <<< 28) ||| rhs := by simp [mword, h64]
    have hlt28 : rhs.toNat < 2 ^ 28 := by omega
    have hbit_rhs : ∀ k, 28 ≤ k → rhs.getLsbD k = false := fun k hk =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt28 (Nat.pow_le_pow_right (by omega) hk))
    have hsh3 : ∀ x : Fin 4,
        (3#32 <<< 28 : BitVec 32).getLsbD (x.val + 28) = (3#32).getLsbD x.val := by
      decide
    have hsh0 : ∀ x : Fin 28, (3#32 <<< 28 : BitVec 32).getLsbD x.val = false := by decide
    have hs : mword >>> 28 = 3#32 := by
      rw [hm]; apply BitVec.eq_of_getLsbD_eq; intro k hk32
      rw [BitVec.getLsbD_ushiftRight]
      by_cases hk4 : k < 4
      · rw [BitVec.getLsbD_or, hbit_rhs _ (by omega), Bool.or_false]
        have q := hsh3 ⟨k, hk4⟩; rwa [Nat.add_comm] at q
      · rw [BitVec.getLsbD_or, hbit_rhs _ (by omega), Bool.or_false]
        have hge : (3#32 <<< 28 : BitVec 32).getLsbD (28 + k) = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by omega) (by omega)))
        rw [hge]; symm
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (3#32).toNat < 2 ^ 4)
          (Nat.pow_le_pow_right (by omega) (by omega)))
    have hand : mword &&& 268435455#32 = rhs := by
      rw [hm]; apply BitVec.eq_of_getLsbD_eq; intro k hk32
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
      by_cases hk28 : k < 28
      · have hm1 : (268435455#32 : BitVec 32).getLsbD k = true := by
          change (2 ^ 28 - 1).testBit k = true
          rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk28
        rw [hsh0 ⟨k, hk28⟩, hm1, Bool.false_or, Bool.and_true]
      · have hm0 : (268435455#32 : BitVec 32).getLsbD k = false := by
          change (2 ^ 28 - 1).testBit k = false
          rw [Nat.testBit_two_pow_sub_one]; simp; omega
        rw [hbit_rhs _ (by omega), hm0, Bool.and_false]
    have har : congGateArity mword = usz.toNat - 1 := by
      rw [congGateArity_of_eq3 hs, hand, h1]
    exact ⟨har, Or.inr ⟨by rw [hs]; rfl, by omega⟩⟩

private theorem andExtract_andGateDef {F_cur : List (List Nat)}
    {ws2 : List (BitVec 32)} {usz isel : Nat} (hisel : isel < usz)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map (fun j => (ws2[j]?.getD 0#32).toNat) (List.range usz))))
    (hm2 : ∀ k, k < usz → k ≠ isel →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [litNeg (ws2[isel]?.getD 0#32).toNat,
                    litNeg (ws2[k]?.getD 0#32).toNat]))
    {rhs : List Nat}
    (hrhs_mem : ∀ x, x ∈ rhs ↔ ∃ k, k < usz ∧ k ≠ isel ∧ x = litNeg (ws2[k]?.getD 0#32).toNat) :
    AndGateDef (cnfOfClauses F_cur) (ws2[isel]?.getD 0#32).toNat rhs := by
  refine ⟨?_, ?_⟩
  · apply entails_perm_clause _ hent
    intro lit hlit; rw [List.mem_map] at hlit
    rcases hlit with ⟨k, hk, rfl⟩; rw [List.mem_range] at hk
    by_cases hki : k = isel
    · subst hki; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨litNeg (ws2[k]?.getD 0#32).toNat, (hrhs_mem _).mpr ⟨k, hk, hki, rfl⟩,
          andExtract_litNeg_invol _⟩)
  · intro x hx; rcases (hrhs_mem x).mp hx with ⟨k, hk, hki, rfl⟩; exact hm2 k hk hki

private theorem andExtract_markInv_set {c : FullCfg} {ws2 : List (BitVec 32)}
    {usz idx k : Nat} {lm : List (BitVec 8)} (hinv : aeMarkInv c ws2 usz lm)
    (hk_usz : k < usz) (hidx : idx = litNeg (ws2[k]?.getD 0#32).toNat) (v : BitVec 8) :
    aeMarkInv c ws2 usz (lm.set idx v) := by
  subst hidx; intro l hl hne
  by_cases hlk : l = litNeg (ws2[k]?.getD 0#32).toNat
  · exact ⟨k, hk_usz, hlk⟩
  · rw [List.getElem?_set_ne (Ne.symm hlk)] at hne; exact hinv l hl hne

private theorem andExtract_bit2_clear {c : FullCfg} {lm : List (BitVec 8)} {idx : Nat}
    {v : BitVec 8} (hlm : lm.length = 2 * c.max_vars) (hb : aeBit2Clr c lm)
    (hv : v &&& 2#8 = 0#8) : aeBit2Clr c (lm.set idx v) := by
  intro l hl
  by_cases hli : l = idx
  · subst hli; have hlen : l < lm.length := by omega
    rw [List.getElem?_eq_getElem (by simp [hlen]), Option.getD_some, List.getElem_set_self]
    exact hv
  · rw [List.getElem?_set_ne (Ne.symm hli)]; exact hb l hl

private theorem andExtract_cleanup_clear {c : FullCfg} {ws2 : List (BitVec 32)}
    {usz : Nat} {lm : List (BitVec 8)} (hinv : aeMarkInv c ws2 usz lm)
    (hdone : ∀ k, k < usz → lm[litNeg (ws2[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) :
    ∀ l, l < 2 * c.max_vars → lm[l]?.getD 0#8 = 0#8 := by
  intro l hl; by_cases h0 : lm[l]?.getD 0#8 = 0#8
  · exact h0
  · rcases hinv l hl h0 with ⟨k, hk, hlk⟩; subst hlk; exact absurd (hdone k hk) h0

private theorem andExtract_clear_step {c : FullCfg} {ws2 : List (BitVec 32)}
    {usz k idx : Nat} {lm : List (BitVec 8)} (hk : k < usz)
    (hnd : ∀ j, j < usz → ∀ j2, j2 < usz → j ≠ j2 →
      (ws2[j]?.getD 0#32).toNat ≠ (ws2[j2]?.getD 0#32).toNat)
    (hnot_eq : idx = litNeg (ws2[k]?.getD 0#32).toNat) (hnot_lt : idx < lm.length)
    (hclr_k : ∀ j, j < k → lm[litNeg (ws2[j]?.getD 0#32).toNat]?.getD 0#8 = 0#8)
    (hinv_k : aeMarkInv c ws2 usz lm) :
    (∀ j, j < k + 1 → (lm.set idx 0#8)[litNeg (ws2[j]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
      aeMarkInv c ws2 usz (lm.set idx 0#8) := by
  subst hnot_eq; refine ⟨fun j hj => ?_, fun l hl hne => ?_⟩
  · by_cases hjk : j = k
    · subst hjk
      rw [List.getElem?_eq_getElem (by simp [hnot_lt]), Option.getD_some, List.getElem_set_self]
    · have hne : litNeg (ws2[j]?.getD 0#32).toNat ≠ litNeg (ws2[k]?.getD 0#32).toNat := by
        intro heq; have := congrArg litNeg heq
        rw [andExtract_litNeg_invol, andExtract_litNeg_invol] at this
        exact hnd j (by omega) k hk hjk this
      rw [List.getElem?_set_ne (Ne.symm hne)]; exact hclr_k j (by omega)
  · by_cases hlk : l = litNeg (ws2[k]?.getD 0#32).toNat
    · subst hlk
      rw [List.getElem?_eq_getElem (by simp [hnot_lt]),
        Option.getD_some, List.getElem_set_self] at hne
      exact absurd rfl hne
    · rw [List.getElem?_set_ne (Ne.symm hlk)] at hne; exact hinv_k l hl hne

private theorem andExtract_clear_bit1_step {c : FullCfg} {ws2 : List (BitVec 32)}
    {usz k idx : Nat} {lm : List (BitVec 8)} (hk : k < usz)
    (hnd : ∀ j, j < usz → ∀ j2, j2 < usz → j ≠ j2 →
      (ws2[j]?.getD 0#32).toNat ≠ (ws2[j2]?.getD 0#32).toNat)
    (hnot_eq : idx = litNeg (ws2[k]?.getD 0#32).toNat) (hnot_lt : idx < lm.length)
    (hclr : ∀ j, j < k → (lm[litNeg (ws2[j]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (hinv : aeMarkInv c ws2 usz lm) {v : BitVec 8} (hv : v &&& 2#8 = 0#8) :
    (∀ j, j < k + 1 → ((lm.set idx v)[litNeg (ws2[j]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) = 0#8) ∧
      aeMarkInv c ws2 usz (lm.set idx v) := by
  refine ⟨fun j hj => ?_, andExtract_markInv_set hinv hk hnot_eq v⟩
  by_cases hjk : j = k
  · subst hjk; subst hnot_eq
    rw [List.getElem?_eq_getElem (by simp [hnot_lt]),
      Option.getD_some, List.getElem_set_self]; exact hv
  · have hne : litNeg (ws2[j]?.getD 0#32).toNat ≠ litNeg (ws2[k]?.getD 0#32).toNat := by
      intro heq; have := congrArg litNeg heq
      rw [andExtract_litNeg_invol, andExtract_litNeg_invol] at this
      exact hnd j (by omega) k hk hjk this
    rw [hnot_eq, List.getElem?_set_ne (Ne.symm hne)]; exact hclr j (by omega)

private theorem andExtract_bit1_of_mask3 : ∀ x : BitVec 8, x &&& 3#8 = 1#8 →
    (x &&& 2#8 != 0#8) = false ∧ ((x ||| 2#8) &&& 2#8 != 0#8) = true := by
  decide

private theorem andExtract_scan_step {c : FullCfg} {F_cur : List (List Nat)}
    {ws2 : List (BitVec 32)} {usz isel : Nat} (hisel : isel < usz)
    (hnd : ∀ j, j < usz → ∀ j2, j2 < usz → j ≠ j2 →
      (ws2[j]?.getD 0#32).toNat ≠ (ws2[j2]?.getD 0#32).toNat)
    {lmw : List (BitVec 8)} (hlmw : lmw.length = 2 * c.max_vars)
    (hinvw : aeMarkInv c ws2 usz lmw) {mcnt : BitVec 32}
    (hcntw : mcnt.toNat = (List.range usz).countP (fun k =>
      decide (k ≠ isel) && andExtractMarkGood lmw ws2 k))
    {lhs other : BitVec 32} (hlhs_eq : lhs = (ws2[isel]?.getD 0#32) ^^^ 1#32)
    (hot_lt : other.toNat < 2 * c.max_vars) (hot_ne : other ≠ lhs)
    (hot_lm : (BitVec.setWidth 64 other).toNat < lmw.length)
    (hmk3 : lmw[(BitVec.setWidth 64 other).toNat]'hot_lm &&& 3#8 = 1#8)
    (hent_bin : (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs.toNat, other.toNat]))
    (hentw : ∀ k, k < usz → k ≠ isel → andExtractMarkGood lmw ws2 k = true →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lhs.toNat, litNeg (ws2[k]?.getD 0#32).toNat])) :
    let new_v := lmw[(BitVec.setWidth 64 other).toNat]'hot_lm ||| 2#8
    let lmw' := lmw.set (BitVec.setWidth 64 other).toNat new_v
    aeMarkInv c ws2 usz lmw' ∧
    (mcnt.toNat + 1 = (List.range usz).countP (fun k =>
      decide (k ≠ isel) && andExtractMarkGood lmw' ws2 k)) ∧
    (∀ k, k < usz → k ≠ isel → andExtractMarkGood lmw' ws2 k = true →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lhs.toNat, litNeg (ws2[k]?.getD 0#32).toNat])) := by
  intro new_v lmw'
  have hz : (BitVec.setWidth 64 other).toNat = other.toNat := bv_zext32_toNat other
  have hot_len : other.toNat < lmw.length := by rw [hlmw]; exact hot_lt
  have hget_eq : lmw[(BitVec.setWidth 64 other).toNat]'hot_lm = lmw[other.toNat]'hot_len :=
    idx_get_eq hot_lm hot_len hz
  have hmk_nz : lmw[other.toNat]?.getD 0#8 ≠ 0#8 := by
    intro h0; rw [List.getElem?_eq_getElem hot_len, Option.getD_some] at h0
    rw [hget_eq, h0] at hmk3; simp at hmk3
  rcases hinvw other.toNat hot_lt hmk_nz with ⟨kw, hkw_lt, hkw_eq⟩
  have hkw_ne : kw ≠ isel := by
    intro heq; subst heq; apply hot_ne; apply BitVec.eq_of_toNat_eq
    rw [hkw_eq, hlhs_eq, bv32_xor1_eq_litNeg]
  have hgood_f : andExtractMarkGood lmw ws2 kw = false := by
    dsimp only [andExtractMarkGood]; rw [← hkw_eq]
    rw [List.getElem?_eq_getElem hot_len, Option.getD_some]
    exact (andExtract_bit1_of_mask3 _ (hget_eq ▸ hmk3)).1
  have hinc := andExtract_countP_inc (n := usz) (i := isel) (k := kw)
    (g := andExtractMarkGood lmw' ws2) hkw_lt hkw_ne hgood_f ?_ (fun j hj hjk => ?_)
  · refine ⟨andExtract_markInv_set hinvw hkw_lt (by rw [hz, hkw_eq]) new_v,
      by rw [hcntw, hinc], fun k hk hki hg => ?_⟩
    by_cases hkk : k = kw
    · subst hkk; rw [← hkw_eq]; exact hent_bin
    · apply hentw k hk hki
      have hne2 : litNeg (ws2[k]?.getD 0#32).toNat ≠ other.toNat := by
        rw [hkw_eq]; intro heq; have := congrArg litNeg heq
        rw [andExtract_litNeg_invol, andExtract_litNeg_invol] at this
        exact hnd k hk kw hkw_lt hkk this
      dsimp only [andExtractMarkGood, lmw'] at hg ⊢
      rw [hz, List.getElem?_set_ne hne2.symm] at hg; exact hg
  · dsimp only [andExtractMarkGood]
    rw [← hkw_eq, List.getElem?_eq_getElem (by simp [lmw', hot_len]), Option.getD_some]
    have hget2 : (lmw.set (BitVec.setWidth 64 other).toNat new_v)[other.toNat]'(by
        simp [hot_len]) = new_v := by
      simp [hz]
    change ((lmw.set (BitVec.setWidth 64 other).toNat new_v)[other.toNat]'(by
      simp [hot_len]) &&& 2#8 != 0#8) = true
    rw [hget2]; dsimp only [new_v]; rw [hget_eq]
    exact (andExtract_bit1_of_mask3 _ (hget_eq ▸ hmk3)).2
  · dsimp only [andExtractMarkGood]
    have hne2 : litNeg (ws2[j]?.getD 0#32).toNat ≠ other.toNat := by
      rw [hkw_eq]; intro heq; have := congrArg litNeg heq
      rw [andExtract_litNeg_invol, andExtract_litNeg_invol] at this
      exact hnd j hj kw hkw_lt hjk this
    dsimp only [lmw']; rw [hz, List.getElem?_set_ne hne2.symm]

private theorem andExtract_gateLoop_write_step {c : FullCfg} {s : FullState}
    {usz isel : Nat} {g_cur : BitVec 64} {csel mword oi k5 : BitVec 32}
    {scr2 scrk : List (BitVec 32)}
    (hk5_lt : k5.toNat < usz) (hisel_lt : isel < usz) (husz_bd : usz ≤ 2 ^ 31)
    (hne_nat : k5.toNat ≠ isel)
    (hoi : oi.toNat = if k5.toNat ≤ isel then k5.toNat else k5.toNat - 1)
    (hscrk : scrk.length = c.scratch_cap)
    (hg_room : g_cur.toNat + 2 + (usz - 1) ≤ c.scratch_cap)
    (hk5_ws2 : k5.toNat < s.scratch.work_stk2.length)
    (hpk : ∀ idx, idx < g_cur.toNat → scrk[idx]? = scr2[idx]?)
    (hgk0 : scrk[g_cur.toNat]? = some csel) (hgk1 : scrk[g_cur.toNat + 1]? = some mword)
    (hk_has : ∀ j, j < k5.toNat → j ≠ isel →
      litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat ∈
        List.map BitVec.toNat (List.take oi.toNat (List.drop (g_cur.toNat + 2) scrk)))
    (hk_mem : ∀ t, t < oi.toNat → ∃ j, j < k5.toNat ∧ j ≠ isel ∧
      scrk[g_cur.toNat + 2 + t]? = some (s.scratch.work_stk2[j]?.getD 0#32 ^^^ 1#32))
    (hidx_eq : (g_cur + 2#64 + BitVec.setWidth 64 oi).toNat = g_cur.toNat + 2 + oi.toNat) :
    let wlit := s.scratch.work_stk2[k5.toNat]'hk5_ws2 ^^^ 1#32
    let scrk' := scrk.set (g_cur + 2#64 + BitVec.setWidth 64 oi).toNat wlit
    (oi + 1#32).toNat = (if k5.toNat + 1 ≤ isel then k5.toNat + 1 else k5.toNat) ∧
    scrk'.length = c.scratch_cap ∧
    (∀ idx, idx < g_cur.toNat → scrk'[idx]? = scr2[idx]?) ∧
    scrk'[g_cur.toNat]? = some csel ∧ scrk'[g_cur.toNat + 1]? = some mword ∧
    (∀ j, j < k5.toNat + 1 → j ≠ isel →
      litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat ∈
        List.map BitVec.toNat (List.take (oi + 1#32).toNat (List.drop (g_cur.toNat + 2) scrk'))) ∧
    (∀ t, t < (oi + 1#32).toNat → ∃ j, j < k5.toNat + 1 ∧ j ≠ isel ∧
      scrk'[g_cur.toNat + 2 + t]? = some (s.scratch.work_stk2[j]?.getD 0#32 ^^^ 1#32)) := by
  intro wlit scrk'
  have hoi_lt : oi.toNat < usz - 1 := by rw [hoi]; split <;> omega
  have hoi_u32 : oi.toNat + 1 < 2 ^ 32 := by omega
  have hoi1 : (oi + 1#32).toNat = oi.toNat + 1 := bv32_add1_lt_of hoi_u32
  refine ⟨by rw [hoi1, hoi]; split <;> split <;> omega, by simp [scrk', hscrk],
    fun idx hi => by rw [List.getElem?_set_ne (by rw [hidx_eq]; omega)]; exact hpk idx hi,
    by rw [List.getElem?_set_ne (by rw [hidx_eq]; omega)]; exact hgk0,
    by rw [List.getElem?_set_ne (by rw [hidx_eq]; omega)]; exact hgk1,
    fun j hj1 hj2 => ?_, fun t ht => ?_⟩
  · have hsub : ∀ z ∈ List.map BitVec.toNat (List.take oi.toNat
        (List.drop (g_cur.toNat + 2) scrk)), z ∈ List.map
        BitVec.toNat (List.take (oi + 1#32).toNat (List.drop (g_cur.toNat + 2) scrk')) := by
      intro z hz; rw [List.mem_map] at hz ⊢; rcases hz with ⟨v, hv, rfl⟩; refine ⟨v, ?_, rfl⟩
      rcases List.mem_iff_getElem.mp hv with ⟨t, ht, rfl⟩
      simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop] at ht ⊢
      have ht_oi : t < oi.toNat := by omega
      have htake : t <
          (List.take (oi + 1#32).toNat (List.drop (g_cur.toNat + 2) scrk')).length := by
        simp [scrk', hscrk, hoi1]; omega
      have hget : (List.take (oi + 1#32).toNat (List.drop (g_cur.toNat + 2) scrk'))[t]'htake =
          scrk[g_cur.toNat + 2 + t] := by
        simp only [List.getElem_take, List.getElem_drop, scrk', hidx_eq]
        rw [List.getElem_set_ne (by omega)]
      rw [← hget]; exact List.getElem_mem _
    by_cases hjk : j = k5.toNat
    · subst hjk
      have htake : oi.toNat <
          (List.take (oi + 1#32).toNat (List.drop (g_cur.toNat + 2) scrk')).length := by
        simp [scrk', hscrk, hoi1]; omega
      have hget : (List.take (oi + 1#32).toNat
          (List.drop (g_cur.toNat + 2) scrk'))[oi.toNat]'htake = wlit := by
        simp only [List.getElem_take, List.getElem_drop, scrk', hidx_eq]
        rw [List.getElem_set_self]
      rw [List.mem_map]; refine ⟨wlit, by rw [← hget]; exact List.getElem_mem _, ?_⟩
      dsimp only [wlit]
      rw [bv32_xor1_eq_litNeg, List.getElem?_eq_getElem hk5_ws2, Option.getD_some]
    · exact hsub _ (hk_has j (by omega) hj2)
  · by_cases hto : t = oi.toNat
    · subst hto; refine ⟨k5.toNat, by omega, hne_nat, ?_⟩
      simp only [scrk', hidx_eq]
      rw [List.getElem?_eq_getElem (by simp [hscrk]; omega), List.getElem_set_self]
      dsimp only [wlit]; rw [List.getElem?_eq_getElem hk5_ws2, Option.getD_some]
    · have hto' : t < oi.toNat := by omega
      rcases hk_mem t hto' with ⟨j, hj1, hj2, hsq⟩
      refine ⟨j, by omega, hj2, ?_⟩
      rw [← hsq]; dsimp only [scrk']; rw [hidx_eq]; exact List.getElem?_set_ne (by omega)

private theorem andExtract_gate_post {maxA : Nat} {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {usz isel : Nat} {g_len g_cur : BitVec 64}
    {mword : BitVec 32} {scr0 scr : List (BitVec 32)}
    (hisel : isel < usz) (hmax : usz - 1 ≤ maxA)
    (hcv : usz ≤ s.core.cur_vars) (hg_le : g_len.toNat ≤ g_cur.toNat)
    (hg_room : g_cur.toNat + 2 + (usz - 1) ≤ c.scratch_cap)
    (hscr : scr.length = c.scratch_cap)
    (hws2_lt : ∀ j, j < usz → (s.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (List.map
      (fun j => (s.scratch.work_stk2[j]?.getD 0#32).toNat) (List.range usz))))
    (hm2 : ∀ k, k < usz → k ≠ isel → (cnfOfClauses F_cur).EntailsClause (cnfClause
      [litNeg (s.scratch.work_stk2[isel]?.getD 0#32).toNat,
       litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat]))
    (har : congGateArity mword = usz - 1)
    (htag : (mword >>> 28).toNat = 0 ∧ 2 ≤ congGateArity mword ∧ congGateArity mword ≤ 64 ∨
      (mword >>> 28).toNat = 3 ∧ 65 ≤ congGateArity mword)
    (hpre0 : ∀ idx, idx < g_len.toNat → scr0[idx]? = s.scratch.scratch_buf[idx]?)
    (hseq0 : CongGateSeqOk maxA F_cur s.core.cur_vars scr0 g_cur.toNat 0)
    (hpre : ∀ idx, idx < g_cur.toNat → scr[idx]? = scr0[idx]?)
    (hg0 : scr[g_cur.toNat]? = some (s.scratch.work_stk2[isel]?.getD 0#32))
    (hg1 : scr[g_cur.toNat + 1]? = some mword)
    (hrhs_has : ∀ j, j < usz → j ≠ isel → litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat ∈
      List.map BitVec.toNat (List.take (usz - 1) (List.drop (g_cur.toNat + 2) scr)))
    (hrhs_mem : ∀ t, t < usz - 1 → ∃ j, j < usz ∧ j ≠ isel ∧
      scr[g_cur.toNat + 2 + t]? = some (s.scratch.work_stk2[j]?.getD 0#32 ^^^ 1#32)) :
    (∀ idx, idx < g_len.toNat → scr[idx]? = s.scratch.scratch_buf[idx]?) ∧
    CongGateSeqOk maxA F_cur s.core.cur_vars scr (g_cur.toNat + 2 + (usz - 1)) 0 := by
  have hpre_all : ∀ idx, idx < g_len.toNat → scr[idx]? = s.scratch.scratch_buf[idx]? :=
    fun idx hi => (hpre idx (Nat.lt_of_lt_of_le hi hg_le)).trans (hpre0 idx hi)
  refine ⟨hpre_all, congGateSeqOk_append_gate hpre hseq0 ?_ (by omega)⟩
  have hdrop : List.take (usz - 1) (List.drop (g_cur.toNat + 2) scr) =
      List.map (fun t => scr[g_cur.toNat + 2 + t]?.getD 0#32) (List.range (usz - 1)) := by
    apply List.ext_getElem; simp; omega
    intro t ht1 _; have htu : t < usz - 1 := by simp at ht1; omega
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hrhs_lt : ∀ t, t < usz - 1 →
      (scr[g_cur.toNat + 2 + t]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
    intro t ht; rcases hrhs_mem t ht with ⟨j, hj, _, hsq⟩
    rw [hsq, Option.getD_some]; exact andExtract_not_lt (hws2_lt j hj)
  have hiff : ∀ x, x ∈ List.map BitVec.toNat
        (List.take (usz - 1) (List.drop (g_cur.toNat + 2) scr)) ↔
      ∃ k, k < usz ∧ k ≠ isel ∧ x = litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat := by
    intro x; constructor
    · intro hx; rw [hdrop, List.mem_map] at hx; rcases hx with ⟨v, hv, rfl⟩
      rw [List.mem_map] at hv; rcases hv with ⟨t, ht, rfl⟩
      rcases hrhs_mem t (List.mem_range.mp ht) with ⟨j, hj, hji, hsq⟩
      refine ⟨j, hj, hji, ?_⟩; rw [hsq, Option.getD_some, bv32_xor1_eq_litNeg]
    · rintro ⟨j, hj, hji, rfl⟩; exact hrhs_has j hj hji
  have hand := andExtract_andGateDef hisel hent hm2 hiff
  have hat : CongGateAt maxA F_cur s.core.cur_vars scr (g_cur.toNat + 2 + (usz - 1)) g_cur.toNat :=
    ⟨s.scratch.work_stk2[isel]?.getD 0#32, mword, hg0, hg1, hws2_lt isel hisel,
      ⟨by omega, by omega, by omega, fun k hk => by
        have hgk : g_cur.toNat + 2 + k < scr.length := by omega
        refine ⟨scr[g_cur.toNat + 2 + k], List.getElem?_eq_getElem hgk, ?_⟩
        have q := hrhs_lt k (by rw [← har]; exact hk)
        rwa [List.getElem?_eq_getElem hgk, Option.getD_some] at q,
      Or.inl ⟨htag, by simpa [har] using hand⟩⟩⟩
  refine CongGateSeqOk.step hat ?_; rw [hg1, Option.getD_some, har]; exact CongGateSeqOk.done

private abbrev aeLoop1Body (c : FullCfg) (s : FullState) (usz : BitVec 32) (R : Mem 64 → Prop)
    (bi : BitVec 32) (mn : Mem 64) : Prop :=
  (bi.toNat < usz.toNat ∨ bi = usz) ∧
  ∃ lmn : List (BitVec 8), lmn.length = 2 * c.max_vars ∧
    aeMarkInv c s.scratch.work_stk2 usz.toNat lmn ∧ aeBit2Clr c lmn ∧
    aeMem c s lmn s.scratch.scratch_buf R mn

private abbrev aeClearBit2Body (c : FullCfg) (s : FullState) (usz : Nat)
    (scr3 : List (BitVec 32)) (R : Mem 64 → Prop) (k : Nat) (mx : Mem 64) : Prop :=
  ∃ lmc : List (BitVec 8), lmc.length = 2 * c.max_vars ∧
    (∀ j, j < k → (lmc[litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat]?.getD 0#8 &&&
      2#8) = 0#8) ∧
    aeMarkInv c s.scratch.work_stk2 usz lmc ∧ aeMem c s lmc scr3 R mx

private theorem andExtract_not_idx {c : FullCfg} {ws2 : List (BitVec 32)} {usz s_cv : Nat}
    {lm : List (BitVec 8)} {k : BitVec 32}
    (hws2_lt : ∀ j, j < usz → (ws2[j]?.getD 0#32).toNat < 2 * s_cv)
    (hcv_le : s_cv ≤ c.max_vars) (hlml : lm.length = 2 * c.max_vars)
    (hk_nat : k.toNat < usz) (hk_ws2 : k.toNat < ws2.length) :
    let lit := ws2[k.toNat]'hk_ws2 ^^^ 1#32
    lit.toNat < 2 * s_cv ∧ (BitVec.setWidth 64 lit).toNat < lm.length ∧
      (BitVec.setWidth 64 lit).toNat = litNeg (ws2[k.toNat]?.getD 0#32).toNat := by
  intro lit
  have hc_lt : (ws2[k.toNat]'hk_ws2).toNat < 2 * s_cv := by
    have q := hws2_lt k.toNat hk_nat
    rwa [List.getElem?_eq_getElem hk_ws2, Option.getD_some] at q
  have h1 : lit.toNat < 2 * s_cv := andExtract_not_lt hc_lt
  refine ⟨h1, by rw [bv_zext32_toNat, hlml]; omega, ?_⟩
  rw [bv_zext32_toNat, bv32_xor1_eq_litNeg, List.getElem?_eq_getElem hk_ws2, Option.getD_some]

private abbrev aeScanSliceOk (F_cur : List (List Nat)) (s : FullState) (lhs : BitVec 32)
    (widx wend : BitVec 64) : Prop :=
  if s.core.dense_mode = 0#64 then
    WatchSliceOk F_cur s.core lhs.toNat widx.toNat (wend.toNat - widx.toNat)
  else DenseWatchSliceOk F_cur s.core lhs.toNat widx.toNat (wend.toNat - widx.toNat)

private theorem andExtract_wvec_bds {c : FullCfg} {s : FullState}
    (hwvl : s.core.wvec.length = 4 * c.max_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hmaxv : c.max_vars < 2 * dimacsBound) {l : BitVec 32} (hl : l.toNat < 2 * s.core.cur_vars) :
    (BitVec.setWidth 64 l <<< 1#64).toNat < s.core.wvec.length ∧
      (BitVec.setWidth 64 l <<< 1#64 + 1#64).toNat < s.core.wvec.length := by
  have hdv : 4 * s.core.cur_vars + 2 < 2 ^ 64 := by unfold dimacsBound at hmaxv; omega
  have h0 : 2 * (BitVec.setWidth 64 l).toNat < 2 ^ 64 := by rw [bv_zext32_toNat]; omega
  have h1 : 2 * (BitVec.setWidth 64 l).toNat + 1 < 2 ^ 64 := by rw [bv_zext32_toNat]; omega
  refine ⟨?_, ?_⟩
  · rw [bv64_shl1_lt h0, bv_zext32_toNat]; omega
  · rw [bv64_shl1_add1_lt h1, bv_zext32_toNat]; omega

private theorem andExtract_scan_bounds {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {lhs : BitVec 32} (hlhs_lt : lhs.toNat < 2 * s.core.cur_vars)
    (hw0 : (BitVec.setWidth 64 lhs <<< 1#64).toNat < s.core.wvec.length)
    (hw1 : (BitVec.setWidth 64 lhs <<< 1#64 + 1#64).toNat < s.core.wvec.length) :
    let off64 := BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lhs <<< 1#64).toNat]'hw0)
    let wend64 := off64 + BitVec.setWidth 64
      (s.core.wvec[(BitVec.setWidth 64 lhs <<< 1#64 + 1#64).toNat]'hw1)
    off64.toNat ≤ wend64.toNat ∧ wend64.toNat ≤ c.wcap ∧
      aeScanSliceOk F_cur s lhs off64 wend64 := by
  intro off64 wend64
  have hdv : 4 * s.core.cur_vars + 2 < 2 ^ 64 := by
    have := hd.1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
  have hw_bds := fullWatchBounds_of_dense hd lhs.toNat hlhs_lt
  have h0s : (BitVec.setWidth 64 lhs <<< 1#64).toNat = 2 * lhs.toNat := by
    have h0 : 2 * (BitVec.setWidth 64 lhs).toNat < 2 ^ 64 := by rw [bv_zext32_toNat]; omega
    rw [bv64_shl1_lt h0, bv_zext32_toNat]
  have h1s : (BitVec.setWidth 64 lhs <<< 1#64 + 1#64).toNat = 2 * lhs.toNat + 1 := by
    have h1 : 2 * (BitVec.setWidth 64 lhs).toNat + 1 < 2 ^ 64 := by rw [bv_zext32_toNat]; omega
    rw [bv64_shl1_add1_lt h1, bv_zext32_toNat]
  have hoff_eq : off64.toNat = fullWatchOffCore s.core lhs.toNat := by
    dsimp only [off64]; unfold fullWatchOffCore
    rw [bv_zext32_toNat, ← h0s, List.getElem?_eq_getElem hw0, Option.getD_some]
  have hsz_eq :
      (s.core.wvec[(BitVec.setWidth 64 lhs <<< 1#64 + 1#64).toNat]'hw1).toNat =
        fullWatchSizeCore s.core lhs.toNat := by
    unfold fullWatchSizeCore
    rw [← h1s, List.getElem?_eq_getElem hw1, Option.getD_some]
  have hwcap_lt : c.wcap < 2 * dimacsBound := c.hwcap
  have hwend_eq : wend64.toNat =
      off64.toNat + (s.core.wvec[(BitVec.setWidth 64 lhs <<< 1#64 + 1#64).toNat]'hw1).toNat := by
    dsimp only [wend64]; unfold dimacsBound at hwcap_lt; bv_omega
  have hrem : wend64.toNat - off64.toNat = fullWatchSizeCore s.core lhs.toNat := by
    rw [← hsz_eq]; omega
  refine ⟨by omega, by omega, ?_⟩
  dsimp only [aeScanSliceOk]; rw [hrem, hoff_eq]; exact andExtract_dense_slice_ok hd hlhs_lt

private theorem andExtract_gateLoop_done {maxA : Nat} {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {usz isel k5 oi : BitVec 32} {g_len g_cur g_cap : BitVec 64}
    {mword : BitVec 32} {scr2 scrk : List (BitVec 32)}
    (hisel_lt : isel.toNat < usz.toNat) (husz3 : 3 ≤ usz.toNat)
    (husz_maxA : usz.toNat - 1 ≤ maxA) (husz_cv : usz.toNat ≤ s.core.cur_vars)
    (hg_c1 : g_len.toNat ≤ g_cur.toNat) (hg_room : g_cur.toNat + 2 + (usz.toNat - 1) ≤ g_cap.toNat)
    (hg_cap : g_cap.toNat ≤ c.scratch_cap) (hscrk : scrk.length = c.scratch_cap)
    (hws2_lt : ∀ j, j < usz.toNat →
      (s.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hisel_ws2 : isel.toNat < s.scratch.work_stk2.length)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (List.map
      (fun j => (s.scratch.work_stk2[j]?.getD 0#32).toNat) (List.range usz.toNat))))
    (hall_m2 : ∀ k, k < usz.toNat → k ≠ isel.toNat →
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        [litNeg (s.scratch.work_stk2[isel.toNat]?.getD 0#32).toNat,
         litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat]))
    (hmok1 : congGateArity mword = usz.toNat - 1)
    (hmok2 : (mword >>> 28).toNat = 0 ∧ 2 ≤ congGateArity mword ∧ congGateArity mword ≤ 64 ∨
      (mword >>> 28).toNat = 3 ∧ 65 ≤ congGateArity mword)
    (hpre2 : ∀ idx, idx < g_len.toNat → scr2[idx]? = s.scratch.scratch_buf[idx]?)
    (hseq2 : CongGateSeqOk maxA F_cur s.core.cur_vars scr2 g_cur.toNat 0)
    (hpk : ∀ idx, idx < g_cur.toNat → scrk[idx]? = scr2[idx]?)
    (hgk0 : scrk[g_cur.toNat]? = some (s.scratch.work_stk2[isel.toNat]'hisel_ws2))
    (hgk1 : scrk[g_cur.toNat + 1]? = some mword)
    (hk5_eq : k5.toNat = usz.toNat)
    (hoi : oi.toNat = if k5.toNat ≤ isel.toNat then k5.toNat else k5.toNat - 1)
    (hk_has : ∀ j, j < k5.toNat → j ≠ isel.toNat →
      litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat ∈
        List.map BitVec.toNat (List.take oi.toNat (List.drop (g_cur.toNat + 2) scrk)))
    (hk_mem : ∀ t, t < oi.toNat → ∃ j, j < k5.toNat ∧ j ≠ isel.toNat ∧
      scrk[g_cur.toNat + 2 + t]? = some (s.scratch.work_stk2[j]?.getD 0#32 ^^^ 1#32)) :
    let g_nx := g_cur + 2#64 + BitVec.setWidth 64 (usz - 1#32)
    g_len.toNat ≤ g_nx.toNat ∧ g_nx.toNat ≤ g_cap.toNat ∧
      (∀ idx, idx < g_len.toNat → scrk[idx]? = s.scratch.scratch_buf[idx]?) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars scrk g_nx.toNat 0 := by
  intro g_nx
  have hoi_eq : oi.toNat = usz.toNat - 1 := by
    rw [hoi, hk5_eq, ite_eq_right_iff.mpr (fun h => by omega)]
  rw [hk5_eq, hoi_eq] at hk_has hk_mem
  have hgk0' : scrk[g_cur.toNat]? = some (s.scratch.work_stk2[isel.toNat]?.getD 0#32) := by
    rw [List.getElem?_eq_getElem hisel_ws2, Option.getD_some]; exact hgk0
  have hpost := andExtract_gate_post hisel_lt husz_maxA husz_cv hg_c1 (by omega) hscrk hws2_lt
    hent hall_m2 hmok1 hmok2 hpre2 hseq2 hpk hgk0' hgk1 hk_has hk_mem
  have hz_u : (BitVec.setWidth 64 (usz - 1#32)).toNat = usz.toNat - 1 := by
    rw [bv_zext32_toNat]; bv_omega
  have hg_fin : g_nx.toNat = g_cur.toNat + 2 + (usz.toNat - 1) := by dsimp only [g_nx]; bv_omega
  exact ⟨by omega, by omega, hpost.1, hg_fin ▸ hpost.2⟩

private abbrev aeGateWriteBody (c : FullCfg) (s : FullState) (isel : Nat) (g_cur : BitVec 64)
    (csel mword : BitVec 32) (scr2 : List (BitVec 32)) (lmw : List (BitVec 8))
    (R : Mem 64 → Prop) (oi : BitVec 32) (kBound : Nat) (mk : Mem 64) : Prop :=
  oi.toNat = (if kBound ≤ isel then kBound else kBound - 1) ∧
  ∃ scrk : List (BitVec 32), scrk.length = c.scratch_cap ∧
    (∀ idx, idx < g_cur.toNat → scrk[idx]? = scr2[idx]?) ∧
    scrk[g_cur.toNat]? = some csel ∧ scrk[g_cur.toNat + 1]? = some mword ∧
    (∀ j, j < kBound → j ≠ isel → litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat ∈
      List.map BitVec.toNat (List.take oi.toNat (List.drop (g_cur.toNat + 2) scrk))) ∧
    (∀ t, t < oi.toNat → ∃ j, j < kBound ∧ j ≠ isel ∧
      scrk[g_cur.toNat + 2 + t]? = some (s.scratch.work_stk2[j]?.getD 0#32 ^^^ 1#32)) ∧
    aeMem c s lmw scrk R mk

private theorem andExtract_clearBit2_done {c : FullCfg} {ws2 : List (BitVec 32)} {usz : Nat}
    {lmc : List (BitVec 8)}
    (hk : ∀ k, k < usz → (lmc[litNeg (ws2[k]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (hinv : aeMarkInv c ws2 usz lmc) : aeBit2Clr c lmc := fun l hl => by
  by_cases hne : lmc[l]?.getD 0#8 = 0#8
  · rw [hne]; decide
  · rcases hinv l hl hne with ⟨k, hk_lt, rfl⟩; exact hk k hk_lt

private theorem andExtract_all_m2 {F_cur : List (List Nat)} {s : FullState}
    {usz isel : Nat} (hisel : isel < usz) {lmw : List (BitVec 8)} {lhs : BitVec 32}
    (hlhs : lhs.toNat = litNeg (s.scratch.work_stk2[isel]?.getD 0#32).toNat)
    (hcnt : usz - 1 = (List.range usz).countP (fun k =>
      decide (k ≠ isel) && andExtractMarkGood lmw s.scratch.work_stk2 k))
    (hentw : ∀ k, k < usz → k ≠ isel → andExtractMarkGood lmw s.scratch.work_stk2 k = true →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lhs.toNat, litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat])) :
    ∀ k, k < usz → k ≠ isel → (cnfOfClauses F_cur).EntailsClause (cnfClause
      [litNeg (s.scratch.work_stk2[isel]?.getD 0#32).toNat,
       litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat]) := fun k hk hki => by
  rw [← hlhs]; exact hentw k hk hki (andExtract_countP_full hisel hcnt.symm k hk hki)

private theorem andExtract_scan_init_ok {c : FullCfg} {F_cur : List (List Nat)}
    {ws2 : List (BitVec 32)} {usz isel s_cv : Nat}
    (hws2_lt : ∀ k, k < usz → (ws2[k]?.getD 0#32).toNat < 2 * s_cv)
    (hle : s_cv ≤ c.max_vars) {lm2 : List (BitVec 8)} (hb2 : aeBit2Clr c lm2)
    (lhs : BitVec 32) :
    ((0#32 : BitVec 32).toNat = (List.range usz).countP (fun k =>
      decide (k ≠ isel) && andExtractMarkGood lm2 ws2 k)) ∧
    (∀ k, k < usz → k ≠ isel → andExtractMarkGood lm2 ws2 k = true →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lhs.toNat, litNeg (ws2[k]?.getD 0#32).toNat])) := by
  have hcl : ∀ k, k < usz → andExtractMarkGood lm2 ws2 k = false := fun k hk => by
    have hlt : litNeg (ws2[k]?.getD 0#32).toNat < 2 * c.max_vars :=
      Nat.lt_of_lt_of_le (bv32_xor1_lt_even (hws2_lt k hk)) (by omega)
    simp [andExtractMarkGood, hb2 _ hlt]
  refine ⟨?_, fun k hk _ hg => by simp [hcl k hk] at hg⟩
  symm; change (List.range usz).countP _ = 0
  rw [List.countP_eq_zero]; intro k hk; simp [hcl k (List.mem_range.mp hk)]

private theorem andExtract_scan_join_step {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {usz isel : Nat} {lhs : BitVec 32} {scr2 : List (BitVec 32)}
    {R : Mem 64 → Prop} (hisel : isel < usz)
    (hnd : ∀ j, j < usz → ∀ j2, j2 < usz → j ≠ j2 →
      (s.scratch.work_stk2[j]?.getD 0#32).toNat ≠
        (s.scratch.work_stk2[j2]?.getD 0#32).toNat)
    {lmw : List (BitVec 8)} (hlmw : lmw.length = 2 * c.max_vars)
    (hinvw : aeMarkInv c s.scratch.work_stk2 usz lmw) {mcnt : BitVec 32}
    (hcntw : mcnt.toNat = (List.range usz).countP (fun k =>
      decide (k ≠ isel) && andExtractMarkGood lmw s.scratch.work_stk2 k))
    (hlhs_eq : lhs = (s.scratch.work_stk2[isel]?.getD 0#32) ^^^ 1#32)
    (husz_bd : usz < 2 ^ 31)
    {other : BitVec 32} (hot_lt : other.toNat < 2 * c.max_vars) (hot_ne : other ≠ lhs)
    (hot_lm : (BitVec.setWidth 64 other).toNat < lmw.length)
    (hmk3 : lmw[(BitVec.setWidth 64 other).toNat]'hot_lm &&& 3#8 = 1#8)
    (hent_bin : (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs.toNat, other.toNat]))
    (hentw : ∀ k, k < usz → k ≠ isel → andExtractMarkGood lmw s.scratch.work_stk2 k = true →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lhs.toNat, litNeg (s.scratch.work_stk2[k]?.getD 0#32).toNat]))
    {mw : Mem 64}
    (hmw' : aeMem c s (lmw.set (BitVec.setWidth 64 other).toNat
      (lmw[(BitVec.setWidth 64 other).toNat]'hot_lm ||| 2#8)) scr2 R mw) :
    ∃ lmv, aeScanInv c F_cur s usz isel lhs scr2 R (mcnt + 1#32) lmv mw := by
  have hscan := andExtract_scan_step hisel hnd hlmw hinvw hcntw hlhs_eq hot_lt hot_ne hot_lm
    hmk3 hent_bin hentw
  have hcnt_le : mcnt.toNat ≤ usz := by
    rw [hcntw]; exact Nat.le_trans List.countP_le_length (by simp)
  have hmc_lt : mcnt.toNat + 1 < 2 ^ 32 := by omega
  exact ⟨_, by simp [hlmw], hscan.1, by rw [bv32_add1_lt_of hmc_lt]; exact hscan.2.1,
    hscan.2.2, hmw'⟩

private theorem andExtract_mword_scrm1 {c : FullCfg} {g_cur : BitVec 64}
    {csel mword : BitVec 32} {scr2 scrm : List (BitVec 32)}
    (hs_len : scrm.length = c.scratch_cap)
    (hs_pre : ∀ idx, idx < g_cur.toNat → scrm[idx]? = scr2[idx]?)
    (hs_g0 : scrm[g_cur.toNat]? = some csel) (hg_scr1 : (g_cur + 1#64).toNat < scrm.length)
    (hg1_eq : (g_cur + 1#64).toNat = g_cur.toNat + 1) :
    let scrm1 := scrm.set (g_cur + 1#64).toNat mword
    scrm1.length = c.scratch_cap ∧
      (∀ idx, idx < g_cur.toNat → scrm1[idx]? = scr2[idx]?) ∧
      scrm1[g_cur.toNat]? = some csel ∧ scrm1[g_cur.toNat + 1]? = some mword := by
  refine ⟨by simp [hs_len], fun idx hi => by
    rw [List.getElem?_set_ne (by omega)]; exact hs_pre idx hi,
    by rw [List.getElem?_set_ne (by omega)]; exact hs_g0, ?_⟩
  rw [← hg1_eq, List.getElem?_eq_getElem (by simp [hs_len] at hg_scr1 ⊢; exact hg_scr1),
    List.getElem_set_self]

private theorem andExtract_mword_pre {c : FullCfg} {g_cur : BitVec 64} {csel : BitVec 32}
    {scr2 : List (BitVec 32)} (hscr2 : scr2.length = c.scratch_cap)
    (hg : g_cur.toNat < scr2.length) :
    (scr2.set g_cur.toNat csel).length = c.scratch_cap ∧
      (∀ idx, idx < g_cur.toNat → (scr2.set g_cur.toNat csel)[idx]? = scr2[idx]?) ∧
      (scr2.set g_cur.toNat csel)[g_cur.toNat]? = some csel :=
  ⟨by simp [hscr2], fun idx hi => by rw [List.getElem?_set_ne (by omega)],
   by rw [List.getElem?_eq_getElem (by simp [hscr2] at hg ⊢; exact hg), List.getElem_set_self]⟩

private abbrev aeClearBit2Outer (maxA : Nat) (c : FullCfg) (F_cur : List (List Nat))
    (s : FullState) (g_len g_cap : BitVec 64) (lmw : List (BitVec 8)) (R : Mem 64 → Prop)
    (g_nx : BitVec 64) (mg : Mem 64) : Prop :=
  g_len.toNat ≤ g_nx.toNat ∧ g_nx.toNat ≤ g_cap.toNat ∧
    ∃ scr3 : List (BitVec 32), scr3.length = c.scratch_cap ∧
      (∀ idx, idx < g_len.toNat → scr3[idx]? = s.scratch.scratch_buf[idx]?) ∧
      CongGateSeqOk maxA F_cur s.core.cur_vars scr3 g_nx.toNat 0 ∧
      aeMem c s lmw scr3 R mg

private abbrev aeScanOuterInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (usz isel : Nat) (lhs : BitVec 32) (scr2 : List (BitVec 32)) (R : Mem 64 → Prop)
    (wend64 widx : BitVec 64) (mcnt : BitVec 32) (m : Mem 64) : Prop :=
  widx.toNat ≤ wend64.toNat ∧ aeScanSliceOk F_cur s lhs widx wend64 ∧
    ∃ lmw, aeScanInv c F_cur s usz isel lhs scr2 R mcnt lmw m

private theorem andExtract_watch_step {F_cur : List (List Nat)} {s : FullState}
    {lhs : BitVec 32} {w_idx w_nx wend64 : BitVec 64} {d : Nat} (hd : 0 < d)
    (hw_eq : w_nx.toNat = w_idx.toNat + d) (hwn_le : w_nx.toNat ≤ wend64.toNat)
    (hns : if s.core.dense_mode = 0#64 then
        WatchSliceOk F_cur s.core lhs.toNat (w_idx.toNat + d) (wend64.toNat - w_idx.toNat - d)
      else DenseWatchSliceOk F_cur s.core lhs.toNat (w_idx.toNat + d)
        (wend64.toNat - w_idx.toNat - d)) :
    w_idx.toNat < w_nx.toNat ∧ w_nx.toNat ≤ wend64.toNat ∧
      aeScanSliceOk F_cur s lhs w_nx wend64 :=
  ⟨by omega, hwn_le, by
    simpa [aeScanSliceOk, hw_eq, show wend64.toNat - (w_idx.toNat + d) =
      wend64.toNat - w_idx.toNat - d by omega] using hns⟩

private theorem ae_trunc8_and5 : ∀ x : BitVec 8,
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&& 5#32) = x &&& 5#8 := by decide

private theorem ae_trunc8_or2 : ∀ x : BitVec 8,
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| 2#32) = x ||| 2#8 := by decide

private theorem ae_trunc8_mask3 : ∀ x : BitVec 8,
    BitVec.setWidth 32 x &&& 3#32 = 1#32 → x &&& 3#8 = 1#8 := by decide

private theorem andExtract_wend_eq {s : FullState} {isel : BitVec 32}
    (hisel_cv : isel.toNat < s.scratch.work_stk2.length)
    (hw0 : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64).toNat < s.core.wvec.length)
    (hw1 : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64 + 1#64).toNat < s.core.wvec.length)
    (h0b : 2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) % 2 ^ 64 < s.core.wvec.length)
    (h1b : (2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) + BitVec.toNat (1#64)) % 2 ^ 64 <
      s.core.wvec.length) :
    (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
        (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64).toNat]'hw0) +
      BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
        (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64 + 1#64).toNat]'
        hw1)).toNat =
      (s.core.wvec[2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) % 2 ^ 64].toNat +
        s.core.wvec[(2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) +
          BitVec.toNat (1#64)) % 2 ^ 64].toNat) % 2 ^ 64 := by
  have hlt32 : s.scratch.work_stk2[isel.toNat].toNat ^^^ 1 < 2 ^ 32 := by
    have h1 : (1#32).toNat = 1 := rfl
    rw [← h1, ← BitVec.toNat_xor]; exact BitVec.isLt _
  have h0s : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64).toNat = 2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) % 2 ^ 64 := by
    have hzx : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32)).toNat =
        s.scratch.work_stk2[isel.toNat].toNat ^^^ 1 := by
      rw [bv_zext32_toNat, BitVec.toNat_xor]; rfl
    rw [bv64_shl1_lt (by omega), hzx, Nat.mod_eq_of_lt (by omega)]
  have h1s : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64 + 1#64).toNat =
      (2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) + BitVec.toNat (1#64)) % 2 ^ 64 := by
    have hz1 : BitVec.toNat (1#64) = 1 := rfl
    rw [BitVec.toNat_add, h0s, hz1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat]
  simp only [h0s, h1s]

private theorem andExtract_wend_lt {s : FullState} {isel : BitVec 32} {w_idx : BitVec 64}
    (hisel_cv : isel.toNat < s.scratch.work_stk2.length)
    (hw0 : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64).toNat < s.core.wvec.length)
    (hw1 : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64 + 1#64).toNat < s.core.wvec.length)
    {h0b : 2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) % 2 ^ 64 < s.core.wvec.length}
    {h1b : (2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) + BitVec.toNat (1#64)) % 2 ^ 64 <
      s.core.wvec.length}
    (hc : w_idx.toNat < (s.core.wvec[2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) %
      2 ^ 64].toNat + s.core.wvec[(2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) +
        BitVec.toNat (1#64)) % 2 ^ 64].toNat) % 2 ^ 64) :
    w_idx.toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
      (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64).toNat]'hw0) +
      BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
        (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64 + 1#64).toNat]'
        hw1)).toNat := by
  rwa [andExtract_wend_eq hisel_cv hw0 hw1 h0b h1b]

private theorem andExtract_wend_uge_false {c : FullCfg} {s : FullState} {isel : BitVec 32}
    {w_idx : BitVec 64} (hisel_cv : isel.toNat < s.scratch.work_stk2.length)
    (hw0 : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64).toNat < s.core.wvec.length)
    (hw1 : (BitVec.setWidth 64 (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<<
      1#64 + 1#64).toNat < s.core.wvec.length)
    (hwend_bd : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
      (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64).toNat]'hw0) +
      BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
        (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64 + 1#64).toNat]'
        hw1)).toNat ≤ c.wcap)
    (hc_wcap : c.wcap < 2 * dimacsBound)
    (hrem2 : 2 ≤ (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
      (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64).toNat]'hw0) +
      BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
        (s.scratch.work_stk2[isel.toNat]'hisel_cv ^^^ 1#32) <<< 1#64 + 1#64).toNat]'
        hw1)).toNat - w_idx.toNat)
    {h0b : 2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) % 2 ^ 64 < s.core.wvec.length}
    {h1b : (2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) + BitVec.toNat (1#64)) % 2 ^ 64 <
      s.core.wvec.length}
    (huge : (s.core.wvec[2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) % 2 ^ 64].toNat +
      s.core.wvec[(2 * (s.scratch.work_stk2[isel.toNat].toNat ^^^ 1) +
        BitVec.toNat (1#64)) % 2 ^ 64].toNat) % 2 ^ 64 ≤
      (w_idx.toNat + BitVec.toNat (1#64)) % 2 ^ 64) : False := by
  rw [← andExtract_wend_eq hisel_cv hw0 hw1 h0b h1b] at huge
  unfold dimacsBound at hc_wcap
  have h1 : BitVec.toNat (1#64) = 1 := rfl
  rw [h1] at huge; omega

private theorem ae_gw (g_cur : BitVec 64) (oi k5 : BitVec 32)
    (scr_len ws2_len : Nat)
    (h1 : g_cur.toNat + 2 + oi.toNat < scr_len) (hscr : scr_len < 2 ^ 30)
    (hk5 : k5.toNat < ws2_len) :
    (g_cur + 2#64 + BitVec.setWidth 64 oi).toNat < scr_len ∧
      (BitVec.setWidth 64 k5).toNat < ws2_len ∧
      (g_cur + 2#64 + BitVec.setWidth 64 oi).toNat = g_cur.toNat + 2 + oi.toNat := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

private theorem ae_mword_le (u : BitVec 32) (h : (u - 1#32).toNat ≤ 64) :
    u - 1#32 = if (u - 1#32).ule 64#32 = true then u - 1#32 else 3#32 <<< 28 ||| u - 1#32 := by
  have hu : (u - 1#32).ule 64#32 = true := by simp [BitVec.ule]; bv_omega
  rw [hu]; rfl

private theorem ae_mword_gt (u : BitVec 32) (h : ¬ (u - 1#32).toNat ≤ 64) :
    3#32 <<< 28 ||| u - 1#32 =
      if (u - 1#32).ule 64#32 = true then u - 1#32 else 3#32 <<< 28 ||| u - 1#32 := by
  have hu : (u - 1#32).ule 64#32 = false := by simp [BitVec.ule]; bv_omega
  rw [hu]; rfl

public section

theorem full_cong_extract_and_clause_fid_wp {Γ : Env} :
    ∀ args m Q X, Spec.fullCongExtractAndClauseFidSpec args m Q X →
      Func.wp Γ full_cong_extract_and_clause_fid_body args m Q X := by
  rintro ⟨h_arg, usz, g_len, g_cap, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmaxA, rfl, hdense, husz3, husz_maxA, husz_cv,
      hg_le, hg_cap, hseq, hws2_lt, hws2_nd, hent, hm0, hQ⟩
  have hcl := hdense.1.core_ok; have hsc := hdense.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hlml := hcl.lit_mark_len; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hsl := hsc.scratch_buf_len; have hmaxv := c.hmaxv
  have hws1l := hsc.work_stk1_len; have hws2l := hsc.work_stk2_len; have hmrk := hdense.2.2.1
  have hcv_u64 : 4 * s.core.cur_vars + 2 < 2 ^ 64 := by unfold dimacsBound at hmaxv; omega
  dsimp only [Func.wp, full_cong_extract_and_clause_fid_body]; c0_hstraight!
  c0_hsplit; next => exfalso; bv_omega
  clear hc; c0_hstraight!; c0_hsplit
  · exfalso; have hca : congAndArityMax = 1000000 := rfl; bv_omega
  clear hc; c0_hstraight!; c0_hsplit; next => exfalso; bv_omega
  clear hc; c0_hstraight!; c0_hsplit; next => exfalso; bv_omega
  clear hc; c0_hstraight!; c0_hsplit
  · clear hc; c0_hstraight!; exact hQ g_len s.core.lit_mark s.scratch.scratch_buf
      s.scratch.res_sz m0 hdense (Nat.le_refl _) hg_le (fun _ _ => rfl) hseq hm0
  have hroom_bv := hc; clear hc; have hz_u := bv_zext32_toNat (usz - 1#32)
  have hscr_u30 : c.scratch_cap < 2 ^ 30 := by have := c.hscr; unfold dimacsBound at this; omega
  have husz_u31 : usz.toNat < 2 ^ 31 := by have : congAndArityMax = 1000000 := rfl; omega
  have hg_room : g_len.toNat + 2 + (usz.toNat - 1) ≤ g_cap.toNat := by bv_omega
  have hnot_inv0 : aeMarkInv c s.scratch.work_stk2 usz.toNat s.core.lit_mark ∧
      aeBit2Clr c s.core.lit_mark :=
    ⟨fun l hl hne => absurd (hmrk.2 l hl) hne, fun l hl => by rw [hmrk.2 l hl]; decide⟩
  c0_hstraight!; refine wp_loop_group (fun n1 (xs1 : Tup Val [i32, i32, i32]) m1 =>
      n1 = usz.toNat - xs1.snd.snd.fst.toNat ∧ xs1.snd.snd.fst.toNat ≤ usz.toNat ∧
      aeLoop1Body c s usz R xs1.fst m1) ?_ ?_
  · rintro L1 n1 ⟨bi, bw, j, ⟨⟩⟩ m1 hL1 ⟨rfl, hj_le, hbi, lm1, hlm1, hinv1, hb2_1, hm1⟩
    dsimp only [Blocks.get, Member.here]; dsimp only at hj_le hbi
    c0_hstraight!; c0_hsplit
    · have hj_lt := hc; clear hc; have hj_nat : j.toNat < usz.toNat := by bv_omega
      have hj_ws2 : (BitVec.setWidth 64 j).toNat < s.scratch.work_stk2.length := by bv_omega
      c0_hstraight!
      have hc_lt : (s.scratch.work_stk2[j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have q := hws2_lt j.toNat hj_nat; rwa [List.getElem?_eq_getElem (by omega),
          Option.getD_some] at q
      have hcj_ws1 : (BitVec.setWidth 64
          (s.scratch.work_stk2[j.toNat]'(by omega))).toNat < s.scratch.work_stk1.length := by
        bv_omega
      refine wp_join_group (fun xsn mn => aeLoop1Body c s usz R xsn.fst mn) ?_ ?_
      · rintro _ ⟨bi', bw', ⟨⟩⟩ mn ⟨hbi', lmn, hlmn, hinvn, hb2_n, hmn⟩
        dsimp only [Blocks.get, Member.here]; c0_hstraight!
        exact hL1 (usz.toNat - (j + 1#32).toNat) (bi', bw', j + 1#32, ()) mn (by bv_omega)
          ⟨rfl, by bv_omega, hbi', lmn, hlmn, hinvn, hb2_n, hmn⟩
      · intro Jn hJn; c0_hstraight!; c0_hsplit
        · clear hc; obtain ⟨hnot_lt2, hnot_lt, hnot_eq⟩ :=
            andExtract_not_idx hws2_lt hcv_le hlm1 hj_nat (by omega)
          have hnot_wv := (andExtract_wvec_bds hwvl hcv_le hmaxv hnot_lt2).2; c0_hstraight!
          refine wp_join_group (fun xsb mb => (xsb.fst.toNat < usz.toNat ∨ xsb.fst = usz) ∧
              aeMem c s (lm1.set (BitVec.setWidth 64 (s.scratch.work_stk2[j.toNat]'(by omega) ^^^
                1#32)).toNat 5#8) s.scratch.scratch_buf R mb) ?_ ?_
          · rintro _ ⟨bi', bw', ⟨⟩⟩ mb ⟨hbi', hmb⟩
            dsimp only [Blocks.get, Member.here]
            exact hJn (bi', bw', ()) mb ⟨hbi', lm1.set _ 5#8, by simp [hlm1],
              andExtract_markInv_set hinv1 hj_nat hnot_eq 5#8,
              andExtract_bit2_clear hlm1 hb2_1 (by decide), hmb⟩
          · intro Jb hJb; c0_hstraight!; c0_hsplit
            · clear hc; c0_hstraight!; exact hJb (j, _) _ ⟨Or.inl hj_nat, by assumption⟩
            · clear hc; c0_hstraight!; c0_hsplit
              · clear hc; c0_hstraight!; exact hJb (j, _) _ ⟨Or.inl hj_nat, by assumption⟩
              · clear hc; c0_hstraight!; exact hJb (bi, bw, ()) _ ⟨hbi, by assumption⟩
        · clear hc; obtain ⟨_, hnot_lt, hnot_eq⟩ :=
            andExtract_not_idx hws2_lt hcv_le hlm1 hj_nat (by omega)
          c0_hstraight!
          exact hJn (bi, bw, ()) _ ⟨hbi, lm1.set _ 1#8, by simp [hlm1],
            andExtract_markInv_set hinv1 hj_nat hnot_eq 1#8,
            andExtract_bit2_clear hlm1 hb2_1 (by decide), by assumption⟩
    · have hj_dn := hc; clear hc
      have hj_eq : j = usz := BitVec.eq_of_toNat_eq (by bv_omega)
      clear hj_dn hj_le hL1; subst j; c0_hstraight!
      refine wp_join_group (fun xsp mp => g_len.toNat ≤ xsp.fst.toNat ∧
          xsp.fst.toNat ≤ g_cap.toNat ∧ ∃ (lmp : List (BitVec 8)) (scrp : List (BitVec 32)),
            lmp.length = 2 * c.max_vars ∧ scrp.length = c.scratch_cap ∧ (∀ idx,
              idx < g_len.toNat → scrp[idx]? = s.scratch.scratch_buf[idx]?) ∧ CongGateSeqOk maxA
              F_cur s.core.cur_vars scrp xsp.fst.toNat 0 ∧ aeMarkInv c s.scratch.work_stk2 usz.toNat
              lmp ∧ aeMem c s lmp scrp R mp) ?_ ?_
      · rintro _ ⟨ret, _bi, ticks, ⟨⟩⟩ mp
          ⟨hrl, hrg, lmp, scrp, hlmp, hscrp, hpre, hseqp, hinvp, hmp⟩
        refine wp_loop_group (fun nk (xsk : Tup Val [i32]) mk => nk = usz.toNat - xsk.fst.toNat ∧
            xsk.fst.toNat ≤ usz.toNat ∧ ∃ lmc : List (BitVec 8), lmc.length = 2 * c.max_vars ∧
              (∀ j, j < xsk.fst.toNat →
                lmc[litNeg (s.scratch.work_stk2[j]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
              aeMarkInv c s.scratch.work_stk2 usz.toNat lmc ∧ aeMem c s lmc scrp R mk) ?_ ?_
        · rintro Lc nc ⟨kc, ⟨⟩⟩ mk hLc ⟨rfl, hkc_le, lmc, hlmc, hclr_k, hinv_k, hmk⟩
          dsimp only [Blocks.get, Member.here]; c0_hstraight!; c0_hsplit
          · have hkc_lt := hc; clear hc; have hkc_nat : kc.toNat < usz.toNat := by bv_omega
            have hk_ws2 : (BitVec.setWidth 64 kc).toNat < s.scratch.work_stk2.length := by bv_omega
            obtain ⟨_, hnot_lt, hnot_eq⟩ :=
              andExtract_not_idx hws2_lt hcv_le hlmc hkc_nat (by omega)
            c0_hstraight!
            have hstep := andExtract_clear_step hkc_nat hws2_nd hnot_eq hnot_lt hclr_k hinv_k
            have hkcn : (kc + 1#32).toNat = kc.toNat + 1 := by bv_omega
            exact hLc (usz.toNat - (kc + 1#32).toNat) (kc + 1#32, ()) _ (by bv_omega)
              ⟨rfl, by bv_omega, lmc.set _ 0#8, by simp [hlmc],
                by dsimp only; rw [hkcn]; exact hstep.1, hstep.2, by assumption⟩
          · have hkc_dn := hc; clear hc; have hkc_eq : kc.toNat = usz.toNat := by bv_omega
            rw [hkc_eq] at hclr_k; c0_hstraight!
            exact hQ ret lmc scrp ticks _ (andExtract_fullDenseInvW hdense ticks hlmc hscrp
              (andExtract_cleanup_clear hinv_k hclr_k)) hrl hrg hpre hseqp (by assumption)
        · intro Jc hJc
          exact hJc usz.toNat (0#32, ()) mp ⟨rfl, Nat.zero_le _, lmp, hlmp,
            fun _ h => absurd h (Nat.not_lt_zero _), hinvp, hmp⟩
      · intro Jp hJp; c0_hstraight!; c0_hsplit
        · have hbi_lt := hc; clear hc; have hbi_nat : bi.toNat < usz.toNat := by bv_omega
          c0_hstraight!
          refine wp_loop_group (fun n2 xs2 m2 => n2 = usz.toNat - xs2.snd.snd.snd.fst.toNat ∧
              xs2.snd.snd.snd.fst.toNat ≤ usz.toNat ∧ ∃ lm2 scr2,
                aeStateInv maxA c F_cur s usz.toNat g_len g_cap R xs2.fst lm2 scr2 m2) ?_ ?_
          · rintro L2 n2 ⟨g_cur, _dead, ticks, i, ⟨⟩⟩ m2 hL2
              ⟨rfl, hi_le, lm2, scr2, hg_c1, hg_c2, hlm2, hscr2, hpre2, hseq2, hinv2, hb2_2, hm2⟩
            dsimp only [Blocks.get, Member.here]; dsimp only at hi_le; c0_hstraight!; c0_hsplit
            · have hi_lt := hc; clear hc; have hi_nat : i.toNat < usz.toNat := by bv_omega
              c0_hstraight!; c0_hsplit
              · have hg_room2 := hc; clear hc; have hz_u := bv_zext32_toNat (usz - 1#32)
                have hg_room_nat : g_cur.toNat + 2 + (usz.toNat - 1) ≤ g_cap.toNat := by bv_omega
                c0_hstraight!; c0_hsplit
                · clear hc
                  refine wp_join_group (fun xss ms => xss.fst.toNat < usz.toNat ∧ ms = m2) ?_ ?_
                  · rintro _ ⟨isel, ⟨⟩⟩ ms ⟨hisel_lt, rfl⟩
                    dsimp only [Blocks.get, Member.here]; dsimp only at hisel_lt
                    have hisel_cv : isel.toNat < s.scratch.work_stk2.length := by omega
                    have hisel_ws2 : (BitVec.setWidth 64 isel).toNat < s.scratch.work_stk2.length :=
                      by rw [bv_zext32_toNat]; exact hisel_cv
                    c0_hstraight!
                    have hcsel_lt : (s.scratch.work_stk2[isel.toNat]'(by omega)).toNat <
                        2 * s.core.cur_vars := by
                      have q := hws2_lt isel.toNat hisel_lt; rwa [List.getElem?_eq_getElem
                        (by omega), Option.getD_some] at q
                    let csel := s.scratch.work_stk2[isel.toNat]'hisel_cv
                    let lhs := csel ^^^ 1#32
                    have hlhs_lt : lhs.toNat < 2 * s.core.cur_vars := andExtract_not_lt hcsel_lt
                    refine wp_join_group (fun xs3 m3 => ∃ lm3 scr3, aeStateInv maxA c F_cur s
                        usz.toNat g_len g_cap R xs3.fst lm3 scr3 m3) ?_ ?_
                    · rintro _ ⟨g_nx, _d2, ticks_nx, ⟨⟩⟩ m3 ⟨lm3, scr3, hst3⟩
                      c0_hstraight!
                      exact hL2 (usz.toNat - (i + 1#32).toNat) (g_nx, _d2, ticks_nx, i + 1#32, ())
                        m3 (by bv_omega) ⟨rfl, by bv_omega, lm3, scr3, hst3⟩
                    · intro J3 hJ3
                      have hlhs_lm : (BitVec.setWidth 64 lhs).toNat < lm2.length := by
                        rw [bv_zext32_toNat, hlm2]; omega
                      c0_hstraight!; c0_hsplit
                      · clear hc; obtain ⟨hlhs_w0, hlhs_w1⟩ :=
                          andExtract_wvec_bds hwvl hcv_le hmaxv hlhs_lt
                        c0_hstraight!
                        let off64 := BitVec.setWidth 64
                          (s.core.wvec[(BitVec.setWidth 64 lhs <<< 1#64).toNat]'hlhs_w0)
                        let wend64 := off64 + BitVec.setWidth 64
                          (s.core.wvec[(BitVec.setWidth 64 lhs <<< 1#64 + 1#64).toNat]'hlhs_w1)
                        have hw_ok := andExtract_scan_bounds hdense hlhs_lt hlhs_w0 hlhs_w1
                        have hwend_bd : wend64.toNat ≤ c.wcap := by
                          dsimp only [wend64, off64]; exact hw_ok.2.1
                        refine wp_join_group (fun xsw mw => ∃ lmw, aeScanInv c F_cur s usz.toNat
                            isel.toNat lhs scr2 R xsw.snd.snd.fst lmw mw) ?_ ?_
                        · rintro _ ⟨tkw, _, mcnt, ⟨⟩⟩ mw ⟨lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                          dsimp only [Blocks.get, Member.here]
                          refine wp_join_group (fun xsg mg => aeClearBit2Outer maxA c F_cur s
                              g_len g_cap lmw R xsg.fst mg) ?_ ?_
                          · rintro _ ⟨g_nx, ⟨⟩⟩ mg ⟨hgna, hgnb, scr3, hscr3, hpre3, hseq3, hmg⟩
                            dsimp only [Blocks.get, Member.here]
                            refine wp_loop_group (fun n4 xs4 m4 => n4 = usz.toNat - xs4.fst.toNat ∧
                                xs4.fst.toNat ≤ usz.toNat ∧ aeClearBit2Body c s usz.toNat scr3 R
                                  xs4.fst.toNat m4) ?_ ?_
                            · rintro L4 n4 ⟨k4, ⟨⟩⟩ m4 hL4
                                ⟨rfl, hk4_le, lmc, hlmc, hclr4, hinv4, hm4⟩
                              dsimp only [Blocks.get, Member.here]; c0_hstraight!; c0_hsplit
                              · have hk4_lt := hc; clear hc
                                have hk4_nat : k4.toNat < usz.toNat := by bv_omega
                                have hk4_ws2 : (BitVec.setWidth 64 k4).toNat <
                                    s.scratch.work_stk2.length := by bv_omega
                                obtain ⟨_, hnot4_lt, hnot4_eq⟩ :=
                                  andExtract_not_idx hws2_lt hcv_le hlmc hk4_nat (by omega)
                                c0_hstraight!
                                refine wp_join_group (fun xsx mx => xsx = () ∧
                                    aeClearBit2Body c s usz.toNat scr3 R (k4.toNat + 1) mx) ?_ ?_
                                · rintro _ ⟨⟩ mx ⟨_, lmc', hlmc', hclr4', hinv4', hmx⟩
                                  dsimp only [Blocks.get, Member.here]; c0_hstraight!
                                  exact hL4 (usz.toNat - (k4 + 1#32).toNat) (k4 + 1#32, ()) mx
                                    (by bv_omega) ⟨rfl, by bv_omega, lmc', hlmc', by
                                      rwa [show (k4 + 1#32).toNat = k4.toNat + 1 by bv_omega],
                                      hinv4', hmx⟩
                                · intro Jx hJx; c0_hstraight!; c0_hsplit
                                  · clear hc; c0_hstraight!
                                    let val := (lmc[(BitVec.setWidth 64
                                      (s.scratch.work_stk2[k4.toNat]'(by omega) ^^^ 1#32)).toNat]'
                                      hnot4_lt) &&& 5#8
                                    have hv2 : val &&& 2#8 = 0#8 := by
                                      dsimp only [val]
                                      exact (by
                                        decide : ∀ x : BitVec 8, (x &&& 5#8) &&& 2#8 = 0#8) _
                                    have hstep := andExtract_clear_bit1_step hk4_nat hws2_nd
                                      hnot4_eq hnot4_lt hclr4 hinv4 (v := val) hv2
                                    exact hJx () _ ⟨rfl, lmc.set _ val, by simp [hlmc], hstep.1,
                                      hstep.2, (by dsimp only [val] at *
                                                   simp only [bv_zext32_toNat, ae_trunc8_and5] at *
                                                   assumption)⟩
                                  · clear hc; c0_hstraight!
                                    have hstep := andExtract_clear_bit1_step hk4_nat hws2_nd
                                      hnot4_eq hnot4_lt hclr4 hinv4 (v := 1#8) (by decide)
                                    exact hJx () _ ⟨rfl, lmc.set _ 1#8, by simp [hlmc], hstep.1,
                                      hstep.2, (by simp only [bv_zext32_toNat] at *; assumption)⟩
                              · have hk4_dn := hc; clear hc
                                have hk4_eq : k4.toNat = usz.toNat := by bv_omega
                                rw [hk4_eq] at hclr4
                                have hb2_all := andExtract_clearBit2_done hclr4 hinv4; c0_hstraight!
                                exact hJ3 (g_nx, k4, tkw, ()) _ ⟨lmc, scr3, hgna, hgnb, hlmc,
                                  hscr3, hpre3, hseq3, hinv4, hb2_all, hm4⟩
                            · intro J4 hJ4; c0_hstraight!
                              exact hJ4 usz.toNat (0#32, ()) mg ⟨rfl, Nat.zero_le _, lmw, hlmw,
                                fun _ h => absurd h (Nat.not_lt_zero _), hinvw, hmg⟩
                          · intro Jg hJg; c0_hstraight!; c0_hsplit
                            · have hmc_eq := hc; clear hc
                              have hmc_nat : mcnt.toNat = usz.toNat - 1 := by bv_omega
                              rw [hmc_nat] at hcntw
                              have hlhs_nat : lhs.toNat =
                                  litNeg (s.scratch.work_stk2[isel.toNat]?.getD 0#32).toNat := by
                                dsimp only [lhs, csel]; rw [bv32_xor1_eq_litNeg,
                                  List.getElem?_eq_getElem hisel_cv, Option.getD_some]
                              have hall_m2 := andExtract_all_m2 hisel_lt hlhs_nat hcntw hentw
                              have hg_scr0 : g_cur.toNat < scr2.length := by omega
                              c0_hstraight!
                              let mword := if (usz - 1#32).ule 64#32 then usz - 1#32
                                else (3#32 <<< 28) ||| (usz - 1#32)
                              have hmok := andExtract_mword_ok husz3 (Nat.le_trans husz_maxA hmaxA)
                              refine wp_join_group (fun xsm mm => xsm.fst = mword ∧
                                  ∃ scrm : List (BitVec 32), scrm.length = c.scratch_cap ∧
                                    (∀ idx, idx < g_cur.toNat → scrm[idx]? = scr2[idx]?) ∧
                                    scrm[g_cur.toNat]? = some csel ∧ aeMem c s lmw scrm R mm) ?_ ?_
                              · rintro _ ⟨mw_val, ⟨⟩⟩ mm ⟨hmw_eq, scrm, hs_len, hs_pre, hs_g0, hmm⟩
                                dsimp only [Blocks.get, Member.here]; subst hmw_eq
                                have hg_scr1 : (g_cur + 1#64).toNat < scrm.length := by bv_omega
                                c0_hstraight!
                                have hs1 := andExtract_mword_scrm1 (mword := mword) hs_len hs_pre
                                  hs_g0 hg_scr1 (by bv_omega)
                                refine wp_loop_group (fun n5 (xs5 : Tup Val [i32, i32]) m5 =>
                                    n5 = usz.toNat - xs5.snd.fst.toNat ∧
                                    aeGateWriteInv c s usz.toNat isel.toNat g_cur csel mword scr2
                                      lmw R xs5.fst xs5.snd.fst m5) ?_ ?_
                                · rintro L5 n5 ⟨oi, k5, ⟨⟩⟩ m5 hL5 ⟨rfl, hk5_le, hoi, scrk, hscrk,
                                      hpk, hgk0, hgk1, hk_has, hk_mem, hm5⟩
                                  dsimp only [Blocks.get, Member.here]
                                  dsimp only at hk5_le hoi hpk hk_has hk_mem
                                  c0_hstraight!; c0_hsplit
                                  · have hk5_lt := hc; clear hc
                                    have hk5_nat : k5.toNat < usz.toNat := by bv_omega
                                    refine wp_join_group (fun xso mo => aeGateWriteBody c s
                                      isel.toNat g_cur csel mword scr2 lmw R xso.fst (k5.toNat + 1)
                                      mo) ?_ ?_
                                    · rintro _ ⟨oi', ⟨⟩⟩ mo
                                        ⟨hoi', scrk', hs1, hs2, hs3, hs4, hs5, hs6, hmo⟩
                                      dsimp only [Blocks.get, Member.here] at *; c0_hstraight!
                                      have hk5n : (k5 + 1#32).toNat = k5.toNat + 1 := by bv_omega
                                      exact hL5 (usz.toNat - (k5 + 1#32).toNat) (oi', k5 + 1#32, ())
                                        mo (by bv_omega) ⟨rfl, by bv_omega,
                                          by dsimp only; rwa [hk5n], scrk', hs1, hs2, hs3, hs4,
                                          by dsimp only; rwa [hk5n], by dsimp only; rwa [hk5n], hmo⟩
                                    · intro Jo hJo; c0_hstraight!; c0_hsplit
                                      · have hne_isel := hc; clear hc
                                        have hne_nat : k5.toNat ≠ isel.toNat :=
                                          fun h => hne_isel (BitVec.eq_of_toNat_eq h)
                                        have hz_oi := bv_zext32_toNat oi
                                        have hz_k5 := bv_zext32_toNat k5
                                        have hoi_lt : oi.toNat < usz.toNat - 1 := by
                                          rw [hoi]; split <;> omega
                                        obtain ⟨hidx_scr, hk5_ws2, hidx_eq⟩ := ae_gw g_cur oi k5
                                          scrk.length s.scratch.work_stk2.length
                                          (by omega) (hscrk ▸ hscr_u30) (by omega)
                                        c0_hstraight!
                                        have hstep := andExtract_gateLoop_write_step hk5_nat
                                          hisel_lt (by omega) hne_nat hoi hscrk (by omega)
                                          (by omega) hpk hgk0 hgk1 hk_has hk_mem hidx_eq
                                        exact hJo (oi + 1#32, ())
                                          _ ⟨hstep.1, _, hstep.2.1, hstep.2.2.1,
                                            hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2.1,
                                            hstep.2.2.2.2.2.2, by assumption⟩
                                      · have heq_isel := hc; clear hc; c0_hstraight!
                                        have hk5_is : k5.toNat = isel.toNat := by bv_omega
                                        exact hJo (oi, ())
                                          _ ⟨by rw [hoi]; split <;> split <;> omega, scrk, hscrk,
                                            hpk, hgk0, hgk1,
                                            fun j hj1 hj2 => hk_has j (by omega) hj2,
                                            fun t ht => match hk_mem t ht with
                                              | ⟨j, hj1, hj2, hsq⟩ => ⟨j, by omega, hj2, hsq⟩, hm5⟩
                                  · have hk5_dn := hc; clear hc
                                    have hk5_eq : k5.toNat = usz.toNat := by bv_omega
                                    have hdone := andExtract_gateLoop_done hisel_lt husz3 husz_maxA
                                      husz_cv hg_c1 hg_room_nat hg_cap hscrk hws2_lt hisel_cv hent
                                      hall_m2 hmok.1 hmok.2 hpre2 hseq2 hpk hgk0 hgk1 hk5_eq hoi
                                      hk_has hk_mem; c0_hstraight!
                                    exact hJg (g_cur + 2#64 + BitVec.setWidth 64 (usz - 1#32), ()) _
                                      ⟨hdone.1, hdone.2.1, scrk, hscrk, hdone.2.2.1, hdone.2.2.2,
                                        hm5⟩
                                · intro J5 hJ5; c0_hstraight!; exact hJ5 usz.toNat (0#32, 0#32, ())
                                    _ ⟨rfl, Nat.zero_le _, by split <;> rfl, _, hs1.1, hs1.2.1,
                                      hs1.2.2.1, hs1.2.2.2, fun _ h => absurd h (Nat.not_lt_zero _),
                                      fun _ h => absurd h (Nat.not_lt_zero _), by assumption⟩
                              · intro Jm hJm
                                have hm_p := andExtract_mword_pre (csel := csel) hscr2 hg_scr0
                                c0_hstraight!; c0_hsplit
                                · have hule := hc; clear hc; c0_hstraight!
                                  exact hJm (usz - 1#32, ()) _
                                    ⟨ae_mword_le usz (by bv_omega),
                                      _, hm_p.1, hm_p.2.1, hm_p.2.2, by assumption⟩
                                · have hule := hc; clear hc; c0_hstraight!
                                  exact hJm ((3#32 <<< 28) ||| (usz - 1#32), ()) _
                                    ⟨ae_mword_gt usz (by bv_omega),
                                      _, hm_p.1, hm_p.2.1, hm_p.2.2, by assumption⟩
                            · clear hc; c0_hstraight!; exact hJg (g_cur, ()) _
                                ⟨hg_c1, hg_c2, scr2, hscr2, hpre2, hseq2, hmw⟩
                        · intro Jw hJw; c0_hstraight!
                          refine wp_loop_group (fun nw (xsw : Tup Val [i64, i64, i32]) mw =>
                              nw = wend64.toNat - xsw.snd.fst.toNat ∧ off64.toNat ≤
                                xsw.snd.fst.toNat ∧ aeScanOuterInv c F_cur s usz.toNat isel.toNat
                                  lhs scr2 R wend64 xsw.snd.fst xsw.snd.snd.fst mw) ?_ ?_
                          · rintro Lw nw ⟨tkw, w_idx, mcnt, ⟨⟩⟩ mw hLw
                              ⟨rfl, hw_ge, hw_le, hslice, lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                            dsimp only [Blocks.get, Member.here]
                            dsimp only at hw_ge hw_le hslice hcntw; c0_hstraight!; c0_hsplit
                            · have hw_lt : w_idx.toNat < wend64.toNat :=
                                andExtract_wend_lt hisel_cv hlhs_w0 hlhs_w1 hc
                              clear hc; have hw_cap : wend64.toNat ≤ c.wcap := hwend_bd
                              c0_hstraight!; c0_hsplit
                              · clear hc
                                have hrem_pos : 0 < wend64.toNat - w_idx.toNat := by omega
                                obtain ⟨w0, hw0_some, hw0_cases⟩ := slice_pop_step hslice hrem_pos
                                have hw_wstk : w_idx.toNat < s.core.wstk.length := by omega
                                have hw0_eq : s.core.wstk[w_idx.toNat]'hw_wstk = w0 :=
                                  Option.some.inj (by
                                    rw [← List.getElem?_eq_getElem]; exact hw0_some)
                                c0_hstraight!
                                refine wp_join_group (fun xsv mv => w_idx.toNat < xsv.fst.toNat ∧
                                    aeScanOuterInv c F_cur s usz.toNat isel.toNat lhs scr2 R wend64
                                      xsv.fst xsv.snd.fst mv) ?_ ?_
                                · rintro _ ⟨w_nx, mcnt_nx, ⟨⟩⟩ mv
                                    ⟨hwn_gt, hwn_le, hsn, lmv, hlmv, hinvv, hcntv, hentv, hmv⟩
                                  dsimp only [Blocks.get, Member.here]; c0_hstraight!
                                  dsimp only at hLw hw_ge hw_le hwn_gt hwn_le ⊢
                                  exact hLw (wend64.toNat - w_nx.toNat) (tkw + 1#64, w_nx, mcnt_nx,
                                    ()) mv (by omega) ⟨rfl, by dsimp only; omega, hwn_le, hsn,
                                      lmv, hlmv, hinvv, hcntv, hentv, hmv⟩
                                · intro Jv hJv; c0_hstraight!; c0_hsplit
                                  · have hbin := hc; clear hc
                                    rcases hw0_cases with ⟨_, hent_bin, hslice_nx⟩ | ⟨hzero, _⟩
                                    · rw [hw0_eq]
                                      refine wp_join_group (fun xsm mm => ∃ lmv, aeScanInv c F_cur s
                                          usz.toNat isel.toNat lhs scr2 R xsm.fst lmv mm) ?_ ?_
                                      · rintro _ ⟨mcnt_nx, ⟨⟩⟩ mm
                                          ⟨lmv, hlmv, hinvv, hcntv, hentv, hmm⟩
                                        dsimp only [Blocks.get, Member.here]
                                        have hst := andExtract_watch_step (w_nx := w_idx + 1#64)
                                          (d := 1) Nat.zero_lt_one (by bv_omega) (by bv_omega)
                                          hslice_nx
                                        exact hJv (w_idx + 1#64, mcnt_nx, ()) mm ⟨hst.1, hst.2.1,
                                          hst.2.2, lmv, hlmv, hinvv, hcntv, hentv, hmm⟩
                                      · intro Jm hJm; c0_hstraight!; c0_hsplit
                                        · dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val] at hc
                                          have hot_lt_nat : (w0 &&& 2147483647#32).toNat <
                                              2 * s.core.cur_vars := by bv_omega
                                          clear hc; c0_hstraight!; c0_hsplit
                                          · have hot_ne := hc; clear hc
                                            let other := w0 &&& 2147483647#32
                                            have hot_lm : (BitVec.setWidth 64 other).toNat <
                                                lmw.length := by
                                              rw [bv_zext32_toNat, hlmw]; dsimp only [other]; omega
                                            c0_hstraight!; c0_hsplit
                                            · have hmk3 := hc; clear hc; c0_hstraight!
                                              have hlhs_eq : lhs =
                                                (s.scratch.work_stk2[isel.toNat]?.getD 0#32)
                                                  ^^^ 1#32 := by
                                                simp [lhs, csel, List.getElem?_eq_getElem hisel_cv]
                                              have hmk3' : lmw[(BitVec.setWidth 64 other).toNat]'
                                                  hot_lm &&& 3#8 = 1#8 := by
                                                dsimp only [LeanQbe.T.lift2,
                                                  LeanQbe.T.Arg.val] at hmk3 ⊢
                                                simp only [bv_zext32_toNat]
                                                exact ae_trunc8_mask3 _ hmk3
                                              have hnxt := andExtract_scan_join_step hisel_lt
                                                hws2_nd hlmw hinvw hcntw hlhs_eq husz_u31
                                                (Nat.lt_of_lt_of_le hot_lt_nat
                                                  (Nat.mul_le_mul_left 2 hcv_le)) hot_ne hot_lm
                                                hmk3' hent_bin hentw (by
                                                  try dsimp only [other] at *
                                                  dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val] at
                                                    *
                                                  simp only [bv_zext32_toNat, ae_trunc8_or2] at *
                                                  assumption)
                                              exact hJm (mcnt + 1#32, ()) _ hnxt
                                            · clear hc; c0_hstraight!; exact hJm (mcnt, ()) mw
                                                ⟨lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                                          · clear hc; c0_hstraight!; exact hJm (mcnt, ()) mw
                                              ⟨lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                                        · clear hc; c0_hstraight!; exact hJm (mcnt, ()) mw
                                            ⟨lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                                    · rw [hw0_eq] at hbin; exact absurd hzero (by simpa using hbin)
                                  · have hnonbin := hc; clear hc
                                    rcases hw0_cases with
                                      ⟨hne0, _⟩ | ⟨_, hrem2, cr, _, _, hslice_nx⟩
                                    · rw [hw0_eq] at hnonbin
                                      exact absurd (by simpa using hnonbin) hne0
                                    · c0_hstraight!; c0_hsplit
                                      · exact False.elim (andExtract_wend_uge_false hisel_cv
                                          hlhs_w0 hlhs_w1 hwend_bd c.hwcap hrem2 hc)
                                      · clear hc; c0_hstraight!
                                        have hst := andExtract_watch_step
                                          (w_nx := w_idx + 1#64 + 1#64) (d := 2) (by decide)
                                          (by bv_omega) (by bv_omega) hslice_nx
                                        exact hJv (w_idx + 1#64 + 1#64, mcnt, ()) mw ⟨hst.1,
                                          hst.2.1, hst.2.2, lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                              · clear hc; c0_hstraight!; exact hJw (tkw, w_idx, mcnt, ()) mw
                                  ⟨lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                            · clear hc; c0_hstraight!; exact hJw (tkw, w_idx, mcnt, ()) mw
                                ⟨lmw, hlmw, hinvw, hcntw, hentw, hmw⟩
                          · intro L0 hL0; c0_hstraight!
                            have hinit := andExtract_scan_init_ok (F_cur := F_cur)
                              (isel := isel.toNat) hws2_lt hcv_le hb2_2 lhs
                            exact hL0 (wend64.toNat - off64.toNat) (ticks, off64, 0#32, ()) ms
                              ⟨rfl, Nat.le_refl _, hw_ok.1, hw_ok.2.2, lm2, hlm2, hinv2, hinit.1,
                                hinit.2, hm2⟩
                      · clear hc; c0_hstraight!; exact hJ3 (g_cur, _dead, ticks, ()) ms
                          ⟨lm2, scr2, hg_c1, hg_c2, hlm2, hscr2, hpre2, hseq2, hinv2, hb2_2, hm2⟩
                  · intro Js hJs; c0_hstraight!; c0_hsplit
                    · clear hc; c0_hstraight!; exact hJs (bi, ()) m2 ⟨hbi_nat, rfl⟩
                    · have hi_ne0 := hc; clear hc; c0_hstraight!
                      refine wp_join_group (fun xss ms => xss.fst.toNat < usz.toNat ∧ ms = m2)
                        (fun _ ⟨x, ⟨⟩⟩ ms hx =>
                          by dsimp only [Blocks.get, Member.here]; exact hJs (x, ()) ms hx)
                        (fun Jss hJss => by
                          c0_hstraight!; c0_hsplit
                          · have hi_nz := hc; clear hc; c0_hstraight!
                            exact hJss (i - 1#32, ()) m2 ⟨by bv_omega, rfl⟩
                          · clear hc; c0_hstraight!; exact hJss (i, ()) m2 ⟨hi_nat, rfl⟩)
                · clear hc; c0_hstraight!; exact hJp (g_cur, _dead, ticks, ()) m2
                    ⟨hg_c1, hg_c2, lm2, scr2, hlm2, hscr2, hpre2, hseq2, hinv2, hm2⟩
              · clear hc; c0_hstraight!; exact hJp (g_cur, _dead, ticks, ()) m2
                  ⟨hg_c1, hg_c2, lm2, scr2, hlm2, hscr2, hpre2, hseq2, hinv2, hm2⟩
            · clear hc; c0_hstraight!; exact hJp (g_cur, _dead, ticks, ()) m2
                ⟨hg_c1, hg_c2, lm2, scr2, hlm2, hscr2, hpre2, hseq2, hinv2, hm2⟩
          · intro J2 hJ2; c0_hstraight!; exact hJ2 usz.toNat (g_len, usz, s.scratch.res_sz,
              0#32, ()) m1 ⟨rfl, Nat.zero_le _, lm1, s.scratch.scratch_buf, Nat.le_refl _, hg_le,
                hlm1, hsl, fun _ _ => rfl, hseq, hinv1, hb2_1, hm1⟩
        · clear hc; c0_hstraight!; exact hJp (g_len, usz, s.scratch.res_sz, ()) m1 ⟨Nat.le_refl _,
            hg_le, lm1, s.scratch.scratch_buf, hlm1, hsl, fun _ _ => rfl, hseq, hinv1, hm1⟩
  · intro J1 hJ1; c0_hstraight!; exact hJ1 usz.toNat (usz, 4294967295#32, 0#32, ()) m0
      ⟨rfl, Nat.zero_le _, Or.inr rfl, s.core.lit_mark, hlml, hnot_inv0.1, hnot_inv0.2, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence

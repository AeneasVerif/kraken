/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0
public import LeanQbe.T.Examples.Kissat.FullM8FidV12
import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2c
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 9 Proofs — Congruence (`FullFidelityStep9ProofProbe1`)

M1-clean UNSAT-only parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]`,
`0` `import all`, `std3`, `XPost`-polymorphic) for Step 9 `full_congruence_dense`:
clears `h->tarjan_mark[0..cv)` before calling `full_cong_find_units_equivs(h)` (`S9-P0.2`) and
satisfies `FullM3CongBva.m3CongruenceDenseSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva (m3CongruenceDenseSpec)
open LeanQbe.T.Examples.Kissat.FullM6CongSubst (m6CongExtractBinariesSpec m6CongFindUnitsEquivsSpec
  m6CongFwdSubsumeSpec m6_fullDenseInvW_with_repr bv64_add1_lt)
open LeanQbe.T.Examples.Kissat.FullFidelityCong (FidGateSeqOk FidCongHtInv fidCongHashMaxSz
  fidCongExtractSpec fidCongExtractIteAllSpec fidCongWorklistSpec)
open LeanQbe.T.Examples.Kissat.FullM8FidV12 (M8CtrlLayout)
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

section CongDenseStep9

private theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) : ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ule_true_le {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem bv64_ule_false_lt {a b : BitVec 64} (h : a.ule b = false) : b.toNat < a.toNat := by
  simpa [BitVec.ule] using h

private theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem bv64_setWidth32_eq {x : BitVec 64} {n : Nat} (hx : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  subst hx; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem fid9_denseInvW_with_antsz_ressz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩, hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid9_denseInvW_with_tmk_ar {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch :=
        { s.scratch with tarjan_mark := tmk', ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with tarjan_mark_len := ht }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid9_denseInvW_with_scr_res0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hsl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := 0#64 } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hsl }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid9_cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * 268435456)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem fid9_cd_ht_max_step {ht_max : BitVec 64} {k free_scr : Nat}
    (hk : k ≤ 14) (heq : ht_max.toNat = 64 * 2 ^ k)
    (hlt : ht_max.toNat < 1048576) (hmul : ht_max.toNat * 4 ≤ free_scr) :
    k + 1 ≤ 14 ∧ (ht_max <<< 1#64).toNat = 64 * 2 ^ (k + 1) ∧
    (ht_max <<< 1#64).toNat ≤ 1048576 ∧ (ht_max <<< 1#64).toNat * 2 ≤ free_scr := by
  have hk_lt : k < 14 :=
    Nat.lt_of_le_of_ne hk fun h => by subst h; rw [heq] at hlt; simp at hlt
  have h2k_le : 2 ^ k ≤ 8192 := Nat.pow_le_pow_right (by decide) (by omega : k ≤ 13)
  have hshl : (ht_max <<< 1#64).toNat = 2 * ht_max.toNat := by
    rw [show (ht_max <<< 1#64 : BitVec 64) = ht_max <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpow : 64 * 2 ^ (k + 1) = 2 * (64 * 2 ^ k) := by rw [Nat.pow_succ]; omega
  refine ⟨by omega, by rw [hshl, heq, hpow], by rw [hshl, heq]; omega, by rw [hshl]; omega⟩

private theorem fid9_cd_layout_params {g_len ht_max ht_off rem_occ cap : Nat}
    (hht_lo : 64 ≤ ht_max) (hht_hi : ht_max ≤ 1048576)
    (hmul2 : ht_max * 2 ≤ cap - g_len) (hg_le : g_len ≤ cap) (hcap : cap < 2 ^ 28)
    (hho : ht_off = cap - ht_max) (hrem : rem_occ = ht_off - g_len) :
    let occ_bkt :=
      if 262144 ≤ rem_occ then 8192
      else if 65536 ≤ rem_occ then 2048
      else if 16384 ≤ rem_occ then 512
      else if 2048 ≤ rem_occ then 256
      else if 256 ≤ rem_occ then 32 else 16
    let bkt_off := ht_off - occ_bkt
    let inq_off := bkt_off - occ_bkt
    let q_off := inq_off - occ_bkt
    let ctrl_off := q_off - 8
    0 < occ_bkt ∧ occ_bkt ≤ 8192 ∧
    (∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) ∧
    occ_bkt * 3 + 8 ≤ rem_occ ∧ g_len ≤ ctrl_off ∧
    ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
    inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
    ctrl_off < cap ∧ ctrl_off + 8 ≤ cap ∧ ht_off + ht_max ≤ cap := by
  intro occ_bkt bkt_off inq_off q_off ctrl_off
  have hrem_ge : 64 ≤ rem_occ := by omega
  have hpow : 0 < occ_bkt ∧ occ_bkt ≤ 8192 ∧
      (∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) ∧ occ_bkt * 3 + 8 ≤ rem_occ := by
    dsimp only [occ_bkt]
    split
    · exact ⟨by decide, by decide, ⟨13, by decide, by decide, rfl⟩, by omega⟩
    · split
      · exact ⟨by decide, by decide, ⟨11, by decide, by decide, rfl⟩, by omega⟩
      · split
        · exact ⟨by decide, by decide, ⟨9, by decide, by decide, rfl⟩, by omega⟩
        · split
          · exact ⟨by decide, by decide, ⟨8, by decide, by decide, rfl⟩, by omega⟩
          · split
            · exact ⟨by decide, by decide, ⟨5, by decide, by decide, rfl⟩, by omega⟩
            · exact ⟨by decide, by decide, ⟨4, by decide, by decide, rfl⟩, by omega⟩
  refine ⟨hpow.1, hpow.2.1, hpow.2.2.1, hpow.2.2.2, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

private theorem fid9_cd_ctrl_off_toNat {cap : Nat} {ht_max occ : BitVec 64}
    (hht : ht_max.toNat ≤ cap) (h38 : occ.toNat * 3 + 8 ≤ cap - ht_max.toNat)
    (hcap : cap < 2 ^ 28) :
    (BitVec.ofNat 64 cap - ht_max - occ - occ - occ - 8#64).toNat =
      cap - ht_max.toNat - occ.toNat - occ.toNat - occ.toNat - 8 := by
  have hsc : (BitVec.ofNat 64 cap).toNat = cap := bv64_ofNat_toNat_lt (by omega)
  have h1 : (BitVec.ofNat 64 cap - ht_max).toNat = cap - ht_max.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsc]; exact hht)), hsc]
  have h2 : (BitVec.ofNat 64 cap - ht_max - occ).toNat = cap - ht_max.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; omega)), h1]
  have h3 : (BitVec.ofNat 64 cap - ht_max - occ - occ).toNat =
      cap - ht_max.toNat - occ.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h2]; omega)), h2]
  have h4 : (BitVec.ofNat 64 cap - ht_max - occ - occ - occ).toNat =
      cap - ht_max.toNat - occ.toNat - occ.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h3]; omega)), h3]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
    rw [h4, show (8#64 : BitVec 64).toNat = 8 from rfl]; omega)), h4]; rfl

private theorem fid9_cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
    (hg_le : g_len ≤ ht_off) (hinv1 : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinv2 : ∀ k < i, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_len : ht_off + i < scri.length) :
    (∀ idx < g_len, (scri.set (ht_off + i) 0xFFFFFFFF#32)[idx]? = scr0[idx]?) ∧
    (∀ k < i + 1,
      (scri.set (ht_off + i) 0xFFFFFFFF#32)[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
  refine ⟨fun idx hidx => by rw [List.getElem?_set_ne (by omega)]; exact hinv1 idx hidx,
    fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki; rw [List.getElem?_set_self hi_len, Option.getD_some]
  · rw [List.getElem?_set_ne (by omega)]; exact hinv2 k (by omega)

private theorem fid9_cd_ctrl_store_layout {c : FullCfg} {F_cur : List (List Nat)} {cv0 : Nat}
    {scr0 scri : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hg_co : g_len ≤ ctrl_off) (hg_24 : g_len ≤ 0x01000000)
    (ho_pos : 0 < occ_bkt) (ho_8192 : occ_bkt ≤ 8192)
    (hopow : ∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) (hht_pos : 0 < ht_sz)
    (hc_cap : ctrl_off < c.scratch_cap) (hc8 : ctrl_off + 8 ≤ c.scratch_cap)
    (hcq : ctrl_off + 8 ≤ q_off) (hqi : q_off + occ_bkt ≤ inq_off)
    (hib : inq_off + occ_bkt ≤ bkt_off) (hbh : bkt_off + occ_bkt ≤ ht_off)
    (hhc : ht_off + ht_sz ≤ c.scratch_cap) (hscrl : scri.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv0 scr0 scri g_len ht_off ht_sz) :
    let scr' := (((((((scri.set ctrl_off (BitVec.ofNat 32 occ_bkt)).set
      (ctrl_off + 1) (BitVec.ofNat 32 bkt_off)).set
      (ctrl_off + 2) (BitVec.ofNat 32 inq_off)).set
      (ctrl_off + 3) (BitVec.ofNat 32 q_off)).set
      (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32).set
      (ctrl_off + 6) (BitVec.ofNat 32 ht_off)).set (ctrl_off + 7) (BitVec.ofNat 32 ht_sz)
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv0 scr0 scr' g_len ht_off ht_sz := by
  intro scr'
  have hsl : scr'.length = c.scratch_cap := by dsimp only [scr']; simp [hscrl]
  have hhold_out : ∀ idx, idx < ctrl_off ∨ ctrl_off + 8 ≤ idx → scr'[idx]? = scri[idx]? := by
    intro idx hidx; dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
  have hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]? := fun idx hidx =>
    (hhold_out idx (Or.inl (by omega))).trans (hpref idx hidx)
  have hht' : FidCongHtInv 64 F_cur cv0 scr0 scr' g_len ht_off ht_sz := fun k hk => by
    dsimp only; rw [hhold_out (ht_off + k) (Or.inr (by omega))]; exact hht k hk
  have hg : ∀ j, j < 8 → scr'[ctrl_off + j]? =
      ([BitVec.ofNat 32 occ_bkt, BitVec.ofNat 32 bkt_off, BitVec.ofNat 32 inq_off,
        BitVec.ofNat 32 q_off, 0#32, 0#32, BitVec.ofNat 32 ht_off,
        BitVec.ofNat 32 ht_sz])[j]? := by
    intro j _; dsimp only [scr']
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (repeat rw [List.getElem?_set_ne (by omega)]) <;>
      (try rw [Nat.add_zero]) <;>
      rw [List.getElem?_set_self (by simp [hscrl]; omega)] <;> rfl
  have hs0 : scr'[ctrl_off]?.getD 0#32 = BitVec.ofNat 32 occ_bkt := by
    have h0 := hg 0 (by decide); rw [Nat.add_zero] at h0; exact congrArg (Option.getD · 0#32) h0
  have h5 := hg 5 (by decide)
  have h5' : scr'[ctrl_off + 5]?.getD 0#32 = 0#32 := congrArg (Option.getD · 0#32) h5
  exact ⟨hsl,
    ⟨hc_cap, hc8, hg_co, hg_24, hs0,
     congrArg (Option.getD · 0#32) (hg 1 (by decide)),
     congrArg (Option.getD · 0#32) (hg 2 (by decide)),
     congrArg (Option.getD · 0#32) (hg 3 (by decide)),
     congrArg (Option.getD · 0#32) (hg 6 (by decide)),
     congrArg (Option.getD · 0#32) (hg 7 (by decide)),
     ho_pos, ho_8192, hopow, hht_pos, hcq, hqi, hib, hbh, hhc,
     by have := hg 4 (by decide); rw [this]; simpa using ho_pos,
     by rw [h5]; exact Nat.zero_le _,
     fun k hk => by rw [h5', show (0#32 : BitVec 32).toNat = 0 from rfl] at hk; omega⟩,
    hpref', hht'⟩

/-- Parametric `Func.wp` proof for `fidStep9CongruenceDenseFn` (`full_congruence_dense`)
against `FullM3CongBva.m3CongruenceDenseSpec`. -/
theorem full_congruence_dense_step9_wp (Γ : Env)
    (hExtBins : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, fidCongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hExtIteAll : ∀ a m Q X, fidCongExtractIteAllSpec a m Q X →
      Γ "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X)
    (hWorklist : ∀ a m Q X, fidCongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ fidStep9CongruenceDenseFn.body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, hm0, hQ⟩
  have hsc : c.scratch_cap < 2 ^ 28 := Nat.lt_of_lt_of_le c.hscr (by decide)
  have hmx : c.max_vars < 2 * 268435456 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
  obtain ⟨hlen0, ⟨F_cur, hw0⟩⟩ := hden0.1
  have hdw0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hlen0, hw0, hden0.2.1, hden0.2.2.1, hden0.2.2.2.1, hden0.2.2.2.2.1, hden0.2.2.2.2.2⟩
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have hcv_le : cv0 ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  unfold Func.wp
  rw [show fidStep9CongruenceDenseFn.body = full_congruence_dense_body from rfl]
  unfold full_congruence_dense_body
  m6b_split
  · m6b_steps; exact hQ 1#64 s0 m0 hden0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have h256 : 256 ≤ c.scratch_cap := by
      have := bv64_ult_not_lt hc
      rw [show (256 : BitVec 64).toNat = 256 from rfl, bv64_ofNat_toNat_lt (by omega)] at this
      omega
    clear hc; m6b_split
    · m6b_steps; exact hQ 1#64 s0 m0 hden0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
    · clear hc; m6b_steps
      let s0a : FullState := { s0 with scratch := { s0.scratch with ant_sz := 0#64 } }
      have hdw0a : FullDenseInvW c F0 F_cur s0a :=
        fid9_denseInvW_with_antsz_ressz hdw0 0#64 s0.scratch.res_sz
      m6b_call hExtBins
      refine ⟨c, F0, F_cur, s0a, R, rfl, hdw0a, hm,
        fun r1 s1 m1 hdw1 hcv1 hfl1 _hr1_dom hr1_uns hm1 => ?_⟩
      have hcv10 : s1.core.cur_vars = cv0 := hcv1
      m6b_split
      · m6b_steps
        exact hQ 20#64 _ m (fid9_denseInvW_with_antsz_ressz hdw1 0#64 s1.scratch.res_sz).toDense
          hcv1 hfl1 (Or.inr rfl) (fun _ => hr1_uns (beq_iff_eq.mp hc)) hm
      · clear hc
        have hcv1_lt : cv0 < 2 ^ 32 := by omega
        have h2cv1_64 : 2 * cv0 < 2 ^ 64 := by omega
        m6b_to_group
        refine wp_loop_inv (ts := [i64])
          (fun (i, ()) mi => ∃ repri : List (BitVec 32),
            repri.length = 2 * c.max_vars ∧ i.toNat ≤ 2 * cv0 ∧
            (∀ k < i.toNat, repri[k]? = some (BitVec.ofNat 32 k)) ∧
            (FullMem c { s1 with core := { s1.core with repr := repri } } ⋆ R) mi)
          (fun (i, ()) _ => 2 * cv0 - i.toNat)
          (fun Ji hJi => by
            m6b_let
            exact hJi (0#64, ()) m1
              ⟨s1.core.repr, hdw1.1.core_ok.repr_len, Nat.zero_le _,
               fun _ h => by simp at h, hm1⟩)
          (fun Ji (i, ()) mi ⟨repri, hrl, hi_le, hinit, hmi⟩ ihi => ?_)
        m6b_split
        · have hi_lt : i.toNat < 2 * cv0 := by
            have h := bv64_ult_lt hc; rw [hcv10] at h
            change i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at h
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
              bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h2cv1_64] at h; exact h
          have hi1_n : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
          have hi_arr : i.toNat < repri.length := by omega
          have hi_tr : i.setWidth 32 = BitVec.ofNat 32 i.toNat := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          clear hc; m6b_steps
          exact ihi (i + 1#64, ()) m (by dsimp only; omega)
            ⟨repri.set i.toNat (i.setWidth 32), by simp [hrl], by rw [hi1_n]; omega,
             fun k hk => by
               rw [hi1_n] at hk
               by_cases hki : k = i.toNat
               · subst hki; rw [List.getElem?_set_self hi_arr, hi_tr]
               · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit k (by omega),
             hm⟩
        · have hi_eq : i.toNat = 2 * cv0 := by
            have h := bv64_ult_not_lt hc; rw [hcv10] at h
            change ¬ i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at h
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
              bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h2cv1_64] at h; omega
          rw [hi_eq] at hinit
          clear hc; m6b_to_group
          refine wp_loop_inv (ts := [i64])
            (fun (it0, ()) mt0 => ∃ tmk0 : List (BitVec 32),
              tmk0.length = 2 * c.max_vars ∧ it0.toNat ≤ cv0 ∧
              (FullMem c { s1 with core := { s1.core with repr := repri }
                                   scratch := { s1.scratch with tarjan_mark := tmk0 } } ⋆ R) mt0)
            (fun (it0, ()) _ => cv0 - it0.toNat)
            (fun Jt0 hJt0 => by
              m6b_let
              exact hJt0 (0#64, ()) mi
                ⟨s1.scratch.tarjan_mark, hdw1.1.scratch_ok.tarjan_mark_len, Nat.zero_le _, hmi⟩)
            (fun Jt0 (it0, ()) mt0 ⟨tmk0, htlt0, hit0_le, hmt0⟩ iht0 => ?_)
          m6b_split
          · have hit0_lt : it0.toNat < cv0 := by
              have h := bv64_ult_lt hc; rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
            have hit0_1 : (it0 + 1#64).toNat = it0.toNat + 1 := bv64_add1_lt (by omega)
            have hit0_arr : it0.toNat < tmk0.length := by omega
            clear hc; m6b_steps
            exact iht0 (it0 + 1#64, ()) m (by dsimp only; omega)
              ⟨tmk0.set it0.toNat 0#32, by simp [htlt0], by rw [hit0_1]; omega, hm⟩
          · clear hc
            let s2 : FullState :=
              { s1 with core := { s1.core with repr := repri }
                        scratch := { s1.scratch with tarjan_mark := tmk0 } }
            have hdw2 := fid9_denseInvW_with_tmk_ar (m6_fullDenseInvW_with_repr hdw1 hrl) htlt0
              s1.scratch.ant_sz s1.scratch.res_sz
            have hrepr2 : FullCongReprInv F_cur (2 * s2.core.cur_vars) s2.core.repr := by
              rw [show s2.core.cur_vars = cv0 from hcv1]
              exact fid9_cd_repr_init_inv hrl hcv_le hmx hinit
            m6b_steps; m6b_call hFindUE
            refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, hrepr2, hmt0,
              fun r2 s3 m3 hdw3 hcv3 hfl3 hrepr3 _hr2_dom hr2_uns hm3 => ?_⟩
            have hcv30 : s3.core.cur_vars = cv0 := hcv3.trans hcv1
            have hfl30 : s3.core.fuel = fuel0 := hfl3.trans hfl1
            m6b_split
            · m6b_to_group
              refine wp_loop_inv (ts := [i64])
                (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                  tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                  (FullMem c { s3 with scratch := { s3.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                (fun (it, ()) _ => cv0 - it.toNat)
                (fun Jt hJt => by
                  m6b_let; exact hJt (0#64, ()) m3
                    ⟨s3.scratch.tarjan_mark, hdw3.1.scratch_ok.tarjan_mark_len, Nat.zero_le _, hm3⟩)
                (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
              m6b_split
              · have hit_lt : it.toNat < cv0 := by
                  have h := bv64_ult_lt hc; rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                have hit_arr : it.toNat < tmkt.length := by omega
                clear hc; m6b_steps
                exact iht (it + 1#64, ()) m (by dsimp only; omega)
                  ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
              · clear hc; m6b_steps
                exact hQ 20#64 _ m (fid9_denseInvW_with_tmk_ar hdw3 htlt 0#64 0#64).toDense
                  hcv30 hfl30 (Or.inr rfl) (fun _ => hr2_uns (beq_iff_eq.mp hc)) hm
            · clear hc
              have hhalf : (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat =
                  c.scratch_cap / 2 := by
                rw [BitVec.toNat_ushiftRight, bv64_ofNat_toNat_lt (by omega),
                  Nat.shiftRight_eq_div_pow]
              m6b_to_group
              refine wp_join_group (ts := [i64])
                (fun (g_cap, ()) mg => mg = m3 ∧
                  g_cap.toNat ≤ c.scratch_cap / 2 ∧ g_cap.toNat ≤ 0x00FFFFFF)
                ?_
                (fun Jgc hJgc => by
                  m6b_split
                  · have hlt := bv64_ult_lt hc
                    rw [show (0x00FFFFFF : BitVec 64).toNat = 0x00FFFFFF from rfl] at hlt
                    change 0x00FFFFFF < (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat at hlt
                    rw [hhalf] at hlt; m6b_steps
                    exact hJgc (0x00FFFFFF#64, ()) m3 ⟨rfl, by
                      rw [show (0x00FFFFFF#64 : BitVec 64).toNat = 0x00FFFFFF from rfl]; omega,
                      by decide⟩
                  · have hnot := bv64_ult_not_lt hc
                    rw [show (0x00FFFFFF : BitVec 64).toNat = 0x00FFFFFF from rfl] at hnot
                    change ¬ 0x00FFFFFF <
                      (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat at hnot
                    m6b_let
                    exact hJgc (_, ()) m3 ⟨rfl, by rw [hhalf]; exact Nat.le_refl _,
                      by rw [hhalf] at hnot ⊢; omega⟩)
              rintro _ ⟨g_cap, ⟨⟩⟩ mg ⟨hmg, hgc_half, hgc_24⟩
              m6b_steps; m6b_call hExtract
              refine ⟨c, F0, F_cur, s3, R, rfl, hdw3, by omega, hmg ▸ hm3,
                fun g_len0 s4a m4a hdw4a hcv4a hfl4a hrepr4a _hinc4a hgl0_le hseq4a hm4a => ?_⟩
              have hcv4a0 : s4a.core.cur_vars = cv0 := hcv4a.trans hcv30
              have hfl4a0 : s4a.core.fuel = fuel0 := hfl4a.trans hfl30
              have hrepr4a_inv : FullCongReprInv F_cur (2 * cv0) s4a.core.repr := by
                rw [hrepr4a, ← hcv30]; exact hrepr3
              m6b_to_group
              refine wp_join_group (ts := [i64])
                (fun (g_len, ()) m4 => ∃ s4 : FullState,
                  FullDenseInvW c F0 F_cur s4 ∧ s4.core.cur_vars = cv0 ∧ s4.core.fuel = fuel0 ∧
                  FullCongReprInv F_cur (2 * cv0) s4.core.repr ∧ g_len.toNat ≤ g_cap.toNat ∧
                  FidGateSeqOk 64 F_cur s4.core.cur_vars s4.scratch.scratch_buf g_len.toNat 0 ∧
                  (FullMem c s4 ⋆ R) m4)
                (fun _ ⟨g_len, ⟨⟩⟩ m4
                    ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hgl_le, hseq4, hm4⟩ => by
                  clear hExtBins hFindUE hExtract hExtIteAll
                    hdw0 hdw0a hdw1 hdw2 hdw3 hdw4a hden0 hw0 hlen0 hrepr2 hrepr3 hrepr4a
                    hrepr4a_inv hm1 hm3 hm4a hmg hcv1 hfl1 hcv3 hfl3 hcv30 hfl30 hcv4a hfl4a
                    hcv4a0 hfl4a0 hcv1_lt h2cv1_64 hgl0_le hseq4a _hinc4a hhalf
                    tmk0 htlt0 hit0_le hmt0 s2 hmi
                  m6b_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (_i', ()) mj => ∃ sj : FullState,
                      FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = cv0 ∧ sj.core.fuel = fuel0 ∧
                      FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧ (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨_i', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, hflj, hreprj, hmj⟩ => by
                      m6b_steps; m6b_call hFwdSub
                      refine ⟨c, F0, F_cur, sj, R, rfl, hdj, hcvj ▸ hreprj, hmj,
                        fun r5 s5 m5 hdw5 hcv5 hfl5 hrepr5 _hr5_dom hr5_uns hm5 => ?_⟩
                      have hcv50 : s5.core.cur_vars = cv0 := hcv5.trans hcvj
                      have hfl50 : s5.core.fuel = fuel0 := hfl5.trans hflj
                      m6b_split
                      · m6b_to_group
                        refine wp_loop_inv (ts := [i64])
                          (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                            tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                            (FullMem c { s5 with scratch :=
                              { s5.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                          (fun (it, ()) _ => cv0 - it.toNat)
                          (fun Jt hJt => by
                            m6b_let; exact hJt (0#64, ()) m5
                              ⟨s5.scratch.tarjan_mark, hdw5.1.scratch_ok.tarjan_mark_len,
                               Nat.zero_le _, hm5⟩)
                          (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
                        m6b_split
                        · have hit_lt : it.toNat < cv0 := by
                            have h := bv64_ult_lt hc
                            rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                          have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                          have hit_arr : it.toNat < tmkt.length := by omega
                          clear hc; m6b_steps
                          exact iht (it + 1#64, ()) m (by dsimp only; omega)
                            ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                        · clear hc; m6b_steps
                          exact hQ 20#64 _ m
                            (fid9_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64).toDense
                            hcv50 hfl50 (Or.inr rfl) (fun _ => hr5_uns (beq_iff_eq.mp hc)) hm
                      · clear hc; m6b_to_group
                        refine wp_loop_inv (ts := [i64])
                          (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                            tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                            (FullMem c { s5 with scratch :=
                              { s5.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                          (fun (it, ()) _ => cv0 - it.toNat)
                          (fun Jt hJt => by
                            m6b_let; exact hJt (0#64, ()) m5
                              ⟨s5.scratch.tarjan_mark, hdw5.1.scratch_ok.tarjan_mark_len,
                               Nat.zero_le _, hm5⟩)
                          (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
                        m6b_split
                        · have hit_lt : it.toNat < cv0 := by
                            have h := bv64_ult_lt hc
                            rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                          have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                          have hit_arr : it.toNat < tmkt.length := by omega
                          clear hc; m6b_steps
                          exact iht (it + 1#64, ()) m (by dsimp only; omega)
                            ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                        · clear hc; m6b_steps
                          let sf := { s5 with scratch :=
                            { s5.scratch with
                              tarjan_mark := tmkt, res_sz := 0#64, ant_sz := 0#64 } }
                          have hdwf := fid9_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64
                          m6b_split
                          · m6b_steps; apply_assumption; m6b_steps
                            exact hQ 20#64 sf m hdwf.toDense hcv50 hfl50 (Or.inr rfl)
                              (fun _ => FullM3CongBva.unsat_of_inconsistent_w hdwf.2.1
                                (bne_iff_ne.mp hc)) hm
                          · m6b_steps; apply_assumption; m6b_steps
                            exact hQ 1#64 sf m hdwf.toDense hcv50 hfl50 (Or.inl rfl)
                              (fun h => by cases h) hm)
                    ?_
                  intro Jwl_if hJwl_if
                  m6b_split
                  · have hg_pos : 0 < g_len.toNat := by
                      have h := bv64_ult_lt hc; rwa [show (0 : BitVec 64).toNat = 0 from rfl] at h
                    clear hc; m6b_split
                    · clear hc; m6b_to_group
                      let free_scr := BitVec.ofNat 64 c.scratch_cap - g_len
                      have hfree_n : free_scr.toNat = c.scratch_cap - g_len.toNat := by
                        dsimp only [free_scr]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                          rw [bv64_ofNat_toNat_lt (by omega)]; omega)),
                          bv64_ofNat_toNat_lt (by omega)]
                      have hfree_ge : 128 ≤ free_scr.toNat := by rw [hfree_n]; omega
                      refine wp_loop_inv (ts := [i64])
                        (fun (ht_max, ()) mhm => mhm = m4 ∧ ∃ k : Nat,
                          k ≤ 14 ∧ ht_max.toNat = 64 * 2 ^ k ∧ ht_max.toNat ≤ 1048576 ∧
                          ht_max.toNat * 2 ≤ free_scr.toNat)
                        (fun (ht_max, ()) _ => 1048576 - ht_max.toNat)
                        (fun Jhm hJhm => by
                          m6b_let
                          exact hJhm (64#64, ()) m4
                            ⟨rfl, 0, Nat.zero_le _, rfl, by decide,
                             by rw [show (64#64 : BitVec 64).toNat = 64 from rfl]; omega⟩)
                        (fun Jhm (ht_max, ()) mhm ⟨hmhm, k, hk_le, hpow, h1m, hmul2⟩ ih_hm => ?_)
                      have hhm_ge : 64 ≤ ht_max.toNat := by
                        rw [hpow]; have := Nat.one_le_two_pow (n := k); omega
                      m6b_to_group
                      refine wp_join_group (ts := []) (fun () me => me = m4) ?_
                        (fun Jhm_exit hJhm_exit => by
                          m6b_steps; m6b_split
                          · have hmul4 : ht_max.toNat * 4 ≤ free_scr.toNat := by
                              have h := bv64_ule_true_le hc
                              rw [show (4 : BitVec 64) = 4#64 from rfl, BitVec.toNat_mul,
                                show (4#64 : BitVec 64).toNat = 4 from rfl,
                                Nat.mod_eq_of_lt (by omega)] at h; exact h
                            clear hc; m6b_split
                            · have hlt : ht_max.toNat < 1048576 := bv64_ult_lt hc
                              obtain ⟨hk1, hpow1, h1m1, hmul2_1⟩ :=
                                fid9_cd_ht_max_step hk_le hpow hlt hmul4
                              clear hc; m6b_steps
                              exact ih_hm (ht_max <<< 1#64, ()) mhm
                                (by dsimp only; rw [hpow1, hpow]; omega)
                                ⟨hmhm, k + 1, hk1, hpow1, h1m1, hmul2_1⟩
                            · m6b_let; exact hJhm_exit () mhm hmhm
                          · m6b_let; exact hJhm_exit () mhm hmhm)
                      rintro _ ⟨⟩ me hme
                      have hme4 : (FullMem c s4 ⋆ R) me := hme ▸ hm4
                      let ht_off := BitVec.ofNat 64 c.scratch_cap - ht_max
                      have hht_off_n : ht_off.toNat = c.scratch_cap - ht_max.toNat := by
                        dsimp only [ht_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                          rw [bv64_ofNat_toNat_lt (by omega)]; omega)),
                          bv64_ofNat_toNat_lt (by omega)]
                      let rem_occ := ht_off - g_len
                      have hrem_n : rem_occ.toNat = ht_off.toNat - g_len.toNat := by
                        dsimp only [rem_occ]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
                      m6b_to_group
                      refine wp_join_group (ts := [i64])
                        (fun (occ_bkt_bv, ()) mo => mo = m4 ∧
                          occ_bkt_bv.toNat =
                            (if 262144 ≤ rem_occ.toNat then 8192
                             else if 65536 ≤ rem_occ.toNat then 2048
                             else if 16384 ≤ rem_occ.toNat then 512
                             else if 2048 ≤ rem_occ.toNat then 256
                             else if 256 ≤ rem_occ.toNat then 32 else 16))
                        ?_
                        (fun Jocc hJocc => by
                          m6b_split
                          · have h262k : 262144 ≤ rem_occ.toNat := by
                              have h := bv64_ule_true_le hc
                              rw [show (262144 : BitVec 64).toNat = 262144 from rfl] at h; exact h
                            m6b_let; exact hJocc (8192#64, ()) me ⟨hme, by simp [h262k]⟩
                          · have hlt262k : ¬ 262144 ≤ rem_occ.toNat := by
                              have h := bv64_ule_false_lt hc
                              rw [show (262144 : BitVec 64).toNat = 262144 from rfl] at h
                              change rem_occ.toNat < 262144 at h; omega
                            clear hc; m6b_to_group
                            refine wp_join_group (ts := [i64])
                              (fun (o1, ()) mo1 => mo1 = m4 ∧ o1.toNat =
                                (if 65536 ≤ rem_occ.toNat then 2048
                                 else if 16384 ≤ rem_occ.toNat then 512
                                 else if 2048 ≤ rem_occ.toNat then 256
                                 else if 256 ≤ rem_occ.toNat then 32 else 16))
                              (fun _ ⟨o1, ⟨⟩⟩ mo1 ⟨hmo1, ho1⟩ =>
                                hJocc (o1, ()) mo1 ⟨hmo1, by simp [hlt262k, ho1]⟩)
                              (fun Jocc1 hJocc1 => by
                                m6b_split
                                · have h65k : 65536 ≤ rem_occ.toNat := by
                                    have h := bv64_ule_true_le hc
                                    rw [show (65536 : BitVec 64).toNat = 65536 from rfl] at h
                                    exact h
                                  m6b_let; exact hJocc1 (2048#64, ()) me ⟨hme, by simp [h65k]⟩
                                · have hlt65k : ¬ 65536 ≤ rem_occ.toNat := by
                                    have h := bv64_ule_false_lt hc
                                    rw [show (65536 : BitVec 64).toNat = 65536 from rfl] at h
                                    change rem_occ.toNat < 65536 at h; omega
                                  clear hc; m6b_to_group
                                  refine wp_join_group (ts := [i64])
                                    (fun (o2, ()) mo2 => mo2 = m4 ∧ o2.toNat =
                                      (if 16384 ≤ rem_occ.toNat then 512
                                       else if 2048 ≤ rem_occ.toNat then 256
                                       else if 256 ≤ rem_occ.toNat then 32 else 16))
                                    (fun _ ⟨o2, ⟨⟩⟩ mo2 ⟨hmo2, ho2⟩ =>
                                      hJocc1 (o2, ()) mo2 ⟨hmo2, by simp [hlt65k, ho2]⟩)
                                    (fun Jocc2 hJocc2 => by
                                      m6b_split
                                      · have h16k : 16384 ≤ rem_occ.toNat := by
                                          have h := bv64_ule_true_le hc
                                          rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                                          exact h
                                        m6b_let; exact hJocc2 (512#64, ()) me ⟨hme, by simp [h16k]⟩
                                      · have hlt16k : ¬ 16384 ≤ rem_occ.toNat := by
                                          have h := bv64_ule_false_lt hc
                                          rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                                          change rem_occ.toNat < 16384 at h; omega
                                        clear hc; m6b_to_group
                                        refine wp_join_group (ts := [i64])
                                          (fun (o3, ()) mo3 => mo3 = m4 ∧ o3.toNat =
                                            (if 2048 ≤ rem_occ.toNat then 256
                                             else if 256 ≤ rem_occ.toNat then 32 else 16))
                                          (fun _ ⟨o3, ⟨⟩⟩ mo3 ⟨hmo3, ho3⟩ =>
                                            hJocc2 (o3, ()) mo3 ⟨hmo3, by simp [hlt16k, ho3]⟩)
                                          (fun Jocc3 hJocc3 => by
                                            m6b_split
                                            · have h2k : 2048 ≤ rem_occ.toNat := by
                                                have h := bv64_ule_true_le hc
                                                rw [show (2048 : BitVec 64).toNat = 2048 from rfl]
                                                  at h; exact h
                                              m6b_let
                                              exact hJocc3 (256#64, ()) me ⟨hme, by simp [h2k]⟩
                                            · have hlt2k : ¬ 2048 ≤ rem_occ.toNat := by
                                                have h := bv64_ule_false_lt hc
                                                rw [show (2048 : BitVec 64).toNat = 2048 from rfl]
                                                  at h
                                                change rem_occ.toNat < 2048 at h; omega
                                              clear hc; m6b_to_group
                                              refine wp_join_group (ts := [i64])
                                                (fun (o4, ()) mo4 => mo4 = m4 ∧ o4.toNat =
                                                  (if 256 ≤ rem_occ.toNat then 32 else 16))
                                                (fun _ ⟨o4, ⟨⟩⟩ mo4 ⟨hmo4, ho4⟩ =>
                                                  hJocc3 (o4, ()) mo4 ⟨hmo4, by simp [hlt2k, ho4]⟩)
                                                (fun Jocc4 hJocc4 => by
                                                  m6b_split
                                                  · have h256o : 256 ≤ rem_occ.toNat := by
                                                      have h := bv64_ule_true_le hc
                                                      rw [show (256 : BitVec 64).toNat = 256
                                                        from rfl]
                                                        at h; exact h
                                                    m6b_let
                                                    exact hJocc4 (32#64, ()) me
                                                      ⟨hme, by simp [h256o]⟩
                                                  · have hlt256o : ¬ 256 ≤ rem_occ.toNat := by
                                                      have h := bv64_ule_false_lt hc
                                                      rw [show (256 : BitVec 64).toNat = 256
                                                        from rfl]
                                                        at h
                                                      change rem_occ.toNat < 256 at h; omega
                                                    m6b_let
                                                    exact hJocc4 (16#64, ()) me
                                                      ⟨hme, by simp [hlt256o]⟩)))))
                      rintro _ ⟨occ_bkt_bv, ⟨⟩⟩ mo ⟨hmo, hocc_eq⟩
                      let occ_bkt := occ_bkt_bv.toNat
                      have ⟨ho_pos, ho_8192, hopow, hocc38, hg_le_co, hcq, hqi, hib, hbh, hc_cap,
                          hc8, hhm_cap⟩ :=
                        fid9_cd_layout_params hhm_ge h1m (by rw [← hfree_n]; exact hmul2) (by omega)
                          hsc hht_off_n hrem_n
                      rw [← hocc_eq] at ho_pos ho_8192 hopow hocc38 hg_le_co hcq hqi hib hbh
                      rw [← hocc_eq] at hc_cap hc8
                      let bkt_off := ht_off.toNat - occ_bkt
                      let inq_off := bkt_off - occ_bkt
                      let q_off := inq_off - occ_bkt
                      let ctrl_off := q_off - 8
                      have hco_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                          occ_bkt_bv - occ_bkt_bv - 8#64).toNat = ctrl_off := by
                        dsimp only [ctrl_off, q_off, inq_off, bkt_off]; rw [hht_off_n]
                        exact fid9_cd_ctrl_off_toNat (by omega) (by omega) hsc
                      have hco_eq : BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                          occ_bkt_bv - occ_bkt_bv - 8#64 = BitVec.ofNat 64 ctrl_off :=
                        BitVec.eq_of_toNat_eq (hco_n.trans (bv64_ofNat_toNat_lt (by omega)).symm)
                      m6b_to_group
                      refine wp_loop_inv (ts := [i64])
                        (fun (ht_sz, ()) mhs => mhs = m4 ∧ 64 ≤ ht_sz.toNat ∧
                          ht_sz.toNat ≤ ht_max.toNat)
                        (fun (ht_sz, ()) _ => ht_max.toNat - ht_sz.toNat)
                        (fun Jhs hJhs => by
                          m6b_let
                          exact hJhs (64#64, ()) mo ⟨hmo, by decide,
                            by rw [show (64#64 : BitVec 64).toNat = 64 from rfl]; omega⟩)
                        (fun Jhs (ht_sz, ()) mhs ⟨hmhs, hhs_lo, hhs_hi⟩ ih_hs => ?_)
                      m6b_to_group
                      refine wp_join_group (ts := []) (fun () mhs2 => mhs2 = m4) ?_
                        (fun Jhs_exit hJhs_exit => by
                          m6b_steps; m6b_split
                          · clear hc; m6b_split
                            · have hshl_n : (ht_sz <<< 1#64).toNat = 2 * ht_sz.toNat := by
                                rw [show (ht_sz <<< 1#64 : BitVec 64) =
                                    ht_sz <<< (1 : Nat) from rfl,
                                  BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
                                exact Nat.mod_eq_of_lt (by omega)
                              have hle_hm : (ht_sz <<< 1#64).toNat ≤ ht_max.toNat :=
                                bv64_ule_true_le hc
                              clear hc; m6b_steps
                              exact ih_hs (ht_sz <<< 1#64, ()) mhs
                                (by dsimp only; rw [hshl_n]; omega)
                                ⟨hmhs, by rw [hshl_n]; omega, hle_hm⟩
                            · m6b_let; exact hJhs_exit () mhs hmhs
                          · m6b_let; exact hJhs_exit () mhs hmhs)
                      rintro _ ⟨⟩ mhs2 hmhs2
                      m6b_to_group
                      refine wp_loop_inv (ts := [i64])
                        (fun (i3, ()) ms => ∃ scri : List (BitVec 32),
                          scri.length = c.scratch_cap ∧ i3.toNat ≤ ht_sz.toNat ∧
                          (∀ idx < g_len.toNat, scri[idx]? = s4.scratch.scratch_buf[idx]?) ∧
                          (∀ k' < i3.toNat,
                            scri[ht_off.toNat + k']?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
                          (FullMem c
                            { s4 with scratch := { s4.scratch with scratch_buf := scri } } ⋆ R) ms)
                        (fun (i3, ()) _ => ht_sz.toNat - i3.toNat)
                        (fun Js hJs => by
                          m6b_let
                          exact hJs (0#64, ()) mhs2
                            ⟨s4.scratch.scratch_buf, hdw4.1.scratch_ok.scratch_buf_len,
                             Nat.zero_le _, fun _ _ => rfl, fun _ h => by simp at h, hmhs2 ▸ hm4⟩)
                        (fun Js (i3, ()) ms ⟨scri, hscrl_i, hi3_le, hpref_i, hinit_i, hms⟩
                            ihs => ?_)
                      m6b_split
                      · have hi3_lt : i3.toNat < ht_sz.toNat := bv64_ult_lt hc
                        have hi3_1 : (i3 + 1#64).toNat = i3.toNat + 1 := bv64_add1_lt (by omega)
                        have hadd_n : (ht_off + i3).toNat = ht_off.toNat + i3.toNat := by
                          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                        have hadd_arr : (ht_off + i3).toNat < scri.length := by rw [hadd_n]; omega
                        clear hc; m6b_steps; rw [hadd_n] at hm
                        obtain ⟨hpref_i', hinit_i'⟩ :=
                          fid9_cd_ht_set_step (by omega) hpref_i hinit_i (by omega)
                        exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                          ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i],
                           by rw [hi3_1]; omega, hpref_i', hi3_1 ▸ hinit_i', hm⟩
                      · have hi3_eq : i3.toNat = ht_sz.toNat := by
                          have := bv64_ult_not_lt hc; omega
                        rw [hi3_eq] at hinit_i
                        have hht4 : FidCongHtInv 64 F_cur cv0 s4.scratch.scratch_buf scri
                            g_len.toNat ht_off.toNat ht_sz.toNat :=
                          fun k' hk' => Or.inl (hinit_i k' hk')
                        have hctrl_st := fid9_cd_ctrl_store_layout hg_le_co (by omega) ho_pos
                          ho_8192 hopow (by omega) hc_cap hc8 hcq hqi hib hbh (by omega)
                          hscrl_i hpref_i (hcv40 ▸ hht4)
                        have hco_add : ∀ j : BitVec 64, j.toNat < 8 →
                            (BitVec.ofNat 64 ctrl_off + j).toNat = ctrl_off + j.toNat := fun j hj =>
                          by rw [BitVec.toNat_add, bv64_ofNat_toNat_lt (by omega),
                            Nat.mod_eq_of_lt (by omega)]
                        have hco_b1 := hco_add 1 (by decide)
                        have hco_b2 := hco_add 2 (by decide)
                        have hco_b3 := hco_add 3 (by decide)
                        have hco_b4 := hco_add 4 (by decide)
                        have hco_b5 := hco_add 5 (by decide)
                        have hco_b6 := hco_add 6 (by decide)
                        have hco_b7 := hco_add 7 (by decide)
                        clear hc
                        try rw [show (8 : BitVec 64) = 8#64 from rfl, hco_eq]
                        m6b_steps
                        have hbkt_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv).toNat =
                            bkt_off := by
                          dsimp only [bkt_off]
                          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                            change occ_bkt ≤ ht_off.toNat; omega))]
                        have hinq_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                            occ_bkt_bv).toNat = inq_off := by
                          dsimp only [inq_off]
                          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hbkt_n]; omega)),
                            hbkt_n]
                        have hq_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                            occ_bkt_bv - occ_bkt_bv).toNat = q_off := by
                          dsimp only [q_off]
                          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hinq_n]; omega)),
                            hinq_n]
                        simp only [bv64_ofNat_toNat_lt (by omega : ctrl_off < 2 ^ 64),
                          hco_b1, hco_b2, hco_b3, hco_b4, hco_b5, hco_b6, hco_b7,
                          bv64_setWidth32_eq (rfl : occ_bkt_bv.toNat = occ_bkt),
                          bv64_setWidth32_eq hbkt_n, bv64_setWidth32_eq hinq_n,
                          bv64_setWidth32_eq hq_n,
                          bv64_setWidth32_eq (rfl : ht_sz.toNat = ht_sz.toNat)] at hm
                        try rw [show (8 : BitVec 64) = 8#64 from rfl, hco_eq]
                        m6b_call hWorklist
                        refine ⟨c, F0, F_cur, _, s4.scratch.scratch_buf, occ_bkt,
                          bkt_off, inq_off, q_off, ht_off.toNat, ht_sz.toNat, R, rfl,
                          fid9_denseInvW_with_scr_res0 hdw4 hctrl_st.1,
                          hcv40 ▸ hrepr4_inv, hg_pos, by unfold fidCongHashMaxSz; omega,
                          by rw [bv64_ofNat_toNat_lt (by omega)]; exact hctrl_st.2.1,
                          hseq4, hctrl_st.2.2.1, hcv40 ▸ hctrl_st.2.2.2,
                          hm, fun r4 s4w m4w hdw4w hcv4w hfl4w hrepr4w _hr4_dom hr4_uns hm4w => ?_⟩
                        have hcv4w0 : s4w.core.cur_vars = cv0 := hcv4w.trans hcv40
                        have hfl4w0 : s4w.core.fuel = fuel0 := hfl4w.trans hfl40
                        m6b_split
                        · m6b_to_group
                          refine wp_loop_inv (ts := [i64])
                            (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                              tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                              (FullMem c { s4w with scratch :=
                                { s4w.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                            (fun (it, ()) _ => cv0 - it.toNat)
                            (fun Jt hJt => by
                              m6b_let; exact hJt (0#64, ()) m4w
                                ⟨s4w.scratch.tarjan_mark, hdw4w.1.scratch_ok.tarjan_mark_len,
                                 Nat.zero_le _, hm4w⟩)
                            (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
                          m6b_split
                          · have hit_lt : it.toNat < cv0 := by
                              have h := bv64_ult_lt hc
                              rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                            have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                            have hit_arr : it.toNat < tmkt.length := by omega
                            clear hc; m6b_steps
                            exact iht (it + 1#64, ()) m (by dsimp only; omega)
                              ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                          · clear hc; m6b_steps
                            exact hQ 20#64 _ m
                              (fid9_denseInvW_with_tmk_ar hdw4w htlt 0#64 0#64).toDense
                              hcv4w0 hfl4w0 (Or.inr rfl) (fun _ => hr4_uns (beq_iff_eq.mp hc)) hm
                        · m6b_let
                          exact hJwl_if (_, ()) m4w
                            ⟨s4w, hdw4w, hcv4w0, hfl4w0, hcv4w0 ▸ hcv4w ▸ hrepr4w, hm4w⟩
                    · clear hc; m6b_let
                      exact hJwl_if (_, ()) m4 ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩
                  · clear hc; m6b_let
                    exact hJwl_if (_, ()) m4 ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩)
                ?_
              intro Jite hJite
              m6b_split
              · have hgl32 : (g_len0.setWidth 32).toNat = g_len0.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                have hgc32 : (g_cap.setWidth 32).toNat = g_cap.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                clear hc; m6b_steps; m6b_call hExtIteAll
                refine ⟨64, c, F0, F_cur, s4a, R, by decide, by decide, rfl, hdw4a,
                  by rw [hgl32, hgc32]; exact hgl0_le, by rw [hgc32]; omega,
                  by rw [hgl32, hcv4a]; exact hseq4a, hm4a,
                  fun ret32 s4b m4b hdw4b hcore4b _ _ _ _ _ _ _ _ hg_hi _ hseq4b hm4b => ?_⟩
                have hret64 : (ret32.setWidth 64).toNat = ret32.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ret32.isLt; omega)]
                have hcv4b0 : s4b.core.cur_vars = cv0 :=
                  (congrArg FullCoreState.cur_vars hcore4b).trans hcv4a0
                have hfl4b0 : s4b.core.fuel = fuel0 :=
                  (congrArg FullCoreState.fuel hcore4b).trans hfl4a0
                have hrepr4b_inv : FullCongReprInv F_cur (2 * cv0) s4b.core.repr := by
                  rw [congrArg FullCoreState.repr hcore4b]; exact hrepr4a_inv
                m6b_steps
                exact hJite (ret32.setWidth 64, ()) m4b
                  ⟨s4b, hdw4b, hcv4b0, hfl4b0, hrepr4b_inv,
                   by rw [← hret64, hgc32] at hg_hi; exact hg_hi,
                   by rw [hret64, hcore4b]; exact hseq4b, hm4b⟩
              · exfalso
                have hgt := bv64_ule_false_lt hc
                omega

end CongDenseStep9

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end

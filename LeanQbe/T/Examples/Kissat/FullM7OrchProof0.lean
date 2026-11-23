/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7Transport2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat `D-Full` Unified `M7` Orchestration Tail (`FullM7OrchProof0`)

Proves the two `M7`-modified top-level orchestration functions and assembles the full Part 3
`TableImpl`:
1. `full_congruence_dense_m7_wp` (`FullM7.full_congruence_dense_body` at `[275]`, extending
   `ht_sz < 131072` and wiring `full_cong_extract_ite_all_m7`).
2. `full_search_m6_m7_wp` (`FullM7.full_search_m6_body` at `[405]`, calling
   `full_lucky_late_m7` once before the `while` loop per `#3909`, canonical `full_propagate`,
   `full_switch_mode_m7`, `full_rephase`, and `full_decide_m7`).
3. `m7OrchTail_tableImpl` (`[405..409]`) and `m7Part3_tableImpl` (`[276..409]`, `134` fns).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva (m3CongruenceDenseSpec)
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open scoped Full.FullArenaTactics FullCongHelpers FullCongTactics M6bHeadTactics
open scoped FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. `full_congruence_dense` (`[275]`, `ht_sz < 131072` + `full_cong_extract_ite_all_m7`) -/

section M7CongDense

private theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) :
    ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem bv64_setWidth32_eq {x : BitVec 64} {n : Nat} (hx : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  subst hx; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem m7_denseInvW_with_antsz_ressz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩, hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m7_denseInvW_with_tmk_ar {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch :=
        { s.scratch with tarjan_mark := tmk', ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with tarjan_mark_len := ht }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m7_denseInvW_with_scr_res0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hsl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := 0#64 } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hsl }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m7_denseInvW_after_iteAll {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' := by
  have hw' : FullWitnessInv c F0 F_cur s'.core := by rw [hcore]; exact hd.2.1
  have hmk' : FullLitMarksClear c s' :=
    fullLitMarksClear_of_eq hd.2.2.1 (congrArg FullCoreState.mrk hcore)
      (congrArg FullCoreState.lit_mark hcore)
  have hnd' : FullArenaVarsNodup s' :=
    fullArenaVarsNodup_of_eq hd.2.2.2.1 (congrArg FullCoreState.arena hcore)
      (congrArg FullCoreState.arena_len hcore)
  have hext' : FullExtScratchOk c s' :=
    fullExtScratchOk_of_eq hd.2.2.2.2.1 (congrArg FullCoreState.arena hcore)
      (congrArg FullCoreState.arena_len hcore) hll hel
  have hc1 : s'.core.cur_level = 0 := by rw [hcore]; exact hd.2.2.2.2.2.1
  have hc2 : s'.core.dense_mode ≠ 0#64 := by rw [hcore]; exact hd.2.2.2.2.2.2
  exact ⟨hlen', hw', hmk', hnd', hext', hc1, hc2⟩

private theorem m7_cd_ht_pow_step {ht_sz : BitVec 64} {k cap : Nat}
    (hk : k ≤ 11) (heq : ht_sz.toNat = 64 * 2 ^ k)
    (hlt : ht_sz.toNat < 131072) (hmul : ht_sz.toNat * 8 ≤ cap) :
    k + 1 ≤ 11 ∧ (ht_sz <<< 1#64).toNat = 64 * 2 ^ (k + 1) ∧
    (ht_sz <<< 1#64).toNat ≤ 131072 ∧ (ht_sz <<< 1#64).toNat ≤ cap := by
  have hk_lt : k < 11 :=
    Nat.lt_of_le_of_ne hk fun h => by subst h; rw [heq] at hlt; simp at hlt
  have h2k_le : 2 ^ k ≤ 1024 := by
    match k, hk_lt with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _
    | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ => decide
  have h512 : 512 * 2 ^ k ≤ cap := by rw [heq] at hmul; omega
  have hshl : (ht_sz <<< 1#64).toNat = 2 * ht_sz.toNat := by
    rw [show (ht_sz <<< 1#64 : BitVec 64) = ht_sz <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpow : 64 * 2 ^ (k + 1) = 2 * (64 * 2 ^ k) := by rw [Nat.pow_succ]; omega
  refine ⟨by omega, by rw [hshl, heq, hpow], by rw [hshl, heq]; omega,
    by rw [hshl, heq]; omega⟩

private theorem m7_cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * 268435456)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem m7_cd_ht_clear_inv {F_cur : List (List Nat)} {cv0 g_len ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinit : ∀ k < ht_sz, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    (∀ idx < g_len, scri[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv0 scr0 scri g_len ht_off ht_sz :=
  ⟨hpref, fun k hk => Or.inl (hinit k hk)⟩

private theorem m7_cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
    (hg_le : g_len ≤ ht_off) (hinv1 : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinv2 : ∀ k < i, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_len : ht_off + i < scri.length) :
    (∀ idx < g_len, (scri.set (ht_off + i) 0xFFFFFFFF#32)[idx]? = scr0[idx]?) ∧
    (∀ k < i + 1,
      (scri.set (ht_off + i) 0xFFFFFFFF#32)[ht_off + k]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32) := by
  refine ⟨fun idx hidx => ?_, fun k hk => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hinv1 idx hidx
  · by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self hi_len, Option.getD_some]
    · rw [List.getElem?_set_ne (by omega)]; exact hinv2 k (by omega)

private theorem m7_cd_layout_params {ht_off ht_sz cap : Nat}
    (h256 : 256 ≤ cap) (hht_pos : 0 < ht_sz) (hht_le : ht_sz ≤ cap)
    (hmul : ht_sz = 64 ∨ ht_sz * 4 ≤ cap) (hcap : cap < 2 ^ 28) (hho : ht_off = cap - ht_sz) :
    let occ_bkt := if 16384 ≤ ht_off then 512 else if 2048 ≤ ht_off then 256
      else if 256 ≤ ht_off then 32 else 16
    let bkt_off := ht_off - occ_bkt
    let inq_off := bkt_off - occ_bkt
    let q_off := inq_off - occ_bkt
    let ctrl_off := q_off - 8
    0 < occ_bkt ∧ occ_bkt ≤ 512 ∧
    (∃ p : Nat, 1 ≤ p ∧ p ≤ 9 ∧ occ_bkt = 2 ^ p) ∧
    occ_bkt * 3 + 8 ≤ ht_off ∧
    ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
    inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
    ctrl_off < cap ∧ ctrl_off + 8 ≤ cap ∧ ht_off + ht_sz ≤ cap := by
  intro occ_bkt bkt_off inq_off q_off ctrl_off
  have hht_off_ge : 192 ≤ ht_off := by
    rcases hmul with rfl | h4 <;> omega
  have hpow : 0 < occ_bkt ∧ occ_bkt ≤ 512 ∧
      (∃ p : Nat, 1 ≤ p ∧ p ≤ 9 ∧ occ_bkt = 2 ^ p) ∧ occ_bkt * 3 + 8 ≤ ht_off := by
    dsimp only [occ_bkt]
    split
    · exact ⟨by decide, by decide, ⟨9, by decide, by decide, rfl⟩, by omega⟩
    · split
      · exact ⟨by decide, by decide, ⟨8, by decide, by decide, rfl⟩, by omega⟩
      · split
        · exact ⟨by decide, by decide, ⟨5, by decide, by decide, rfl⟩, by omega⟩
        · exact ⟨by decide, by decide, ⟨4, by decide, by decide, rfl⟩, by omega⟩
  refine ⟨hpow.1, hpow.2.1, hpow.2.2.1, hpow.2.2.2, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩

private theorem m7_cd_gcap_le {ctrl_off : Nat} (hcap : ctrl_off < 2 ^ 28) :
    ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64).toNat ≤ ctrl_off := by
  have hmul : (BitVec.ofNat 64 ctrl_off * 3#64).toNat = ctrl_off * 3 := by
    rw [BitVec.toNat_mul, bv64_ofNat_toNat_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [show ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64 : BitVec 64) =
      (BitVec.ofNat 64 ctrl_off * 3#64) >>> (2 : Nat) from rfl,
    BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow]
  omega

private theorem m7_cd_ctrl_off_toNat {cap : Nat} {ht_sz occ : BitVec 64}
    (hht : ht_sz.toNat ≤ cap) (h38 : occ.toNat * 3 + 8 ≤ cap - ht_sz.toNat)
    (hcap : cap < 2 ^ 28) :
    (BitVec.ofNat 64 cap - ht_sz - occ - occ - occ - 8#64).toNat =
      cap - ht_sz.toNat - occ.toNat - occ.toNat - occ.toNat - 8 := by
  have hsc : (BitVec.ofNat 64 cap).toNat = cap := bv64_ofNat_toNat_lt (by omega)
  have h1 : (BitVec.ofNat 64 cap - ht_sz).toNat = cap - ht_sz.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsc]; exact hht)), hsc]
  have h2 : (BitVec.ofNat 64 cap - ht_sz - occ).toNat = cap - ht_sz.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; omega)), h1]
  have h3 : (BitVec.ofNat 64 cap - ht_sz - occ - occ).toNat =
      cap - ht_sz.toNat - occ.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h2]; omega)), h2]
  have h4 : (BitVec.ofNat 64 cap - ht_sz - occ - occ - occ).toNat =
      cap - ht_sz.toNat - occ.toNat - occ.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h3]; omega)), h3]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
    rw [h4, show (8#64 : BitVec 64).toNat = 8 from rfl]; omega)), h4]
  rfl

private theorem m7_cd_ctrl_store_layout {c : FullCfg} {F_cur : List (List Nat)} {cv0 : Nat}
    {scr0 scri : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hg_co : g_len ≤ ctrl_off) (hg_24 : g_len ≤ 0x01000000)
    (ho_pos : 0 < occ_bkt) (ho_512 : occ_bkt ≤ 512)
    (hopow : ∃ p : Nat, 1 ≤ p ∧ p ≤ 9 ∧ occ_bkt = 2 ^ p)
    (hht_pos : 0 < ht_sz) (_hht_bnd : ht_sz < 2 ^ 30)
    (hc_cap : ctrl_off < c.scratch_cap) (hc8 : ctrl_off + 8 ≤ c.scratch_cap)
    (hcq : ctrl_off + 8 ≤ q_off) (hqi : q_off + occ_bkt ≤ inq_off)
    (hib : inq_off + occ_bkt ≤ bkt_off) (hbh : bkt_off + occ_bkt ≤ ht_off)
    (hhc : ht_off + ht_sz ≤ c.scratch_cap)
    (hscrl : scri.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv0 scr0 scri g_len ht_off ht_sz) :
    let scr' := (((((((scri.set ctrl_off (BitVec.ofNat 32 occ_bkt)).set
      (ctrl_off + 1) (BitVec.ofNat 32 bkt_off)).set
      (ctrl_off + 2) (BitVec.ofNat 32 inq_off)).set
      (ctrl_off + 3) (BitVec.ofNat 32 q_off)).set
      (ctrl_off + 4) 0#32).set
      (ctrl_off + 5) 0#32).set
      (ctrl_off + 6) (BitVec.ofNat 32 ht_off)).set
      (ctrl_off + 7) (BitVec.ofNat 32 ht_sz)
    scr'.length = c.scratch_cap ∧
    M6CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv0 scr0 scr' g_len ht_off ht_sz := by
  intro scr'
  have hsc : c.scratch_cap < 2 ^ 28 := Nat.lt_of_lt_of_le c.hscr (by decide)
  have hsl : scr'.length = c.scratch_cap := by dsimp only [scr']; simp [hscrl]
  have hhold_out : ∀ idx, idx < ctrl_off ∨ ctrl_off + 8 ≤ idx → scr'[idx]? = scri[idx]? := by
    intro idx hidx; dsimp only [scr']
    repeat rw [List.getElem?_set_ne (by omega)]
  have hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]? := fun idx hidx =>
    (hhold_out idx (Or.inl (by omega))).trans (hpref idx hidx)
  have hht' : M6CongHtInv F_cur cv0 scr0 scr' g_len ht_off ht_sz := by
    intro k hk; dsimp only
    rw [hhold_out (ht_off + k) (Or.inr (by omega))]; exact hht k hk
  have hg : ∀ j, j < 8 → scr'[ctrl_off + j]? =
      ([BitVec.ofNat 32 occ_bkt, BitVec.ofNat 32 bkt_off, BitVec.ofNat 32 inq_off,
        BitVec.ofNat 32 q_off, 0#32, 0#32, BitVec.ofNat 32 ht_off,
        BitVec.ofNat 32 ht_sz])[j]? := by
    intro j _; dsimp only [scr']
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
      rw [Nat.add_zero, List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
      rw [List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
      rw [List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
      rw [List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
      rw [List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
      rw [List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
    · rw [List.getElem?_set_self (by simp [hscrl]; omega)]; rfl
  have hs0 : scr'[ctrl_off]?.getD 0#32 = BitVec.ofNat 32 occ_bkt := by
    have h0 := hg 0 (by decide); rw [Nat.add_zero] at h0
    exact congrArg (Option.getD · 0#32) h0
  have hs1 := congrArg (Option.getD · 0#32) (hg 1 (by decide))
  have hs2 := congrArg (Option.getD · 0#32) (hg 2 (by decide))
  have hs3 := congrArg (Option.getD · 0#32) (hg 3 (by decide))
  have hs6 := congrArg (Option.getD · 0#32) (hg 6 (by decide))
  have hs7 := congrArg (Option.getD · 0#32) (hg 7 (by decide))
  have h5 := hg 5 (by decide)
  have h5' : scr'[ctrl_off + 5]?.getD 0#32 = 0#32 := congrArg (Option.getD · 0#32) h5
  have hlay : M6CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz :=
    ⟨hc_cap, hc8, hg_co, hg_24, hs0, hs1, hs2, hs3, hs6, hs7,
     ho_pos, ho_512, hopow, hht_pos, hcq, hqi, hib, hbh, hhc,
     by have := hg 4 (by decide); rw [this]; simpa using ho_pos,
     by rw [h5]; exact Nat.zero_le _,
     fun k hk => by
       rw [h5', show (0#32 : BitVec 32).toNat = 0 from rfl] at hk
       omega⟩
  exact ⟨hsl, hlay, hpref', hht'⟩

/-- UNSAT-sound WP proof for `FullM7.full_congruence_dense_body` (`ht_sz < 131072` and
`full_cong_extract_ite_all_m7`) against canonical `FullM3CongBva.m3CongruenceDenseSpec`. -/
theorem full_congruence_dense_m7_wp (Γ : Env)
    (hExtBin : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m6CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hIteAll : ∀ a m Q X, FullM7CongIte.m7ExtractIteAllM6Spec a m Q X →
      Γ "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X)
    (hWork : ∀ a m Q X, m6CongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ FullM7.full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, hm0, hQ⟩
  have hsc : c.scratch_cap < 2 ^ 28 := Nat.lt_of_lt_of_le c.hscr (by decide)
  have hmx : c.max_vars < 2 * 268435456 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
  obtain ⟨hlen0, ⟨F_cur, hw0⟩⟩ := hden0.1
  have hdw0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hlen0, hw0, hden0.2.1, hden0.2.2.1, hden0.2.2.2.1, hden0.2.2.2.2.1, hden0.2.2.2.2.2⟩
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have hcv_le : cv0 ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  unfold Func.wp FullM7.full_congruence_dense_body
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
        m7_denseInvW_with_antsz_ressz hdw0 0#64 s0.scratch.res_sz
      m6b_call hExtBin
      refine ⟨c, F0, F_cur, s0a, R, rfl, hdw0a, hm,
        fun r1 s1 m1 hdw1 hcv1 hfl1 _hr1_dom hr1_uns hm1 => ?_⟩
      have hcv10 : s1.core.cur_vars = cv0 := hcv1
      m6b_split
      · m6b_steps
        exact hQ 20#64 _ m (m7_denseInvW_with_antsz_ressz hdw1 0#64 s1.scratch.res_sz).toDense
          hcv1 hfl1 (Or.inr rfl) (fun _ => hr1_uns (beq_iff_eq.mp hc)) hm
      · clear hc
        have hcv1_lt : cv0 < 2 ^ 32 := by omega
        have h2cv1_64 : 2 * cv0 < 2 ^ 64 := by omega
        m6b_steps
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
            have h := bv64_ult_lt hc
            rw [hcv10] at h
            change i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at h
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
              bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h2cv1_64] at h
            exact h
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
            have h := bv64_ult_not_lt hc
            rw [hcv10] at h
            change ¬ i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at h
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
              bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h2cv1_64] at h
            omega
          rw [hi_eq] at hinit
          let s2 : FullState := { s1 with core := { s1.core with repr := repri } }
          have hdw2 := m6_fullDenseInvW_with_repr hdw1 hrl
          have hrepr2 : FullCongReprInv F_cur (2 * s2.core.cur_vars) s2.core.repr := by
            rw [show s2.core.cur_vars = cv0 from hcv1]
            exact m7_cd_repr_init_inv hrl hcv_le hmx hinit
          clear hc; m6b_steps; m6b_call hFindUE
          refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, hrepr2, hmi,
            fun r2 s3 m3 hdw3 hcv3 hfl3 hrepr3 _hr2_dom hr2_uns hm3 => ?_⟩
          have hcv30 : s3.core.cur_vars = cv0 := hcv3.trans hcv1
          have hfl30 : s3.core.fuel = fuel0 := hfl3.trans hfl1
          m6b_split
          · m6b_steps
            refine wp_loop_inv (ts := [i64])
              (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                (FullMem c { s3 with scratch := { s3.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
              (fun (it, ()) _ => cv0 - it.toNat)
              (fun Jt hJt => by
                m6b_let
                exact hJt (0#64, ()) m3
                  ⟨s3.scratch.tarjan_mark, hdw3.1.scratch_ok.tarjan_mark_len,
                   Nat.zero_le _, hm3⟩)
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
              exact hQ 20#64 _ m (m7_denseInvW_with_tmk_ar hdw3 htlt 0#64 0#64).toDense
                hcv30 hfl30 (Or.inr rfl) (fun _ => hr2_uns (beq_iff_eq.mp hc)) hm
          · clear hc; m6b_steps
            refine wp_loop_inv (ts := [i64])
              (fun (ht_sz, ()) mht => mht = m3 ∧ ∃ k : Nat,
                k ≤ 11 ∧ ht_sz.toNat = 64 * 2 ^ k ∧ ht_sz.toNat ≤ 131072 ∧
                ht_sz.toNat ≤ c.scratch_cap ∧ (ht_sz = 64#64 ∨ ht_sz.toNat * 4 ≤ c.scratch_cap))
              (fun (ht_sz, ()) _ => 131072 - ht_sz.toNat)
              (fun Jht hJht => by
                m6b_let
                exact hJht (64#64, ()) m3
                  ⟨rfl, 0, Nat.zero_le _, rfl, by decide,
                   by rw [show (64#64 : BitVec 64).toNat = 64 from rfl]; omega, Or.inl rfl⟩)
              (fun Jht (ht_sz, ()) mht ⟨hmht, k, hk_le, hpow, h128k, hsc_le, hmul4⟩ ih_ht => ?_)
            have hht_pos : 0 < ht_sz.toNat := by
              rw [hpow]; exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)
            m6b_to_group
            refine wp_join_group (ts := []) (fun () me => me = m3)
              ?_
              (fun Jht_exit hJht_exit => by
                have hmht3 : (FullMem c s3 ⋆ R) mht := hmht ▸ hm3
                m6b_steps; m6b_split
                · have hmul_le : ht_sz.toNat * 8 ≤ c.scratch_cap := by
                    have h := bv64_ule_true_le hc
                    rw [show (8 : BitVec 64) = 8#64 from rfl, BitVec.toNat_mul,
                      show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega),
                      bv64_ofNat_toNat_lt (by omega)] at h
                    exact h
                  clear hc; m6b_split
                  · have hlt : ht_sz.toNat < 131072 := bv64_ult_lt hc
                    obtain ⟨hk1, hpow1, h128k1, hsc1⟩ := m7_cd_ht_pow_step hk_le hpow hlt hmul_le
                    clear hc; m6b_steps
                    exact ih_ht (ht_sz <<< 1#64, ()) mht (by dsimp only; rw [hpow1, hpow]; omega)
                      ⟨hmht, k + 1, hk1, hpow1, h128k1, hsc1,
                       Or.inr (by rw [hpow1]; rw [hpow] at hmul_le; omega)⟩
                  · m6b_let; exact hJht_exit () mht hmht
                · m6b_let; exact hJht_exit () mht hmht)
            rintro _ ⟨⟩ me hme
            let ht_off := BitVec.ofNat 64 c.scratch_cap - ht_sz
            have hht_off_n : ht_off.toNat = c.scratch_cap - ht_sz.toNat := by
              dsimp only [ht_off]
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                rw [bv64_ofNat_toNat_lt (by omega)]; exact hsc_le)),
                bv64_ofNat_toNat_lt (by omega)]
            have hme3 : (FullMem c s3 ⋆ R) me := hme ▸ hm3
            m6b_to_group
            refine wp_join_group (ts := [i64])
              (fun (occ_bkt_bv, ()) mo => mo = m3 ∧
                occ_bkt_bv.toNat = (if 16384 ≤ ht_off.toNat then 512
                  else if 2048 ≤ ht_off.toNat then 256
                  else if 256 ≤ ht_off.toNat then 32 else 16))
              ?_
              (fun Jocc hJocc => by
                m6b_split
                · have h16k : 16384 ≤ ht_off.toNat := by
                    have h := bv64_ule_true_le hc
                    rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                    exact h
                  m6b_let; exact hJocc (512#64, ()) me ⟨hme, by simp [h16k]⟩
                · have hlt16k : ¬ 16384 ≤ ht_off.toNat := by
                    have h := bv64_ule_false_lt hc
                    rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                    dsimp only [ht_off]; omega
                  clear hc; m6b_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (o2, ()) mo2 => mo2 = m3 ∧
                      o2.toNat = (if 2048 ≤ ht_off.toNat then 256
                        else if 256 ≤ ht_off.toNat then 32 else 16))
                    (fun _ ⟨o2, ⟨⟩⟩ mo2 ⟨hmo2, ho2⟩ =>
                      hJocc (o2, ()) mo2 ⟨hmo2, by simp [hlt16k, ho2]⟩)
                    (fun Jocc2 hJocc2 => by
                      m6b_split
                      · have h2k : 2048 ≤ ht_off.toNat := by
                          have h := bv64_ule_true_le hc
                          rw [show (2048 : BitVec 64).toNat = 2048 from rfl] at h
                          exact h
                        m6b_let; exact hJocc2 (256#64, ()) me ⟨hme, by simp [h2k]⟩
                      · have hlt2k : ¬ 2048 ≤ ht_off.toNat := by
                          have h := bv64_ule_false_lt hc
                          rw [show (2048 : BitVec 64).toNat = 2048 from rfl] at h
                          dsimp only [ht_off]; omega
                        clear hc; m6b_to_group
                        refine wp_join_group (ts := [i64])
                          (fun (o3, ()) mo3 => mo3 = m3 ∧
                            o3.toNat = (if 256 ≤ ht_off.toNat then 32 else 16))
                          (fun _ ⟨o3, ⟨⟩⟩ mo3 ⟨hmo3, ho3⟩ =>
                            hJocc2 (o3, ()) mo3 ⟨hmo3, by simp [hlt2k, ho3]⟩)
                          (fun Jocc3 hJocc3 => by
                            m6b_split
                            · have h256o : 256 ≤ ht_off.toNat := by
                                have h := bv64_ule_true_le hc
                                rw [show (256 : BitVec 64).toNat = 256 from rfl] at h
                                exact h
                              m6b_let; exact hJocc3 (32#64, ()) me ⟨hme, by simp [h256o]⟩
                            · have hlt256o : ¬ 256 ≤ ht_off.toNat := by
                                have h := bv64_ule_false_lt hc
                                rw [show (256 : BitVec 64).toNat = 256 from rfl] at h
                                dsimp only [ht_off]; omega
                              m6b_let; exact hJocc3 (16#64, ()) me ⟨hme, by simp [hlt256o]⟩)))
            rintro _ ⟨occ_bkt_bv, ⟨⟩⟩ mo ⟨hmo, hocc_eq⟩
            let occ_bkt := occ_bkt_bv.toNat
            have hmul4' : ht_sz.toNat = 64 ∨ ht_sz.toNat * 4 ≤ c.scratch_cap :=
              hmul4.elim (fun h => Or.inl (by subst h; rfl)) Or.inr
            have ⟨ho_pos, ho_512, hopow, hocc38, hcq, hqi, hib, hbh, hc_cap, hc8, hhc⟩ :=
              m7_cd_layout_params h256 hht_pos hsc_le hmul4' hsc hht_off_n
            rw [← hocc_eq] at ho_pos ho_512 hopow hocc38 hcq hqi hib hbh hc_cap hc8
            let bkt_off := ht_off.toNat - occ_bkt
            let inq_off := bkt_off - occ_bkt
            let q_off := inq_off - occ_bkt
            let ctrl_off := q_off - 8
            have hco_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                occ_bkt_bv - occ_bkt_bv - 8#64).toNat = ctrl_off := by
              dsimp only [ctrl_off, q_off, inq_off, bkt_off]
              rw [hht_off_n]
              exact m7_cd_ctrl_off_toNat hsc_le (hht_off_n ▸ hocc38) hsc
            have hco_le_fn := m7_cd_gcap_le (by omega : ctrl_off < 2 ^ 28)
            have hco_eq : BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv - occ_bkt_bv -
                occ_bkt_bv - 8#64 = BitVec.ofNat 64 ctrl_off :=
              BitVec.eq_of_toNat_eq (hco_n.trans (bv64_ofNat_toNat_lt (by omega)).symm)
            m6b_to_group
            refine wp_join_group (ts := [i64])
              (fun (g_cap, ()) mg => mg = m3 ∧
                g_cap.toNat ≤ ctrl_off ∧ g_cap.toNat ≤ 0x00FFFFFF)
              ?_
              (fun Jgc hJgc => by
                m6b_split
                · have hlt := bv64_ult_lt hc
                  rw [show (0x00FFFFFF : BitVec 64).toNat = 0x00FFFFFF from rfl,
                    show (8 : BitVec 64) = 8#64 from rfl,
                    show (3 : BitVec 64) = 3#64 from rfl, hco_eq] at hlt
                  change 0x00FFFFFF < ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64).toNat at hlt
                  m6b_steps
                  have hco_le16 : (0x00FFFFFF#64 : BitVec 64).toNat ≤ ctrl_off := by
                    rw [show (0x00FFFFFF#64 : BitVec 64).toNat = 0x00FFFFFF from rfl]
                    omega
                  exact hJgc (0x00FFFFFF#64, ()) mo ⟨hmo, hco_le16, by decide⟩
                · have hnot := bv64_ult_not_lt hc
                  rw [show (0x00FFFFFF : BitVec 64).toNat = 0x00FFFFFF from rfl] at hnot
                  m6b_let; refine hJgc (_, ()) mo ⟨hmo, ?_, by omega⟩
                  rw [show (8 : BitVec 64) = 8#64 from rfl,
                    show (3 : BitVec 64) = 3#64 from rfl, hco_eq]
                  exact hco_le_fn)
            rintro _ ⟨g_cap, ⟨⟩⟩ mg ⟨hmg, hgc_co, hgc_24⟩
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
                FullDenseInvW c F0 F_cur s4 ∧
                s4.core.cur_vars = cv0 ∧ s4.core.fuel = fuel0 ∧
                FullCongReprInv F_cur (2 * cv0) s4.core.repr ∧
                g_len.toNat ≤ g_cap.toNat ∧
                M6GateSeqOk F_cur s4.core.cur_vars s4.scratch.scratch_buf g_len.toNat 0 ∧
                (FullMem c s4 ⋆ R) m4)
              (fun _ ⟨g_len, ⟨⟩⟩ m4
                  ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hgl_le, hseq4, hm4⟩ => by
                clear hExtBin hFindUE hExtract hIteAll
                  hdw0 hdw0a hdw1 hdw2 hdw3 hdw4a hden0 hw0 hlen0 hrepr2 hrepr3 hrepr4a hrepr4a_inv
                  hm1 hm3 hm4a hmg hcv1 hfl1 hcv3 hfl3 hcv30 hfl30 hcv4a hfl4a hcv4a0 hfl4a0
                  hcv1_lt h2cv1_64 hgl0_le hseq4a _hinc4a hco_le_fn hocc_eq hmul4'
                m6b_to_group
                refine wp_join_group (ts := [i64])
                  (fun (_i', ()) mj => ∃ sj : FullState,
                    FullDenseInvW c F0 F_cur sj ∧
                    sj.core.cur_vars = cv0 ∧ sj.core.fuel = fuel0 ∧
                    FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧ (FullMem c sj ⋆ R) mj)
                  (fun _ ⟨_i', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, hflj, hreprj, hmj⟩ => by
                    m6b_steps; m6b_call hFwdSub
                    refine ⟨c, F0, F_cur, sj, R, rfl, hdj, hcvj ▸ hreprj, hmj,
                      fun r5 s5 m5 hdw5 hcv5 hfl5 hrepr5 _hr5_dom hr5_uns hm5 => ?_⟩
                    have hcv50 : s5.core.cur_vars = cv0 := hcv5.trans hcvj
                    have hfl50 : s5.core.fuel = fuel0 := hfl5.trans hflj
                    m6b_split
                    · m6b_steps
                      refine wp_loop_inv (ts := [i64])
                        (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                          tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                          (FullMem c { s5 with scratch :=
                            { s5.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                        (fun (it, ()) _ => cv0 - it.toNat)
                        (fun Jt hJt => by
                          m6b_let
                          exact hJt (0#64, ()) m5
                            ⟨s5.scratch.tarjan_mark, hdw5.1.scratch_ok.tarjan_mark_len,
                             Nat.zero_le _, hm5⟩)
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
                        exact hQ 20#64 _ m (m7_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64).toDense
                          hcv50 hfl50 (Or.inr rfl) (fun _ => hr5_uns (beq_iff_eq.mp hc)) hm
                    · clear hc; m6b_steps
                      refine wp_loop_inv (ts := [i64])
                        (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                          tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                          (FullMem c { s5 with scratch :=
                            { s5.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                        (fun (it, ()) _ => cv0 - it.toNat)
                        (fun Jt hJt => by
                          m6b_let
                          exact hJt (0#64, ()) m5
                            ⟨s5.scratch.tarjan_mark, hdw5.1.scratch_ok.tarjan_mark_len,
                             Nat.zero_le _, hm5⟩)
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
                        let sf := { s5 with scratch :=
                          { s5.scratch with tarjan_mark := tmkt, res_sz := 0#64, ant_sz := 0#64 } }
                        have hdwf := m7_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64
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
                  · have hg_le_co : g_len.toNat ≤ ctrl_off := by
                      have h := bv64_ule_true_le hc
                      rwa [show (8 : BitVec 64) = 8#64 from rfl, hco_n] at h
                    clear hc; m6b_steps
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
                        exact hJs (0#64, ()) m4
                          ⟨s4.scratch.scratch_buf, hdw4.1.scratch_ok.scratch_buf_len,
                           Nat.zero_le _, fun _ _ => rfl, fun _ h => by simp at h, hm4⟩)
                      (fun Js (i3, ()) ms ⟨scri, hscrl_i, hi3_le, hpref_i, hinit_i, hms⟩ ihs => ?_)
                    m6b_split
                    · have hi3_lt : i3.toNat < ht_sz.toNat := bv64_ult_lt hc
                      have hi3_1 : (i3 + 1#64).toNat = i3.toNat + 1 := bv64_add1_lt (by omega)
                      have hadd_n : (ht_off + i3).toNat = ht_off.toNat + i3.toNat := by
                        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                      have hadd_arr : (ht_off + i3).toNat < scri.length := by rw [hadd_n]; omega
                      clear hc; m6b_steps; rw [hadd_n] at hm
                      obtain ⟨hpref_i', hinit_i'⟩ :=
                        m7_cd_ht_set_step (by omega) hpref_i hinit_i (by omega)
                      exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                        ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i],
                         by rw [hi3_1]; omega, hpref_i', hi3_1 ▸ hinit_i', hm⟩
                    · have hi3_eq : i3.toNat = ht_sz.toNat := by
                        have := bv64_ult_not_lt hc; omega
                      rw [hi3_eq] at hinit_i
                      obtain ⟨hpref4, hht4⟩ :=
                        m7_cd_ht_clear_inv (F_cur := F_cur) (cv0 := cv0) hpref_i hinit_i
                      have hctrl_st := m7_cd_ctrl_store_layout hg_le_co (by omega) ho_pos
                        ho_512 hopow hht_pos (by omega) hc_cap hc8 hcq hqi hib hbh hhc
                        hscrl_i hpref4 (hcv40 ▸ hht4)
                      clear hc; m6b_steps
                      have hco_add : ∀ j : BitVec 64, j.toNat < 8 →
                          (BitVec.ofNat 64 ctrl_off + j).toNat = ctrl_off + j.toNat := fun j hj =>
                        by rw [BitVec.toNat_add, bv64_ofNat_toNat_lt (by omega),
                          Nat.mod_eq_of_lt (by omega)]
                      have hbkt_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv).toNat =
                          bkt_off := by
                        dsimp only [bkt_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                          change occ_bkt ≤ ht_off.toNat; omega))]
                      have hinq_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                          occ_bkt_bv).toNat = inq_off := by
                        dsimp only [inq_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hbkt_n]; omega)),
                          hbkt_n]
                      have hq_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                          occ_bkt_bv - occ_bkt_bv).toNat = q_off := by
                        dsimp only [q_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hinq_n]; omega)),
                          hinq_n]
                      simp only [show (8 : BitVec 64) = 8#64 from rfl, hco_eq,
                        bv64_ofNat_toNat_lt (by omega : ctrl_off < 2 ^ 64),
                        hco_add 1 (by decide), hco_add 2 (by decide), hco_add 3 (by decide),
                        hco_add 4 (by decide), hco_add 5 (by decide), hco_add 6 (by decide),
                        hco_add 7 (by decide),
                        bv64_setWidth32_eq (rfl : occ_bkt_bv.toNat = occ_bkt),
                        bv64_setWidth32_eq hbkt_n, bv64_setWidth32_eq hinq_n,
                        bv64_setWidth32_eq hq_n,
                        bv64_setWidth32_eq (rfl : ht_sz.toNat = ht_sz.toNat)] at hm
                      rw [show (8 : BitVec 64) = 8#64 from rfl, hco_eq]
                      m6b_call hWork
                      refine ⟨c, F0, F_cur, _, s4.scratch.scratch_buf, occ_bkt,
                        bkt_off, inq_off, q_off, ht_off.toNat, ht_sz.toNat, R, rfl,
                        m7_denseInvW_with_scr_res0 hdw4 hctrl_st.1,
                        hcv40 ▸ hrepr4_inv, hg_pos, by omega,
                        by rw [bv64_ofNat_toNat_lt (by omega)]; exact hctrl_st.2.1,
                        hseq4,
                        hctrl_st.2.2.1, hcv40 ▸ hctrl_st.2.2.2,
                        hm, fun r4 s4w m4w hdw4w hcv4w hfl4w hrepr4w _hr4_dom hr4_uns hm4w => ?_⟩
                      have hcv4w0 : s4w.core.cur_vars = cv0 := hcv4w.trans hcv40
                      have hfl4w0 : s4w.core.fuel = fuel0 := hfl4w.trans hfl40
                      m6b_split
                      · m6b_steps
                        refine wp_loop_inv (ts := [i64])
                          (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                            tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                            (FullMem c { s4w with scratch :=
                              { s4w.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                          (fun (it, ()) _ => cv0 - it.toNat)
                          (fun Jt hJt => by
                            m6b_let
                            exact hJt (0#64, ()) m4w
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
                            (m7_denseInvW_with_tmk_ar hdw4w htlt 0#64 0#64).toDense
                            hcv4w0 hfl4w0 (Or.inr rfl) (fun _ => hr4_uns (beq_iff_eq.mp hc)) hm
                      · m6b_let
                        exact hJwl_if (_, ()) m4w
                          ⟨s4w, hdw4w, hcv4w0, hfl4w0, hcv4w0 ▸ hcv4w ▸ hrepr4w, hm4w⟩
                  · clear hc; m6b_let
                    exact hJwl_if (i, ()) m4
                      ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩
                · clear hc; m6b_let
                  exact hJwl_if (i, ()) m4
                    ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩)
              ?_
            intro Jite hJite
            m6b_split
            · have hgl32 : (g_len0.setWidth 32).toNat = g_len0.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              have hgc32 : (g_cap.setWidth 32).toNat = g_cap.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              clear hc; m6b_steps; m6b_call hIteAll
              refine FullM7CongIte.m7ExtractIteAllM6Spec_of hdw4a.1 hdw4a.2.1 hdw4a.2.2.2.2.2.2
                (by rw [hgl32, hgc32]; exact hgl0_le) (by rw [hgc32]; omega)
                (by rw [hgl32, hcv4a]; exact hseq4a) hm4a
                fun ret32 s4b m4b hlen4b hcore4b hll4b hel4b hg_lo hg_hi _hpref hseq4b hm4b => ?_
              have hret64 : (ret32.setWidth 64).toNat = ret32.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ret32.isLt; omega)]
              have hdw4b := m7_denseInvW_after_iteAll hdw4a hlen4b hcore4b hll4b hel4b
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

end M7CongDense

/-! ## 2. `FullM7.full_search_m6` (`[405]`) & `5`-Fn Tail (`[405..409]`) -/

section M7OrchTail

private def m7SearchVariant (c : FullCfg) (s : FullState) : Nat :=
  (c.max_vars + 1) * s.core.fuel.toNat + (c.max_vars - s.core.trail_end)

private theorem m7Hdr_call_luckyLate_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM7Search.m7LuckyLateSpec (c.hdr, ()) m Q' X' →
      Γ "full_lucky_late_m7" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_lucky_late_m7" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (FullM7Search.m7LuckyLateSpec_of hinv.sparse
    ((fullM6HdrMem_iff c ext s R m).mp hm)
    fun r s' m' hlen hr hfu hpr h20 h02 h10 hm' => ?_)
  exact hk r s' m' hlen hr hfu hpr h20
    (fun h => let x := h02 h; ⟨FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk x.1, x.2⟩)
    h10 ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_fullPropagate_invW {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullPropagateSpec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → FullTrailExt s.core s'.core →
      FullArenaPermEq s.core s'.core → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' s'
    hlen' hw' htr' hperm' hfu' hdom hr0 hr1 hr2 hno hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' htr' hperm' hfu' hdom hr0 hr1 hr2 hno
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_m7SwitchMode_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM7Search.m7SwitchModeSpec (c.hdr, ()) m Q' X' →
      Γ "full_switch_mode_m7" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_switch_mode_m7" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (FullM7Search.m7SwitchModeSpec_of hinv.sparse.lengths
    ((fullM6HdrMem_iff c ext s R m).mp hm) fun s' m' hcore hlen hpr _ _ _ hm' => ?_)
  have hinv' : FullM6HdrInv c F0 ext s' :=
    fullM6HdrInv_of_core_eq hinv hlen hcore hpr.1
  exact hk s' m' hinv' hcore hpr ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_m7Rephase_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m7RephaseSpec (c.hdr, ()) m Q' X' →
      Γ "full_rephase" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_rephase" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (m7RephaseSpec_of hinv.sparse ((fullM6HdrMem_iff c ext s R m).mp hm) ?_)
  intro vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' hsp' _ _ _ hfu' _ _ hm'
  exact hk _ m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext _ R m').mpr hm')

private theorem m7Hdr_call_m7Decide_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM7Search.m7DecideSpec (c.hdr, ()) m Q' X' →
      Γ "full_decide_m7" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → (r = 0#64 ∨ r = 1#64) →
      s'.core.fuel = s.core.fuel →
      (r = 0#64 → s'.core.cur_level = s.core.cur_level ∧ s'.core.trail_end = s.core.trail_end) →
      (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧
        s'.core.trail_end = s.core.trail_end + 1) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_decide_m7" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X (FullM7Search.m7DecideSpec_of hcore.coreInv
    ((fullM6HdrMem_iff c ext s R m).mp hm) ?_)
  intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m' s'
    hc' hpres' hdom h0 h1 hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext s' :=
    FullM6HdrInv.mk_inv hcore.cfgOk hcore.extOk ⟨hc', hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk r s' m' hinv' hdom rfl h0 (fun hr1 => ⟨(h1 hr1).1, (h1 hr1).2.1⟩)
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_m6Analyze_invW {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m6HdrAnalyzeSpec (c.hdr, ()) m Q' X' →
      Γ "full_analyze_m6_hdr" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hcok : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6HdrAnalyzeSpec_of hinv hcok hm
    fun r ext' s' m' hext' hlen' hr _ hfu _ hu _ h1 hm' =>
      hk r ext' s' m' hext' hlen' hr hfu hu h1 hm')

private theorem m7Hdr_call_m6Reduce_invW {Γ : Env} {force : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, force, ()))
    (hΓ : ∀ Q' X', m6ReduceSpec (c.hdr, force, ()) m Q' X' →
      Γ "full_reduce_m6" [i64, .bool] [i64] (c.hdr, force, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reduce_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6ReduceSpec_of hinv hm fun r ext' s' m' hinv' hr _ hfu _ _ _ _ hu _ _ hm' =>
    hk r ext' s' m' hinv' hr hfu hu hm')

private theorem m7Hdr_call_fullRestartDue_inv_exact {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullRestartDueSpec (c.hdr, ()) m Q' X' →
      Γ "full_restart_due" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (r = 0#64 ∨ r = 1#64) → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_restart_due" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse.lengths,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen ⟨hdom, hpres⟩ hm'
  have hceq : s'.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s' hcore
  have hinv' : FullM6HdrInv c F0 ext s' :=
    fullM6HdrInv_of_core_eq hinv hlen hceq hpres
  exact hk r s' m' hinv' hceq hdom ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_fullRestart_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullRestartSpec (c.hdr, ()) m Q' X' →
      Γ "full_restart" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel = s.core.fuel → FullExtScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_restart" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hcore.coreInv,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hc' hcl' hpres' hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext s' :=
    FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk ⟨hc', hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk s' m' hinv' hcl' rfl hpres' ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_m4Reorder_inv {Γ : Env} {budget : BitVec 64} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, budget, ()))
    (hΓ : ∀ Q' X', FullM4.m4ReorderSpec (c.hdr, budget, ()) m Q' X' →
      Γ "full_reorder_m6" [i64, i64] [i64] (c.hdr, budget, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reorder_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r s' m' hsp' _ _ hfu' hm'
  exact hk r s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m7Hdr_call_m6Simplify_inv {Γ : Env} {dp de : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, dp, de, ()))
    (hΓ : ∀ Q' X', fullM6SimplifySpec (c.hdr, dp, de, ()) m Q' X' →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] (c.hdr, dp, de, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
      (m' : Mem 64),
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_simplify_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (fullM6SimplifySpec_of hinv hm hk)

/-- Parametric `Func.wp` proof for `FullM7.full_search_m6_body` against canonical
`FullM6.fullM6SearchSpec` (calling `full_lucky_late_m7` once before `while (true)` per `#3909`,
using canonical `Full.fullPropagateSpec`, `m7SwitchModeSpec`, `m7RephaseSpec`, `m7DecideSpec`). -/
theorem full_search_m6_m7_wp (Γ : Env)
    (hLuckyLate : ∀ a m Q X, FullM7Search.m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, FullM7Search.m7SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m7RephaseSpec a m Q X →
      Γ "full_rephase" [i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM7Search.m7DecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SearchSpec a m Q X →
      Func.wp Γ FullM7.full_search_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6SearchSpec_elim hs with ⟨c0, F0, ext0, s0, R, rfl, hinv0, _, hm0, hQ⟩
  unfold Func.wp FullM7.full_search_m6_body
  c0_hsteps_nogrp
  refine m7Hdr_call_luckyLate_inv rfl (hLuckyLate _ _) hinv0 hm0 ?_
  intro lkr s_lk m_lk hlen_lk hdom_lk _ _ h20_lk h02_lk h10_lk hm_lk
  c0_hsteps_nogrp
  · have hl := hc; rw [hl]
    exact hQ 10#64 c0 ext0 s_lk m_lk (FullCfgCompat.refl c0) hlen_lk hinv0.cfgOk hinv0.extOk
      (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => h10_lk hl) hm_lk
  · have hl := hc; rw [hl]
    exact hQ 20#64 c0 ext0 s_lk m_lk (FullCfgCompat.refl c0) hlen_lk hinv0.cfgOk hinv0.extOk
      (Or.inr (Or.inr rfl)) (fun _ => h20_lk hl) (fun h => by cases h) hm_lk
  · have hlkr02 : lkr = 0#64 ∨ lkr = 2#64 := by
      rcases hdom_lk with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl (by assumption)
      · exact absurd rfl hc
    have hinv_lk := (h02_lk hlkr02).1
    refine wp_while_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState) Prod.fst
      (fun ⟨_, c, _, s⟩ => m7SearchVariant c s)
      (fun ⟨_, c, ext, s⟩ ml =>
        FullCfgCompat c0 c ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) ml)
      (fun J hJ => by
        c0_hsteps
        exact hJ (10000#64, c0, ext0, s_lk) m_lk ⟨FullCfgCompat.refl c0, hinv_lk, hm_lk⟩)
      ?_
    rintro J ⟨rlim, c, ext, s⟩ ml ⟨hcompat, hinv, hml⟩ ih
    rw [← hcompat.hdr]
    have hsp := hinv.sparse
    have hlen := hsp.lengths
    have hmx : c.max_vars < 2 * 268435456 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
    have hml_f := fullM6HdrMem_focus hml
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    · -- `h->oom != 0ULL`
      exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => absurd hc (by decide)) (fun hc => absurd hc (by decide)) hml
    · -- `h->fuel == 0ULL`
      exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => absurd hc (by decide)) (fun hc => absurd hc (by decide)) hml
    · -- `oom == 0` and `fuel != 0`: propagate
      have hfu_pos : 0 < s.core.fuel.toNat := by
        have hpos : s.core.fuel.toNat ≠ 0 :=
          fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        omega
      obtain ⟨F_cur, hinvW⟩ := fullM6HdrInv_exists_witness hinv
      refine m7Hdr_call_fullPropagate_invW rfl (hProp _ _) hinvW hml ?_
      intro pr s1 m1 hinvW1 htr1 _ hfu1 hdom1 _ hr1 _ _ hm1
      have hinv1 := hinvW1.toInv
      have hlen1 := hinv1.sparse.lengths
      have hm1_f := fullM6HdrMem_focus hm1
      c0_hsteps
      · -- `pr == 2#64`: return `0#64`
        exact hQ 0#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
          (fun hc => by cases hc) (fun hc => by cases hc) hm1
      · -- `pr == 1#64`: conflict!
        have hpr1 : pr = 1#64 := hc
        obtain ⟨hfu_lt, _, hcok1⟩ := hr1 hpr1
        have hmu_conf : ∀ {c' : FullCfg} {ext' : List (BitVec 64)} {s' : FullState},
            c'.max_vars = c.max_vars → s'.core.fuel.toNat ≤ s1.core.fuel.toNat →
            FullM6HdrInv c' F0 ext' s' → m7SearchVariant c' s' < m7SearchVariant c s := by
          intro c' ext' s' hmveq hfule hinv'
          unfold m7SearchVariant
          rw [hmveq]
          have h1 : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by omega
          have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
              (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
            Nat.mul_le_mul_left (c.max_vars + 1) h1
          have hte' : s'.core.trail_end ≤ c'.max_vars :=
            Nat.le_trans hinv'.sparse.lengths.core_ok.trail_end_le
              hinv'.sparse.lengths.core_ok.cur_vars_le
          have h2 : c.max_vars - s'.core.trail_end ≤ c.max_vars := Nat.sub_le _ _
          have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
              (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
            have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
            calc (c.max_vars + 1) * s.core.fuel.toNat
                = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
              _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
          omega
        refine m7Hdr_call_m6Analyze_invW rfl (hAnalyze _ _) hinvW1 hcok1 hm1 ?_
        intro ast ext2 s2 m2 hext2 hlen2 hast hfu2 hu2 ha1 hm2
        have hm2_f := fullM6HdrMem_focus hm2
        c0_hsteps_nogrp
        · -- `ast == 20#64`
          exact hQ 20#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inr (Or.inr rfl))
            (fun _ => hu2 hc) (fun hc => by cases hc) hm2
        · -- `ast != 1#64`
          exact hQ 0#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inl rfl)
            (fun hc => by cases hc) (fun hc => by cases hc) hm2
        · -- `ast == 1#64`
          have hast1 : ast = 1#64 := hc
          obtain ⟨hinvW2, _⟩ := ha1 hast1
          have hinv2 := hinvW2.toInv
          let ContInv : BitVec 64 × FullCfg × List (BitVec 64) × FullState → Mem 64 → Prop :=
            fun ⟨_, c8, ext8, s8⟩ m8 =>
              FullCfgCompat c0 c8 ∧ FullM6HdrInv c8 F0 ext8 s8 ∧
              s8.core.fuel.toNat ≤ s2.core.fuel.toNat ∧ (FullM6HdrMem c8 ext8 s8 ⋆ R) m8
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
            (fun v => (v, ())) (fun _ => True) ?_
            (fun _ hJmd => by c0_hsteps <;> exact hJmd _ trivial)
          intro _ mode_due _
          c0_hsteps_nogrp
          refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
            Prod.fst ContInv ?_ ?_
          · intro _ ⟨r8, c8, ext8, s8⟩ m8 ⟨hc8, hinv8, hfu8, hm8⟩
            c0_hsteps
            exact ih (r8, c8, ext8, s8) m8
              (hmu_conf (hc8.max_vars.trans hcompat.max_vars.symm)
                (Nat.le_trans hfu8 hfu2) hinv8)
              ⟨hc8, hinv8, hm8⟩
          · intro Jr1 hJr1
            have hm2_f1 := fullM6HdrMem_focus hm2
            c0_hsplit
            · c0_hsteps
              refine m7Hdr_call_m6Reduce_invW rfl (hReduce _ _) hinvW2 hm2 ?_
              intro rr ext3 s3 m3 hinvW3 _ hfu3 hu3 hm3
              have hinv3 := hinvW3.toInv
              have hlen3 := hinv3.sparse.lengths
              c0_hsteps
              · exact hQ 20#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                  (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
              · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                  (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
              · exact hJr1 (rlim, c, ext3, s3) m3 ⟨hcompat, hinv3, hfu3, hm3⟩
            · refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                Prod.fst ContInv ?_ ?_
              · intro _ p mp hp; c0_hsteps; exact hJr1 p mp hp
              · intro Jr2 hJr2
                c0_hsplit
                · c0_hsteps
                  refine m7Hdr_call_m7SwitchMode_inv rfl (hSwitch _ _) hinv2 hm2 ?_
                  intro s3 m3 hinv3 hcore3 _ hm3
                  c0_hsteps
                  exact hJr2 (rlim, c, ext2, s3) m3
                    ⟨hcompat, hinv3, by rw [hcore3]; exact Nat.le_refl _, hm3⟩
                · refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                    Prod.fst ContInv ?_ ?_
                  · intro _ p mp hp; c0_hsteps; exact hJr2 p mp hp
                  · intro Jr3 hJr3
                    c0_hsteps
                    refine m7Hdr_call_fullRestartDue_inv_exact rfl (hRstDue _ _) hinv2 hm2 ?_
                    intro rdu s3 m3 hinv3 hcore3 _ hm3
                    have hm3_f := fullM6HdrMem_focus hm3
                    c0_hsplit
                    · c0_hsteps
                      refine m7Hdr_call_fullRestart_inv rfl (hRst _ _) hinv3 hm3 ?_
                      intro s4 m4 hinv4 _ hfu4 _ hm4
                      c0_hsteps
                      exact hJr3 (rlim, c, ext2, s4) m4
                        ⟨hcompat, hinv4, by rw [hfu4, hcore3]; exact Nat.le_refl _, hm4⟩
                    · refine wp_join_state1
                        (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                        Prod.fst ContInv ?_ ?_
                      · intro _ p mp hp; c0_hsteps; exact hJr3 p mp hp
                      · intro Jr4 hJr4
                        c0_hsteps
                        · -- `stable == 0 && conflicts >= reorder_limit`
                          refine m7Hdr_call_m4Reorder_inv rfl (hReorder _ _) hinv3 hm3 ?_
                          intro _r s4 m4 hinv4 hfu4 hm4
                          c0_hsteps
                          exact hJr4 (s3.scratch.conflicts + 10000#64, c, ext2, s4) m4
                            ⟨hcompat, hinv4, by rw [hfu4, hcore3]; exact Nat.le_refl _, hm4⟩
                        all_goals
                          have hm3_f' := fullM6HdrMem_focus hm3
                          first
                          | exact hJr4 (rlim, c, ext2, s3) m3
                              ⟨hcompat, hinv3, by rw [hcore3]; exact Nat.le_refl _, hm3⟩
                          | (refine m7Hdr_call_m7Rephase_inv rfl (hRephase _ _) hinv3 hm3 ?_
                             intro s4 m4 hinv4 hfu4 hm4
                             c0_hsteps
                             exact hJr4 (rlim, c, ext2, s4) m4
                               ⟨hcompat, hinv4, by rw [← hcore3]; exact hfu4, hm4⟩)
                          | (refine m7Hdr_call_m6Simplify_inv (dp := true) (de := false)
                               rfl (hSimplify _ _) hinv3 hm3 ?_
                             intro sr c4 ext4 s4 m4 hcomp4 hlen4 hcfg4 hext4 _hsr hfu4 hu4 hs1 hm4
                             have hcompat4 := hcompat.trans hcomp4
                             c0_hsteps
                             · exact hQ 20#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                                 (Or.inr (Or.inr rfl)) (fun _ => hu4 hc) (fun hc => by cases hc)
                                 hm4
                             · exact hQ 0#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                                 (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm4
                             · obtain ⟨hinv4, _⟩ := hs1 hc
                               exact hJr4 (rlim, c4, ext4, s4) m4
                                 ⟨hcompat4, hinv4, by rw [← hcore3]; exact hfu4, hm4⟩)
                          | (refine m7Hdr_call_m6Simplify_inv (dp := false) (de := true)
                               rfl (hSimplify _ _) hinv3 hm3 ?_
                             intro sr c4 ext4 s4 m4 hcomp4 hlen4 hcfg4 hext4 _hsr hfu4 hu4 hs1 hm4
                             have hcompat4 := hcompat.trans hcomp4
                             c0_hsteps
                             · exact hQ 20#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                                 (Or.inr (Or.inr rfl)) (fun _ => hu4 hc) (fun hc => by cases hc)
                                 hm4
                             · exact hQ 0#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                                 (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm4
                             · obtain ⟨hinv4, _⟩ := hs1 hc
                               exact hJr4 (rlim, c4, ext4, s4) m4
                                 ⟨hcompat4, hinv4, by rw [← hcore3]; exact hfu4, hm4⟩)
      · -- `pr == 0#64`: unassigned == 0
        exact hQ 10#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inr (Or.inl rfl))
          (fun hc => by cases hc) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
      · -- `pr == 0#64`: `full_decide_m7(h)`
        refine m7Hdr_call_m7Decide_inv rfl (hDecide _ _) hinv1 hm1 ?_
        intro dr s2 m2 hinv2 hdomd hfu2 h0d h1d hm2
        have hlen2 := hinv2.sparse.lengths
        have hm2_f := fullM6HdrMem_focus hm2
        c0_hsteps
        · exact hQ 10#64 c ext s2 m2 hcompat hlen2 hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inl rfl)) (fun hc => by cases hc)
            (fun _ => hinv2.sparse.2.2.2.1.2) hm2
        · exact hQ 0#64 c ext s2 m2 hcompat hlen2 hinv2.cfgOk hinv2.extOk
            (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm2
        · -- `dr == 1#64`: continue loop!
          have hdr1 : dr = 1#64 := hdomd.resolve_left hc
          obtain ⟨_, hte2⟩ := h1d hdr1
          have hte_lt : s.core.trail_end < s2.core.trail_end := by
            have := htr1.1; omega
          have hte2_le : s2.core.trail_end ≤ c.max_vars :=
            Nat.le_trans hlen2.core_ok.trail_end_le hlen2.core_ok.cur_vars_le
          have hmu_dec : m7SearchVariant c s2 < m7SearchVariant c s := by
            unfold m7SearchVariant
            rw [hfu2]
            have hmul : (c.max_vars + 1) * s1.core.fuel.toNat ≤
                (c.max_vars + 1) * s.core.fuel.toNat :=
              Nat.mul_le_mul_left (c.max_vars + 1) hfu1
            have hte0_le : s.core.trail_end ≤ c.max_vars :=
              Nat.le_trans hlen.core_ok.trail_end_le hlen.core_ok.cur_vars_le
            omega
          exact ih (rlim, c, ext, s2) m2 hmu_dec ⟨hcompat, hinv2, hm2⟩

/-- Tail `5` specification rows aligned 1-to-1 with `FullM7.m7FnsPart3.drop 129`. -/
def m7OrchTailRows
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  [ ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_search", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩ ]

theorem m7OrchTailRows_sigs
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m7OrchTailRows solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      (m7FnsPart3.drop 129).map Fn.sig := by
  unfold m7OrchTailRows m7FnsPart3
  t_kernel_rfl

theorem m7OrchTailRows_noExit
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m7OrchTailRows solveSpec).all SpecEntry.noExit = true := by
  unfold m7OrchTailRows
  rfl

theorem m7OrchTail_solve_mem (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7OrchTailRows solveSpec ∧
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7OrchTailRows solveSpec :=
  ⟨ List.mem_of_getElem? (i := 1) rfl, List.mem_of_getElem? (i := 4) rfl ⟩

/-- `5`-fn orchestration tail (`FullM7.m7FnsPart3.drop 129`, `full_search_m6` through
`kissat_solve_bytes`). -/
def m7OrchTailFns : List Fn :=
  [ ⟨"full_search_m6", [i64], [i64], FullM7.full_search_m6_body⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_m6_body⟩
  , ⟨"full_preprocess", [i64], [i64], FullM6Orch.full_preprocess_body⟩
  , ⟨"full_search", [i64], [i64], FullM6Orch.full_search_body⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_body⟩ ]

private theorem m7OrchTailFns_eq_drop :
    m7FnsPart3.drop 129 = m7OrchTailFns := by
  unfold m7OrchTailFns m7FnsPart3; t_kernel_rfl

/-- Parametric `TableImpl` for `m7OrchTailFns` (`FullM7.m7FnsPart3.drop 129`) against
`m7OrchTailRows solveSpec`. -/
theorem m7OrchTail_tableImpl (Γ : Env)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hLuckyLate : ∀ a m Q X, FullM7Search.m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, FullM7Search.m7SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m7RephaseSpec a m Q X →
      Γ "full_rephase" [i64] [] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM7Search.m7DecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X)
    (hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Γ "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    TableImpl Γ m7OrchTailFns (m7OrchTailRows solveSpec) := by
  unfold m7OrchTailFns m7OrchTailRows
  refine tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
      wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
    (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
        wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
      (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
          wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
        (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
            wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
          (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
              wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
            (tableImpl_nil Γ [])))))
  · exact full_search_m6_m7_wp Γ hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst
      hReorder hRephase hSimplify hDecide xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_m6_core_wp Γ hMemInit hParse hPre hSearchM6 hExt hCheck xs m Q
      (fun _ _ _ _ => False) (hWeaken xs m Q (fun _ _ _ _ => False) hs)
  · exact full_preprocess_wp Γ hPre xs m Q (fun _ _ _ _ => False) hs
  · exact full_search_wp Γ hSearchM6 xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_core_wp Γ solveSpec hSolveM6 xs m Q (fun _ _ _ _ => False) hs

/-- Certifies all `134` functions of `FullM7.m7FnsPart3` against
`m7RowsPart3Pfx tPfx tBve ++ m7OrchTailRows solveSpec` in `Env.ofTable tbl`. -/
theorem m7Part3_tableImpl {tPfx tBve tbl : List SpecEntry}
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hnoExit : tbl.all SpecEntry.noExit = true)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxOk : TableImpl (Env.ofTable tbl) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveOk : TableImpl (Env.ofTable tbl) m7BveAllFns tBve)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (htBve : ∀ e ∈ tBve, e ∈ tbl)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hc1 : M7Part1Callees tbl) (hc2 : M7Part2Callees tbl)
    (ht1Mem : (⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
        fullM6MemInitExactSpec, true⟩ : SpecEntry) ∈ tbl ∧
      (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
        kissatCheckModelExactSpec, true⟩ : SpecEntry) ∈ tbl)
    (hOwnPfx : ∀ e ∈ m7RowsPart3Pfx tPfx tBve, e ∈ tbl)
    (hOwnTail : ∀ e ∈ m7OrchTailRows solveSpec, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m7FnsPart3
      (m7RowsPart3Pfx tPfx tBve ++ m7OrchTailRows solveSpec) := by
  have hPfxLen : m7OrchPfxFns.length = tPfx.length := by
    have h1 := (congrArg List.length hPfxSigs).symm
    simpa only [List.length_map] using h1
  have hBveLen : m7BveAllFns.length = tBve.length := by
    have h1 := (congrArg List.length hBveSigs).symm
    simpa only [List.length_map] using h1
  have h129_len : (m7FnsPart3.take 129).length = (m7RowsPart3Pfx tPfx tBve).length := by
    have h1 := (congrArg List.length (m7RowsPart3Pfx_sigs hPfxSigs hBveSigs)).symm
    simpa only [List.length_map] using h1
  have hc3 := m7Part3TailCallees_of_sub hOwnPfx
  have rParseBody := htPfx _ hPfxSpecs.parseBody
  have rReduceM6 := htPfx _ hPfxSpecs.reduceM6
  have rReorderM6 := htPfx _ hPfxSpecs.reorderM6
  have rPreM6 := htPfx _ hPfxSpecs.preprocessM6
  have rSimpM6 := htPfx _ hPfxSpecs.simplifyM6
  have rSrchM6 : (⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ : SpecEntry) ∈ tbl :=
    hOwnTail _ (List.mem_of_getElem? (i := 0) rfl)
  have rSolveM6 : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ tbl :=
    hOwnTail _ (List.mem_of_getElem? (i := 1) rfl)
  have i_pfx := m7RowsPart3Pfx_tableImpl hnd hPfxLen hPfxOk hBveLen hBveOk hBveSpecs htBve
    hPfxSpecs htPfx hc1 hc2 hOwnPfx
  have hLkLate := envRow_mem hnd _ _ _ _ hc3.luckyLateM7
    (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h)
  have hMi := envRow_mem hnd _ _ _ _ ht1Mem.1
    (fun _ _ _ _ h => fullM6MemInitExactSpec_monoX h)
  have hPb := envRow_mem hnd _ _ _ _ rParseBody
  have hPr := envRow_mem hnd _ _ _ _ hc1.propagate
  have hAn := envRow_mem hnd _ _ _ _ hc2.analyzeM6 (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h)
  have hRd := envRow_mem hnd _ _ _ _ rReduceM6 (fun _ _ _ _ h => m6ReduceSpec_monoX h)
  have hSw := envRow_mem hnd _ _ _ _ hc3.switchModeM7
    (fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h)
  have hRdDue := envRow_mem hnd _ _ _ _ hc2.restartDue
  have hRst := envRow_mem hnd _ _ _ _ hc2.restart
  have hReord := envRow_mem hnd _ _ _ _ rReorderM6
  have hReph := envRow_mem hnd _ _ _ _ hc2.rephase (fun _ _ _ _ h => m7RephaseSpec_monoX h)
  have hPreM6 := envRow_mem hnd _ _ _ _ rPreM6 (fun _ _ _ _ h => fullM6PreprocessSpec_monoX h)
  have hSimp := envRow_mem hnd _ _ _ _ rSimpM6 (fun _ _ _ _ h => fullM6SimplifySpec_monoX h)
  have hDec := envRow_mem hnd _ _ _ _ hc3.decideM7
    (fun _ _ _ _ h => FullM7Search.m7DecideSpec_monoX h)
  have hExt := envRow_mem hnd _ _ _ _ hc2.extend
  have hChk := envRow_mem hnd _ _ _ _ ht1Mem.2
  have hSrch := envRow_mem hnd _ _ _ _ rSrchM6 (fun _ _ _ _ h => fullM6SearchSpec_monoX h)
  have hSlv : ∀ a m Q X, solveSpec a m Q X →
      Env.ofTable tbl "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X :=
    fun a m Q X hs => env_ofTable_noExit_all hnoExit _ _ _ _ _ _ (fun _ _ _ _ => False) X
      (Env.ofTable_of_mem rSolveM6 hnd (hSolveMonoX a m Q X (fun _ _ _ _ => False) hs))
  have i_tail := m7OrchTail_tableImpl (Env.ofTable tbl) solveSpec hWeaken
    hLkLate hMi hPb hPr hAn hRd hSw hRdDue hRst hReord hReph hPreM6 hSimp hDec hExt hChk hSrch hSlv
  have h129 : m7FnsPart3.take 129 ++ m7OrchTailFns = m7FnsPart3 := by
    rw [← m7OrchTailFns_eq_drop, List.take_append_drop]
  rw [← h129]
  exact tableImpl_append h129_len i_pfx i_tail

end M7OrchTail

end LeanQbe.T.Examples.Kissat.FullM7Proof

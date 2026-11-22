module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2d

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 2e

Builds on `FullM6CongSubstProof2d` to prove the top-level congruence closure
parametric `(Γ : Env)` `Func.wp` contract (`FullM6CongSubst.lean` #23):
23. `full_congruence_dense` (`full_congruence_dense_wp`, `m3CongruenceDenseSpec`)

All proofs operate strictly within UNSAT-only `FullDenseInvW` / `FullDenseInv` /
`M6CongHtInv` / `M6CtrlLayout` invariants (complete proofs, default heartbeats, `<= 100` c/l).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva (m3CongruenceDenseSpec)
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullCongTactics M6bHeadTactics

section CongruenceDenseHelpers

private theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) :
    ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem m6_denseInvW_with_antsz_ressz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩, hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m6_denseInvW_with_tmk_ar {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch :=
        { s.scratch with tarjan_mark := tmk', ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with tarjan_mark_len := ht }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m6_denseInvW_with_scr_res0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hsl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := 0#64 } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hsl }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem bv64_setWidth32_eq {x : BitVec 64} {n : Nat} (hx : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  subst hx; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem m6_cd_ht_pow_step {ht_sz : BitVec 64} {k cap : Nat}
    (hk : k ≤ 6) (heq : ht_sz.toNat = 64 * 2 ^ k)
    (hlt : ht_sz.toNat < 4096) (hmul : ht_sz.toNat * 8 ≤ cap) :
    k + 1 ≤ 6 ∧ (ht_sz <<< 1#64).toNat = 64 * 2 ^ (k + 1) ∧
    (ht_sz <<< 1#64).toNat ≤ 4096 ∧ (ht_sz <<< 1#64).toNat ≤ cap := by
  have hk_lt : k < 6 :=
    Nat.lt_of_le_of_ne hk fun h => by subst h; rw [heq] at hlt; simp at hlt
  have h2k_le : 2 ^ k ≤ 32 := by
    match k, hk_lt with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  have h512 : 512 * 2 ^ k ≤ cap := by rw [heq] at hmul; omega
  have hshl : (ht_sz <<< 1#64).toNat = 2 * ht_sz.toNat := by
    rw [show (ht_sz <<< 1#64 : BitVec 64) = ht_sz <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpow : 64 * 2 ^ (k + 1) = 2 * (64 * 2 ^ k) := by rw [Nat.pow_succ]; omega
  refine ⟨by omega, by rw [hshl, heq, hpow], by rw [hshl, heq]; omega,
    by rw [hshl, heq]; omega⟩

private theorem m6_cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * dimacsBound)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  unfold dimacsBound at hmax
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem m6_cd_ht_clear_inv {F_cur : List (List Nat)} {cv0 g_len ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinit : ∀ k < ht_sz, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    (∀ idx < g_len, scri[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv0 scr0 scri g_len ht_off ht_sz :=
  ⟨hpref, fun k hk => Or.inl (hinit k hk)⟩

private theorem m6_cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
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

private theorem m6_cd_layout_params {ht_off ht_sz cap : Nat}
    (h256 : 256 ≤ cap) (hht_pos : 0 < ht_sz) (hht_4k : ht_sz ≤ 4096)
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

private theorem m6_cd_ctrl_store_layout {c : FullCfg} {F_cur : List (List Nat)} {cv0 : Nat}
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
  have hsc := c.hscr; unfold dimacsBound at hsc
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
    exact (congrArg (Option.getD · 0#32) h0)
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

private theorem m6_cd_gcap_le {ctrl_off : Nat} (hcap : ctrl_off < 2 ^ 28) :
    ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64).toNat ≤ ctrl_off := by
  have hmul : (BitVec.ofNat 64 ctrl_off * 3#64).toNat = ctrl_off * 3 := by
    rw [BitVec.toNat_mul, bv64_ofNat_toNat_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [show ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64 : BitVec 64) =
      (BitVec.ofNat 64 ctrl_off * 3#64) >>> (2 : Nat) from rfl,
    BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow]
  omega

private theorem m6_cd_ctrl_off_toNat {cap : Nat} {ht_sz occ : BitVec 64}
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

end CongruenceDenseHelpers

/-! ## `#23` `full_congruence_dense_wp` (`m3CongruenceDenseSpec`) -/

section CongruenceDenseProof

theorem full_congruence_dense_wp (Γ : Env)
    (hExtBin : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m6CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m6CongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  obtain ⟨hlen0, ⟨F_cur, hw0⟩⟩ := hden0.1
  have hdw0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hlen0, hw0, hden0.2.1, hden0.2.2.1, hden0.2.2.2.1, hden0.2.2.2.2.1, hden0.2.2.2.2.2⟩
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have hcv_le : cv0 ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  unfold Func.wp full_congruence_dense_body
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
        m6_denseInvW_with_antsz_ressz hdw0 0#64 s0.scratch.res_sz
      m6b_call hExtBin
      refine ⟨c, F0, F_cur, s0a, R, rfl, hdw0a, hm,
        fun r1 s1 m1 hdw1 hcv1 hfl1 hr1_dom hr1_uns hm1 => ?_⟩
      have hcv10 : s1.core.cur_vars = cv0 := hcv1
      m6b_split
      · m6b_steps
        exact hQ 20#64 _ m (m6_denseInvW_with_antsz_ressz hdw1 0#64 s1.scratch.res_sz).toDense
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
            exact m6_cd_repr_init_inv hrl hcv_le hmx hinit
          clear hc; m6b_steps; m6b_call hFindUE
          refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, hrepr2, hmi,
            fun r2 s3 m3 hdw3 hcv3 hfl3 hrepr3 hr2_dom hr2_uns hm3 => ?_⟩
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
              exact hQ 20#64 _ m (m6_denseInvW_with_tmk_ar hdw3 htlt 0#64 0#64).toDense
                hcv30 hfl30 (Or.inr rfl) (fun _ => hr2_uns (beq_iff_eq.mp hc)) hm
          · clear hc; m6b_steps
            refine wp_loop_inv (ts := [i64])
              (fun (ht_sz, ()) mht => mht = m3 ∧ ∃ k : Nat,
                k ≤ 6 ∧ ht_sz.toNat = 64 * 2 ^ k ∧ ht_sz.toNat ≤ 4096 ∧
                ht_sz.toNat ≤ c.scratch_cap ∧ (ht_sz = 64#64 ∨ ht_sz.toNat * 4 ≤ c.scratch_cap))
              (fun (ht_sz, ()) _ => 4096 - ht_sz.toNat)
              (fun Jht hJht => by
                m6b_let
                exact hJht (64#64, ()) m3
                  ⟨rfl, 0, Nat.zero_le _, rfl, by decide,
                   by rw [show (64#64 : BitVec 64).toNat = 64 from rfl]; omega, Or.inl rfl⟩)
              (fun Jht (ht_sz, ()) mht ⟨hmht, k, hk_le, hpow, h4k, hsc_le, hmul4⟩ ih_ht => ?_)
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
                  · have hlt : ht_sz.toNat < 4096 := bv64_ult_lt hc
                    obtain ⟨hk1, hpow1, h4k1, hsc1⟩ := m6_cd_ht_pow_step hk_le hpow hlt hmul_le
                    clear hc; m6b_steps
                    exact ih_ht (ht_sz <<< 1#64, ()) mht (by dsimp only; rw [hpow1, hpow]; omega)
                      ⟨hmht, k + 1, hk1, hpow1, h4k1, hsc1,
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
              m6_cd_layout_params h256 hht_pos h4k hmul4' hsc hht_off_n
            rw [← hocc_eq] at ho_pos ho_512 hopow hocc38 hcq hqi hib hbh hc_cap hc8
            let bkt_off := ht_off.toNat - occ_bkt
            let inq_off := bkt_off - occ_bkt
            let q_off := inq_off - occ_bkt
            let ctrl_off := q_off - 8
            have hco_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                occ_bkt_bv - occ_bkt_bv - 8#64).toNat = ctrl_off := by
              dsimp only [ctrl_off, q_off, inq_off, bkt_off]
              rw [hht_off_n]
              exact m6_cd_ctrl_off_toNat hsc_le (hht_off_n ▸ hocc38) hsc
            have hco_le_fn := m6_cd_gcap_le (by omega : ctrl_off < 2 ^ 28)
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
              fun g_len s4 m4 hdw4 hcv4 hfl4 hrepr4 hinc4 hgl_le hseq4 hm4 => ?_⟩
            have hcv40 : s4.core.cur_vars = cv0 := hcv4.trans hcv30
            have hfl40 : s4.core.fuel = fuel0 := hfl4.trans hfl30
            have hrepr4_inv : FullCongReprInv F_cur (2 * cv0) s4.core.repr := by
              rw [hrepr4, ← hcv30]; exact hrepr3
            m6b_to_group
            refine wp_join_group (ts := [i64])
              (fun (_i', ()) mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur sj ∧
                sj.core.cur_vars = cv0 ∧ sj.core.fuel = fuel0 ∧
                FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧ (FullMem c sj ⋆ R) mj)
              (fun _ ⟨_i', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, hflj, hreprj, hmj⟩ => by
                m6b_steps; m6b_call hFwdSub
                refine ⟨c, F0, F_cur, sj, R, rfl, hdj, hcvj ▸ hreprj, hmj,
                  fun r5 s5 m5 hdw5 hcv5 hfl5 hrepr5 hr5_dom hr5_uns hm5 => ?_⟩
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
                    exact hQ 20#64 _ m (m6_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64).toDense
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
                    have hdwf := m6_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64
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
                    (FullMem c { s4 with scratch := { s4.scratch with scratch_buf := scri } } ⋆ R)
                      ms)
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
                    m6_cd_ht_set_step (by omega) hpref_i hinit_i (by omega)
                  exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                    ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i],
                     by rw [hi3_1]; omega, hpref_i', hi3_1 ▸ hinit_i', hm⟩
                · have hi3_eq : i3.toNat = ht_sz.toNat := by
                    have := bv64_ult_not_lt hc; omega
                  rw [hi3_eq] at hinit_i
                  obtain ⟨hpref4, hht4⟩ :=
                    m6_cd_ht_clear_inv (F_cur := F_cur) (cv0 := cv0) hpref_i hinit_i
                  have hctrl_st := m6_cd_ctrl_store_layout hg_le_co (by omega) ho_pos
                    ho_512 hopow hht_pos (by omega) hc_cap hc8 hcq hqi hib hbh hhc
                    hscrl_i hpref4 (hcv40 ▸ hht4)
                  clear hc; m6b_steps
                  have hco_add : ∀ j : BitVec 64, j.toNat < 8 →
                      (BitVec.ofNat 64 ctrl_off + j).toNat = ctrl_off + j.toNat := fun j hj => by
                    rw [BitVec.toNat_add, bv64_ofNat_toNat_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]
                  have hbkt_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv).toNat =
                      bkt_off := by
                    dsimp only [bkt_off]
                    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                      change occ_bkt ≤ ht_off.toNat; omega))]
                  have hinq_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                      occ_bkt_bv).toNat = inq_off := by
                    dsimp only [inq_off]
                    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hbkt_n]; omega)), hbkt_n]
                  have hq_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                      occ_bkt_bv - occ_bkt_bv).toNat = q_off := by
                    dsimp only [q_off]
                    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hinq_n]; omega)), hinq_n]
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
                    m6_denseInvW_with_scr_res0 hdw4 hctrl_st.1,
                    hcv40 ▸ hrepr4_inv, hg_pos, by omega,
                    by rw [bv64_ofNat_toNat_lt (by omega)]; exact hctrl_st.2.1,
                    hcv4.symm ▸ hseq4,
                    hctrl_st.2.2.1, hcv40 ▸ hctrl_st.2.2.2,
                    hm, fun r4 s4w m4w hdw4w hcv4w hfl4w hrepr4w hr4_dom hr4_uns hm4w => ?_⟩
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
                        have h := bv64_ult_lt hc; rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                      have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                      have hit_arr : it.toNat < tmkt.length := by omega
                      clear hc; m6b_steps
                      exact iht (it + 1#64, ()) m (by dsimp only; omega)
                        ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                    · clear hc; m6b_steps
                      exact hQ 20#64 _ m
                        (m6_denseInvW_with_tmk_ar hdw4w htlt 0#64 0#64).toDense
                        hcv4w0 hfl4w0 (Or.inr rfl) (fun _ => hr4_uns (beq_iff_eq.mp hc)) hm
                  · m6b_let
                    exact hJwl_if (_, ()) m4w
                      ⟨s4w, hdw4w, hcv4w0, hfl4w0, hcv4w0 ▸ hcv4w ▸ hrepr4w, hm4w⟩
              · clear hc; m6b_let
                exact hJwl_if (i, ()) m4
                  ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩
            · clear hc; m6b_let
              exact hJwl_if (i, ()) m4
                ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩

end CongruenceDenseProof

end LeanQbe.T.Examples.Kissat.FullM6CongSubst

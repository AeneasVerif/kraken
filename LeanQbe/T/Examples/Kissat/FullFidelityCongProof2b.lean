/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2c
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat 4.0.4 Congruence Worklist Parity Proof (`FullFidelityCongProof2b`)

Proves `full_cong_worklist_wp` (`fidCongWorklistSpec`) for `full_cong_worklist_body` with wide
gates (`FidGateAt 64` / `FidGateSeqOk 64` / `FidCongHtInv 64`) and dynamic in-place HT doubling
(`do_grow`) up to `1,048,576` buckets (`GAP-CONG-01`, `GAP-CONG-03`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

section WorklistHelpers

private theorem fid_denseInvW_with_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {scr' : List (BitVec 32)}
    (hl : scr'.length = c.scratch_cap) (rs' : BitVec 64 := s.scratch.res_sz) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rs' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩, hd.2.1, hd.2.2.1,
    hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid_bkt_lt {occ_bkt : Nat} (ho_pos : 0 < occ_bkt)
    (hopow : ∃ p, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) (x : BitVec 32) :
    ((x >>> (1 : Nat)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))).toNat < occ_bkt := by
  rw [show (x >>> (1 : Nat)) = x >>> 1#32 from rfl,
    show BitVec.ofNat 32 occ_bkt - (1 : BitVec 32) = BitVec.ofNat 32 occ_bkt - 1#32 from rfl,
    m8_and_sub1_u32_eq_mod hopow]
  exact Nat.mod_lt _ ho_pos

private theorem fid_shl1_toNat {x : BitVec 64} (hlt : x.toNat < fidCongHashMaxSz) :
    (x <<< (1 : BitVec 64)).toNat = 2 * x.toNat := by
  unfold fidCongHashMaxSz at hlt
  rw [show (x <<< (1 : BitVec 64) : BitVec 64) = x <<< (1 : Nat) from rfl,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt (by omega)

private theorem fidGateSeqOk_inv_lt {maxA : Nat} {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : FidGateSeqOk maxA F_cur cur_vars scr g_len g) (hlt : g < g_len) :
    FidGateAt maxA F_cur cur_vars scr g_len g ∧
      FidGateSeqOk maxA F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) := by
  cases hs with
  | done => omega
  | step hg hrest => exact ⟨hg, hrest⟩

private theorem fid_ff24_getLsbD {i : Nat} (hi : i < 32) :
    (0x00FFFFFF#32 : BitVec 32).getLsbD i = decide (i < 24) := by
  have hall : ∀ j : BitVec 5, (0x00FFFFFF#32 : BitVec 32).getLsbD j.toNat =
      decide (j.toNat < 24) := by decide
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using hall (BitVec.ofNat 5 i)

private theorem fid_pack_entry_gn {slot gn : Nat} (_hslot : slot < 256) (hgn : gn < 2 ^ 24) :
    (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) &&& 0x00FFFFFF#32).toNat = gn := by
  have heq : (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) &&& 0x00FFFFFF#32) =
      BitVec.ofNat 32 gn := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      fid_ff24_getLsbD hi]
    by_cases hi24 : i < 24
    · simp [hi24]
    · have hgn0 : (BitVec.ofNat 32 gn).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [hi, decide_true, Bool.true_and]
        exact m6_testBit_false_of_lt
          (Nat.lt_of_lt_of_le hgn (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hi24, hgn0]
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem fid_pack_entry_slot {slot gn : Nat} (hslot : slot < 256) (hgn : gn < 2 ^ 24) :
    (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) >>> 24).toNat = slot := by
  have heq : (((BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn) >>> 24) =
      BitVec.ofNat 32 slot := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases hi8 : 24 + i < 32
    · have hgn0 : (BitVec.ofNat 32 gn).getLsbD (24 + i) = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [hi8, decide_true, Bool.true_and]
        exact m6_testBit_false_of_lt
          (Nat.lt_of_lt_of_le hgn (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [hgn0, show 24 + i - 24 = i by omega]; simp [hi8, show 24 ≤ 24 + i by omega]
    · have hlt8 : slot < 2 ^ i :=
        Nat.lt_of_lt_of_le (show slot < 2 ^ 8 from hslot)
          (Nat.pow_le_pow_right (by decide) (by omega))
      simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, eq_false hi8,
        decide_false, Bool.false_and, Bool.false_or]
      rw [m6_testBit_false_of_lt hlt8]
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem fidOccNodesOk_push {F_cur : List (List Nat)} {cv g_len occ_end ctrl_off bkt_off
    occ_bkt gn slot b : Nat} {scr0 scr : List (BitVec 32)}
    (hok : FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (heven : (occ_end - g_len) % 2 = 0)
    (hctrl : bkt_off + occ_bkt ≤ scr.length) (hocc2 : occ_end + 2 ≤ ctrl_off)
    (hcv2 : occ_end + 1 < 2 ^ 32) (hgn_lt : gn < g_len) (hg_lt24 : g_len ≤ 0x01000000)
    (hgat : FidGateAt 64 F_cur cv scr0 g_len gn)
    (hslot_le : slot ≤ ((scr0[gn + 1]?.getD 0#32) &&& 0xFF#32).toNat)
    (hb : b < occ_bkt) (_hg_ctrl : g_len ≤ ctrl_off) (hdisj : ctrl_off ≤ bkt_off) :
    let head := scr[bkt_off + b]?.getD 0xFFFFFFFF#32
    let entry : BitVec 32 :=
      if slot = 0 then BitVec.ofNat 32 gn
      else (BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn
    let scr' := ((scr.set occ_end entry).set (occ_end + 1) head).set (bkt_off + b)
      (BitVec.ofNat 32 occ_end)
    FidOccNodesOk 64 F_cur cv g_len (occ_end + 2) ctrl_off bkt_off occ_bkt scr0 scr' := by
  intro head entry scr'
  have h_le : g_len ≤ occ_end := hok.1
  have hslot_lt256 : slot < 256 := by
    obtain ⟨_, mword, _, h1, _, _, _, ha64, _⟩ := hgat
    rw [h1, Option.getD_some] at hslot_le; omega
  have hgn_24 : gn < 2 ^ 24 := by omega
  have hptr_up : ∀ p, M6OccNodePtrOk g_len occ_end p → M6OccNodePtrOk g_len (occ_end + 2) p := by
    rintro p (rfl | ⟨h1, h2, h3⟩); · exact Or.inl rfl
    · exact Or.inr ⟨h1, by omega, h3⟩
  have hnew_ptr : M6OccNodePtrOk g_len (occ_end + 2) (BitVec.ofNat 32 occ_end) := by
    right; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨h_le, by omega, heven⟩
  have hentry_eq : entry = (BitVec.ofNat 32 slot <<< 24) ||| BitVec.ofNat 32 gn := by
    dsimp only [entry]; split
    · rename_i h0; subst h0
      rw [show (BitVec.ofNat 32 0 <<< 24 : BitVec 32) = 0#32 from by decide, BitVec.zero_or]
    · rfl
  have hgn_rec : (entry &&& 0x00FFFFFF#32).toNat = gn :=
    hentry_eq ▸ fid_pack_entry_gn hslot_lt256 hgn_24
  have hslot_rec : (entry >>> 24).toNat = slot :=
    hentry_eq ▸ fid_pack_entry_slot hslot_lt256 hgn_24
  refine ⟨by omega, hocc2, fun b' hb' => ?_, fun nd hnd1 hnd2 hnd_ev => ?_⟩
  · by_cases hbe : b' = b
    · subst hbe; dsimp only [scr']
      rw [List.getElem?_set_self (by simp; omega), Option.getD_some]; exact hnew_ptr
    · dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
      exact hptr_up _ (hok.2.2.1 b' hb')
  · by_cases hnd_new : nd = occ_end
    · subst hnd_new; dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some,
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega),
        Option.getD_some, hgn_rec, hslot_rec]
      exact ⟨hgn_lt, hgat, hslot_le, hptr_up _ (hok.2.2.1 b hb)⟩
    · have hnd_old : nd + 1 < occ_end := by omega
      dsimp only [scr']
      repeat rw [List.getElem?_set_ne (by omega)]
      obtain ⟨h1, h2, h3, h4⟩ := hok.2.2.2 nd hnd1 hnd_old hnd_ev
      exact ⟨h1, h2, h3, hptr_up _ h4⟩

private theorem fidOccNodesOk_relink {F_cur : List (List Nat)} {cv g_len occ_end ctrl_off bkt_off
    occ_bkt nd b_dst : Nat} {scr0 scr : List (BitVec 32)}
    (hok : FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (hctrl : bkt_off + occ_bkt ≤ scr.length) (hdisj : ctrl_off ≤ bkt_off)
    (hnd1 : g_len ≤ nd) (hnd2 : nd + 1 < occ_end) (hnd_ev : (nd - g_len) % 2 = 0)
    (hcv2 : occ_end + 1 < 2 ^ 32) (hb : b_dst < occ_bkt) :
    let scr' := (scr.set (nd + 1) (scr[bkt_off + b_dst]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst) (BitVec.ofNat 32 nd)
    FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr' := by
  intro scr'
  have hptr_nd : M6OccNodePtrOk g_len occ_end (BitVec.ofNat 32 nd) := by
    right; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨hnd1, hnd2, hnd_ev⟩
  have hocc_le := hok.2.1
  refine ⟨hok.1, hok.2.1, fun b' hb' => ?_, fun nd' hn1 hn2 hn_ev => ?_⟩
  · by_cases hbe : b' = b_dst
    · subst hbe; dsimp only [scr']
      rw [List.getElem?_set_self (by simp; omega), Option.getD_some]; exact hptr_nd
    · dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
      exact hok.2.2.1 b' hb'
  · have hent_eq : scr'[nd']? = scr[nd']? := by
      dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    obtain ⟨h1, h2, h3, h4⟩ := hok.2.2.2 nd' hn1 hn2 hn_ev
    refine ⟨by rw [hent_eq]; exact h1, by rw [hent_eq]; exact h2, by rw [hent_eq]; exact h3, ?_⟩
    by_cases hne : nd' = nd
    · subst hne; dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      exact hok.2.2.1 b_dst hb
    · dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
      exact h4

private theorem fid_m8CtrlLayout_of_eq_ctrl_q {c : FullCfg} {scr scr' : List (BitVec 32)}
    {g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen : scr'.length = scr.length)
    (heq : ∀ idx, co ≤ idx → idx < q_off + occ_bkt → scr'[idx]? = scr[idx]?) :
    M8CtrlLayout c scr' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, ho_pos, _, _, _, hcq, _, _, _, _, _, hql, hqok⟩
  refine m8CtrlLayout_same_tail hlay' hlen
    (by rw [heq (co + 5) (by omega) (by omega)]; exact hql)
    (fun j hj _ => heq (co + j) (by omega) (by omega)) (fun k hk => ?_)
  rw [heq (co + 5) (by omega) (by omega)] at hk
  rw [heq (co + 4) (by omega) (by omega)]
  have hslot := Nat.mod_lt ((scr[co + 4]?.getD 0#32).toNat + k) ho_pos
  rw [heq (q_off + ((scr[co + 4]?.getD 0#32).toNat + k) % occ_bkt) (by omega) (by omega)]
  exact hqok k hk

private theorem fid_m8CtrlLayout_eq_of_frame {c : FullCfg} {scr1 scr2 : List (BitVec 32)}
    {g_len co o1 b1 i1 q1 o2 b2 i2 q2 ht_off ht_sz : Nat}
    (h1 : M8CtrlLayout c scr1 g_len co o1 b1 i1 q1 ht_off ht_sz)
    (h2 : M8CtrlLayout c scr2 g_len co o2 b2 i2 q2 ht_off ht_sz)
    (hfr : ∀ idx < c.scratch_cap, idx < ht_off →
      (co = c.scratch_cap → scr2[idx]? = scr1[idx]?) ∧
      (∀ o b i q, M8CtrlLayout c scr1 g_len co o b i q ht_off ht_sz →
        idx ≠ co + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        scr2[idx]? = scr1[idx]?)) :
    M8CtrlLayout c scr2 g_len co o1 b1 i1 q1 ht_off ht_sz := by
  have h1' := h1; have h2' := h2
  rcases h1 with ⟨hc1, hc8, _, _, s0_1, s1_1, s2_1, s3_1, _, _, ho1, _, _, _,
    hcq, hqi, hib, hbh, hht_1, _⟩
  rcases h2 with ⟨_, _, _, _, s0_2, s1_2, s2_2, s3_2, _, _, _, ho2_le, _, _,
    _, hqi2, hib2, hbh2, hht_2, _⟩
  have hkeep : ∀ j < 4, scr2[co + j]? = scr1[co + j]? := fun j hj =>
    (hfr (co + j) (by omega) (by omega)).2 o1 b1 i1 q1 h1' (by omega) (by omega) (by omega)
  have hsc := c.hscr; unfold dimacsBound at hsc
  have eq_of_bv : ∀ a b : Nat, a < 2 ^ 32 → b < 2 ^ 32 →
      BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun a b ha hb h => by
    have := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have h0 : o2 = o1 := eq_of_bv _ _ (by omega) (by omega) (by
    have h0e := hkeep 0 (by omega); rw [← s0_2]; simp only [Nat.add_zero] at h0e; rw [h0e, s0_1])
  have h1_eq : b2 = b1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s1_2, hkeep 1 (by omega), s1_1])
  have h2_eq : i2 = i1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s2_2, hkeep 2 (by omega), s2_1])
  have h3_eq : q2 = q1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s3_2, hkeep 3 (by omega), s3_1])
  subst h0 h1_eq h2_eq h3_eq; exact h2'

private theorem fid_m8CtrlLayout_grow {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr)
    (hht2_cap : ht_off + 2 * ht_sz ≤ c.scratch_cap) :
    let scr' := scr.set (co + 7) (BitVec.ofNat 32 (2 * ht_sz))
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len co occ_bkt bkt_off inq_off q_off ht_off (2 * ht_sz) ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    FidOccNodesOk 64 F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr' := by
  intro scr'
  rcases hlay with ⟨hc1, hc8, hgc, hg24, s0, s1, s2, s3, s6, _, ho_pos, ho_le, hopow, hht_pos,
    hcq, hqi, hib, hbh, _, hqh, hql, hqok⟩
  have hne : ∀ idx, idx ≠ co + 7 → scr'[idx]? = scr[idx]? :=
    fun _ h => List.getElem?_set_ne (Ne.symm h)
  have h7 : scr'[co + 7]?.getD 0#32 = BitVec.ofNat 32 (2 * ht_sz) := by
    dsimp only [scr']; rw [List.getElem?_set_self (by omega), Option.getD_some]
  refine ⟨by simp only [scr', List.length_set, hscrl],
    ⟨hc1, hc8, hgc, hg24, by rw [hne co (by omega)]; exact s0,
      by rw [hne (co + 1) (by omega)]; exact s1, by rw [hne (co + 2) (by omega)]; exact s2,
      by rw [hne (co + 3) (by omega)]; exact s3, by rw [hne (co + 6) (by omega)]; exact s6,
      h7, ho_pos, ho_le, hopow, by omega, hcq, hqi, hib, hbh, hht2_cap,
      by rw [hne (co + 4) (by omega)]; exact hqh, by rw [hne (co + 5) (by omega)]; exact hql,
      fun k hk => by
        rw [hne (co + 5) (by omega)] at hk
        rw [hne (co + 4) (by omega), hne _ (by omega)]; exact hqok k hk⟩,
    fun idx hidx => by rw [hne idx (by omega)]; exact hpref idx hidx,
    ⟨hocc.1, hocc.2.1,
     fun b hb => by rw [hne (bkt_off + b) (by omega)]; exact hocc.2.2.1 b hb,
     fun nd hn1 hn2 hev => by
       have hoc := hocc.2.1; rw [hne nd (by omega), hne (nd + 1) (by omega)]
       exact hocc.2.2.2 nd hn1 hn2 hev⟩⟩

private def FidWlStOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat) (scr0 : List (BitVec 32)) (st : FullState) : Prop :=
  FullDenseInvW c F0 F_cur st ∧
  st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  M8CtrlLayout c st.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
  (∀ idx < g_len, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  FidCongHtInv 64 F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz ∧
  FidOccNodesOk 64 F_cur cv0 g_len occ_end ctrl_off bkt_off occ_bkt scr0 st.scratch.scratch_buf

private theorem fidWlStOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat} {scr0 : List (BitVec 32)} {st : FullState}
    (hok : FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 st)
    {r : List (BitVec 32)} (hr : r.length = 2 * c.max_vars)
    (hrepr : FullCongReprInv F_cur (2 * cv0) r) :
    FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 { st with core := { st.core with repr := r } } :=
  ⟨m6_fullDenseInvW_with_repr hok.1 hr, hok.2.1, hok.2.2.1, hrepr, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2⟩

private theorem fidWlStOk_with_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ht_sz'
      occ_end occ_end' : Nat} {scr0 scr' : List (BitVec 32)} {st : FullState}
    (hok : FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 st)
    (hl : scr'.length = c.scratch_cap)
    (hlay' : M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz')
    (hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]?)
    (hht' : FidCongHtInv 64 F_cur cv0 scr0 scr' g_len ht_off ht_sz')
    (hocc' : FidOccNodesOk 64 F_cur cv0 g_len occ_end' ctrl_off bkt_off occ_bkt scr0 scr')
    (rs' : BitVec 64 := st.scratch.res_sz) :
    FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz'
      occ_end' scr0 { st with scratch := { st.scratch with scratch_buf := scr', res_sz := rs' } } :=
  ⟨fid_denseInvW_with_scr hok.1 hl rs', hok.2.1, hok.2.2.1, hok.2.2.2.1,
    hlay', hpref', hht', hocc'⟩

private theorem fidOccNodesOk_of_ev_frame {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len occ_end ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scr scr' : List (BitVec 32)}
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hfr : ∀ idx < c.scratch_cap, idx < ht_off →
      (ctrl_off = c.scratch_cap → scr'[idx]? = scr[idx]?) ∧
      (∀ o b i q, M8CtrlLayout c scr g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        scr'[idx]? = scr[idx]?)) :
    FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr' := by
  have hlay' := hlay; have h_occ1 := hocc.1; have h_occ2 := hocc.2.1
  rcases hlay with ⟨_, _, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hkeep : ∀ idx, (g_len ≤ idx ∧ idx < occ_end) ∨ (bkt_off ≤ idx ∧ idx < bkt_off + occ_bkt) →
      scr'[idx]? = scr[idx]? := fun idx hi =>
    (hfr idx (by rcases hi with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
      (by rcases hi with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)).2 occ_bkt bkt_off inq_off q_off hlay'
      (by rcases hi with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
      (by rcases hi with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
      (by rcases hi with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
  refine ⟨hocc.1, hocc.2.1, fun b hb => ?_, fun nd hn1 hn2 hev => ?_⟩
  · rw [hkeep (bkt_off + b) (Or.inr ⟨by omega, by omega⟩)]; exact hocc.2.2.1 b hb
  · rw [hkeep nd (Or.inl ⟨hn1, by omega⟩), hkeep (nd + 1) (Or.inl ⟨by omega, by omega⟩)]
    exact hocc.2.2.2 nd hn1 hn2 hev

private theorem fidWl_phase0_finalize {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scr_i scr_f : List (BitVec 32)}
    (hlay0 : M8CtrlLayout c scr_i g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl_i : scr_i.length = c.scratch_cap)
    (hpref_i : ∀ idx < g_len, scr_i[idx]? = scr0[idx]?)
    (hht_i : FidCongHtInv 64 F_cur cv scr0 scr_i g_len ht_off ht_sz)
    (hbkt_i : ∀ b < occ_bkt, scr_i[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hdef : scr_f = (scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32) :
    scr_f.length = c.scratch_cap ∧
    M8CtrlLayout c scr_f g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_f[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr_f g_len ht_off ht_sz ∧
    FidOccNodesOk 64 F_cur cv g_len g_len ctrl_off bkt_off occ_bkt scr0 scr_f := by
  subst hdef; have hlay0' := hlay0
  rcases hlay0 with ⟨hc1, hc8, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _, hcq, hqi, hib, hbh, _, _⟩
  have hq4 : ((scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32)[ctrl_off + 4]?.getD 0#32 =
      0#32 := by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hq5 : ((scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32)[ctrl_off + 5]?.getD 0#32 =
      0#32 := by
    rw [List.getElem?_set_self (by simp [hscrl_i]; omega), Option.getD_some]
  refine ⟨by simp only [List.length_set, hscrl_i],
    m8CtrlLayout_set_q hlay0' (by simp only [List.length_set])
      (fun i _ h4 h5 => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
      (by rw [hq4]; exact ho_pos) (by rw [hq5]; exact Nat.zero_le _)
      (fun _ hk => by rw [hq5] at hk; cases hk),
    fun idx hidx => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hpref_i idx hidx,
    fun k hk => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hht_i k hk,
    ⟨Nat.le_refl _, hgc, fun b hb => Or.inl (by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hbkt_i b hb),
     fun _ _ _ _ => by omega⟩⟩

private theorem fidWl_push_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end b : Nat}
    {scr0 scr : List (BitVec 32)} {entry : BitVec 32}
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hge : g_len ≤ occ_end) (hocc2 : occ_end + 2 ≤ ctrl_off) (hb : b < occ_bkt) :
    let scr' := ((scr.set occ_end entry).set (occ_end + 1)
      (scr[bkt_off + b]?.getD 0xFFFFFFFF#32)).set (bkt_off + b) (BitVec.ofNat 32 occ_end)
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr' g_len ht_off ht_sz := by
  intro scr'; have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, _, _⟩
  have hlen' : scr'.length = c.scratch_cap := by simp only [scr', List.length_set, hscrl]
  have hno : ∀ idx, (ctrl_off ≤ idx ∧ idx < q_off + occ_bkt) ∨ idx < g_len ∨ ht_off ≤ idx →
      scr'[idx]? = scr[idx]? := fun idx h => by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega),
      List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega),
      List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega)]
  refine ⟨hlen', fid_m8CtrlLayout_of_eq_ctrl_q hlay' (by rw [hlen', hscrl])
      (fun idx h1 h2 => hno idx (Or.inl ⟨h1, h2⟩)),
    fun idx hidx => by rw [hno idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx,
    fun k hk => by rw [hno (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk⟩

private theorem fidWl_relink_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end nd b_dst : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hge : g_len ≤ nd) (hnd1 : nd + 1 < occ_end) (hocc_c : occ_end ≤ ctrl_off)
    (hb : b_dst < occ_bkt) :
    let scr' := (scr.set (nd + 1) (scr[bkt_off + b_dst]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst) (BitVec.ofNat 32 nd)
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr' g_len ht_off ht_sz := by
  intro scr'; have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, _, _⟩
  have hlen' : scr'.length = c.scratch_cap := by simp only [scr', List.length_set, hscrl]
  have hno : ∀ idx, (ctrl_off ≤ idx ∧ idx < q_off + occ_bkt) ∨ idx < g_len ∨ ht_off ≤ idx →
      scr'[idx]? = scr[idx]? := fun idx h => by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega),
      List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega)]
  refine ⟨hlen', fid_m8CtrlLayout_of_eq_ctrl_q hlay' (by rw [hlen', hscrl])
      (fun idx h1 h2 => hno idx (Or.inl ⟨h1, h2⟩)),
    fun idx hidx => by rw [hno idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx,
    fun k hk => by rw [hno (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk⟩

private theorem fidWl_pop_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (hpos : 0 < (scr[ctrl_off + 5]?.getD 0#32).toNat) :
    let qh := scr[ctrl_off + 4]?.getD 0#32
    let ql := scr[ctrl_off + 5]?.getD 0#32
    let b := scr[q_off + qh.toNat]?.getD 0#32
    let nqh := (qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
    let scr1 := (((scr.set (ctrl_off + 4) nqh).set (ctrl_off + 5) (ql - 1#32)).set
      (inq_off + b.toNat) 0#32).set (bkt_off + b.toNat) 0xFFFFFFFF#32
    b.toNat < occ_bkt ∧ nqh.toNat < occ_bkt ∧ scr1.length = c.scratch_cap ∧
    M8CtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr1[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr1 g_len ht_off ht_sz ∧
    M6OccNodePtrOk g_len occ_end (scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
    FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr1 := by
  intro qh ql b nqh scr1
  have ⟨hb_lt, hnqh_lt, hlay_pop⟩ := m8CtrlLayout_pop_q hlay hscrl hpos
  let scr_pop := ((scr.set (ctrl_off + 4) nqh).set (ctrl_off + 5) (ql - 1#32)).set
    (inq_off + b.toNat) 0#32
  have hscrl_pop : scr_pop.length = c.scratch_cap := by simp only [scr_pop, List.length_set, hscrl]
  have hlay_pop' := hlay_pop
  rcases hlay_pop with ⟨_, _, hgc, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, _, _⟩
  have hlen1 : scr1.length = c.scratch_cap := by simp only [scr1, List.length_set, hscrl]
  have hb_lt' : (scr[q_off + qh.toNat]?.getD 0#32).toNat < occ_bkt := hb_lt
  have hlay1 := fid_m8CtrlLayout_of_eq_ctrl_q hlay_pop' (by rw [hlen1, hscrl_pop])
    (fun idx _ h2 => by dsimp only [scr1]; exact List.getElem?_set_ne (by omega))
  have hdisj1 : ∀ idx, idx < ctrl_off ∨ ht_off ≤ idx → scr1[idx]? = scr[idx]? := fun idx h => by
    dsimp only [scr1]
    rw [List.getElem?_set_ne (by dsimp only [b]; rcases h with _ | _ <;> omega),
      List.getElem?_set_ne (by dsimp only [b]; rcases h with _ | _ <;> omega),
      List.getElem?_set_ne (by rcases h with _ | _ <;> omega),
      List.getElem?_set_ne (by rcases h with _ | _ <;> omega)]
  refine ⟨hb_lt, hnqh_lt, hlen1, hlay1,
    fun idx hidx => by rw [hdisj1 idx (Or.inl (by omega))]; exact hpref idx hidx,
    fun k hk => by rw [hdisj1 (ht_off + k) (Or.inr (by omega))]; exact hht k hk,
    hocc.2.2.1 b.toNat hb_lt, ⟨hocc.1, hocc.2.1, fun b' hb' => ?_, fun nd h1 h2 hev => ?_⟩⟩
  · change M6OccNodePtrOk g_len occ_end (scr1[bkt_off + b']?.getD 0xFFFFFFFF#32)
    by_cases hbb : b' = b.toNat
    · subst hbb; dsimp only [scr1]
      rw [List.getElem?_set_self (by rw [hscrl_pop]; omega), Option.getD_some]; exact Or.inl rfl
    · dsimp only [scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by dsimp only [b]; omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hocc.2.2.1 b' hb'
  · have hoc := hocc.2.1
    rw [hdisj1 nd (Or.inl (by omega)), hdisj1 (nd + 1) (Or.inl (by omega))]
    exact hocc.2.2.2 nd h1 h2 hev

private def FullScratchRestFid (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆
   array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s)

private theorem focus_full_scratch_fid {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (FullScratchRestFid c s ⋆ R)) m := by
  rw [fullMem_eq_scrDyn] at hm; unfold FullScrDynArrs at hm; unfold FullScratchRestFid; ecancel

private theorem unfocus_full_scratch_fid {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆ (FullScratchRestFid c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  rw [fullMem_eq_scrDyn]; unfold FullScrDynArrs; unfold FullScratchRestFid at hm
  change ((array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
    array (t := i32) c.pScratchBuf scr') ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
     FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s) ⋆ R) m
  ecancel

private theorem fidWl_phase0_clear_step {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} {i : BitVec 64}
    (hlay_i : M8CtrlLayout c scri g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl_i : scri.length = c.scratch_cap)
    (hpref_i : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht_i : FidCongHtInv 64 F_cur cv scr0 scri g_len ht_off ht_sz)
    (hbkt_i : ∀ b < i.toNat, scri[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_lt : i.toNat < occ_bkt) :
    let scri' := (scri.set (bkt_off + i.toNat) 0xFFFFFFFF#32).set (inq_off + i.toNat) 0#32
    (BitVec.ofNat 64 bkt_off + i).toNat = bkt_off + i.toNat ∧
    (BitVec.ofNat 64 inq_off + i).toNat = inq_off + i.toNat ∧
    (BitVec.ofNat 64 bkt_off + i).toNat < scri.length ∧
    (BitVec.ofNat 64 inq_off + i).toNat <
      (scri.set (BitVec.ofNat 64 bkt_off + i).toNat 0xFFFFFFFF#32).length ∧
    (i + 1#64).toNat = i.toNat + 1 ∧ scri'.length = c.scratch_cap ∧
    M8CtrlLayout c scri' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scri'[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scri' g_len ht_off ht_sz ∧
    (∀ b < i.toNat + 1, scri'[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
  intro scri'; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay_i' := hlay_i
  rcases hlay_i with ⟨_, _, _, _, _, _, _, _, _, _, _, ho_8192, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hbkt_i_n : (BitVec.ofNat 64 bkt_off + i).toNat = bkt_off + i.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hinq_i_n : (BitVec.ofNat 64 inq_off + i).toNat = inq_off + i.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlen' : scri'.length = c.scratch_cap := by simp only [scri', List.length_set, hscrl_i]
  have hno : ∀ idx, (co ≤ idx ∧ idx < q_off + occ_bkt) ∨ idx < g_len ∨ ht_off ≤ idx →
      scri'[idx]? = scri[idx]? := fun idx h => by
    dsimp only [scri']
    rw [List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega),
      List.getElem?_set_ne (by rcases h with ⟨_, _⟩ | _ | _ <;> omega)]
  refine ⟨hbkt_i_n, hinq_i_n, by rw [hbkt_i_n]; omega,
    by rw [List.length_set, hinq_i_n]; omega,
    bv64_add1_toNat (n := occ_bkt) hi_lt (by omega), hlen',
    fid_m8CtrlLayout_of_eq_ctrl_q hlay_i' (by rw [hlen', hscrl_i])
      (fun idx h1 h2 => hno idx (Or.inl ⟨h1, h2⟩)),
    fun idx hidx => by rw [hno idx (Or.inr (Or.inl hidx))]; exact hpref_i idx hidx,
    fun k hk => by rw [hno (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht_i k hk,
    fun b hb => ?_⟩
  by_cases hbi : b = i.toNat
  · subst hbi; dsimp only [scri']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  · dsimp only [scri']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hbkt_i b (by omega)

private theorem fidWl_rehash_clear_step {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scrh : List (BitVec 32)} {ih : BitVec 64}
    (hlay_h : M8CtrlLayout c scrh g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl_h : scrh.length = c.scratch_cap)
    (hpref_h : ∀ idx < g_len, scrh[idx]? = scr0[idx]?)
    (hht_h : ∀ k < ih.toNat, scrh[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hocc_h : FidOccNodesOk 64 F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh)
    (hih_lt : ih.toNat < ht_sz) :
    let scrh' := scrh.set (ht_off + ih.toNat) 0xFFFFFFFF#32
    (BitVec.ofNat 64 ht_off + ih).toNat = ht_off + ih.toNat ∧
    (BitVec.ofNat 64 ht_off + ih).toNat < scrh.length ∧
    (ih + 1#64).toNat = ih.toNat + 1 ∧ scrh'.length = c.scratch_cap ∧
    M8CtrlLayout c scrh' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scrh'[idx]? = scr0[idx]?) ∧
    (∀ k < ih.toNat + 1, scrh'[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
    FidOccNodesOk 64 F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh' := by
  intro scrh'; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay_h' := hlay_h
  rcases hlay_h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hht_cap, _⟩
  have hhti_n : (BitVec.ofNat 64 ht_off + ih).toNat = ht_off + ih.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlen' : scrh'.length = c.scratch_cap := by simp only [scrh', List.length_set, hscrl_h]
  have hno : ∀ idx, idx < ht_off → scrh'[idx]? = scrh[idx]? :=
    fun _ _ => List.getElem?_set_ne (by omega)
  refine ⟨hhti_n, by rw [hhti_n]; omega, bv64_add1_lt (by omega), hlen',
    fid_m8CtrlLayout_of_eq_ctrl_q hlay_h' (by rw [hlen', hscrl_h])
      (fun idx _ _ => hno idx (by omega)),
    fun idx hidx => by rw [hno idx (by omega)]; exact hpref_h idx hidx,
    fun k hk => ?_,
    ⟨hocc_h.1, hocc_h.2.1,
     fun b' hb' => by rw [hno (bkt_off + b') (by omega)]; exact hocc_h.2.2.1 b' hb',
     fun nd' hn1 hn2 hev => by
       have hoc := hocc_h.2.1
       rw [hno nd' (by omega), hno (nd' + 1) (by omega)]; exact hocc_h.2.2.2 nd' hn1 hn2 hev⟩⟩
  by_cases hki : k = ih.toNat
  · subst hki; dsimp only [scrh']; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · dsimp only [scrh']; rw [List.getElem?_set_ne (by omega)]; exact hht_h k (by omega)

private structure FidWlCtrlFacts (c : FullCfg) (scr : List (BitVec 32)) (ctrl_off : BitVec 64)
    (occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat) : Prop where
  hc1_n : (ctrl_off + 1).toNat = ctrl_off.toNat + 1
  hc2_n : (ctrl_off + 2).toNat = ctrl_off.toNat + 2
  hc3_n : (ctrl_off + 3).toNat = ctrl_off.toNat + 3
  hc4_n : (ctrl_off + 4).toNat = ctrl_off.toNat + 4
  hc5_n : (ctrl_off + 5).toNat = ctrl_off.toNat + 5
  hc6_n : (ctrl_off + 6).toNat = ctrl_off.toNat + 6
  hc7_n : (ctrl_off + 7).toNat = ctrl_off.toNat + 7
  hco0_arr : ctrl_off.toNat < scr.length
  hco1_arr : (ctrl_off + 1).toNat < scr.length
  hco2_arr : (ctrl_off + 2).toNat < scr.length
  hco3_arr : (ctrl_off + 3).toNat < scr.length
  hco4_arr : (ctrl_off + 4).toNat < scr.length
  hco5_arr : (ctrl_off + 5).toNat < scr.length
  hco6_arr : (ctrl_off + 6).toNat < scr.length
  hco7_arr : (ctrl_off + 7).toNat < scr.length
  heq_co0 : scr[ctrl_off.toNat]'hco0_arr = BitVec.ofNat 32 occ_bkt
  heq_co1 : scr[(ctrl_off + 1).toNat]'hco1_arr = BitVec.ofNat 32 bkt_off
  heq_co2 : scr[(ctrl_off + 2).toNat]'hco2_arr = BitVec.ofNat 32 inq_off
  heq_co3 : scr[(ctrl_off + 3).toNat]'hco3_arr = BitVec.ofNat 32 q_off
  heq_co6 : scr[(ctrl_off + 6).toNat]'hco6_arr = BitVec.ofNat 32 ht_off
  heq_co7 : scr[(ctrl_off + 7).toNat]'hco7_arr = BitVec.ofNat 32 ht_sz
  hbkt32 : (BitVec.ofNat 32 bkt_off).setWidth 64 = BitVec.ofNat 64 bkt_off
  hinq32 : (BitVec.ofNat 32 inq_off).setWidth 64 = BitVec.ofNat 64 inq_off
  hq32 : (BitVec.ofNat 32 q_off).setWidth 64 = BitVec.ofNat 64 q_off
  hho32 : (BitVec.ofNat 32 ht_off).setWidth 64 = BitVec.ofNat 64 ht_off
  hhs32 : (BitVec.ofNat 32 ht_sz).setWidth 64 = BitVec.ofNat 64 ht_sz
  hocc32 : (BitVec.ofNat 32 occ_bkt).setWidth 64 = BitVec.ofNat 64 occ_bkt
  hho_n : (BitVec.ofNat 64 ht_off).toNat = ht_off
  hhs_n : (BitVec.ofNat 64 ht_sz).toNat = ht_sz

private theorem fidWl_ctrl_arith {c : FullCfg} {scr : List (BitVec 32)} {g_len : Nat}
    {ctrl_off : BitVec 64} {occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hht_bnd : ht_sz < 2 ^ 30) (hscrl : scr.length = c.scratch_cap)
    (hlay : M8CtrlLayout c scr g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    FidWlCtrlFacts c scr ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  rcases hlay with ⟨hc_cap, hc_8, _, _, hs0, hs1, hs2, hs3, hs6, hs7,
    _, ho_8192, _, _, hcq, hqi, hib, hbh, hht_cap, _⟩
  have mkAdd : ∀ k ≤ 7, (ctrl_off + BitVec.ofNat 64 k).toNat = ctrl_off.toNat + k :=
    fun k hk => bv64_add_nat_lt k (by omega) (by omega)
  have hc1 : (ctrl_off + 1).toNat = ctrl_off.toNat + 1 := mkAdd 1 (by omega)
  have hc2 : (ctrl_off + 2).toNat = ctrl_off.toNat + 2 := mkAdd 2 (by omega)
  have hc3 : (ctrl_off + 3).toNat = ctrl_off.toNat + 3 := mkAdd 3 (by omega)
  have hc4 : (ctrl_off + 4).toNat = ctrl_off.toNat + 4 := mkAdd 4 (by omega)
  have hc5 : (ctrl_off + 5).toNat = ctrl_off.toNat + 5 := mkAdd 5 (by omega)
  have hc6 : (ctrl_off + 6).toNat = ctrl_off.toNat + 6 := mkAdd 6 (by omega)
  have hc7 : (ctrl_off + 7).toNat = ctrl_off.toNat + 7 := mkAdd 7 (by omega)
  have ha0 : ctrl_off.toNat < scr.length := by omega
  have ha1 : (ctrl_off + 1).toNat < scr.length := by rw [hc1]; omega
  have ha2 : (ctrl_off + 2).toNat < scr.length := by rw [hc2]; omega
  have ha3 : (ctrl_off + 3).toNat < scr.length := by rw [hc3]; omega
  have ha4 : (ctrl_off + 4).toNat < scr.length := by rw [hc4]; omega
  have ha5 : (ctrl_off + 5).toNat < scr.length := by rw [hc5]; omega
  have ha6 : (ctrl_off + 6).toNat < scr.length := by rw [hc6]; omega
  have ha7 : (ctrl_off + 7).toNat < scr.length := by rw [hc7]; omega
  have mkEq : ∀ (k off : Nat) (hkn : (ctrl_off + BitVec.ofNat 64 k).toNat = ctrl_off.toNat + k)
      (ha : (ctrl_off + BitVec.ofNat 64 k).toNat < scr.length)
      (hkl : ctrl_off.toNat + k < scr.length)
      (hs : scr[ctrl_off.toNat + k]?.getD 0#32 = BitVec.ofNat 32 off),
      scr[(ctrl_off + BitVec.ofNat 64 k).toNat]'ha = BitVec.ofNat 32 off :=
    fun _ _ hkn ha hkl hs => by
      rw [List.getElem?_eq_getElem hkl, Option.getD_some] at hs
      exact (list_getElem_congr hkn ha hkl).trans hs
  have mkZw : ∀ {n : Nat}, n < 2 ^ 32 → (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n :=
    fun hn => BitVec.eq_of_toNat_eq (by
      rw [bv_zext32_toNat, bv32_ofNat_toNat hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  refine ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ?_,
    mkEq 1 bkt_off hc1 ha1 (by omega) hs1, mkEq 2 inq_off hc2 ha2 (by omega) hs2,
    mkEq 3 q_off hc3 ha3 (by omega) hs3, mkEq 6 ht_off hc6 ha6 (by omega) hs6,
    mkEq 7 ht_sz hc7 ha7 (by omega) hs7, mkZw (by omega), mkZw (by omega), mkZw (by omega),
    mkZw (by omega), mkZw (by omega), mkZw (by omega),
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩
  rwa [← Option.getD_some (a := scr[ctrl_off.toNat]'ha0) (b := 0#32),
    ← List.getElem?_eq_getElem ha0]

private theorem fidWl_pop_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {ctrl_off : BitVec 64} {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off.toNat bkt_off occ_bkt scr0 scr)
    (hpos : 0 < (scr[ctrl_off.toNat + 5]?.getD 0#32).toNat)
    (hc4_n : (ctrl_off + 4).toNat = ctrl_off.toNat + 4)
    (hc5_n : (ctrl_off + 5).toNat = ctrl_off.toNat + 5) :
    let qh := scr[ctrl_off.toNat + 4]?.getD 0#32
    let ql := scr[ctrl_off.toNat + 5]?.getD 0#32
    let b := scr[q_off + qh.toNat]?.getD 0#32
    let nqh := (qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
    let scr_pop := (((scr.set (ctrl_off.toNat + 4) nqh).set
      (ctrl_off.toNat + 5) (ql - 1#32)).set (inq_off + b.toNat) 0#32).set
      (bkt_off + b.toNat) 0xFFFFFFFF#32
    ∃ (hco4 : (ctrl_off + 4).toNat < scr.length) (hco5 : (ctrl_off + 5).toNat < scr.length)
      (hq_ld : (BitVec.ofNat 64 q_off +
        (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat < scr.length),
      let nqh_ex := (scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
        (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
      let ql1_ex := scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32)
      let b_ex := scr[(BitVec.ofNat 64 q_off +
        (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld
      let scr3 := ((scr.set (ctrl_off + 4).toNat nqh_ex).set (ctrl_off + 5).toNat ql1_ex).set
        (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat (0 : BitVec 32)
      scr_pop.length = c.scratch_cap ∧
      M8CtrlLayout c scr_pop g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
      (∀ idx < g_len, scr_pop[idx]? = scr0[idx]?) ∧
      FidCongHtInv 64 F_cur cv scr0 scr_pop g_len ht_off ht_sz ∧
      M6OccNodePtrOk g_len occ_end (scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
      FidOccNodesOk 64 F_cur cv g_len occ_end ctrl_off.toNat bkt_off occ_bkt scr0 scr_pop ∧
      (ctrl_off + 5).toNat < (scr.set (ctrl_off + 4).toNat nqh_ex).length ∧
      (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat <
        ((scr.set (ctrl_off + 4).toNat nqh_ex).set (ctrl_off + 5).toNat ql1_ex).length ∧
      (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat < scr3.length ∧
      (∀ (hbkt_cap : (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat < scr3.length),
        scr3[(BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat]'hbkt_cap =
          scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
      scr3.set (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat (4294967295 : BitVec 32) =
        scr_pop ∧
      (scr_pop[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat := by
  intro qh ql b nqh scr_pop
  have hsc := c.hscr; unfold dimacsBound at hsc; have hlay' := hlay
  rcases hlay with ⟨hc_cap, hc_8, _, _, _, _, _, _, _, _, _, ho_8192, _, _,
    hcq, hqi, hib, hbh, hht_cap, hqh_lt, _, _⟩
  have hco4 : (ctrl_off + 4).toNat < scr.length := by rw [hc4_n]; omega
  have hco5 : (ctrl_off + 5).toNat < scr.length := by rw [hc5_n]; omega
  have hpop := fidWl_pop_pres hlay' hscrl hpref hht hocc hpos
  have hb_lt : b.toNat < occ_bkt := hpop.1
  have mk64 : ∀ n < 2 ^ 64, (BitVec.ofNat 64 n).toNat = n :=
    fun _ hn => by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hq64_n := mk64 q_off (by omega); have hinq64_n := mk64 inq_off (by omega)
  have hbkt64_n := mk64 bkt_off (by omega); have hqh_lt' : qh.toNat < occ_bkt := hqh_lt
  have hq_idx : (BitVec.ofNat 64 q_off + qh.setWidth 64).toNat = q_off + qh.toNat := by
    rw [bv64_add_zext32_0 (by rw [hq64_n]; omega), hq64_n]
  have hq_arr : (BitVec.ofNat 64 q_off + qh.setWidth 64).toNat < scr.length := by rw [hq_idx]; omega
  have hb_eq : scr[(BitVec.ofNat 64 q_off + qh.setWidth 64).toNat]'hq_arr = b := by
    dsimp only [b]
    rw [list_getElem_congr hq_idx hq_arr (by omega), List.getElem?_eq_getElem (by omega)]
    rfl
  have hqh_u : scr[(ctrl_off + 4).toNat]'hco4 = qh := by
    dsimp only [qh]
    rw [list_getElem_congr hc4_n hco4 (by omega), List.getElem?_eq_getElem (by omega)]; rfl
  have hql_u : scr[(ctrl_off + 5).toNat]'hco5 = ql := by
    dsimp only [ql]
    rw [list_getElem_congr hc5_n hco5 (by omega), List.getElem?_eq_getElem (by omega)]; rfl
  have hq_ld_n : (BitVec.ofNat 64 q_off + (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat =
      (BitVec.ofNat 64 q_off + qh.setWidth 64).toNat := by rw [hqh_u]
  have hq_ld : (BitVec.ofNat 64 q_off + (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat <
      scr.length := by rw [hq_ld_n]; exact hq_arr
  have hb_raw_eq : scr[(BitVec.ofNat 64 q_off +
      (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld = b :=
    (list_getElem_congr hq_ld_n hq_ld hq_arr).trans hb_eq
  have hinqb_n : (BitVec.ofNat 64 inq_off + b.setWidth 64).toNat = inq_off + b.toNat := by
    rw [bv64_add_zext32_0 (by rw [hinq64_n]; omega), hinq64_n]
  have hbktb_n : (BitVec.ofNat 64 bkt_off + b.setWidth 64).toNat = bkt_off + b.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hnqh_ex : (scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
      (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32)) = nqh := by rw [hqh_u]; rfl
  have hql1_ex : scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32) = ql - 1#32 := by
    rw [hql_u]; rfl
  have hlist3_eq :
      ((scr.set (ctrl_off + 4).toNat ((scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
          (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32)))).set
        (ctrl_off + 5).toNat (scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32))).set
        (BitVec.ofNat 64 inq_off +
          (scr[(BitVec.ofNat 64 q_off + (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld
            ).setWidth 64).toNat (0 : BitVec 32) =
      ((scr.set (ctrl_off.toNat + 4) nqh).set (ctrl_off.toNat + 5) (ql - 1#32)).set
        (inq_off + b.toNat) 0#32 := by
    rw [hnqh_ex, hql1_ex, hb_raw_eq, hc4_n, hc5_n, hinqb_n]; rfl
  have hidx_eq : (BitVec.ofNat 64 bkt_off +
      (scr[(BitVec.ofNat 64 q_off + (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld
        ).setWidth 64).toNat = bkt_off + b.toNat := by rw [hb_raw_eq, hbktb_n]
  refine ⟨hco4, hco5, hq_ld, hpop.2.2.1, hpop.2.2.2.1, hpop.2.2.2.2.1, hpop.2.2.2.2.2.1,
    hpop.2.2.2.2.2.2.1, hpop.2.2.2.2.2.2.2, by rw [List.length_set]; exact hco5,
    by simp only [List.length_set]; rw [hb_raw_eq, hinqb_n]; omega,
    by simp only [List.length_set]; rw [hb_raw_eq, hbktb_n]; omega, fun hcap => ?_, ?_, ?_⟩
  · rw [← Option.getD_some (a := (((scr.set (ctrl_off + 4).toNat _).set _ _).set _ _)[_]'hcap)
        (b := 0xFFFFFFFF#32), ← List.getElem?_eq_getElem hcap, hlist3_eq, hidx_eq,
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  · rw [hlist3_eq, hidx_eq]; rfl
  · have hql_pos : 0 < ql.toNat := hpos; dsimp only [scr_pop]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp only [List.length_set, hscrl]; omega), Option.getD_some,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr
        (show (1#32 : BitVec 32).toNat ≤ ql.toNat from Nat.succ_le_of_lt hql_pos))]
    have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega

private theorem fidWl_relink_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scr : List (BitVec 32)} {nd b_dst : BitVec 32}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr)
    (hnd_lo : g_len ≤ nd.toNat) (hnd_hi : nd.toNat + 1 < occ_end)
    (hnd_ev : (nd.toNat - g_len) % 2 = 0)
    (_hnd1_n : (nd.setWidth 64 + 1#64).toNat = nd.toNat + 1)
    (hbdst : b_dst.toNat < occ_bkt) :
    let bkt_64 := BitVec.ofNat 64 bkt_off
    let scr_rel := (scr.set (nd.toNat + 1)
      (scr[bkt_off + b_dst.toNat]?.getD 0xFFFFFFFF#32)).set (bkt_off + b_dst.toNat) nd
    (bkt_64 + b_dst.setWidth 64).toNat = bkt_off + b_dst.toNat ∧
    scr_rel.length = c.scratch_cap ∧
    M8CtrlLayout c scr_rel g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_rel[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr_rel g_len ht_off ht_sz ∧
    FidOccNodesOk 64 F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr_rel ∧
    (∀ (hb_cap : bkt_off + b_dst.toNat < scr.length),
      (scr.set (nd.toNat + 1) (scr[bkt_off + b_dst.toNat]'hb_cap)).set
        (bkt_off + b_dst.toNat) nd = scr_rel) := by
  intro bkt_64 scr_rel; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbh, hht_cap, _⟩
  have hocc_c := hocc.2.1
  have hbkt64_n : bkt_64.toNat = bkt_off := by
    dsimp only [bkt_64]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb_idx_n : (bkt_64 + b_dst.setWidth 64).toNat = bkt_off + b_dst.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hrel_p := fidWl_relink_pres hlay' hscrl hpref hht hnd_lo hnd_hi (by omega) hbdst
  have hocc_rel := fidOccNodesOk_relink hocc (by omega) (by omega) hnd_lo hnd_hi hnd_ev
    (by omega) hbdst
  have hrel_eq : (scr.set (nd.toNat + 1)
      (scr[bkt_off + b_dst.toNat]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst.toNat) (BitVec.ofNat 32 nd.toNat) = scr_rel := by
    dsimp only [scr_rel]; rw [@bv_ofNat_toNat_eq 32 nd]
  rw [hrel_eq] at hrel_p hocc_rel
  refine ⟨hb_idx_n, hrel_p.1, hrel_p.2.1, hrel_p.2.2.1, hrel_p.2.2.2, hocc_rel, fun hb_cap => ?_⟩
  dsimp only [scr_rel]; rw [List.getElem?_eq_getElem hb_cap, Option.getD_some]

private theorem fidWl_push0_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {occ_end g : BitVec 64} {lhs0 mw1 b0 : BitVec 32} {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_end.toNat co bkt_off occ_bkt scr0 scr)
    (hgat : FidGateAt 64 F_cur cv scr0 g_len g.toNat)
    (_hs0_g : scr0[g.toNat]? = some lhs0) (hs0_g1 : scr0[g.toNat + 1]? = some mw1)
    (hg_co : g_len ≤ co) (hg_lt : g.toNat < g_len) (hoe_lo : g_len ≤ occ_end.toNat)
    (hoe_ev : (occ_end.toNat - g_len) % 2 = 0) (hb0 : b0.toNat < occ_bkt)
    (hle : (occ_end + BitVec.setWidth 64 (1#32 + (mw1 &&& 0xFF#32)) * 2#64).toNat ≤ co) :
    let arity := mw1 &&& 0xFF#32
    let bkt_64 := BitVec.ofNat 64 bkt_off
    let scr_p0 := ((scr.set occ_end.toNat (g.setWidth 32)).set (occ_end.toNat + 1)
      (scr[bkt_off + b0.toNat]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b0.toNat) (BitVec.ofNat 32 occ_end.toNat)
    occ_end.toNat + (1 + arity.toNat) * 2 ≤ co ∧
    (bkt_64 + b0.setWidth 64).toNat = bkt_off + b0.toNat ∧
    (occ_end + 1#64).toNat = occ_end.toNat + 1 ∧
    (occ_end + 2#64).toNat = occ_end.toNat + 2 ∧
    g.setWidth 32 = BitVec.ofNat 32 g.toNat ∧
    scr_p0.length = c.scratch_cap ∧
    M8CtrlLayout c scr_p0 g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_p0[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr_p0 g_len ht_off ht_sz ∧
    FidOccNodesOk 64 F_cur cv g_len (occ_end.toNat + 2) co bkt_off occ_bkt scr0 scr_p0 ∧
    (∀ (hb_cap : bkt_off + b0.toNat < scr.length),
      ((scr.set occ_end.toNat (g.setWidth 32)).set (occ_end.toNat + 1)
        (scr[bkt_off + b0.toNat]'hb_cap)).set (bkt_off + b0.toNat)
          (occ_end.setWidth 32) = scr_p0) := by
  intro arity bkt_64 scr_p0; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay' := hlay
  rcases hlay with ⟨hc_cap, _, _, hg24, _, _, _, _, _, _, _, _, _, _, _, _, _, hbh, hht_cap, _⟩
  have hgat' := hgat; obtain ⟨_, mword, _, hg1, _, _, _, har_64, _, _⟩ := hgat
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hs0_g1)
  have har_le64 : arity.toNat ≤ 64 := by dsimp only [arity]; rw [← hmw]; exact har_64
  have hocc_c := hocc.2.1
  have h1a : (1#32 + arity).toNat = 1 + arity.toNat := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hmul_lt : ((1#32 + arity).setWidth 64 * 2#64).toNat = (1 + arity.toNat) * 2 := by
    rw [BitVec.toNat_mul, bv_zext32_toNat, h1a, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hoe_fit : occ_end.toNat + (1 + arity.toNat) * 2 ≤ co :=
    (by rw [BitVec.toNat_add, hmul_lt, Nat.mod_eq_of_lt (by omega)] :
      (occ_end + (1#32 + arity).setWidth 64 * 2#64).toNat = _) ▸ hle
  have hbkt64_n : bkt_64.toNat = bkt_off := by
    dsimp only [bkt_64]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb0_n : (bkt_64 + b0.setWidth 64).toNat = bkt_off + b0.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hg_32 : g.setWidth 32 = BitVec.ofNat 32 g.toNat := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hoe_32 : occ_end.setWidth 32 = BitVec.ofNat 32 occ_end.toNat := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hpush0 := fidWl_push_pres hlay' hscrl hpref hht hoe_lo (by omega) hb0
    (entry := g.setWidth 32)
  have hocc_p0 := fidOccNodesOk_push (slot := 0) hocc hoe_ev (by omega) (by omega)
    (by omega) hg_lt (by omega) hgat'
    (by rw [hs0_g1, Option.getD_some]; exact Nat.zero_le _) hb0 hg_co (by omega)
  refine ⟨hoe_fit, hb0_n, bv64_add1_lt (by omega), bv64_add_nat_lt 2 (by decide) (by omega),
    hg_32, hpush0.1, hpush0.2.1, hpush0.2.2.1, hpush0.2.2.2,
    by simpa only [scr_p0, hg_32, ite_true] using hocc_p0, fun hb_cap => ?_⟩
  dsimp only [scr_p0]; rw [hoe_32, List.getElem?_eq_getElem hb_cap, Option.getD_some]

private theorem fidWl_pushs_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {occ_s g : BitVec 64} {s_i mw1 bs : BitVec 32} {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : FidOccNodesOk 64 F_cur cv g_len occ_s.toNat co bkt_off occ_bkt scr0 scr)
    (hgat : FidGateAt 64 F_cur cv scr0 g_len g.toNat)
    (hs0_g1 : scr0[g.toNat + 1]? = some mw1)
    (hg_co : g_len ≤ co) (hg_lt : g.toNat < g_len)
    (hs_lt : s_i.toNat < (mw1 &&& 0xFF#32).toNat)
    (hoes_lo : g_len ≤ occ_s.toNat)
    (hoes_cap : occ_s.toNat + 2 * ((mw1 &&& 0xFF#32).toNat - s_i.toNat) ≤ co)
    (hoes_ev : (occ_s.toNat - g_len) % 2 = 0) (hbs : bs.toNat < occ_bkt)
    (hg_32 : g.setWidth 32 = BitVec.ofNat 32 g.toNat) :
    let bkt_64 := BitVec.ofNat 64 bkt_off
    let entry_s := ((s_i + 1#32) <<< 24) ||| g.setWidth 32
    let scr_ps := ((scr.set occ_s.toNat entry_s).set (occ_s.toNat + 1)
      (scr[bkt_off + bs.toNat]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + bs.toNat) (BitVec.ofNat 32 occ_s.toNat)
    (bkt_64 + bs.setWidth 64).toNat = bkt_off + bs.toNat ∧ occ_s.toNat + 2 ≤ co ∧
    (occ_s + 1#64).toNat = occ_s.toNat + 1 ∧ (occ_s + 2#64).toNat = occ_s.toNat + 2 ∧
    (s_i + 1#32).toNat = s_i.toNat + 1 ∧ scr_ps.length = c.scratch_cap ∧
    M8CtrlLayout c scr_ps g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_ps[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv scr0 scr_ps g_len ht_off ht_sz ∧
    FidOccNodesOk 64 F_cur cv g_len (occ_s.toNat + 2) co bkt_off occ_bkt scr0 scr_ps ∧
    (∀ (hb_cap : bkt_off + bs.toNat < scr.length),
      ((scr.set occ_s.toNat entry_s).set (occ_s.toNat + 1)
        (scr[bkt_off + bs.toNat]'hb_cap)).set (bkt_off + bs.toNat)
          (occ_s.setWidth 32) = scr_ps) := by
  intro bkt_64 entry_s scr_ps; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay' := hlay
  rcases hlay with ⟨hc_cap, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbh, hht_cap, _⟩
  have hgat' := hgat; obtain ⟨_, mword, _, hg1, _, _, _, har_64, _, _⟩ := hgat
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hs0_g1)
  have har_le64 : (mw1 &&& 0xFF#32).toNat ≤ 64 := hmw ▸ har_64
  have hoes_hi : occ_s.toNat + 2 ≤ co := by omega
  have hbkt64_n : bkt_64.toNat = bkt_off := by
    dsimp only [bkt_64]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs_n : (bkt_64 + bs.setWidth 64).toNat = bkt_off + bs.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hs1_n : (s_i + 1#32).toNat = s_i.toNat + 1 := bv32_add1_lt_of (by omega)
  have hoes_32 : occ_s.setWidth 32 = BitVec.ofNat 32 occ_s.toNat := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hs1_32 : s_i + 1#32 = BitVec.ofNat 32 (s_i.toNat + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hs1_n, bv32_ofNat_toNat (by omega)])
  have hentry_eq : entry_s =
      (BitVec.ofNat 32 (s_i.toNat + 1) <<< 24) ||| BitVec.ofNat 32 g.toNat := by
    dsimp only [entry_s]; rw [hs1_32, hg_32]
  have hpush := fidWl_push_pres hlay' hscrl hpref hht hoes_lo hoes_hi hbs (entry := entry_s)
  have hocc_ps := fidOccNodesOk_push hocc hoes_ev (by omega) hoes_hi (by omega) hg_lt (by omega)
    hgat' (by rw [hs0_g1, Option.getD_some]; change s_i.toNat + 1 ≤ (mw1 &&& 0xFF#32).toNat; omega)
    hbs hg_co (by omega)
  have hsn0 : s_i.toNat + 1 ≠ 0 := by omega
  refine ⟨hbs_n, hoes_hi, bv64_add1_lt (by omega), bv64_add_nat_lt 2 (by decide) (by omega),
    hs1_n, hpush.1, hpush.2.1, hpush.2.2.1, hpush.2.2.2,
    by simpa only [scr_ps, ite_eq_right hsn0, ← hentry_eq] using hocc_ps, fun hb_cap => ?_⟩
  dsimp only [scr_ps]; rw [hoes_32, List.getElem?_eq_getElem hb_cap, Option.getD_some]

private theorem fidWl_stOk_of_eval {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat} {scr0 : List (BitVec 32)} {s s' : FullState} {er : BitVec 64}
    (hok : FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 s)
    (hc_cap : ctrl_off < c.scratch_cap) (_he2_0 : (er &&& 2#64) = 0#64)
    (hdw' : FullDenseInvW c F0 F_cur s') (hcv' : s'.core.cur_vars = s.core.cur_vars)
    (hfl' : s'.core.fuel = s.core.fuel)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr)
    (hpref' : ∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?)
    (hht' : FidCongHtInv 64 F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf g_len ht_off ht_sz)
    (hq' : M8QueueCtx c s'.scratch.scratch_buf g_len ctrl_off ht_off ht_sz)
    (hfr' : ∀ idx < c.scratch_cap, idx < ht_off →
      (ctrl_off = c.scratch_cap → s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
      (∀ o b i q, M8CtrlLayout c s.scratch.scratch_buf g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)) :
    FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 s' := by
  have ⟨_, hcvs, hfls, _, hlays, _, _, hoccs⟩ := hok
  have hlay' : M8CtrlLayout c s'.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz := by
    rcases hq' with hcap | ⟨o', b', i', q', hlo⟩
    · exact absurd hcap (Nat.ne_of_lt hc_cap)
    · exact fid_m8CtrlLayout_eq_of_frame hlays hlo hfr'
  exact ⟨hdw', hcv'.trans hcvs, hfl'.trans hfls, (hcv'.trans hcvs) ▸ hrepr', hlay', hpref',
    (hcv'.trans hcvs) ▸ hht', fidOccNodesOk_of_ev_frame hoccs hlays hfr'⟩

end WorklistHelpers

section WorklistSubExprs

private def fidWl_relinkExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reprPtr scrPtr : V i64) (occ_u : V i32) (bkt_64 gn : V i64)
    (nd slot_i : V i32) (er : V i64) (Jrel : L []) : Expr V L rs :=
  .let_ ⟨.and i64, (.var er, (.imm 4, ()))⟩ fun p721 =>
  .let_ ⟨.cmp .ne i64 .bool rfl, (.var p721.1, (.imm 0, ()))⟩ fun p722 =>
  .jnz (.var p722.1) (
    .group (sig := [[i32]]) (fun _ => .cons (fun p823 =>
      .let_ ⟨.zext 32 64, (.var p823.1, ())⟩ fun p824 =>
      .let_ ⟨.add i64, (.var gn, (.var p824.1, ()))⟩ fun p825 =>
      .let_ ⟨.mul i64, (.var p825.1, (.imm 4, ()))⟩ fun p826 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p826.1, ()))⟩ fun p827 =>
      .load i32 (.var p827.1) fun v828 =>
      .call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
        (.var reprPtr, (.var v828, ())) fun p829 =>
      .let_ ⟨.lshr i32, (.var p829.1, (.imm 1, ()))⟩ fun p830 =>
      .let_ ⟨.sub i32, (.var occ_u, (.imm 1, ()))⟩ fun p831 =>
      .let_ ⟨.and i32, (.var p830.1, (.var p831.1, ()))⟩ fun p832 =>
      .let_ ⟨.zext 32 64, (.var nd, ())⟩ fun p833 =>
      .let_ ⟨.add i64, (.var p833.1, (.imm 1, ()))⟩ fun p834 =>
      .let_ ⟨.mul i64, (.var p834.1, (.imm 4, ()))⟩ fun p835 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p835.1, ()))⟩ fun p836 =>
      .let_ ⟨.zext 32 64, (.var p832.1, ())⟩ fun p837 =>
      .let_ ⟨.add i64, (.var bkt_64, (.var p837.1, ()))⟩ fun p838 =>
      .let_ ⟨.mul i64, (.var p838.1, (.imm 4, ()))⟩ fun p839 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p839.1, ()))⟩ fun p840 =>
      .load i32 (.var p840.1) fun v841 =>
      .store (t := i32) (.var v841) (.var p836.1) (
      .let_ ⟨.zext 32 64, (.var p832.1, ())⟩ fun p842 =>
      .let_ ⟨.add i64, (.var bkt_64, (.var p842.1, ()))⟩ fun p843 =>
      .let_ ⟨.mul i64, (.var p843.1, (.imm 4, ()))⟩ fun p844 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p844.1, ()))⟩ fun p845 =>
      .store (t := i32) (.var nd) (.var p845.1) (.jump Jrel ()))) .nil)
    (fun J723 =>
      .let_ ⟨.cmp .eq i32 .bool rfl, (.var slot_i, (.imm 0, ()))⟩ fun p724 =>
      .jnz (.var p724.1) (.jump J723.1 (.imm 0, ()))
        (.let_ ⟨.add i32, (.imm 1, (.var slot_i, ()))⟩ fun p725 => .jump J723.1 (.var p725.1, ())))
  ) (.jump Jrel ())

private theorem fidWl_relink_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 : List (BitVec 32)} {sj : FullState} {mj : Mem 64} {gn er : BitVec 64}
    {nd slot_i : BitVec 32} {R : Mem 64 → Prop} {Jrel : Cont []} {Q : Post [i64]} {X : XPost}
    (hg_co : g_len ≤ ctrl_off) (_hht_cap : ht_off + ht_sz ≤ c.scratch_cap)
    (hc_cap : ctrl_off < c.scratch_cap)
    (ho_pos : 0 < occ_bkt) (hopow : ∃ p, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p)
    (hnd_lo : g_len ≤ nd.toNat) (hnd_hi : nd.toNat + 1 < occ_end)
    (hnd_ev : (nd.toNat - g_len) % 2 = 0)
    (hnd1_n : (nd.setWidth 64 + 1#64).toNat = nd.toNat + 1)
    (hgn_lt : gn.toNat < g_len) (hgat_gn : FidGateAt 64 F_cur cv0 scr0 g_len gn.toNat)
    (hslot_le : slot_i.toNat ≤ ((scr0[gn.toNat + 1]?.getD 0#32) &&& 0xFF#32).toNat)
    (hokj : FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 sj)
    (hmj : (FullMem c sj ⋆ R) mj)
    (hJrel : ∀ m_nd,
      (∃ snd : FullState,
        FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz occ_end scr0 snd ∧ (FullMem c snd ⋆ R) m_nd) → Jrel () m_nd) :
    wp Γ Q X (fidWl_relinkExpr c.pRepr c.pScratchBuf (BitVec.ofNat 32 occ_bkt)
      (BitVec.ofNat 64 bkt_off) gn nd slot_i er Jrel) mj := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨hdwj, hcvj, hflj, hreprj, hlay_j, hprefj, hht_j, hocc_j⟩ := hokj
  have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len
  unfold fidWl_relinkExpr; m6b_steps; m6b_split
  · clear hc; m6b_to_group
    refine wp_join_group (ts := [i32])
      (fun (r_off, ()) mr => mr = mj ∧ (gn.toNat + r_off.toNat < g_len ∧
        ∃ v : BitVec 32, scr0[gn.toNat + r_off.toNat]? = some v ∧ v.toNat < 2 * cv0))
      (fun _ ⟨r_off, ⟨⟩⟩ mr ⟨hmr, hr_lt, rv0, hrv0_get, hrv0_lt⟩ => by
        subst mr
        have hgnr_n : (gn + r_off.setWidth 64).toNat = gn.toNat + r_off.toNat := by
          rw [BitVec.toNat_add, bv_zext32_toNat r_off, Nat.mod_eq_of_lt (by omega)]
        have hgnr_arr : (gn + r_off.setWidth 64).toNat < sj.scratch.scratch_buf.length := by
          rw [hgnr_n]; omega
        have hscr_r0 : sj.scratch.scratch_buf[(gn + r_off.setWidth 64).toNat]'hgnr_arr = rv0 :=
          (list_getElem_congr hgnr_n hgnr_arr (by omega)).trans
            (scr_eq_of_pref hprefj hr_lt (by omega) hrv0_get)
        m6b_steps; m6b_call hFind
        refine ⟨F_cur, 2 * cv0, sj.core.repr, FullReprRest c sj ⋆ R,
          hcvj ▸ hreprj, ?_, focus_full_repr hmj,
          fun dst repri mi hrl_i hrepr_i _ _ _ hmi => ?_⟩
        · change (sj.scratch.scratch_buf[(gn + r_off.setWidth 64).toNat]'hgnr_arr).toNat < 2 * cv0
          rw [hscr_r0]; exact hrv0_lt
        let sj_r : FullState := { sj with core := { sj.core with repr := repri } }
        have hscrl_jr : sj_r.scratch.scratch_buf.length = c.scratch_cap := hscrl_j
        have hmi' : (FullMem c sj_r ⋆ R) mi := unfocus_full_repr hmi; clear hmi
        have hoki := fidWlStOk_with_repr hokj (hrl_i.trans hdwj.1.core_ok.repr_len) hrepr_i
        let b_dst := (dst >>> (1 : Nat)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
        have hbdst_lt : b_dst.toNat < occ_bkt := fid_bkt_lt ho_pos hopow dst
        obtain ⟨hb_idx_n, hscrl_rel, hlay_rel, hpref_rel, hht_rel, hocc_rel, hrel_eq⟩ :=
          fidWl_relink_step_prep hlay_j hscrl_j hprefj (hcvj ▸ hht_j) hocc_j hnd_lo hnd_hi
            hnd_ev hnd1_n hbdst_lt
        have hoe_co : occ_end ≤ ctrl_off := hocc_j.2.1
        have hbh_j : bkt_off + occ_bkt ≤ ht_off :=
          hlay_j.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hnd1_nat : (nd.setWidth 64 + (1 : BitVec 64)).toNat = nd.toNat + 1 := hnd1_n
        have hb_dst_arr0 : (BitVec.ofNat 64 bkt_off + b_dst.setWidth 64).toNat <
            sj_r.scratch.scratch_buf.length := by rw [hscrl_jr, hb_idx_n]; omega
        have hnd1_arr0 : (nd.setWidth 64 + (1 : BitVec 64)).toNat <
            sj_r.scratch.scratch_buf.length := by rw [hscrl_jr, hnd1_nat]; omega
        have hb_dst_arr1 : (BitVec.ofNat 64 bkt_off + b_dst.setWidth 64).toNat <
            (sj_r.scratch.scratch_buf.set (nd.setWidth 64 + (1 : BitVec 64)).toNat
              (sj_r.scratch.scratch_buf[(BitVec.ofNat 64 bkt_off +
                b_dst.setWidth 64).toNat]'hb_dst_arr0)).length := by
          rw [List.length_set]; exact hb_dst_arr0
        have hfs_r := focus_full_scratch_fid hmi'; clear hmi'
        generalize hRs_r : FullScratchRestFid c sj_r ⋆ R = Rs_r at hfs_r
        m6b_steps
        have hrel_val : sj_r.scratch.scratch_buf[(BitVec.ofNat 64 bkt_off +
            b_dst.setWidth 64).toNat]'hb_dst_arr0 =
            sj.scratch.scratch_buf[bkt_off + b_dst.toNat]'(by rw [hscrl_j]; omega) :=
          list_getElem_congr hb_idx_n hb_dst_arr0 (by rw [hscrl_j]; omega)
        rw [hrel_val, show (1 : BitVec 64) = 1#64 from rfl, hb_idx_n, hnd1_n, hrel_eq _] at hm
        subst hRs_r
        exact hJrel m ⟨_, fidWlStOk_with_scr hoki hscrl_rel hlay_rel hpref_rel hht_rel hocc_rel,
          unfocus_full_scratch_fid hm⟩)
      (fun Jr hJr => by
        obtain ⟨lhs_g, mw_g, hg0_g, hg1_g, hl_lt_g, _, _, _, hrhs_g, _⟩ := hgat_gn
        rw [hg1_g, Option.getD_some] at hslot_le
        m6b_split
        · have hs0 : slot_i.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
          m6b_let
          exact hJr (0, ()) mj ⟨rfl, by simp [hgn_lt], lhs_g, by simpa using hg0_g, hl_lt_g⟩
        · have hsne : slot_i.toNat ≠ 0 := fun h =>
            (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
          have h1s : (1#32 + slot_i).toNat = 2 + (slot_i.toNat - 1) := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]; omega
          obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_g (slot_i.toNat - 1) (by omega)
          m6b_let; rw [show (1 : BitVec 32) + slot_i = 1#32 + slot_i from rfl]
          exact hJr (1#32 + slot_i, ()) mj
            ⟨rfl, by rw [h1s]; omega, rv, by rw [h1s, ← Nat.add_assoc]; exact hrv_get, hrv_lt⟩)
  · m6b_let; exact hJrel mj ⟨sj, hokj, hmj⟩

private def fidWl_rehashExpr {V : Ty → Type} {L : List Ty → Type}
    (h scrPtr tlim ht_off_64 ht_sz_o g_len ctrl_off i_o rehashes g_o : V i64)
    (ep : V i32) (ticks_n : V i64) (do_grow do_flush : V .bool)
    (Jreh : L [i64, i64, i64, i64, i64]) : Expr V L [i64] :=
  .group (sig := [[]]) (fun _ => .cons (fun _ =>
    .let_ ⟨.cmp .ult i64 .bool rfl, (.var ticks_n, (.var tlim, ()))⟩ fun p485 =>
    .jnz (.var p485.1) (
      .group (sig := [[i64, i64]]) (fun _ => .cons (fun p496 =>
        .group (sig := [[i64]]) (fun J506 => .cons (fun p516 =>
          .let_ ⟨.cmp .ult i64 .bool rfl, (.var p516.1, (.var p496.1, ()))⟩ fun p526 =>
          .jnz (.var p526.1) (
            .let_ ⟨.add i64, (.var ht_off_64, (.var p516.1, ()))⟩ fun p527 =>
            .let_ ⟨.mul i64, (.var p527.1, (.imm 4, ()))⟩ fun p528 =>
            .let_ ⟨.add i64, (.var scrPtr, (.var p528.1, ()))⟩ fun p529 =>
            .store (t := i32) (.imm 4294967295) (.var p529.1) (
            .let_ ⟨.add i64, (.var p516.1, (.imm 1, ()))⟩ fun p530 =>
            .jump J506.1 (.var p530.1, ()))
          ) (
            .let_ ⟨.add i64, (.var h, (.imm 1144, ()))⟩ fun p527 =>
            .store (t := i64) (.imm 0) (.var p527.1) (
            .group (sig := [[i64, i64]]) (fun J528 => .cons (fun p538 =>
              .let_ ⟨.cmp .ult i64 .bool rfl, (.var p538.2.1, (.var g_len, ()))⟩ fun p548 =>
              .jnz (.var p548.1) (
                .let_ ⟨.add i64, (.var h, (.imm 1024, ()))⟩ fun p549 =>
                .load i64 (.var p549.1) fun v550 =>
                .let_ ⟨.cmp .eq i64 .bool rfl, (.var v550, (.imm 0, ()))⟩ fun p551 =>
                .jnz (.var p551.1) (
                  .let_ ⟨.cmp .ult i64 .bool rfl, (.var p538.1, (.var tlim, ()))⟩ fun p552 =>
                  .jnz (.var p552.1) (
                    .let_ ⟨.add i64, (.var p538.2.1, (.imm 1, ()))⟩ fun p553 =>
                    .let_ ⟨.mul i64, (.var p553.1, (.imm 4, ()))⟩ fun p554 =>
                    .let_ ⟨.add i64, (.var scrPtr, (.var p554.1, ()))⟩ fun p555 =>
                    .load i32 (.var p555.1) fun v556 =>
                    .let_ ⟨.and i32, (.var v556, (.imm 255, ()))⟩ fun p557 =>
                    .let_ ⟨.add i64, (.var p538.1, (.imm 1, ()))⟩ fun p558 =>
                    .call (as := [i64, i64, i64, i64, i32, i64]) (bs := [i64])
                      "full_cong_eval_gate"
                      (.var h, (.var p538.2.1, (.var ht_off_64, (.var p496.1,
                        (.var ep, (.var ctrl_off, ())))))) fun p559 =>
                    .let_ ⟨.and i64, (.var p559.1, (.imm 2, ()))⟩ fun p560 =>
                    .let_ ⟨.cmp .ne i64 .bool rfl, (.var p560.1, (.imm 0, ()))⟩ fun p561 =>
                    .jnz (.var p561.1) (.ret (.imm 20, ())) (
                      .let_ ⟨.add i64, (.var p538.2.1, (.imm 2, ()))⟩ fun p562 =>
                      .let_ ⟨.zext 32 64, (.var p557.1, ())⟩ fun p563 =>
                      .let_ ⟨.add i64, (.var p562.1, (.var p563.1, ()))⟩ fun p564 =>
                      .jump J528.1 (.var p558.1, (.var p564.1, ())))
                  ) (.jump Jreh (.var p496.1, (.var p516.1, (.var p538.1, (.var p496.2.1,
                      (.var p538.2.1, ()))))))
                ) (.jump Jreh (.var p496.1, (.var p516.1, (.var p538.1, (.var p496.2.1,
                    (.var p538.2.1, ()))))))
              ) (.jump Jreh (.var p496.1, (.var p516.1, (.var p538.1, (.var p496.2.1,
                  (.var p538.2.1, ()))))))
            ) .nil) (fun J528 => .jump J528.1 (.var ticks_n, (.imm 0, ())))))
        ) .nil) (fun J506 => .jump J506.1 (.imm 0, ()))) .nil)
      (fun J486 =>
        .jnz (.var do_grow) (
          .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p586 =>
          .let_ ⟨.shl i64, (.var ht_sz_o, (.var p586.1, ()))⟩ fun p587 =>
          .let_ ⟨.add i64, (.var ctrl_off, (.imm 7, ()))⟩ fun p588 =>
          .let_ ⟨.mul i64, (.var p588.1, (.imm 4, ()))⟩ fun p589 =>
          .let_ ⟨.add i64, (.var scrPtr, (.var p589.1, ()))⟩ fun p590 =>
          .let_ ⟨.trunc 64 32, (.var p587.1, ())⟩ fun p591 =>
          .store (t := i32) (.var p591.1) (.var p590.1) (
          .jump J486.1 (.var p587.1, (.var rehashes, ())))
        ) (
          .let_ ⟨.add i64, (.var rehashes, (.imm 1, ()))⟩ fun p586 =>
          .jump J486.1 (.var ht_sz_o, (.var p586.1, ()))))
    ) (.jump Jreh (.var ht_sz_o, (.var i_o, (.var ticks_n, (.var rehashes, (.var g_o, ()))))))
  ) .nil) (fun J465 =>
    .jnz (.var do_grow) (.jump J465.1 ())
      (.jnz (.var do_flush) (.jump J465.1 ())
        (.jump Jreh (.var ht_sz_o, (.var i_o, (.var ticks_n, (.var rehashes, (.var g_o, ()))))))))

private theorem fidWl_rehash_wp (Γ : Env)
    (hEvalGate : ∀ a m Q X, fidCongEvalGateSpec a m Q X →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 occ_bkt bkt_off inq_off q_off ht_off occ_end : Nat}
    {ht_sz_o g_len ctrl_off tlim i_o ticks_o rehashes g_o ticks_n : BitVec 64}
    {ql ep : BitVec 32} {do_grow do_flush : Bool}
    {scr0 : List (BitVec 32)} {sa : FullState} {ma : Mem 64} {R : Mem 64 → Prop}
    {Q : Post [i64]} {X : XPost} {Jreh : Cont [i64, i64, i64, i64, i64]}
    (hg_pos : 0 < g_len.toNat) (hht_pos : 0 < ht_sz_o.toNat) (hht_bnd : ht_sz_o.toNat < 2 ^ 30)
    (hg_ht_le : g_len.toNat ≤ ht_off) (hc_cap : ctrl_off.toNat < c.scratch_cap)
    (hc7_n : (ctrl_off + 7).toNat = ctrl_off.toNat + 7)
    (htlim_le : tlim.toNat ≤ 2 ^ 63 - 1) (hreh_le : rehashes.toNat ≤ 4)
    (hta_lo : ticks_o.toNat ≤ ticks_n.toNat) (hta_hi : ticks_n.toNat ≤ tlim.toNat + 2)
    (hta_eq : ticks_n.toNat = ticks_o.toNat →
      sa.core.inconsistent = 0#64 ∧
      (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat)
    (hgrow_ok : do_grow = true →
      ht_sz_o.toNat < fidCongHashMaxSz ∧ ht_off + 2 * ht_sz_o.toNat ≤ c.scratch_cap)
    (hflush_ok : do_flush = true → do_grow = false ∧ rehashes.toNat < 4)
    (hseq0 : FidGateSeqOk 64 F_cur cv0 scr0 g_len.toNat 0)
    (hoka : FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
      q_off ht_off ht_sz_o.toNat occ_end scr0 sa)
    (hma : (FullMem c sa ⋆ R) ma)
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = cv0 → s'.core.fuel = fuel0 →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJreh : ∀ ys mb,
      (match ys with
        | (ht_sz_b, _i_b, ticks_b, reh_b, _g_b, ()) => ∃ sb : FullState,
          0 < ht_sz_b.toNat ∧ ht_sz_b.toNat < 2 ^ 30 ∧
          reh_b.toNat ≤ 4 ∧ ticks_o.toNat ≤ ticks_b.toNat ∧ ticks_b.toNat ≤ tlim.toNat + 3 ∧
          (ticks_o.toNat < ticks_b.toNat ∨
            (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
          FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz_b.toNat occ_end scr0 sb ∧ (FullMem c sb ⋆ R) mb) → Jreh ys mb) :
    wp Γ Q X (fidWl_rehashExpr c.hdr c.pScratchBuf tlim
      (BitVec.ofNat 64 ht_off) ht_sz_o g_len ctrl_off i_o rehashes g_o ep
      ticks_n do_grow do_flush Jreh) ma := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨hdw_a, hcv_a, hfl_a, hrepr_a, hlay_a, hpref_a, hht_a, hocc_a⟩ := hoka
  have hscrl_a := hdw_a.1.scratch_ok.scratch_buf_len
  have hht_o_cap : ht_off + ht_sz_o.toNat ≤ c.scratch_cap :=
    hlay_a.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hho_n : (BitVec.ofNat 64 ht_off).toNat = ht_off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstep_a : ticks_o.toNat < ticks_n.toNat ∨
      (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat := by
    by_cases hteq : ticks_n.toNat = ticks_o.toNat
    · exact Or.inr (hta_eq hteq).2
    · exact Or.inl (by omega)
  have hjreh_sa : Jreh (ht_sz_o, i_o, ticks_n, rehashes, g_o, ()) ma :=
    hJreh (ht_sz_o, i_o, ticks_n, rehashes, g_o, ()) ma
      ⟨sa, hht_pos, hht_bnd, hreh_le, hta_lo, by omega, hstep_a, hoka, hma⟩
  unfold fidWl_rehashExpr; m6b_to_group
  refine wp_join_group (ts := [])
    (fun () m_in => m_in = ma ∧ (do_grow = true ∨ do_flush = true)) ?_
    (fun J465 hJ465 => by
      m6b_split
      · m6b_let; exact hJ465 () ma ⟨rfl, Or.inl hc⟩
      · m6b_split
        · m6b_let; exact hJ465 () ma ⟨rfl, Or.inr hc⟩
        · m6b_let; exact hjreh_sa)
  rintro _ ⟨⟩ m_in ⟨hm_in, hgf⟩; subst m_in
  m6b_steps; m6b_split
  · have hta_lt : ticks_n.toNat < tlim.toNat := bv64_ult_lt hc
    clear hc; m6b_to_group
    refine wp_join_group (ts := [i64, i64])
      (fun (ht_sz_n, reh_n, ()) mg => ∃ sg : FullState,
        0 < ht_sz_n.toNat ∧ ht_sz_n.toNat < 2 ^ 30 ∧ reh_n.toNat ≤ 4 ∧
        FullDenseInvW c F0 F_cur sg ∧ sg.core.cur_vars = cv0 ∧ sg.core.fuel = fuel0 ∧
        FullCongReprInv F_cur (2 * cv0) sg.core.repr ∧
        (ticks_n.toNat = ticks_o.toNat → sg.core.inconsistent = 0#64) ∧
        M8CtrlLayout c sg.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off
          inq_off q_off ht_off ht_sz_n.toNat ∧
        (∀ idx < g_len.toNat, sg.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
        FidOccNodesOk 64 F_cur cv0 g_len.toNat occ_end ctrl_off.toNat bkt_off occ_bkt
          scr0 sg.scratch.scratch_buf ∧ (FullMem c sg ⋆ R) mg) ?_
      (fun J486 hJ486 => by
        m6b_split
        · obtain ⟨hht_1m, hht2_cap⟩ := hgrow_ok hc
          have hshl2 : (ht_sz_o <<< (1 : BitVec 64)).toNat = 2 * ht_sz_o.toNat :=
            fid_shl1_toNat hht_1m
          have hshl32 : (ht_sz_o <<< (1 : BitVec 64)).setWidth 32 =
              BitVec.ofNat 32 (2 * ht_sz_o.toNat) :=
            BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth, hshl2, BitVec.toNat_ofNat])
          have hc7_arr : (ctrl_off + (7 : BitVec 64)).toNat < sa.scratch.scratch_buf.length := by
            have := hlay_a.2.1; rw [hc7_n, hscrl_a]; omega
          have hfs_g := focus_full_scratch_fid hma
          generalize hRs_g : FullScratchRestFid c sa ⋆ R = Rs_g at hfs_g
          clear hc; m6b_steps
          change (array (t := i32) c.pScratchBuf
            (sa.scratch.scratch_buf.set (ctrl_off + (7 : BitVec 64)).toNat
              ((ht_sz_o <<< (1 : BitVec 64)).setWidth 32)) ⋆ Rs_g) m at hm
          rw [hc7_n, hshl32] at hm; subst hRs_g
          obtain ⟨hscrl_g, hlay_g, hpref_g, hocc_g⟩ :=
            fid_m8CtrlLayout_grow hlay_a hscrl_a hpref_a hocc_a hht2_cap
          unfold fidCongHashMaxSz at hht_1m
          exact hJ486 (ht_sz_o <<< (1 : BitVec 64), rehashes, ()) m
            ⟨_, by rw [hshl2]; omega, by rw [hshl2]; omega, hreh_le,
              fid_denseInvW_with_scr hdw_a hscrl_g, hcv_a, hfl_a, hrepr_a,
              fun h => (hta_eq h).1, hshl2 ▸ hlay_g, hpref_g, hocc_g,
              unfocus_full_scratch_fid hm⟩
        · have hfl_t : do_flush = true := by
            rcases hgf with hg | hf
            · rw [hg] at hc; cases hc
            · exact hf
          have hr1_n : (rehashes + 1#64).toNat = rehashes.toNat + 1 :=
            bv64_add1_toNat (n := 4) (hflush_ok hfl_t).2 (by decide)
          clear hc; m6b_steps
          rw [show rehashes + (1 : BitVec 64) = rehashes + 1#64 from rfl]
          exact hJ486 (ht_sz_o, rehashes + 1#64, ()) ma
            ⟨sa, hht_pos, hht_bnd, by have := (hflush_ok hfl_t).2; omega, hdw_a, hcv_a, hfl_a,
              hrepr_a, fun h => (hta_eq h).1, hlay_a, hpref_a, hocc_a, hma⟩)
    rintro _ ⟨ht_sz_n, reh_n, ⟨⟩⟩ mg
      ⟨sg, hht_n_pos, hht_n_bnd, hreh_n_le, hdw_g, hcv_g, hfl_g, hrepr_g, hinc_g,
        hlay_g, hpref_g, hocc_g, hmg⟩
    have hscrl_g := hdw_g.1.scratch_ok.scratch_buf_len
    have hht_n_cap : ht_off + ht_sz_n.toNat ≤ c.scratch_cap :=
      hlay_g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    m6b_to_group
    have hfs_g := focus_full_scratch_fid hmg; clear hmg
    generalize hRs_g : FullScratchRestFid c sg ⋆ R = Rs_g at hfs_g
    refine wp_loop_inv (ts := [i64])
      (fun (ih, ()) mh => ∃ scrh : List (BitVec 32),
        scrh.length = c.scratch_cap ∧ ih.toNat ≤ ht_sz_n.toNat ∧
        M8CtrlLayout c scrh g_len.toNat ctrl_off.toNat occ_bkt bkt_off
          inq_off q_off ht_off ht_sz_n.toNat ∧
        (∀ idx < g_len.toNat, scrh[idx]? = scr0[idx]?) ∧
        (∀ k < ih.toNat, scrh[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
        FidOccNodesOk 64 F_cur cv0 g_len.toNat occ_end ctrl_off.toNat
          bkt_off occ_bkt scr0 scrh ∧ (array (t := i32) c.pScratchBuf scrh ⋆ Rs_g) mh)
      (fun (ih, ()) _ => ht_sz_n.toNat - ih.toNat)
      (fun Jh hJh => by
        m6b_steps; exact hJh (0#64, ()) mg ⟨sg.scratch.scratch_buf, hscrl_g, Nat.zero_le _,
          hlay_g, hpref_g, fun _ h => absurd h (Nat.not_lt_zero _), hocc_g, hfs_g⟩)
      (fun Jh (ih, ()) mh ⟨scrh, hscrl_h, hih_le, hlay_h, hpref_h, hht_h, hocc_h, hmh⟩ ihh => ?_)
    m6b_split
    · have hih_lt : ih.toNat < ht_sz_n.toNat := bv64_ult_lt hc
      obtain ⟨hhti_n, hhti_arr, hih1, hscrl_h', hlay_h', hpref_h', hht_h', hocc_h'⟩ :=
        fidWl_rehash_clear_step hlay_h hscrl_h hpref_h hht_h hocc_h hih_lt
      clear hc; m6b_steps; rw [hhti_n] at hm
      exact ihh (ih + 1#64, ()) m (by dsimp only; omega)
        ⟨_, hscrl_h', by rw [hih1]; omega, hlay_h', hpref_h',
         fun k hk => hht_h' k (hih1 ▸ hk), hocc_h', hm⟩
    · have hih_eq : ih.toNat = ht_sz_n.toNat := by have := bv64_ult_not_lt hc; omega
      rw [hih_eq] at hht_h
      have hht_clr : FidCongHtInv 64 F_cur cv0 scr0 scrh g_len.toNat ht_off ht_sz_n.toNat :=
        fun k hk => Or.inl (hht_h k hk)
      subst hRs_g; have hmh_u := unfocus_full_scratch_fid hmh
      clear hc; m6b_steps
      let sg_r : FullState :=
        { sg with scratch := { sg.scratch with scratch_buf := scrh, res_sz := 0#64 } }
      have hok_r : FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat
          occ_bkt bkt_off inq_off q_off ht_off ht_sz_n.toNat occ_end scr0 sg_r :=
        ⟨fid_denseInvW_with_scr hdw_g hscrl_h 0#64, hcv_g, hfl_g, hrepr_g, hlay_h, hpref_h,
          hht_clr, hocc_h⟩
      m6b_to_group
      refine wp_loop_inv (ts := [i64, i64])
        (fun (ticks_r, gr, ()) mr => ∃ sr : FullState,
          gr.toNat ≤ g_len.toNat ∧ ticks_n.toNat ≤ ticks_r.toNat ∧
          ticks_r.toNat ≤ tlim.toNat + 1 ∧ (0 < gr.toNat → ticks_n.toNat < ticks_r.toNat) ∧
          (ticks_n.toNat = ticks_o.toNat → gr.toNat = 0 → sr.core.inconsistent = 0#64) ∧
          FidGateSeqOk 64 F_cur cv0 scr0 g_len.toNat gr.toNat ∧
          FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
            bkt_off inq_off q_off ht_off ht_sz_n.toNat occ_end scr0 sr ∧ (FullMem c sr ⋆ R) mr)
        (fun (_, gr, ()) _ => g_len.toNat - gr.toNat)
        (fun Jr hJr => by
          m6b_steps; exact hJr (ticks_n, 0#64, ()) m ⟨sg_r, Nat.zero_le _, Nat.le_refl _,
            by omega, fun h => absurd h (by decide), fun h _ => hinc_g h, hseq0, hok_r, hm⟩)
        (fun Jr (ticks_r, gr, ()) mr
          ⟨sr, hgr_le, htr_lo, htr_hi, hgr_lt, htr_inc, hseq_r, hok_r, hmr⟩ ihr => ?_)
      have ⟨hdw_r, hcv_r, hfl_r, hrepr_r, hlay_r, hpref_r, hht_r, hocc_r⟩ := hok_r
      have hscrl_r := hdw_r.1.scratch_ok.scratch_buf_len
      have hreh_exit : (¬ gr.toNat < g_len.toNat ∨ sr.core.inconsistent ≠ 0#64 ∨
          ¬ ticks_r.toNat < tlim.toNat) → ticks_o.toNat < ticks_r.toNat := by
        intro hwhy; rcases Nat.eq_or_lt_of_le hta_lo with hteq | htlt
        · rcases Nat.eq_zero_or_pos gr.toNat with hg0 | hgp
          · rcases hwhy with h1 | h2 | h3
            · omega
            · exact absurd (htr_inc hteq.symm hg0) h2
            · omega
          · exact hteq ▸ hgr_lt hgp
        · exact Nat.lt_of_lt_of_le htlt htr_lo
      m6b_steps; m6b_split
      · have hgr_lt_g : gr.toNat < g_len.toNat := bv64_ult_lt hc
        clear hc; m6b_steps; m6b_split
        · clear hc; m6b_split
          · have htr_lt : ticks_r.toNat < tlim.toNat := bv64_ult_lt hc
            obtain ⟨hgat_r, hseq_r'⟩ := fidGateSeqOk_inv_lt hseq_r hgr_lt_g
            have ⟨_, mword_r, _, hscr_r1, _, hbd_r, _, _, _, _⟩ := hgat_r
            have hgr1_n : (gr + 1#64).toNat = gr.toNat + 1 :=
              bv64_add1_toNat (by omega) (by omega)
            have hgr1_arr : (gr + 1#64).toNat < sr.scratch.scratch_buf.length := by
              rw [hgr1_n]; omega
            have hsr_g1 : sr.scratch.scratch_buf[(gr + 1#64).toNat]'hgr1_arr = mword_r :=
              scr_eq_of_pref hpref_r (by omega) hgr1_arr (by rw [hgr1_n]; exact hscr_r1)
            let ar_r := mword_r &&& 0xFF#32
            have hnext_gr : (gr + 2#64 + ar_r.setWidth 64).toNat = gr.toNat + 2 + ar_r.toNat :=
              bv64_add_zext32 (k := 2) (by omega)
            have hseq_r'' : FidGateSeqOk 64 F_cur cv0 scr0 g_len.toNat
                (gr + 2#64 + ar_r.setWidth 64).toNat := by
              rw [hnext_gr]; simpa only [hscr_r1, Option.getD_some, ar_r] using hseq_r'
            clear hc; m6b_steps; m6b_call hEvalGate
            dsimp only [fidCongEvalGateSpec]; rw [hho_n]
            refine ⟨64, c, F0, F_cur, sr, scr0, g_len.toNat, R, by decide, rfl, hdw_r,
              hcv_r ▸ hrepr_r, hht_n_pos, hht_n_bnd, hgr_lt_g, by omega, hht_n_cap, hpref_r,
              hcv_r ▸ hgat_r, hcv_r ▸ hht_r,
              Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay_r⟩, hmr,
              fun er su mu hdwu hcvu hflu _ _ hrepru hprefu hhtu hqu hfru he2_u hmu => ?_⟩
            m6b_split
            · m6b_steps
              exact hQ 20#64 su mu hdwu (hcvu.trans hcv_r) (hflu.trans hfl_r)
                ((hcvu.trans hcv_r) ▸ hrepru) (Or.inr rfl)
                (fun _ => he2_u (bne_iff_ne.mp hc)) hmu
            · have he2_0 : (er &&& 2#64) = 0#64 := by simpa using hc
              have hoku := fidWl_stOk_of_eval hok_r hc_cap he2_0 hdwu hcvu hflu
                hrepru hprefu hhtu hqu (hfru he2_0)
              have htr1 : (ticks_r + 1#64).toNat = ticks_r.toNat + 1 := bv64_add1_lt (by omega)
              have hsr_g1_any : ∀ h, sr.scratch.scratch_buf[(gr + (1 : BitVec 64)).toNat]'h =
                  mword_r := fun _ => hsr_g1
              m6b_steps
              rw [show ticks_r + (1 : BitVec 64) = ticks_r + 1#64 from rfl, hsr_g1_any _,
                show (255 : BitVec 32) = 0xFF#32 from rfl, show (2 : BitVec 64) = 2#64 from rfl]
              exact ihr (ticks_r + 1#64, gr + 2#64 + ar_r.setWidth 64, ()) mu
                (by dsimp only; rw [hnext_gr]; omega)
                ⟨su, by rw [hnext_gr]; exact hbd_r, by rw [htr1]; omega, by rw [htr1]; omega,
                 fun _ => by rw [htr1]; omega, fun _ hg0 => by rw [hnext_gr] at hg0; omega,
                 hseq_r'', hoku, hmu⟩
          · m6b_let; exact hJreh (ht_sz_n, ih, ticks_r, reh_n, gr, ()) mr
              ⟨sr, hht_n_pos, hht_n_bnd, hreh_n_le, by omega, by omega,
               Or.inl (hreh_exit (Or.inr (Or.inr (bv64_ult_not_lt hc)))), hok_r, hmr⟩
        · m6b_let; exact hJreh (ht_sz_n, ih, ticks_r, reh_n, gr, ()) mr
            ⟨sr, hht_n_pos, hht_n_bnd, hreh_n_le, by omega, by omega,
             Or.inl (hreh_exit (Or.inr (Or.inl (beq_eq_false_iff_ne.mp hc)))), hok_r, hmr⟩
      · m6b_let; exact hJreh (ht_sz_n, ih, ticks_r, reh_n, gr, ()) mr
          ⟨sr, hht_n_pos, hht_n_bnd, hreh_n_le, by omega, by omega,
           Or.inl (hreh_exit (Or.inl (bv64_ult_not_lt hc))), hok_r, hmr⟩
  · m6b_let; exact hjreh_sa

private def fidWl_pushsExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reprPtr scrPtr : V i64) (occ_u : V i32) (bkt_64 occ_s_init g : V i64)
    (arity : V i32) (Jocc : L [i64]) : Expr V L rs :=
  .group (sig := [[i64, i32]]) (fun J395 => .cons (fun p495 =>
    .let_ ⟨.cmp .ult i32 .bool rfl, (.var p495.2.1, (.var arity, ()))⟩ fun p497 =>
    .jnz (.var p497.1) (
      .let_ ⟨.add i64, (.var g, (.imm 2, ()))⟩ fun p498 =>
      .let_ ⟨.zext 32 64, (.var p495.2.1, ())⟩ fun p499 =>
      .let_ ⟨.add i64, (.var p498.1, (.var p499.1, ()))⟩ fun p500 =>
      .let_ ⟨.mul i64, (.var p500.1, (.imm 4, ()))⟩ fun p501 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p501.1, ()))⟩ fun p502 =>
      .load i32 (.var p502.1) fun v503 =>
      .call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
        (.var reprPtr, (.var v503, ())) fun p504 =>
      .let_ ⟨.lshr i32, (.var p504.1, (.imm 1, ()))⟩ fun p505 =>
      .let_ ⟨.sub i32, (.var occ_u, (.imm 1, ()))⟩ fun p506 =>
      .let_ ⟨.and i32, (.var p505.1, (.var p506.1, ()))⟩ fun p507 =>
      .let_ ⟨.mul i64, (.var p495.1, (.imm 4, ()))⟩ fun p508 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p508.1, ()))⟩ fun p509 =>
      .let_ ⟨.add i32, (.var p495.2.1, (.imm 1, ()))⟩ fun p510 =>
      .let_ ⟨.shl i32, (.var p510.1, (.imm 24, ()))⟩ fun p511 =>
      .let_ ⟨.trunc 64 32, (.var g, ())⟩ fun p512 =>
      .let_ ⟨.or i32, (.var p511.1, (.var p512.1, ()))⟩ fun p513 =>
      .store (t := i32) (.var p513.1) (.var p509.1) (
      .let_ ⟨.add i64, (.var p495.1, (.imm 1, ()))⟩ fun p514 =>
      .let_ ⟨.mul i64, (.var p514.1, (.imm 4, ()))⟩ fun p515 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p515.1, ()))⟩ fun p516 =>
      .let_ ⟨.zext 32 64, (.var p507.1, ())⟩ fun p517 =>
      .let_ ⟨.add i64, (.var bkt_64, (.var p517.1, ()))⟩ fun p518 =>
      .let_ ⟨.mul i64, (.var p518.1, (.imm 4, ()))⟩ fun p519 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p519.1, ()))⟩ fun p520 =>
      .load i32 (.var p520.1) fun v521 =>
      .store (t := i32) (.var v521) (.var p516.1) (
      .let_ ⟨.zext 32 64, (.var p507.1, ())⟩ fun p522 =>
      .let_ ⟨.add i64, (.var bkt_64, (.var p522.1, ()))⟩ fun p523 =>
      .let_ ⟨.mul i64, (.var p523.1, (.imm 4, ()))⟩ fun p524 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p524.1, ()))⟩ fun p525 =>
      .let_ ⟨.trunc 64 32, (.var p495.1, ())⟩ fun p526 =>
      .store (t := i32) (.var p526.1) (.var p525.1) (
      .let_ ⟨.add i64, (.var p495.1, (.imm 2, ()))⟩ fun p527 =>
      .let_ ⟨.add i32, (.var p495.2.1, (.imm 1, ()))⟩ fun p528 =>
      .jump J395.1 (.var p527.1, (.var p528.1, ())))))
    ) (.jump Jocc (.var p495.1, ()))) .nil)
  (fun J395 => .jump J395.1 (.var occ_s_init, (.imm 0, ())))

private theorem fidWl_pushs_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st_p0 : FullState} {m_p0 : Mem 64} {occ_end g : BitVec 64}
    {mw1 : BitVec 32} {R : Mem 64 → Prop} {Jocc : Cont [i64]} {Q : Post [i64]} {X : XPost}
    (hg_co : g_len ≤ ctrl_off) (_hht_cap : ht_off + ht_sz ≤ c.scratch_cap)
    (hc_cap : ctrl_off < c.scratch_cap)
    (ho_pos : 0 < occ_bkt) (hopow : ∃ p, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p)
    (hg_lt : g.toNat < g_len) (hgat_1 : FidGateAt 64 F_cur cv0 scr0 g_len g.toNat)
    (hscr0_g1 : scr0[g.toNat + 1]? = some mw1)
    (hocc_fit : occ_end.toNat + (1 + (mw1 &&& 0xFF#32).toNat) * 2 ≤ ctrl_off)
    (hoe_lo : g_len ≤ occ_end.toNat) (hoe_ev : (occ_end.toNat - g_len) % 2 = 0)
    (hoe2_n : (occ_end + 2#64).toNat = occ_end.toNat + 2)
    (hg_32 : g.setWidth 32 = BitVec.ofNat 32 g.toNat)
    (hok_p0 : FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz (occ_end.toNat + 2) scr0 st_p0)
    (hm_p0 : (FullMem c st_p0 ⋆ R) m_p0)
    (hJocc : ∀ (occ_e' : BitVec 64) me,
      (∃ se : FullState, g_len ≤ occ_e'.toNat ∧ occ_e'.toNat ≤ ctrl_off ∧
        (occ_e'.toNat - g_len) % 2 = 0 ∧
        FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz occ_e'.toNat scr0 se ∧ (FullMem c se ⋆ R) me) → Jocc (occ_e', ()) me) :
    wp Γ Q X (fidWl_pushsExpr c.pRepr c.pScratchBuf (BitVec.ofNat 32 occ_bkt)
      (BitVec.ofNat 64 bkt_off) (occ_end + 2#64) g (mw1 &&& 0xFF#32) Jocc) m_p0 := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  let arity := mw1 &&& 0xFF#32
  have ⟨_, mword, _, hg1, _, hbd_g, _, _, hrhs_1, _⟩ := hgat_1
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hscr0_g1)
  have hbd_mw : g.toNat + 2 + arity.toNat ≤ g_len := by dsimp only [arity]; rw [← hmw]; exact hbd_g
  unfold fidWl_pushsExpr; m6b_to_group
  refine wp_loop_inv (ts := [i64, i32])
    (fun (occ_s, s_i, ()) ms => ∃ st_s : FullState,
      s_i.toNat ≤ arity.toNat ∧ g_len ≤ occ_s.toNat ∧
      occ_s.toNat + 2 * (arity.toNat - s_i.toNat) ≤ ctrl_off ∧
      (occ_s.toNat - g_len) % 2 = 0 ∧
      FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
        ht_off ht_sz occ_s.toNat scr0 st_s ∧ (FullMem c st_s ⋆ R) ms)
    (fun (_, s_i, ()) _ => arity.toNat - s_i.toNat)
    (fun Js hJs => by
      m6b_steps
      exact hJs (occ_end + 2#64, 0#32, ()) m_p0 ⟨_, Nat.zero_le _, by rw [hoe2_n]; omega,
        by rw [hoe2_n]; dsimp only [arity]; omega, by rw [hoe2_n]; omega, hoe2_n ▸ hok_p0, hm_p0⟩)
    (fun Js (occ_s, s_i, ()) ms ⟨st_s, hs_le, hoes_lo, hoes_cap, hoes_ev, hok_s, hms⟩ ihs => ?_)
  have ⟨hdw_s, hcv_s, hfl_s, hrepr_s, hlay_s, hpref_s, hht_s, hocc_s⟩ := hok_s
  have hscrl_s := hdw_s.1.scratch_ok.scratch_buf_len
  m6b_split
  · have hs_lt : s_i.toNat < arity.toNat := bv32_ult_lt hc
    obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_1 s_i.toNat (by simpa only [arity, ← hmw] using hs_lt)
    have hg2s_n : (g + 2#64 + s_i.setWidth 64).toNat = g.toNat + 2 + s_i.toNat :=
      bv64_add_zext32 (k := 2) (by omega)
    have hg2s_arr : (g + 2#64 + s_i.setWidth 64).toNat < st_s.scratch.scratch_buf.length := by
      rw [hg2s_n]; omega
    have hs_g2s : st_s.scratch.scratch_buf[(g + 2#64 + s_i.setWidth 64).toNat]'hg2s_arr = rv :=
      scr_eq_of_pref hpref_s (by omega) hg2s_arr (by rw [hg2s_n]; exact hrv_get)
    clear hc; m6b_steps; m6b_call hFind
    refine ⟨F_cur, 2 * cv0, st_s.core.repr, FullReprRest c st_s ⋆ R, hcv_s ▸ hrepr_s,
      (congrArg BitVec.toNat (hs_g2s : st_s.scratch.scratch_buf[(g + (2 : BitVec 64) +
        s_i.setWidth 64).toNat]'hg2s_arr = rv)) ▸ hrv_lt,
      focus_full_repr hms, fun rr repr_r mr hrl_r hrepr_r _ _ _ hmr => ?_⟩
    let st_r : FullState := { st_s with core := { st_s.core with repr := repr_r } }
    have hscrl_sr : st_r.scratch.scratch_buf.length = c.scratch_cap := hscrl_s
    have hmr' : (FullMem c st_r ⋆ R) mr := unfocus_full_repr hmr; clear hmr
    have hokr := fidWlStOk_with_repr hok_s (hrl_r.trans hdw_s.1.core_ok.repr_len) hrepr_r
    let bs := (rr >>> (1 : Nat)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
    have hbs_lt : bs.toNat < occ_bkt := fid_bkt_lt ho_pos hopow rr
    obtain ⟨hbs_n, hoes_hi, hoes1_n, hoes2_n, hs1_n, hscrl_ps, hlay_ps, hpref_ps, hht_ps,
      hocc_ps, hps_eq⟩ :=
      fidWl_pushs_step_prep hlay_s hscrl_s hpref_s (hcv_s ▸ hht_s) hocc_s
        hgat_1 hscr0_g1 hg_co hg_lt hs_lt hoes_lo hoes_cap hoes_ev hbs_lt hg_32
    have hco_bkt : ctrl_off < bkt_off ∧ bkt_off + occ_bkt ≤ c.scratch_cap := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hq1, hq2, hq3, hbh, hhc, _⟩ := hlay_s
      exact ⟨by omega, by omega⟩
    let entry_s := ((s_i + 1#32) <<< 24) ||| g.setWidth 32
    have hoes1_nat : (occ_s + (1 : BitVec 64)).toNat = occ_s.toNat + 1 := hoes1_n
    rw [show (1 : BitVec 32) = 1#32 from rfl, show (1 : BitVec 64) = 1#64 from rfl] at *
    have hbs_arr1 : (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat <
        (st_r.scratch.scratch_buf.set occ_s.toNat entry_s).length := by
      rw [List.length_set, hscrl_sr, hbs_n]; omega
    have hoes1_arr1 : (occ_s + 1#64).toNat <
        (st_r.scratch.scratch_buf.set occ_s.toNat entry_s).length := by
      rw [List.length_set, hscrl_sr, hoes1_nat]; omega
    have hbs_arr2 : (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat <
        ((st_r.scratch.scratch_buf.set occ_s.toNat entry_s).set (occ_s + 1#64).toNat
          ((st_r.scratch.scratch_buf.set occ_s.toNat entry_s)[
            (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1)).length := by
      simp only [List.length_set]; rw [hscrl_sr, hbs_n]; omega
    have hfs_ps := focus_full_scratch_fid hmr'; clear hmr'
    generalize hRs_ps : FullScratchRestFid c st_r ⋆ R = Rs_ps at hfs_ps
    m6b_steps
    let scr_ps := ((st_s.scratch.scratch_buf.set occ_s.toNat entry_s).set (occ_s.toNat + 1)
      (st_s.scratch.scratch_buf[bkt_off + bs.toNat]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + bs.toNat) (BitVec.ofNat 32 occ_s.toNat)
    have hmem_scr :
        ((st_r.scratch.scratch_buf.set occ_s.toNat
            (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32)).set
          (occ_s + (1 : BitVec 64)).toNat
          ((st_r.scratch.scratch_buf.set occ_s.toNat
              (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32))[
            (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1)).set
          (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat (occ_s.setWidth 32) = scr_ps := by
      have h2 : (st_r.scratch.scratch_buf.set occ_s.toNat entry_s)[
          (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1 =
          st_s.scratch.scratch_buf[bkt_off + bs.toNat]'(by rw [hscrl_s]; omega) := by
        rw [List.getElem_set_ne (by change _ ≠ _; rw [hbs_n]; omega)]
        exact list_getElem_congr hbs_n _ _
      change ((st_r.scratch.scratch_buf.set occ_s.toNat entry_s).set
        (occ_s + 1#64).toNat
        ((st_r.scratch.scratch_buf.set occ_s.toNat entry_s)[
          (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1)).set
        (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat (occ_s.setWidth 32) = scr_ps
      rw [h2, hoes1_nat, hbs_n]; exact hps_eq (by rw [hscrl_s]; omega)
    dsimp only [bs] at hmem_scr
    have hm_ps_arr : (array (t := i32) c.pScratchBuf scr_ps ⋆ Rs_ps) m :=
      (congrArg (fun xs => (array (t := i32) c.pScratchBuf xs ⋆ Rs_ps) m) hmem_scr).mp hm
    subst hRs_ps
    have hok_ps' : FidWlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
        ht_off ht_sz (occ_s.toNat + 2) scr0
        { st_r with scratch := { st_r.scratch with scratch_buf := scr_ps } } :=
      fidWlStOk_with_scr hokr hscrl_ps hlay_ps hpref_ps hht_ps hocc_ps
    exact ihs (occ_s + 2#64, s_i + 1#32, ()) m (by dsimp only; omega)
      ⟨_, by rw [hs1_n]; omega, by rw [hoes2_n]; omega, by rw [hoes2_n, hs1_n]; omega,
        by rw [hoes2_n]; omega, hoes2_n ▸ hok_ps', unfocus_full_scratch_fid hm_ps_arr⟩
  · clear hc; m6b_let; exact hJocc occ_s ms ⟨st_s, hoes_lo, by omega, hoes_ev, hok_s, hms⟩

end WorklistSubExprs

section WorklistMain

theorem full_cong_worklist_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hEvalGate : ∀ a m Q X, fidCongEvalGateSpec a m Q X →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, fidCongWorklistSpec a m Q X → Func.wp Γ full_cong_worklist_body a m Q X := by
  rintro ⟨h, g_len, ctrl_off, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, occ_bkt, bkt_off, inq_off, q_off, ht_off, ht_sz, R,
     rfl, hdw0, hrepr0, hg_pos, hht_max, hlay0, hseq0, hpref0, hht0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hht_bnd : ht_sz < 2 ^ 30 := by unfold fidCongHashMaxSz at hht_max; omega
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have ⟨hc_cap, _hc_8, hg_co, hg_24, _, _, _, _, _, _,
    ho_pos, ho_8192, hopow, hht_pos, hcq, hqi, hib, hbh, hht_cap, _, _, _⟩ := hlay0
  have hg_ht_le : g_len.toNat ≤ ht_off := by omega
  have hscrl0 := hdw0.1.scratch_ok.scratch_buf_len
  m6b_to_group
  refine wp_join_group (ts := [i64]) (fun (tlim, ()) mt => mt = m0 ∧ tlim.toNat ≤ 2 ^ 63 - 1) ?_ ?_
  · rintro _ ⟨tlim, ⟨⟩⟩ mt ⟨hmt, htlim_le⟩; subst mt
    rcases fidWl_ctrl_arith hht_bnd hscrl0 hlay0 with
      ⟨hc1_n, hc2_n, hc3_n, hc4_n, hc5_n, hc6_n, hc7_n,
      hco0_arr, hco1_arr, hco2_arr, hco3_arr, hco4_arr, hco5_arr, hco6_arr, hco7_arr,
      heq_co0, heq_co1, heq_co2, heq_co3, heq_co6, heq_co7,
      hbkt32, hinq32, hq32, hho32, hhs32, hocc32, hho_n, hhs_n⟩
    let occ_u := BitVec.ofNat 32 occ_bkt
    let bkt_64 := BitVec.ofNat 64 bkt_off
    m6b_steps
    have hfs0 := focus_full_scratch_fid hm0; clear hm0
    generalize hRs0 : FullScratchRestFid c s0 ⋆ R = Rs0 at hfs0
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) mi => ∃ scri : List (BitVec 32),
        scri.length = c.scratch_cap ∧ i.toNat ≤ occ_bkt ∧
        M8CtrlLayout c scri g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
        (∀ idx < g_len.toNat, scri[idx]? = scr0[idx]?) ∧
        FidCongHtInv 64 F_cur cv0 scr0 scri g_len.toNat ht_off ht_sz ∧
        (∀ b < i.toNat, scri[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
        (array (t := i32) c.pScratchBuf scri ⋆ Rs0) mi)
      (fun (i, ()) _ => occ_bkt - i.toNat)
      (fun Ji hJi => by
        m6b_steps; exact hJi (0#64, ()) m0 ⟨s0.scratch.scratch_buf, hscrl0, Nat.zero_le _,
          hlay0, hpref0, hht0, (fun _ h => absurd h (Nat.not_lt_zero _)), hfs0⟩)
      (fun Ji (i, ()) mi ⟨scri, hscrl_i, hi_le, hlay_i, hpref_i, hht_i, hbkt_i, hmi⟩ ihi => ?_)
    m6b_split
    · have hi_lt : i.toNat < occ_bkt := by
        have hlt := bv64_ult_lt hc
        rw [heq_co0, hocc32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
      obtain ⟨hbkt_i_n, hinq_i_n, hbi_arr, hii_arr, hi1_n,
        hscrl', hlay', hpref', hht', hbkt'⟩ :=
        fidWl_phase0_clear_step hlay_i hscrl_i hpref_i hht_i hbkt_i hi_lt
      clear hc; rw [heq_co1, hbkt32, heq_co2, hinq32]; m6b_steps
      rw [hbkt_i_n, hinq_i_n] at hm
      exact ihi (i + 1#64, ()) m (by dsimp only; omega)
        ⟨_, hscrl', by omega, hlay', hpref', hht', fun b hb => hbkt' b (hi1_n ▸ hb), hm⟩
    · have hi_eq : i.toNat = occ_bkt := by
        have := bv64_ult_not_lt hc
        rw [heq_co0, hocc32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; omega
      rw [hi_eq] at hbkt_i
      have hc4_arr : (ctrl_off + 4).toNat < scri.length := by rw [hc4_n, hscrl_i]; omega
      have hc5_arr : (ctrl_off + 5).toNat < (scri.set (ctrl_off + 4).toNat 0#32).length := by
        rw [List.length_set, hc5_n, hscrl_i]; omega
      clear hc; m6b_steps; rw [hc4_n, hc5_n] at hm; subst hRs0
      have hm_p0 := unfocus_full_scratch_fid hm
      obtain ⟨hscrl_p0, hlay_p0, hpref_p0, hht_p0, hocc_p0⟩ :=
        fidWl_phase0_finalize hlay_i hscrl_i hpref_i hht_i hbkt_i rfl
      let st_p0 : FullState :=
        { s0 with scratch := { s0.scratch with
          scratch_buf := (scri.set (ctrl_off.toNat + 4) 0#32).set (ctrl_off.toNat + 5) 0#32 } }
      have hok_p0 : FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
          inq_off q_off ht_off ht_sz g_len.toNat scr0 st_p0 :=
        ⟨fid_denseInvW_with_scr hdw0 hscrl_p0, rfl, rfl, hrepr0, hlay_p0, hpref_p0, hht_p0, hocc_p0⟩
      m6b_to_group
      refine wp_loop_inv (ts := [i64, i64, i64])
        (fun (occ_end, ticks, g, ()) m1 => ∃ s1 : FullState,
          g.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ occ_end.toNat ∧ occ_end.toNat ≤ ctrl_off.toNat ∧
          (occ_end.toNat - g_len.toNat) % 2 = 0 ∧ ticks.toNat ≤ tlim.toNat + 2 ∧
          FidGateSeqOk 64 F_cur cv0 scr0 g_len.toNat g.toNat ∧
          FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz occ_end.toNat scr0 s1 ∧ (FullMem c s1 ⋆ R) m1)
        (fun (_, _, g, ()) _ => g_len.toNat - g.toNat)
        (fun J1 hJ1 => by
          m6b_steps; exact hJ1 (g_len, 0#64, 0#64, ()) m ⟨st_p0, Nat.zero_le _, Nat.le_refl _,
            hg_co, by simp, Nat.zero_le _, hseq0, hok_p0, hm_p0⟩)
        (fun J1 (occ_end, ticks, g, ()) m1
            ⟨s1, hg_le, hoe_lo, hoe_hi, hoe_ev, htk_le, hseq_1, hok_1, hm1⟩ ih1 => ?_)
      have ⟨hdw_1, hcv_1, hfl_1, hrepr_1, hlay_1, hpref_1, hht_1, hocc_1⟩ := hok_1
      have hscrl_1 := hdw_1.1.scratch_ok.scratch_buf_len
      m6b_to_group
      refine wp_join_group (ts := []) (fun () mp2 => mp2 = m1) ?_ ?_
      · rintro _ ⟨⟩ mp2 hmp2; subst mp2
        let p5Addr := c.pScratchBuf + BitVec.ofNat 64 (4 * (ctrl_off.toNat + 5))
        have fidWl_v_eq : ∀ {st : FullState} {m : Mem 64}
            (h : ctrl_off.toNat + 5 < st.scratch.scratch_buf.length), (FullMem c st ⋆ R) m →
            ((loadVal m i32 p5Addr).getD 0#32).toNat =
              (st.scratch.scratch_buf[ctrl_off.toNat + 5]'h).toNat := fun h hm => by
          dsimp only [p5Addr]; rw [FullArenaTactics.load_full_scratch_buf h hm, Option.getD_some]
        m6b_to_group
        refine wp_loop_inv (ts := [i64, i64, i64, i64, i64, i32])
          (fun (ht_sz_o, _i, ticks_o, rehashes, _g, _ep, ()) mo => ∃ so : FullState,
            0 < ht_sz_o.toNat ∧ ht_sz_o.toNat < 2 ^ 30 ∧
            rehashes.toNat ≤ 4 ∧ ticks_o.toNat ≤ tlim.toNat + 3 ∧
            FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
              q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 so ∧ (FullMem c so ⋆ R) mo)
          (fun (_, _, ticks_o, _, _, _, ()) mo =>
            (tlim.toNat - ticks_o.toNat) * (occ_bkt + 1) +
              ((loadVal mo i32 p5Addr).getD 0#32).toNat) ?_ ?_
        · intro Jo hJo
          m6b_steps; rw [heq_co7, hhs32]
          exact hJo (BitVec.ofNat 64 ht_sz, i, ticks, 0#64, g, 3#32, ()) m1
            ⟨s1, by rw [hhs_n]; exact hht_pos, by rw [hhs_n]; exact hht_bnd, Nat.zero_le _,
              by omega, by rw [hhs_n]; exact hok_1, hm1⟩
        rintro Jo ⟨ht_sz_o, _i_o, ticks_o, rehashes, _g_o, ep, ⟨⟩⟩ mo
          ⟨so, hht_o_pos, hht_o_bnd, hreh_le, hto_le, hok_o, hmo⟩ iho
        have ⟨hdw_o, hcv_o, hfl_o, hrepr_o, hlay_o, hpref_o, hht_o, hocc_o⟩ := hok_o
        have hscrl_o := hdw_o.1.scratch_ok.scratch_buf_len
        have hht_o_cap : ht_off + ht_sz_o.toNat ≤ c.scratch_cap :=
          hlay_o.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hc5_o : ctrl_off.toNat + 5 < so.scratch.scratch_buf.length := by
          have := hlay_o.1; omega
        have hp5_o : ((loadVal mo i32 p5Addr).getD 0#32).toNat =
            (so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
          rw [fidWl_v_eq hc5_o hmo, List.getElem?_eq_getElem hc5_o, Option.getD_some]
        m6b_to_group
        refine wp_join_group (ts := [])
          (fun () m_out => ∃ sx : FullState,
            FullDenseInvW c F0 F_cur sx ∧ sx.core.cur_vars = cv0 ∧ sx.core.fuel = fuel0 ∧
            FullCongReprInv F_cur (2 * cv0) sx.core.repr ∧ (FullMem c sx ⋆ R) m_out) ?_ ?_
        · rintro _ ⟨⟩ m_out ⟨sx, hdwx, hcvx, hflx, hreprx, hmx⟩
          m6b_to_group
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mr => ∃ sx' : FullState,
              FullDenseInvW c F0 F_cur sx' ∧ sx'.core.cur_vars = cv0 ∧
              sx'.core.fuel = fuel0 ∧ FullCongReprInv F_cur (2 * cv0) sx'.core.repr ∧
              (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullMem c sx' ⋆ R) mr)
            (fun _ ⟨r, ⟨⟩⟩ mr ⟨sx', hdwx', hcvx', hflx', hreprx', hr, huns, hmx'⟩ => by
              m6b_steps; exact hQ r sx' mr hdwx' hcvx' hflx' (hcvx' ▸ hreprx') hr huns hmx')
            (fun Jret hJret => by
              m6b_steps; m6b_split
              · m6b_steps
                exact hJret (20#64, ()) m_out ⟨sx, hdwx, hcvx, hflx, hreprx, Or.inr rfl,
                  (fun _ => unsat_of_inconsistent_w hdwx.2.1 (bne_iff_ne.mp hc)), hmx⟩
              · m6b_steps
                exact hJret (1#64, ()) m_out ⟨sx, hdwx, hcvx, hflx, hreprx, Or.inl rfl,
                  (fun h => by cases h), hmx⟩)
        intro Jout hJout
        have hjout_so : Jout () mo := hJout () mo ⟨so, hdw_o, hcv_o, hfl_o, hrepr_o, hmo⟩
        m6b_steps; m6b_split
        · have hql_pos : 0 < (so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
            have hlt := bv32_ult_lt (by rw [BitVec.ult] at hc; exact hc)
            have hco5' : (ctrl_off + 5).toNat < so.scratch.scratch_buf.length := by
              rw [hc5_n]; omega
            change 0 < (so.scratch.scratch_buf[(ctrl_off + 5).toNat]'hco5').toNat at hlt
            rw [list_getElem_congr hc5_n hco5' (by omega),
              ← Option.getD_some (a := so.scratch.scratch_buf[ctrl_off.toNat + 5]'(by omega))
                (b := 0#32), ← List.getElem?_eq_getElem (by omega)] at hlt
            exact hlt
          clear hc; m6b_split
          · have hinc_0 : so.core.inconsistent = 0#64 := beq_iff_eq.mp hc
            clear hc; m6b_split
            · have hto_lt : ticks_o.toNat < tlim.toNat := bv64_ult_lt hc
              let qh := so.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32
              let ql := so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32
              let b := so.scratch.scratch_buf[q_off + qh.toNat]?.getD 0#32
              let nqh := (qh + 1#32) &&& (occ_u - 1#32)
              obtain ⟨hco4_o, hco5_o, hq_ld_arr, hscrl_pop, hlay_pop, hpref_pop, hht_pop,
                hnd0_ptr, hocc_pop, hco5_s4, hinq_s45_arr, hbkt_s45i_arr, hnd0_scr3,
                hscr_pop_eq, hql_pop_lt⟩ :=
                fidWl_pop_step_prep hlay_o hscrl_o hpref_o hht_o hocc_o hql_pos hc4_n hc5_n
              clear hc
              have hfs_o := focus_full_scratch_fid hmo; clear hmo
              generalize hRs_o : FullScratchRestFid c so ⋆ R = Rs_o at hfs_o
              rw [heq_co0, heq_co1, hbkt32, heq_co2, hinq32, heq_co3, hq32]
              m6b_steps; rw [hnd0_scr3 _]; rw [hscr_pop_eq] at hm; subst hRs_o
              have hm_pop := unfocus_full_scratch_fid hm
              let scr_pop := (((so.scratch.scratch_buf.set (ctrl_off.toNat + 4) nqh).set
                (ctrl_off.toNat + 5) (ql - 1#32)).set (inq_off + b.toNat) 0#32).set
                (bkt_off + b.toNat) 0xFFFFFFFF#32
              let st_pop : FullState :=
                { so with scratch := { so.scratch with scratch_buf := scr_pop } }
              have hok_pop : FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                  bkt_off inq_off q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 st_pop :=
                fidWlStOk_with_scr hok_o hscrl_pop hlay_pop hpref_pop hht_pop hocc_pop
              let nd0 := so.scratch.scratch_buf[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32
              clear hco4_o hco5_o hq_ld_arr hco5_s4 hinq_s45_arr hbkt_s45i_arr hnd0_scr3
                hscr_pop_eq hscrl_pop hlay_pop hpref_pop hht_pop hocc_pop
              m6b_to_group
              refine wp_loop_inv (ts := [i64, i32])
                (fun (ticks_n, nd, ()) mn => ∃ sn : FullState,
                  ticks_o.toNat ≤ ticks_n.toNat ∧ ticks_n.toNat ≤ tlim.toNat + 2 ∧
                  (ticks_n.toNat = ticks_o.toNat → sn.core.inconsistent = 0#64 ∧
                    (sn.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
                  M6OccNodePtrOk g_len.toNat occ_end.toNat nd ∧
                  FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
                    inq_off q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 sn ∧
                  (FullMem c sn ⋆ R) mn)
                (fun (ticks_n, _, ()) _ => tlim.toNat - ticks_n.toNat)
                (fun Jn hJn => by
                  m6b_steps; exact hJn (ticks_o, nd0, ()) m ⟨st_pop, Nat.le_refl _, by omega,
                    (fun _ => ⟨hinc_0, hql_pop_lt⟩), hnd0_ptr, hok_pop, hm_pop⟩)
                (fun Jn (ticks_n, nd, ()) mn
                  ⟨sn, htn_lo, htn_hi, htn_eq, hnd_ptr, hok_n, hmn⟩ ihn => ?_)
              have ⟨hdw_n, hcv_n, hfl_n, hrepr_n, hlay_n, hpref_n, hht_n, hocc_n⟩ := hok_n
              have hscrl_n := hdw_n.1.scratch_ok.scratch_buf_len
              m6b_to_group
              refine wp_join_group (ts := []) (fun () ma => ∃ sa : FullState,
                ticks_o.toNat ≤ ticks_n.toNat ∧ ticks_n.toNat ≤ tlim.toNat + 2 ∧
                (ticks_n.toNat = ticks_o.toNat → sa.core.inconsistent = 0#64 ∧
                  (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
                FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
                  q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 sa ∧ (FullMem c sa ⋆ R) ma)
                (fun _ ⟨⟩ ma ⟨sa, hta_lo, hta_hi, hta_eq, hok_a, hma⟩ => by
                  rw [heq_co6, hho32]; m6b_to_group
                  refine wp_join_group (ts := [.bool])
                    (fun (do_grow, ()) mg => mg = ma ∧
                      (do_grow = true → ht_sz_o.toNat < fidCongHashMaxSz ∧
                        ht_off + 2 * ht_sz_o.toNat ≤ c.scratch_cap)) ?_
                    (fun Jgr hJgr => by
                      m6b_steps; m6b_split
                      · clear hc; m6b_split
                        · have hlt_1m : ht_sz_o.toNat < fidCongHashMaxSz := bv64_ult_lt hc
                          clear hc; m6b_steps; m6b_split
                          · have hule := bv64_ule_true_le hc
                            change (BitVec.ofNat 64 ht_off +
                              (ht_sz_o <<< (1 : BitVec 64))).toNat ≤
                              (BitVec.ofNat 64 c.scratch_cap).toNat at hule
                            have hshl2 := fid_shl1_toNat hlt_1m
                            have hsum2 :
                                (BitVec.ofNat 64 ht_off + (ht_sz_o <<< (1 : BitVec 64))).toNat =
                                  ht_off + 2 * ht_sz_o.toNat := by
                              unfold fidCongHashMaxSz at hlt_1m
                              rw [BitVec.toNat_add, hho_n, hshl2, Nat.mod_eq_of_lt (by omega)]
                            have hcap64 : (BitVec.ofNat 64 c.scratch_cap).toNat =
                                c.scratch_cap := by
                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                            rw [hsum2, hcap64] at hule
                            m6b_let; exact hJgr (true, ()) ma ⟨rfl, fun _ => ⟨hlt_1m, hule⟩⟩
                          · m6b_let; exact hJgr (false, ()) ma ⟨rfl, fun h => by cases h⟩
                        · m6b_let; exact hJgr (false, ()) ma ⟨rfl, fun h => by cases h⟩
                      · m6b_let; exact hJgr (false, ()) ma ⟨rfl, fun h => by cases h⟩)
                  rintro _ ⟨do_grow, ⟨⟩⟩ mg ⟨hmg, hgrow_ok⟩; subst mg
                  m6b_to_group
                  refine wp_join_group (ts := [.bool])
                    (fun (do_flush, ()) mf => mf = ma ∧
                      (do_flush = true → do_grow = false ∧ rehashes.toNat < 4)) ?_
                    (fun Jfl hJfl => by
                      m6b_split
                      · m6b_let; exact hJfl (false, ()) ma ⟨rfl, fun h => by cases h⟩
                      · have hdg_f : do_grow = false := hc
                        clear hc; m6b_steps; m6b_split
                        · clear hc; m6b_split
                          · m6b_let
                            exact hJfl (true, ()) ma ⟨rfl, fun _ => ⟨hdg_f, bv64_ult_lt hc⟩⟩
                          · m6b_let; exact hJfl (false, ()) ma ⟨rfl, fun h => by cases h⟩
                        · m6b_let; exact hJfl (false, ()) ma ⟨rfl, fun h => by cases h⟩)
                  rintro _ ⟨do_flush, ⟨⟩⟩ mf ⟨hmf, hflush_ok⟩; subst mf
                  m6b_to_group
                  refine wp_join_group (ts := [i64, i64, i64, i64, i64])
                    (fun (ht_sz_b, _i_b, ticks_b, reh_b, _g_b, ()) mb => ∃ sb : FullState,
                      0 < ht_sz_b.toNat ∧ ht_sz_b.toNat < 2 ^ 30 ∧
                      reh_b.toNat ≤ 4 ∧ ticks_o.toNat ≤ ticks_b.toNat ∧
                      ticks_b.toNat ≤ tlim.toNat + 3 ∧
                      (ticks_o.toNat < ticks_b.toNat ∨
                        (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat <
                          ql.toNat) ∧
                      FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
                        inq_off q_off ht_off ht_sz_b.toNat occ_end.toNat scr0 sb ∧
                      (FullMem c sb ⋆ R) mb)
                    (fun _ ⟨ht_sz_b, _i_b, ticks_b, reh_b, _g_b, ⟨⟩⟩ mb
                      ⟨sb, hht_b_pos, hht_b_bnd, hreh_b, htb_lo, htb_hi, hstep_b, hok_b, hmb⟩ => by
                      have hlay_b := hok_b.2.2.2.2.1
                      have hscrl_b := hok_b.1.1.scratch_ok.scratch_buf_len
                      have hql_b_le : (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD
                          0#32).toNat ≤ occ_bkt :=
                        hlay_b.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                      have hc5_b : ctrl_off.toNat + 5 < sb.scratch.scratch_buf.length := by
                        have := hlay_b.1; omega
                      have hdec : (tlim.toNat - ticks_b.toNat) * (occ_bkt + 1) +
                          ((loadVal mb i32 p5Addr).getD 0#32).toNat <
                          (tlim.toNat - ticks_o.toNat) * (occ_bkt + 1) +
                          ((loadVal mo i32 p5Addr).getD 0#32).toNat := by
                        rw [fidWl_v_eq hc5_b hmb, hp5_o,
                          show (sb.scratch.scratch_buf[ctrl_off.toNat + 5]'hc5_b).toNat =
                            (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat by
                            rw [List.getElem?_eq_getElem hc5_b, Option.getD_some]]
                        exact m6Wl_outer_dec hto_lt htb_lo hstep_b hql_b_le
                      m6b_steps; rw [show ep + (1 : BitVec 32) = ep + 1#32 from rfl]
                      exact iho (ht_sz_b, _i_b, ticks_b, reh_b, _g_b, ep + 1#32, ()) mb hdec
                        ⟨sb, hht_b_pos, hht_b_bnd, hreh_b, htb_hi, hok_b, hmb⟩) ?_
                  intro Jreh hJreh
                  exact fidWl_rehash_wp Γ hEvalGate hg_pos hht_o_pos hht_o_bnd hg_ht_le hc_cap
                    hc7_n htlim_le hreh_le hta_lo hta_hi hta_eq hgrow_ok hflush_ok hseq0
                    hok_a hma hQ hJreh) ?_
              intro Jnd hJnd
              m6b_steps; m6b_split
              · have hnd_ne : nd ≠ 0xFFFFFFFF#32 := bne_iff_ne.mp hc
                clear hc; m6b_steps; m6b_split
                · clear hc; m6b_split
                  · have htn_lt : ticks_n.toNat < tlim.toNat := bv64_ult_lt hc
                    rcases hnd_ptr with rfl | ⟨hnd_lo, hnd_hi, hnd_ev⟩
                    · exact absurd rfl hnd_ne
                    have hnd_arr : nd.toNat < sn.scratch.scratch_buf.length := by omega
                    have hnd1_n : (nd.setWidth 64 + 1#64).toNat = nd.toNat + 1 := by
                      rw [BitVec.toNat_add, bv_zext32_toNat,
                        show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                    have hnd1_arr : (nd.setWidth 64 + 1#64).toNat <
                        sn.scratch.scratch_buf.length := by rw [hnd1_n]; omega
                    let entry := sn.scratch.scratch_buf[(nd.setWidth 64).toNat]'
                      (by rw [bv_zext32_toNat]; exact hnd_arr)
                    let nxt := sn.scratch.scratch_buf[(nd.setWidth 64 + 1#64).toNat]'hnd1_arr
                    have hentry_eq : sn.scratch.scratch_buf[nd.toNat]?.getD 0#32 = entry := by
                      dsimp only [entry]
                      rw [list_getElem_congr (bv_zext32_toNat nd) _ hnd_arr,
                        List.getElem?_eq_getElem hnd_arr, Option.getD_some]
                    have hnxt_eq : sn.scratch.scratch_buf[nd.toNat + 1]?.getD 0xFFFFFFFF#32 =
                        nxt := by
                      dsimp only [nxt]
                      rw [list_getElem_congr hnd1_n hnd1_arr (by omega),
                        List.getElem?_eq_getElem (by omega), Option.getD_some]
                    obtain ⟨hgn_lt, hgat_gn, hslot_le, hnxt_ptr⟩ :=
                      hocc_n.2.2.2 nd.toNat hnd_lo hnd_hi hnd_ev
                    rw [hentry_eq] at hgn_lt hgat_gn hslot_le; rw [hnxt_eq] at hnxt_ptr
                    let gn := (entry &&& 0x00FFFFFF#32).setWidth 64
                    have hgn_n : gn.toNat = (entry &&& 0x00FFFFFF#32).toNat := bv_zext32_toNat _
                    let slot_i := entry >>> 24
                    have htn2 : (ticks_n + 2#64).toNat = ticks_n.toNat + 2 :=
                      bv64_add_nat_lt 2 (by decide) (by omega)
                    clear hc; m6b_steps; rw [heq_co6, hho32]; m6b_call hEvalGate
                    dsimp only [fidCongEvalGateSpec]; rw [hho_n]
                    refine ⟨64, c, F0, F_cur, sn, scr0, g_len.toNat, R, by decide, rfl, hdw_n,
                      hcv_n ▸ hrepr_n, hht_o_pos, hht_o_bnd, hgn_n ▸ hgn_lt, hg_ht_le, hht_o_cap,
                      hpref_n, hcv_n ▸ hgn_n ▸ hgat_gn, hcv_n ▸ hht_n,
                      Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay_n⟩, hmn,
                      fun er sj mj hdwj hcvj hflj _ _ hreprj hprefj hhtj hqj hfrj he2_u hmj => ?_⟩
                    m6b_split
                    · m6b_steps
                      exact hQ 20#64 sj mj hdwj (hcvj.trans hcv_n) (hflj.trans hfl_n)
                        ((hcvj.trans hcv_n) ▸ hreprj) (Or.inr rfl)
                        (fun _ => he2_u (bne_iff_ne.mp hc)) hmj
                    · have he2_0 : (er &&& 2#64) = 0#64 := by simpa using hc
                      have hokj := fidWl_stOk_of_eval hok_n hc_cap he2_0 hdwj hcvj hflj hreprj
                        hprefj hhtj hqj (fun idx h1 h2 => hfrj he2_0 idx h1 h2)
                      clear hc; m6b_to_group
                      refine wp_join_group (ts := [])
                        (fun () m_nd => ∃ snd : FullState,
                          FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                            bkt_off inq_off q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 snd ∧
                          (FullMem c snd ⋆ R) m_nd)
                        (fun _ ⟨⟩ m_nd ⟨snd, hok_nd, hm_nd⟩ => by
                          m6b_let; rw [show ticks_n + (2 : BitVec 64) = ticks_n + 2#64 from rfl]
                          exact ihn (ticks_n + 2#64, nxt, ()) m_nd (by dsimp only; rw [htn2]; omega)
                            ⟨snd, by rw [htn2]; omega, by rw [htn2]; omega,
                             fun h => by rw [htn2] at h; omega, hnxt_ptr, hok_nd, hm_nd⟩)
                        (fun Jrel hJrel =>
                          have hslot_gn :
                              slot_i.toNat ≤ (scr0[gn.toNat + 1]?.getD 0#32 &&& 0xFF#32).toNat := by
                            dsimp only [gn, slot_i]; rw [bv_zext32_toNat]; exact hslot_le
                          fidWl_relink_wp Γ hFind hg_co hht_o_cap hc_cap ho_pos hopow
                            hnd_lo hnd_hi hnd_ev hnd1_n (hgn_n ▸ hgn_lt) (hgn_n ▸ hgat_gn)
                            hslot_gn hokj hmj (fun m_nd h => hJrel () m_nd h))
                  · m6b_let; exact hJnd () mn ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩
                · m6b_let; exact hJnd () mn ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩
              · m6b_let; exact hJnd () mn ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩
            · m6b_let; exact hjout_so
          · m6b_let; exact hjout_so
        · m6b_let; exact hjout_so
      · intro Jp2 hJp2
        have hjp2_s1 : Jp2 () m1 := hJp2 () m1 rfl
        m6b_steps; m6b_split
        · have hg_lt : g.toNat < g_len.toNat := bv64_ult_lt hc
          clear hc; m6b_split
          · clear hc; m6b_split
            · have htk_lt : ticks.toNat < tlim.toNat := bv64_ult_lt hc
              obtain ⟨hgat_1, hseq_next⟩ := fidGateSeqOk_inv_lt hseq_1 hg_lt
              have ⟨lhs0, mw1, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, _, _, hrhs_1, _⟩ := hgat_1
              have hg_arr : g.toNat < s1.scratch.scratch_buf.length := by omega
              have hg1_n : (g + 1).toNat = g.toNat + 1 := bv64_add1_lt (by omega)
              have hg1_arr : (g + 1).toNat < s1.scratch.scratch_buf.length := by rw [hg1_n]; omega
              have hs1_g1 : s1.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mw1 :=
                scr_eq_of_pref hpref_1 (by omega) hg1_arr (by rw [hg1_n]; exact hscr0_g1)
              let arity := mw1 &&& 0xFF#32
              have hnext_g : (g + 2#64 + arity.setWidth 64).toNat = g.toNat + 2 + arity.toNat :=
                bv64_add_zext32 (k := 2) (by omega)
              have hseq_next' : FidGateSeqOk 64 F_cur cv0 scr0 g_len.toNat
                  (g + 2#64 + arity.setWidth 64).toNat := by
                rw [hnext_g]; simpa [hscr0_g1, arity] using hseq_next
              have htk2 : (ticks + 2#64).toNat = ticks.toNat + 2 :=
                bv64_add_nat_lt 2 (by decide) (by omega)
              clear hc; m6b_steps; rw [heq_co6, hho32, heq_co7, hhs32]; m6b_call hEvalGate
              dsimp only [fidCongEvalGateSpec]; rw [hho_n, hhs_n]
              refine ⟨64, c, F0, F_cur, s1, scr0, g_len.toNat, R, by decide, rfl, hdw_1,
                hcv_1 ▸ hrepr_1, hht_pos, hht_bnd, hg_lt, hg_ht_le, hht_cap, hpref_1,
                hcv_1 ▸ hgat_1, hcv_1 ▸ hht_1,
                Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay_1⟩, hm1,
                fun er sj mj hdwj hcvj hflj _ _ hreprj hprefj hhtj hqj hfrj he2_u hmj => ?_⟩
              m6b_split
              · m6b_steps
                exact hQ 20#64 sj mj hdwj (hcvj.trans hcv_1) (hflj.trans hfl_1)
                  ((hcvj.trans hcv_1) ▸ hreprj) (Or.inr rfl)
                  (fun _ => he2_u (bne_iff_ne.mp hc)) hmj
              · have he2_0 : (er &&& 2#64) = 0#64 := by simpa using hc
                have hokj := fidWl_stOk_of_eval hok_1 hc_cap he2_0 hdwj hcvj hflj hreprj hprefj
                  hhtj hqj (fun idx h1 h2 => hfrj he2_0 idx h1 h2)
                have hlay_j := hokj.2.2.2.2.1; have hocc_j := hokj.2.2.2.2.2.2.2
                clear hc; m6b_to_group
                refine wp_join_group (ts := [i64])
                  (fun (occ_e', ()) me => ∃ se : FullState,
                    g_len.toNat ≤ occ_e'.toNat ∧ occ_e'.toNat ≤ ctrl_off.toNat ∧
                    (occ_e'.toNat - g_len.toNat) % 2 = 0 ∧
                    FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                      bkt_off inq_off q_off ht_off ht_sz occ_e'.toNat scr0 se ∧
                    (FullMem c se ⋆ R) me)
                  (fun _ ⟨occ_e', ⟨⟩⟩ me ⟨se, hoe_lo', hoe_hi', hoe_ev', hoke', hme'⟩ => by
                    have hs1_g1_any : ∀ h, s1.scratch.scratch_buf[(g + (1 : BitVec 64)).toNat]'h =
                        mw1 := fun _ => hs1_g1
                    m6b_steps
                    rw [show ticks + (2 : BitVec 64) = ticks + 2#64 from rfl, hs1_g1_any _,
                      show (255 : BitVec 32) = 0xFF#32 from rfl,
                      show (2 : BitVec 64) = 2#64 from rfl]
                    exact ih1 (occ_e', ticks + 2#64, g + 2#64 + arity.setWidth 64, ()) me
                      (by dsimp only; rw [hnext_g]; omega)
                      ⟨se, by rw [hnext_g]; exact hbd_g, hoe_lo', hoe_hi', hoe_ev',
                       by rw [htk2]; omega, hseq_next', hoke', hme'⟩) ?_
                intro Jocc hJocc
                m6b_steps; m6b_split
                · clear hc; m6b_split
                  · have hle_raw := bv64_ule_true_le hc; rw [hs1_g1] at hle_raw
                    have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len
                    have hg_j_arr : g.toNat < sj.scratch.scratch_buf.length := by omega
                    have hscr_j_g : sj.scratch.scratch_buf[g.toNat]'hg_j_arr = lhs0 :=
                      scr_eq_of_pref hprefj hg_lt hg_j_arr hscr0_g
                    clear hc; m6b_steps; m6b_call hFind
                    refine ⟨F_cur, 2 * cv0, sj.core.repr, FullReprRest c sj ⋆ R,
                      (hcvj.trans hcv_1) ▸ hreprj, by rw [hscr_j_g]; exact hlhs0_lt,
                      focus_full_repr hmj, fun rl repri mi hrl_i hrepr_i _ _ _ hmi => ?_⟩
                    let sj_r : FullState := { sj with core := { sj.core with repr := repri } }
                    have hscrl_jr : sj_r.scratch.scratch_buf.length = c.scratch_cap := hscrl_j
                    have hmi' : (FullMem c sj_r ⋆ R) mi := unfocus_full_repr hmi; clear hmi
                    have hoki := fidWlStOk_with_repr hokj
                      (hrl_i.trans hdwj.1.core_ok.repr_len) hrepr_i
                    let b0 := (rl >>> (1 : Nat)) &&& (occ_u - (1 : BitVec 32))
                    have hb0_lt : b0.toNat < occ_bkt := fid_bkt_lt ho_pos hopow rl
                    obtain ⟨hoe_fit, hb0_n, hoe1_n, hoe2_n, hg_32, hscrl_p0, hlay_p0, hpref_p0,
                      hht_p0, hocc_p0, hp0_eq⟩ :=
                      fidWl_push0_step_prep hlay_j hscrl_j hprefj ((hcvj.trans hcv_1) ▸ hhtj) hocc_j
                        hgat_1 hscr0_g hscr0_g1 hg_co hg_lt hoe_lo hoe_ev hb0_lt hle_raw
                    have hoe1_nat : (occ_end + (1 : BitVec 64)).toNat = occ_end.toNat + 1 := hoe1_n
                    have hb0_arr1 : (BitVec.ofNat 64 bkt_off + b0.setWidth 64).toNat <
                        (sj_r.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32)).length := by
                      rw [List.length_set, hscrl_jr]; change (bkt_64 + b0.setWidth 64).toNat < _
                      rw [hb0_n]; omega
                    have hoe1_arr1 : (occ_end + (1 : BitVec 64)).toNat <
                        (sj_r.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32)).length := by
                      rw [List.length_set, hscrl_jr, hoe1_nat]; omega
                    have hb0_arr2 : (BitVec.ofNat 64 bkt_off + b0.setWidth 64).toNat <
                        ((sj_r.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32)).set
                          (occ_end + (1 : BitVec 64)).toNat
                          ((sj_r.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32))[
                            (BitVec.ofNat 64 bkt_off + b0.setWidth 64).toNat]'hb0_arr1)).length :=
                      by simp only [List.length_set]; rw [hscrl_jr, hb0_n]; omega
                    have hfs_p0 := focus_full_scratch_fid hmi'; clear hmi'
                    generalize hRs_p0 : FullScratchRestFid c sj_r ⋆ R = Rs_p0 at hfs_p0
                    rw [heq_co0, heq_co1, hbkt32]; m6b_steps
                    have hb0_val : (sj_r.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32))[
                        (BitVec.ofNat 64 bkt_off + b0.setWidth 64).toNat]'hb0_arr1 =
                        sj.scratch.scratch_buf[bkt_off + b0.toNat]'(by rw [hscrl_j]; omega) := by
                      rw [List.getElem_set_ne (by change _ ≠ _; rw [hb0_n]; omega)]
                      exact list_getElem_congr hb0_n _ _
                    rw [hb0_val, show (1 : BitVec 64) = 1#64 from rfl, hb0_n, hoe1_n,
                      hp0_eq _] at hm
                    subst hRs_p0
                    let scr_p0 := ((sj.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32)).set
                      (occ_end.toNat + 1)
                      (sj.scratch.scratch_buf[bkt_off + b0.toNat]?.getD 0xFFFFFFFF#32)).set
                      (bkt_off + b0.toNat) (BitVec.ofNat 32 occ_end.toNat)
                    have hok_p0' : FidWlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                        bkt_off inq_off q_off ht_off ht_sz (occ_end.toNat + 2) scr0
                        { sj_r with scratch := { sj_r.scratch with scratch_buf := scr_p0 } } :=
                      fidWlStOk_with_scr hoki hscrl_p0 hlay_p0 hpref_p0 hht_p0 hocc_p0
                    m6b_to_group
                    have hs1_g1_any : ∀ h, s1.scratch.scratch_buf[(g + (1 : BitVec 64)).toNat]'h =
                        mw1 := fun _ => hs1_g1
                    rw [hs1_g1_any _, show (255 : BitVec 32) = 0xFF#32 from rfl,
                      show occ_end + (2 : BitVec 64) = occ_end + 2#64 from rfl]
                    exact fidWl_pushs_wp Γ hFind hg_co hht_cap hc_cap ho_pos hopow hg_lt
                      hgat_1 hscr0_g1 hoe_fit hoe_lo hoe_ev hoe2_n hg_32 hok_p0'
                      (unfocus_full_scratch_fid hm) (fun occ_e' me h => hJocc (occ_e', ()) me h)
                  · clear hc; m6b_let
                    exact hJocc (occ_end, ()) mj ⟨sj, hoe_lo, hoe_hi, hoe_ev, hokj, hmj⟩
                · clear hc; m6b_let
                  exact hJocc (occ_end, ()) mj ⟨sj, hoe_lo, hoe_hi, hoe_ev, hokj, hmj⟩
            · m6b_let; exact hjp2_s1
          · m6b_let; exact hjp2_s1
        · m6b_let; exact hjp2_s1
  · intro Jt hJt
    m6b_split
    · m6b_steps; exact hJt (0x7FFFFFFFFFFFFFFF#64, ()) m0 ⟨rfl, by decide⟩
    · have ht_le : tick_lim.toNat ≤ 2 ^ 63 - 1 := by
        have h := bv64_ult_not_lt hc
        rw [show (9223372036854775807 : BitVec 64).toNat = 2 ^ 63 - 1 from rfl] at h; omega
      m6b_let; exact hJt (tick_lim, ()) m0 ⟨rfl, ht_le⟩

end WorklistMain

end LeanQbe.T.Examples.Kissat.FullFidelityCong

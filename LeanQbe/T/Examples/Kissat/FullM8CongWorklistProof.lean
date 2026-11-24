/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CongEnqEvalProof
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2c
public import LeanQbe.T.Examples.Kissat.FullM7OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM8FidV12
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M8 Worklist (`occ_bkt ≤ 8192`) & `m8_congruence_dense` (`V2c`) Proofs

Proves:
1. `full_cong_worklist_m8_wp` (`m8CongWorklistSpec`, `occ_bkt ≤ 8192`)
2. `m8_congruence_dense_wp` (`m3CongruenceDenseSpec`, scaling `occ_bkt` up to `8192`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8FidV12

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7Proof
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

section WorklistM8


theorem m8CtrlLayout_eq_of_frame {c : FullCfg} {scr1 scr2 : List (BitVec 32)}
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
  have h0e := hkeep 0 (by omega); have h1e := hkeep 1 (by omega)
  have h2e := hkeep 2 (by omega); have h3e := hkeep 3 (by omega)
  have hsc := c.hscr; unfold dimacsBound at hsc
  have eq_of_bv : ∀ a b : Nat, a < 2 ^ 32 → b < 2 ^ 32 →
      BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun a b ha hb h => by
    have := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have h0 : o2 = o1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s0_2]; simp only [Nat.add_zero] at h0e; rw [h0e, s0_1])
  have h1_eq : b2 = b1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s1_2, h1e, s1_1])
  have h2_eq : i2 = i1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s2_2, h2e, s2_1])
  have h3_eq : q2 = q1 := eq_of_bv _ _ (by omega) (by omega)
    (by rw [← s3_2, h3e, s3_1])
  subst h0 h1_eq h2_eq h3_eq; exact h2'

@[expose] def M8WlStOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat) (scr0 : List (BitVec 32)) (st : FullState) : Prop :=
  FullDenseInvW c F0 F_cur st ∧
  st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  M8CtrlLayout c st.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
  (∀ idx < g_len, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  M6CongHtInv F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz ∧
  M6OccNodesOk F_cur cv0 g_len occ_end ctrl_off bkt_off occ_bkt scr0 st.scratch.scratch_buf

theorem m8WlStOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat} {scr0 : List (BitVec 32)} {st : FullState}
    (hok : M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 st)
    {r : List (BitVec 32)} (hr : r.length = 2 * c.max_vars)
    (hrepr : FullCongReprInv F_cur (2 * cv0) r) :
    M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 { st with core := { st.core with repr := r } } :=
  ⟨m6_fullDenseInvW_with_repr hok.1 hr, hok.2.1, hok.2.2.1, hrepr, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2⟩

theorem m8WlStOk_with_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end' : Nat} {scr0 scr' : List (BitVec 32)} {st : FullState}
    (hok : M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end' scr0 st)
    (hl : scr'.length = c.scratch_cap)
    (hlay' : M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]?)
    (hht' : M6CongHtInv F_cur cv0 scr0 scr' g_len ht_off ht_sz)
    (hocc' : M6OccNodesOk F_cur cv0 g_len occ_end' ctrl_off bkt_off occ_bkt scr0 scr')
    (rs' : BitVec 64 := st.scratch.res_sz) :
    M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end' scr0 { st with scratch := { st.scratch with scratch_buf := scr', res_sz := rs' } } :=
  ⟨⟨⟨hok.1.1.core_ok, { hok.1.1.scratch_ok with scratch_buf_len := hl }⟩,
    hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
    fullExtScratchOk_of_eq hok.1.2.2.2.2.1 rfl rfl rfl rfl,
    hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hlay', hpref', hht', hocc'⟩

theorem m8OccNodesOk_of_ev_frame {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len occ_end ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scr scr' : List (BitVec 32)}
    (hocc : M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hfr : ∀ idx < c.scratch_cap, idx < ht_off →
      (ctrl_off = c.scratch_cap → scr'[idx]? = scr[idx]?) ∧
      (∀ o b i q, M8CtrlLayout c scr g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        scr'[idx]? = scr[idx]?)) :
    M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr' := by
  have hlay' := hlay
  have h_occ1 := hocc.1; have h_occ2 := hocc.2.1
  rcases hlay with ⟨_, _, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _,
    hcq, hqi, hib, hbh, hhc, _⟩
  have hkeep : ∀ idx, (g_len ≤ idx ∧ idx < occ_end) ∨ (bkt_off ≤ idx ∧ idx < bkt_off + occ_bkt) →
      scr'[idx]? = scr[idx]? := by
    intro idx hi
    have h1 : idx < c.scratch_cap := by rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have h2 : idx < ht_off := by rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hne5 : idx ≠ ctrl_off + 5 := by rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hnq : ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) := by
      rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hni : ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) := by
      rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    exact (hfr idx h1 h2).2 occ_bkt bkt_off inq_off q_off hlay' hne5 hnq hni
  refine ⟨hocc.1, hocc.2.1, fun b hb => ?_, fun nd hn1 hn2 hev => ?_⟩
  · rw [hkeep (bkt_off + b) (Or.inr ⟨by omega, by omega⟩)]
    exact hocc.2.2.1 b hb
  · have e1 : scr'[nd]? = scr[nd]? := hkeep nd (Or.inl ⟨hn1, by omega⟩)
    have e2 : scr'[nd + 1]? = scr[nd + 1]? := hkeep (nd + 1) (Or.inl ⟨by omega, by omega⟩)
    rw [e1, e2]; exact hocc.2.2.2 nd hn1 hn2 hev

theorem m8Wl_phase0_finalize {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scr_i scr_f : List (BitVec 32)}
    (hlay0 : M8CtrlLayout c scr_i g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl_i : scr_i.length = c.scratch_cap)
    (hpref_i : ∀ idx < g_len, scr_i[idx]? = scr0[idx]?)
    (hht_i : M6CongHtInv F_cur cv scr0 scr_i g_len ht_off ht_sz)
    (hbkt_i : ∀ b < occ_bkt, scr_i[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hdef : scr_f = (scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32) :
    scr_f.length = c.scratch_cap ∧
    M8CtrlLayout c scr_f g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_f[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv scr0 scr_f g_len ht_off ht_sz ∧
    M6OccNodesOk F_cur cv g_len g_len ctrl_off bkt_off occ_bkt scr0 scr_f := by
  subst hdef
  have hlay0' := hlay0
  rcases hlay0 with ⟨hc1, hc8, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _,
    hcq, hqi, hib, hbh, hhc, _⟩
  have hlen_f : ((scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32).length =
      c.scratch_cap := by
    simp only [List.length_set, hscrl_i]
  have hq4 : ((scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32)[ctrl_off + 4]?.getD 0#32 =
      0#32 := by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hq5 : ((scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32)[ctrl_off + 5]?.getD 0#32 =
      0#32 := by
    rw [List.getElem?_set_self (by simp [hscrl_i]; omega), Option.getD_some]
  have hlay_f : M8CtrlLayout c ((scr_i.set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32) g_len
      ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz :=
    m8CtrlLayout_set_q hlay0' (by simp only [List.length_set])
      (fun i hi h4 h5 => by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
      (by rw [hq4]; exact ho_pos) (by rw [hq5]; exact Nat.zero_le _)
      (fun k hk => by rw [hq5] at hk; cases hk)
  refine ⟨hlen_f, hlay_f, fun idx hidx => ?_, fun k hk => ?_,
    ⟨Nat.le_refl _, hgc, fun b hb => Or.inl ?_, fun nd h1 h2 _ => by omega⟩⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpref_i idx hidx
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hht_i k hk
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hbkt_i b hb

theorem m8Wl_push_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end b : Nat}
    {scr0 scr : List (BitVec 32)} {entry : BitVec 32}
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hge : g_len ≤ occ_end) (hocc2 : occ_end + 2 ≤ ctrl_off) (hb : b < occ_bkt) :
    let head := scr[bkt_off + b]?.getD 0xFFFFFFFF#32
    let scr' := ((scr.set occ_end entry).set (occ_end + 1) head).set
      (bkt_off + b) (BitVec.ofNat 32 occ_end)
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv scr0 scr' g_len ht_off ht_sz := by
  intro head scr'
  have hlay' := hlay
  rcases hlay with ⟨hc1, hc8, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _,
    hcq, hqi, hib, hbh, hhc, hqh, hql, hqok⟩
  have hlen' : scr'.length = c.scratch_cap := by simp only [scr', List.length_set, hscrl]
  have hno_hit : ∀ idx, (ctrl_off ≤ idx ∧ idx < inq_off) ∨ idx < g_len ∨ ht_off ≤ idx →
      scr'[idx]? = scr[idx]? := by
    intro idx hidx
    dsimp only [scr']
    have hne1 : occ_end ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    have hne2 : occ_end + 1 ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    have hne3 : bkt_off + b ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    rw [List.getElem?_set_ne hne3, List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
  have hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt := by
    intro k hk
    rw [hno_hit (ctrl_off + 5) (Or.inl ⟨by omega, by omega⟩)] at hk
    rw [hno_hit (ctrl_off + 4) (Or.inl ⟨by omega, by omega⟩)]
    have hslot := Nat.mod_lt ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) ho_pos
    rw [hno_hit (q_off + ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt)
      (Or.inl ⟨by omega, by omega⟩)]
    exact hqok k hk
  refine ⟨hlen', m8CtrlLayout_same_tail hlay' (by rw [hlen', hscrl]) ?_ ?_ hqok',
    fun idx hidx => ?_, fun k hk => ?_⟩
  · rw [hno_hit (ctrl_off + 5) (Or.inl ⟨by omega, by omega⟩)]; exact hql
  · intro i hi _; exact hno_hit (ctrl_off + i) (Or.inl ⟨by omega, by omega⟩)
  · rw [hno_hit idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx
  · rw [hno_hit (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk

theorem m8Wl_relink_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end nd b_dst : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hge : g_len ≤ nd) (hnd1 : nd + 1 < occ_end) (hocc_c : occ_end ≤ ctrl_off)
    (hb : b_dst < occ_bkt) :
    let scr' := (scr.set (nd + 1) (scr[bkt_off + b_dst]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst) (BitVec.ofNat 32 nd)
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv scr0 scr' g_len ht_off ht_sz := by
  intro scr'
  have hlay' := hlay
  rcases hlay with ⟨hc1, hc8, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _,
    hcq, hqi, hib, hbh, hhc, hqh, hql, hqok⟩
  have hlen' : scr'.length = c.scratch_cap := by simp only [scr', List.length_set, hscrl]
  have hno_hit : ∀ idx, (ctrl_off ≤ idx ∧ idx < inq_off) ∨ idx < g_len ∨ ht_off ≤ idx →
      scr'[idx]? = scr[idx]? := by
    intro idx hidx; dsimp only [scr']
    have hne1 : nd + 1 ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    have hne2 : bkt_off + b_dst ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    rw [List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
  have hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt := by
    intro k hk
    rw [hno_hit (ctrl_off + 5) (Or.inl ⟨by omega, by omega⟩)] at hk
    rw [hno_hit (ctrl_off + 4) (Or.inl ⟨by omega, by omega⟩)]
    have hslot := Nat.mod_lt ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) ho_pos
    rw [hno_hit (q_off + ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt)
      (Or.inl ⟨by omega, by omega⟩)]
    exact hqok k hk
  refine ⟨hlen', m8CtrlLayout_same_tail hlay' (by rw [hlen', hscrl]) ?_ ?_ hqok',
    fun idx hidx => ?_, fun k hk => ?_⟩
  · rw [hno_hit (ctrl_off + 5) (Or.inl ⟨by omega, by omega⟩)]; exact hql
  · intro i hi _; exact hno_hit (ctrl_off + i) (Or.inl ⟨by omega, by omega⟩)
  · rw [hno_hit idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx
  · rw [hno_hit (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk

theorem m8Wl_pop_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
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
    M6CongHtInv F_cur cv scr0 scr1 g_len ht_off ht_sz ∧
    M6OccNodePtrOk g_len occ_end (scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
    M6OccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr1 := by
  intro qh ql b nqh scr1
  have ⟨hb_lt, hnqh_lt, hlay_pop⟩ := m8CtrlLayout_pop_q hlay hscrl hpos
  let scr_pop := ((scr.set (ctrl_off + 4) nqh).set (ctrl_off + 5) (ql - 1#32)).set
    (inq_off + b.toNat) 0#32
  have hscrl_pop : scr_pop.length = c.scratch_cap := by
    simp only [scr_pop, List.length_set, hscrl]
  have hlay_pop' := hlay_pop
  rcases hlay_pop with ⟨hc1, hc8, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _,
    hcq, hqi, hib, hbh, hhc, hqh', hql', hqok'⟩
  have hlen1 : scr1.length = c.scratch_cap := by
    simp only [scr1, List.length_set, hscrl]
  have hb_lt' : (scr[q_off + qh.toNat]?.getD 0#32).toNat < occ_bkt := hb_lt
  have hlay1 := m8CtrlLayout_same_tail hlay_pop' (by rw [hlen1, hscrl_pop])
    (by
      have h5 : scr1[ctrl_off + 5]?.getD 0#32 = scr_pop[ctrl_off + 5]?.getD 0#32 := by
        dsimp only [scr1]; rw [List.getElem?_set_ne (by omega)]
      rw [h5]; exact hql')
    (fun i hi _ => by
      dsimp only [scr1]
      exact List.getElem?_set_ne (by omega))
    (fun k hk => by
      have h4 : scr1[ctrl_off + 4]? = scr_pop[ctrl_off + 4]? := by
        dsimp only [scr1]; exact List.getElem?_set_ne (by omega)
      have h5 : scr1[ctrl_off + 5]? = scr_pop[ctrl_off + 5]? := by
        dsimp only [scr1]; exact List.getElem?_set_ne (by omega)
      have hslot := Nat.mod_lt ((scr_pop[ctrl_off + 4]?.getD 0#32).toNat + k) ho_pos
      have hq : scr1[q_off + ((scr_pop[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]? =
          scr_pop[q_off + ((scr_pop[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]? := by
        dsimp only [scr1]; exact List.getElem?_set_ne (by omega)
      rw [h5] at hk; rw [h4, hq]; exact hqok' k hk)
  have hdisj_pop : ∀ idx, idx < ctrl_off ∨ ht_off ≤ idx → scr_pop[idx]? = scr[idx]? := by
    intro idx hidx
    have h1 : ctrl_off + 4 ≠ idx := by rcases hidx with _ | _ <;> omega
    have h2 : ctrl_off + 5 ≠ idx := by rcases hidx with _ | _ <;> omega
    have h3 : inq_off + b.toNat ≠ idx := by
      dsimp only [b]; rcases hidx with _ | _ <;> omega
    dsimp only [scr_pop]
    rw [List.getElem?_set_ne h3, List.getElem?_set_ne h2, List.getElem?_set_ne h1]
  have hdisj1 : ∀ idx, idx < ctrl_off ∨ ht_off ≤ idx → scr1[idx]? = scr[idx]? := by
    intro idx hidx
    have hbne : bkt_off + b.toNat ≠ idx := by
      dsimp only [b]; rcases hidx with _ | _ <;> omega
    dsimp only [scr1]
    rw [List.getElem?_set_ne hbne, hdisj_pop idx hidx]
  refine ⟨hb_lt, hnqh_lt, hlen1, hlay1, fun idx hidx => ?_, fun k hk => ?_,
    hocc.2.2.1 b.toNat hb_lt, ⟨hocc.1, hocc.2.1, fun b' hb' => ?_, fun nd h1 h2 hev => ?_⟩⟩
  · rw [hdisj1 idx (Or.inl (by omega))]; exact hpref idx hidx
  · rw [hdisj1 (ht_off + k) (Or.inr (by omega))]; exact hht k hk
  · change M6OccNodePtrOk g_len occ_end (scr1[bkt_off + b']?.getD 0xFFFFFFFF#32)
    by_cases hbb : b' = b.toNat
    · subst hbb
      dsimp only [scr1]
      rw [List.getElem?_set_self (by rw [hscrl_pop]; omega), Option.getD_some]
      exact Or.inl rfl
    · have hbne : bkt_off + b.toNat ≠ bkt_off + b' := by omega
      have hne1 : ctrl_off + 4 ≠ bkt_off + b' := by omega
      have hne2 : ctrl_off + 5 ≠ bkt_off + b' := by omega
      have hne3 : inq_off + b.toNat ≠ bkt_off + b' := by
        dsimp only [b]; omega
      dsimp only [scr1, scr_pop]
      rw [List.getElem?_set_ne hbne, List.getElem?_set_ne hne3,
        List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
      exact hocc.2.2.1 b' hb'
  · have e1 : scr1[nd]? = scr[nd]? := hdisj1 nd (Or.inl (by have := hocc.2.1; omega))
    have e2 : scr1[nd + 1]? = scr[nd + 1]? :=
      hdisj1 (nd + 1) (Or.inl (by have := hocc.2.1; omega))
    rw [e1, e2]; exact hocc.2.2.2 nd h1 h2 hev


private def FullScratchRest8 (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆
   array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s)

private theorem focus_full_scratch8 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (FullScratchRest8 c s ⋆ R)) m := by
  rw [fullMem_eq_scrDyn] at hm; unfold FullScrDynArrs at hm; unfold FullScratchRest8; ecancel

private theorem unfocus_full_scratch88 {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆ (FullScratchRest8 c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  rw [fullMem_eq_scrDyn]; unfold FullScrDynArrs; unfold FullScratchRest8 at hm
  change ((array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
    array (t := i32) c.pScratchBuf scr') ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
     FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s) ⋆ R) m
  ecancel

private theorem m8Wl_phase0_clear_step {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} {i : BitVec 64}
    (hlay_i : M8CtrlLayout c scri g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl_i : scri.length = c.scratch_cap)
    (hpref_i : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht_i : M6CongHtInv F_cur cv scr0 scri g_len ht_off ht_sz)
    (hbkt_i : ∀ b < i.toNat, scri[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_lt : i.toNat < occ_bkt) :
    let scri' := (scri.set (bkt_off + i.toNat) 0xFFFFFFFF#32).set (inq_off + i.toNat) 0#32
    (BitVec.ofNat 64 bkt_off + i).toNat = bkt_off + i.toNat ∧
    (BitVec.ofNat 64 inq_off + i).toNat = inq_off + i.toNat ∧
    (BitVec.ofNat 64 bkt_off + i).toNat < scri.length ∧
    (BitVec.ofNat 64 inq_off + i).toNat <
      (scri.set (BitVec.ofNat 64 bkt_off + i).toNat 0xFFFFFFFF#32).length ∧
    (i + 1#64).toNat = i.toNat + 1 ∧
    scri'.length = c.scratch_cap ∧
    M8CtrlLayout c scri' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scri'[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv scr0 scri' g_len ht_off ht_sz ∧
    (∀ b < i.toNat + 1, scri'[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
  intro scri'
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hlay_i' := hlay_i
  rcases hlay_i with ⟨_, _, _, _, _, _, _, _, _, _, ho_pos, ho_8192, _, _,
    hcq, hqi, hib, hbh, hht_cap, _, hql_i, hqok_i⟩
  have hbkt_i_n : (BitVec.ofNat 64 bkt_off + i).toNat = bkt_off + i.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hinq_i_n : (BitVec.ofNat 64 inq_off + i).toNat = inq_off + i.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlen' : scri'.length = c.scratch_cap := by simp only [scri', List.length_set, hscrl_i]
  have hno_hit : ∀ idx, (co ≤ idx ∧ idx < q_off + occ_bkt) ∨ idx < g_len ∨ ht_off ≤ idx →
      scri'[idx]? = scri[idx]? := by
    intro idx hidx; dsimp only [scri']
    have h1 : inq_off + i.toNat ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    have h2 : bkt_off + i.toNat ≠ idx := by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega
    rw [List.getElem?_set_ne h1, List.getElem?_set_ne h2]
  have hlay' := m8CtrlLayout_same_tail hlay_i' (by rw [hlen', hscrl_i])
    (by rw [hno_hit (co + 5) (Or.inl ⟨by omega, by omega⟩)]; exact hql_i)
    (fun j hj _ => hno_hit (co + j) (Or.inl ⟨by omega, by omega⟩))
    (fun k hk => by
      rw [hno_hit (co + 5) (Or.inl ⟨by omega, by omega⟩)] at hk
      rw [hno_hit (co + 4) (Or.inl ⟨by omega, by omega⟩)]
      have hslot := Nat.mod_lt ((scri[co + 4]?.getD 0#32).toNat + k) ho_pos
      rw [hno_hit (q_off + ((scri[co + 4]?.getD 0#32).toNat + k) % occ_bkt)
        (Or.inl ⟨by omega, by omega⟩)]
      exact hqok_i k hk)
  refine ⟨hbkt_i_n, hinq_i_n, by rw [hbkt_i_n]; omega,
    by rw [List.length_set, hinq_i_n]; omega,
    bv64_add1_toNat (n := occ_bkt) hi_lt (by omega), hlen', hlay',
    fun idx hidx => by rw [hno_hit idx (Or.inr (Or.inl hidx))]; exact hpref_i idx hidx,
    fun k hk => by rw [hno_hit (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht_i k hk,
    fun b hb => ?_⟩
  by_cases hbi : b = i.toNat
  · subst hbi; dsimp only [scri']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  · dsimp only [scri']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hbkt_i b (by omega)

private theorem m8Wl_rehash_clear_step {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scrh : List (BitVec 32)} {ih : BitVec 64}
    (hlay_h : M8CtrlLayout c scrh g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl_h : scrh.length = c.scratch_cap)
    (hpref_h : ∀ idx < g_len, scrh[idx]? = scr0[idx]?)
    (hht_h : ∀ k < ih.toNat, scrh[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hocc_h : M6OccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh)
    (hih_lt : ih.toNat < ht_sz) :
    let scrh' := scrh.set (ht_off + ih.toNat) 0xFFFFFFFF#32
    (BitVec.ofNat 64 ht_off + ih).toNat = ht_off + ih.toNat ∧
    (BitVec.ofNat 64 ht_off + ih).toNat < scrh.length ∧
    (ih + 1#64).toNat = ih.toNat + 1 ∧
    scrh'.length = c.scratch_cap ∧
    M8CtrlLayout c scrh' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scrh'[idx]? = scr0[idx]?) ∧
    (∀ k < ih.toNat + 1, scrh'[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
    M6OccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh' := by
  intro scrh'
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hlay_h' := hlay_h
  rcases hlay_h with ⟨_, _, _, _, _, _, _, _, _, _, ho_pos, _, _, _,
    hcq, hqi, hib, hbh, hht_cap, _, hql_h, hqok_h⟩
  have hhti_n : (BitVec.ofNat 64 ht_off + ih).toNat = ht_off + ih.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlen' : scrh'.length = c.scratch_cap := by simp only [scrh', List.length_set, hscrl_h]
  have hno_h : ∀ idx, idx < ht_off → scrh'[idx]? = scrh[idx]? :=
    fun idx hidx => List.getElem?_set_ne (by omega)
  have hlay' := m8CtrlLayout_same_tail hlay_h' (by rw [hlen', hscrl_h])
    (by rw [hno_h _ (by omega)]; exact hql_h) (fun j hj _ => hno_h _ (by omega))
    (fun k hk => by
      rw [hno_h (co + 5) (by omega)] at hk
      rw [hno_h (co + 4) (by omega)]
      have hslot := Nat.mod_lt ((scrh[co + 4]?.getD 0#32).toNat + k) ho_pos
      rw [hno_h (q_off + ((scrh[co + 4]?.getD 0#32).toNat + k) % occ_bkt) (by omega)]
      exact hqok_h k hk)
  have hocc' : M6OccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh' :=
    ⟨hocc_h.1, hocc_h.2.1,
     fun b' hb' => by rw [hno_h (bkt_off + b') (by omega)]; exact hocc_h.2.2.1 b' hb',
     fun nd' hn1 hn2 hev => by
       rw [hno_h nd' (by have := hocc_h.2.1; omega),
         hno_h (nd' + 1) (by have := hocc_h.2.1; omega)]
       exact hocc_h.2.2.2 nd' hn1 hn2 hev⟩
  refine ⟨hhti_n, by rw [hhti_n]; omega, bv64_add1_lt (by omega), hlen', hlay',
    fun idx hidx => by rw [hno_h idx (by omega)]; exact hpref_h idx hidx,
    fun k hk => ?_, hocc'⟩
  by_cases hki : k = ih.toNat
  · subst hki; dsimp only [scrh']
    rw [List.getElem?_set_self (by omega), Option.getD_some]
  · dsimp only [scrh']; rw [List.getElem?_set_ne (by omega)]; exact hht_h k (by omega)

private structure M8WlCtrlFacts (c : FullCfg) (scr : List (BitVec 32)) (ctrl_off : BitVec 64)
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
  hbkt64_n : (BitVec.ofNat 64 bkt_off).toNat = bkt_off
  hinq64_n : (BitVec.ofNat 64 inq_off).toNat = inq_off
  hq64_n : (BitVec.ofNat 64 q_off).toNat = q_off

private theorem m8Wl_ctrl_arith {c : FullCfg} {scr : List (BitVec 32)} {g_len : Nat}
    {ctrl_off : BitVec 64} {occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hht_bnd : ht_sz < 2 ^ 30) (hscrl : scr.length = c.scratch_cap)
    (hlay : M8CtrlLayout c scr g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    M8WlCtrlFacts c scr ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  rcases hlay with ⟨hc_cap, hc_8, _, _, hs0, hs1, hs2, hs3, hs6, hs7,
    _, ho_8192, _, _, hcq, hqi, hib, hbh, hht_cap, _⟩
  have hc1 : (ctrl_off + 1).toNat = ctrl_off.toNat + 1 :=
    bv64_add_nat_lt 1 (by decide) (by omega)
  have hc2 : (ctrl_off + 2).toNat = ctrl_off.toNat + 2 :=
    bv64_add_nat_lt 2 (by decide) (by omega)
  have hc3 : (ctrl_off + 3).toNat = ctrl_off.toNat + 3 :=
    bv64_add_nat_lt 3 (by decide) (by omega)
  have hc4 : (ctrl_off + 4).toNat = ctrl_off.toNat + 4 :=
    bv64_add_nat_lt 4 (by decide) (by omega)
  have hc5 : (ctrl_off + 5).toNat = ctrl_off.toNat + 5 :=
    bv64_add_nat_lt 5 (by decide) (by omega)
  have hc6 : (ctrl_off + 6).toNat = ctrl_off.toNat + 6 :=
    bv64_add_nat_lt 6 (by decide) (by omega)
  have hc7 : (ctrl_off + 7).toNat = ctrl_off.toNat + 7 :=
    bv64_add_nat_lt 7 (by decide) (by omega)
  have ha0 : ctrl_off.toNat < scr.length := by omega
  have ha1 : (ctrl_off + 1).toNat < scr.length := by rw [hc1]; omega
  have ha2 : (ctrl_off + 2).toNat < scr.length := by rw [hc2]; omega
  have ha3 : (ctrl_off + 3).toNat < scr.length := by rw [hc3]; omega
  have ha4 : (ctrl_off + 4).toNat < scr.length := by rw [hc4]; omega
  have ha5 : (ctrl_off + 5).toNat < scr.length := by rw [hc5]; omega
  have ha6 : (ctrl_off + 6).toNat < scr.length := by rw [hc6]; omega
  have ha7 : (ctrl_off + 7).toNat < scr.length := by rw [hc7]; omega
  have mkEq : ∀ (k off : Nat)
      (hkn : (ctrl_off + BitVec.ofNat 64 k).toNat = ctrl_off.toNat + k)
      (ha : (ctrl_off + BitVec.ofNat 64 k).toNat < scr.length)
      (hkl : ctrl_off.toNat + k < scr.length)
      (hs : scr[ctrl_off.toNat + k]?.getD 0#32 = BitVec.ofNat 32 off),
      scr[(ctrl_off + BitVec.ofNat 64 k).toNat]'ha = BitVec.ofNat 32 off :=
    fun _ _ hkn ha hkl hs => by
      rw [List.getElem?_eq_getElem hkl, Option.getD_some] at hs
      exact (list_getElem_congr hkn ha hkl).trans hs
  have mkZw : ∀ {n : Nat}, n < 2 ^ 32 →
      (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := fun hn => by
    apply BitVec.eq_of_toNat_eq
    rw [bv_zext32_toNat, bv32_ofNat_toNat hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
    ?_, mkEq 1 bkt_off hc1 ha1 (by omega) hs1, mkEq 2 inq_off hc2 ha2 (by omega) hs2,
    mkEq 3 q_off hc3 ha3 (by omega) hs3, mkEq 6 ht_off hc6 ha6 (by omega) hs6,
    mkEq 7 ht_sz hc7 ha7 (by omega) hs7,
    mkZw (by omega), mkZw (by omega), mkZw (by omega), mkZw (by omega), mkZw (by omega),
    mkZw (by omega),
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩
  rwa [← Option.getD_some (a := scr[ctrl_off.toNat]'ha0) (b := 0#32),
    ← List.getElem?_eq_getElem ha0]

private theorem m8Wl_pop_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {ctrl_off : BitVec 64} {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : M6OccNodesOk F_cur cv g_len occ_end ctrl_off.toNat bkt_off occ_bkt scr0 scr)
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
    ∃ (hco4 : (ctrl_off + 4).toNat < scr.length)
      (hco5 : (ctrl_off + 5).toNat < scr.length)
      (hq_ld : (BitVec.ofNat 64 q_off +
        (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat < scr.length),
      let nqh_ex := (scr[(ctrl_off + 4).toNat]'hco4 + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
      let ql1_ex := scr[(ctrl_off + 5).toNat]'hco5 - 1#32
      let b_ex := scr[(BitVec.ofNat 64 q_off +
        (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld
      b.toNat < occ_bkt ∧ nqh.toNat < occ_bkt ∧ scr_pop.length = c.scratch_cap ∧
      M8CtrlLayout c scr_pop g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
      (∀ idx < g_len, scr_pop[idx]? = scr0[idx]?) ∧
      M6CongHtInv F_cur cv scr0 scr_pop g_len ht_off ht_sz ∧
      M6OccNodePtrOk g_len occ_end (scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
      M6OccNodesOk F_cur cv g_len occ_end ctrl_off.toNat bkt_off occ_bkt scr0 scr_pop ∧
      scr[(ctrl_off + 4).toNat]'hco4 = qh ∧
      scr[(ctrl_off + 5).toNat]'hco5 = ql ∧ b_ex = b ∧
      (ctrl_off + 5).toNat < (scr.set (ctrl_off + 4).toNat nqh_ex).length ∧
      (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat <
        ((scr.set (ctrl_off + 4).toNat nqh_ex).set (ctrl_off + 5).toNat ql1_ex).length ∧
      (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat <
        (((scr.set (ctrl_off + 4).toNat nqh_ex).set (ctrl_off + 5).toNat ql1_ex).set
          (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat 0#32).length ∧
      (BitVec.ofNat 64 inq_off + b.setWidth 64).toNat = inq_off + b.toNat ∧
      (BitVec.ofNat 64 bkt_off + b.setWidth 64).toNat = bkt_off + b.toNat ∧
      (∀ (hbkt_cap : (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat <
          (((scr.set (ctrl_off + 4).toNat
              ((scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
                (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32)))).set
            (ctrl_off + 5).toNat (scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32))).set
            (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat (0 : BitVec 32)).length),
        (((scr.set (ctrl_off + 4).toNat
            ((scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
              (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32)))).set
          (ctrl_off + 5).toNat (scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32))).set
          (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat (0 : BitVec 32))[
            (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat]'hbkt_cap =
              scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
      ((((scr.set (ctrl_off + 4).toNat
            ((scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
              (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32)))).set
          (ctrl_off + 5).toNat (scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32))).set
          (BitVec.ofNat 64 inq_off + b_ex.setWidth 64).toNat (0 : BitVec 32)).set
          (BitVec.ofNat 64 bkt_off + b_ex.setWidth 64).toNat (4294967295 : BitVec 32) =
        scr_pop) ∧
      (scr_pop[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat := by
  intro qh ql b nqh scr_pop
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hlay' := hlay
  rcases hlay with ⟨hc_cap, hc_8, _, _, _, _, _, _, _, _, _, ho_8192, _, _,
    hcq, hqi, hib, hbh, hht_cap, hqh_lt, _, _⟩
  have hco4 : (ctrl_off + 4).toNat < scr.length := by rw [hc4_n]; omega
  have hco5 : (ctrl_off + 5).toNat < scr.length := by rw [hc5_n]; omega
  have hpop := m8Wl_pop_pres hlay' hscrl hpref hht hocc hpos
  have hb_lt : b.toNat < occ_bkt := hpop.1
  have hq64_n : (BitVec.ofNat 64 q_off).toNat = q_off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinq64_n : (BitVec.ofNat 64 inq_off).toNat = inq_off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbkt64_n : (BitVec.ofNat 64 bkt_off).toNat = bkt_off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hqh_lt' : qh.toNat < occ_bkt := hqh_lt
  have hq_idx : (BitVec.ofNat 64 q_off + qh.setWidth 64).toNat = q_off + qh.toNat := by
    rw [bv64_add_zext32_0 (by rw [hq64_n]; omega), hq64_n]
  have hq_arr : (BitVec.ofNat 64 q_off + qh.setWidth 64).toNat < scr.length := by
    rw [hq_idx]; omega
  have hb_eq : scr[(BitVec.ofNat 64 q_off + qh.setWidth 64).toNat]'hq_arr = b := by
    dsimp only [b]
    rw [list_getElem_congr hq_idx hq_arr (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hqh_u : scr[(ctrl_off + 4).toNat]'hco4 = qh := by
    dsimp only [qh]
    rw [list_getElem_congr hc4_n hco4 (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hql_u : scr[(ctrl_off + 5).toNat]'hco5 = ql := by
    dsimp only [ql]
    rw [list_getElem_congr hc5_n hco5 (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
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
  have h0_bv : (0 : BitVec 32) = 0#32 := rfl
  have hff_bv : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
  have hlist3_eq :
      ((scr.set (ctrl_off + 4).toNat ((scr[(ctrl_off + 4).toNat]'hco4 + (1 : BitVec 32)) &&&
          (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32)))).set
        (ctrl_off + 5).toNat (scr[(ctrl_off + 5).toNat]'hco5 - (1 : BitVec 32))).set
        (BitVec.ofNat 64 inq_off +
          (scr[(BitVec.ofNat 64 q_off + (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld
            ).setWidth 64).toNat (0 : BitVec 32) =
      ((scr.set (ctrl_off.toNat + 4) nqh).set (ctrl_off.toNat + 5) (ql - 1#32)).set
        (inq_off + b.toNat) 0#32 := by
    rw [hnqh_ex, hql1_ex, hb_raw_eq, hc4_n, hc5_n, hinqb_n, h0_bv]
  have hidx_eq : (BitVec.ofNat 64 bkt_off +
      (scr[(BitVec.ofNat 64 q_off + (scr[(ctrl_off + 4).toNat]'hco4).setWidth 64).toNat]'hq_ld
        ).setWidth 64).toNat = bkt_off + b.toNat := by
    rw [hb_raw_eq, hbktb_n]
  refine ⟨hco4, hco5, hq_ld, hb_lt, hpop.2.1, hpop.2.2.1, hpop.2.2.2.1, hpop.2.2.2.2.1,
    hpop.2.2.2.2.2.1, hpop.2.2.2.2.2.2.1, hpop.2.2.2.2.2.2.2, hqh_u, hql_u, hb_raw_eq,
    by rw [List.length_set]; exact hco5,
    by simp only [List.length_set]; rw [hb_raw_eq, hinqb_n]; omega,
    by simp only [List.length_set]; rw [hb_raw_eq, hbktb_n]; omega,
    hinqb_n, hbktb_n, fun hcap => ?_, ?_, ?_⟩
  · rw [← Option.getD_some (a := (((scr.set (ctrl_off + 4).toNat _).set _ _).set _ _)[_]'hcap)
        (b := 0xFFFFFFFF#32),
      ← List.getElem?_eq_getElem hcap, hlist3_eq, hidx_eq,
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  · rw [hlist3_eq, hidx_eq, hff_bv]
  · have hql_pos : 0 < ql.toNat := hpos
    dsimp only [scr_pop]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp only [List.length_set, hscrl]; omega), Option.getD_some,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr
        (show (1#32 : BitVec 32).toNat ≤ ql.toNat from Nat.succ_le_of_lt hql_pos))]
    have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega

private theorem m8Wl_relink_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scr : List (BitVec 32)} {nd b_dst : BitVec 32}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : M6OccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr)
    (hnd_lo : g_len ≤ nd.toNat) (hnd_hi : nd.toNat + 1 < occ_end)
    (hnd_ev : (nd.toNat - g_len) % 2 = 0)
    (_hnd1_n : (nd.setWidth 64 + 1#64).toNat = nd.toNat + 1)
    (hbdst : b_dst.toNat < occ_bkt) :
    let bkt_64 := BitVec.ofNat 64 bkt_off
    let scr_rel := (scr.set (nd.toNat + 1)
      (scr[bkt_off + b_dst.toNat]?.getD 0xFFFFFFFF#32)).set (bkt_off + b_dst.toNat) nd
    (bkt_64 + b_dst.setWidth 64).toNat = bkt_off + b_dst.toNat ∧
    ∃ (hb_arr : (bkt_64 + b_dst.setWidth 64).toNat < scr.length),
      (bkt_64 + b_dst.setWidth 64).toNat < (scr.set (nd.setWidth 64 + 1#64).toNat
        (scr[(bkt_64 + b_dst.setWidth 64).toNat]'hb_arr)).length ∧
      scr_rel.length = c.scratch_cap ∧
      M8CtrlLayout c scr_rel g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
      (∀ idx < g_len, scr_rel[idx]? = scr0[idx]?) ∧
      M6CongHtInv F_cur cv scr0 scr_rel g_len ht_off ht_sz ∧
      M6OccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr_rel ∧
      (∀ (hb_cap : bkt_off + b_dst.toNat < scr.length)
         (_hnd1_cap : nd.toNat + 1 < scr.length),
        (scr.set (nd.toNat + 1) (scr[bkt_off + b_dst.toNat]'hb_cap)).set
          (bkt_off + b_dst.toNat) nd = scr_rel) := by
  intro bkt_64 scr_rel
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbh, hht_cap, _⟩
  have hocc_c := hocc.2.1
  have hbkt64_n : bkt_64.toNat = bkt_off := by
    dsimp only [bkt_64]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb_idx_n : (bkt_64 + b_dst.setWidth 64).toNat = bkt_off + b_dst.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hb_arr : (bkt_64 + b_dst.setWidth 64).toNat < scr.length := by
    rw [hb_idx_n, hscrl]; omega
  have hrel_p := m8Wl_relink_pres hlay' hscrl hpref hht hnd_lo hnd_hi (by omega) hbdst
  have hocc_rel := m6OccNodesOk_relink hocc (by omega) (by omega) hnd_lo hnd_hi hnd_ev
    (by omega) hbdst
  have hnd_ofNat : BitVec.ofNat 32 nd.toNat = nd := @bv_ofNat_toNat_eq 32 nd
  have hrel_eq : (scr.set (nd.toNat + 1)
      (scr[bkt_off + b_dst.toNat]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst.toNat) (BitVec.ofNat 32 nd.toNat) = scr_rel := by
    dsimp only [scr_rel]; rw [hnd_ofNat]
  rw [hrel_eq] at hrel_p hocc_rel
  refine ⟨hb_idx_n, hb_arr, by rw [List.length_set]; exact hb_arr,
    hrel_p.1, hrel_p.2.1, hrel_p.2.2.1, hrel_p.2.2.2, hocc_rel, fun hb_cap _ => ?_⟩
  dsimp only [scr_rel]
  rw [List.getElem?_eq_getElem hb_cap, Option.getD_some]

private theorem m8Wl_push0_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {occ_end g : BitVec 64} {lhs0 mw1 b0 : BitVec 32} {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : M6OccNodesOk F_cur cv g_len occ_end.toNat co bkt_off occ_bkt scr0 scr)
    (hgat : M6GateAt F_cur cv scr0 g_len g.toNat)
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
    occ_end.setWidth 32 = BitVec.ofNat 32 occ_end.toNat ∧
    scr_p0.length = c.scratch_cap ∧
    M8CtrlLayout c scr_p0 g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_p0[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv scr0 scr_p0 g_len ht_off ht_sz ∧
    M6OccNodesOk F_cur cv g_len (occ_end.toNat + 2) co bkt_off occ_bkt scr0 scr_p0 ∧
    ∃ (hb0_arr : (bkt_64 + b0.setWidth 64).toNat < scr.length),
      (occ_end + 1#64).toNat < (scr.set occ_end.toNat (g.setWidth 32)).length ∧
      (bkt_64 + b0.setWidth 64).toNat < ((scr.set occ_end.toNat (g.setWidth 32)).set
        (occ_end + 1#64).toNat (scr[(bkt_64 + b0.setWidth 64).toNat]'hb0_arr)).length ∧
      (∀ (hb_cap : bkt_off + b0.toNat < scr.length),
        ((scr.set occ_end.toNat (g.setWidth 32)).set (occ_end.toNat + 1)
          (scr[bkt_off + b0.toNat]'hb_cap)).set (bkt_off + b0.toNat)
            (occ_end.setWidth 32) = scr_p0) := by
  intro arity bkt_64 scr_p0
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hlay' := hlay
  rcases hlay with ⟨hc_cap, _, _, hg24, _, _, _, _, _, _, _, _, _, _, _, _, _, hbh, hht_cap, _⟩
  have hgat' := hgat
  obtain ⟨_, mword, _, hg1, _, _, _, har_31, _, _⟩ := hgat
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hs0_g1)
  have har_le31 : arity.toNat ≤ 31 := by dsimp only [arity]; rw [← hmw]; exact har_31
  have hocc_c := hocc.2.1
  have h1a : (1#32 + arity).toNat = 1 + arity.toNat := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h1a_64 : ((1#32 + arity).setWidth 64).toNat = 1 + arity.toNat := by
    rw [bv_zext32_toNat, h1a]
  have hmul_lt : ((1#32 + arity).setWidth 64 * 2#64).toNat = (1 + arity.toNat) * 2 := by
    rw [BitVec.toNat_mul, h1a_64, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hsum_lt : (occ_end + (1#32 + arity).setWidth 64 * 2#64).toNat =
      occ_end.toNat + (1 + arity.toNat) * 2 := by
    rw [BitVec.toNat_add, hmul_lt, Nat.mod_eq_of_lt (by omega)]
  have hoe_fit : occ_end.toNat + (1 + arity.toNat) * 2 ≤ co := hsum_lt ▸ hle
  have hbkt64_n : bkt_64.toNat = bkt_off := by
    dsimp only [bkt_64]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb0_n : (bkt_64 + b0.setWidth 64).toNat = bkt_off + b0.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hoe1_n : (occ_end + 1#64).toNat = occ_end.toNat + 1 := bv64_add1_lt (by omega)
  have hoe2_n : (occ_end + 2#64).toNat = occ_end.toNat + 2 :=
    bv64_add_nat_lt 2 (by decide) (by omega)
  have hg_32 : g.setWidth 32 = BitVec.ofNat 32 g.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoe_32 : occ_end.setWidth 32 = BitVec.ofNat 32 occ_end.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpush0 := m8Wl_push_pres hlay' hscrl hpref hht hoe_lo (by omega) hb0
    (entry := g.setWidth 32)
  have hocc_p0 := m6OccNodesOk_push (slot := 0) hocc hoe_ev (by omega) (by omega)
    (by omega) hg_lt (by omega) hgat'
    (by rw [hs0_g1, Option.getD_some]; exact Nat.zero_le _) hb0 hg_co (by omega)
  have hocc_p0' : M6OccNodesOk F_cur cv g_len (occ_end.toNat + 2) co bkt_off occ_bkt scr0
      scr_p0 := by
    simpa only [scr_p0, hg_32, ite_true] using hocc_p0
  have hb0_arr : (bkt_64 + b0.setWidth 64).toNat < scr.length := by rw [hb0_n, hscrl]; omega
  refine ⟨hoe_fit, hb0_n, hoe1_n, hoe2_n, hg_32, hoe_32,
    by simpa only [scr_p0, List.getElem?_eq_getElem (by rw [hscrl]; omega),
      Option.getD_some] using hpush0.1,
    by simpa only [scr_p0, List.getElem?_eq_getElem (by rw [hscrl]; omega),
      Option.getD_some] using hpush0.2.1,
    fun idx h => by
      simpa only [scr_p0, List.getElem?_eq_getElem (by rw [hscrl]; omega),
        Option.getD_some] using hpush0.2.2.1 idx h,
    by simpa only [scr_p0, List.getElem?_eq_getElem (by rw [hscrl]; omega),
      Option.getD_some] using hpush0.2.2.2,
    hocc_p0', hb0_arr, by rw [List.length_set, hoe1_n, hscrl]; omega,
    by simp only [List.length_set]; rw [hb0_n, hscrl]; omega, fun hb_cap => ?_⟩
  dsimp only [scr_p0]; rw [hoe_32, List.getElem?_eq_getElem hb_cap, Option.getD_some]

private theorem m8Wl_pushs_step_prep {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {occ_s g : BitVec 64} {s_i mw1 bs : BitVec 32} {scr0 scr : List (BitVec 32)}
    (hlay : M8CtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : M6OccNodesOk F_cur cv g_len occ_s.toNat co bkt_off occ_bkt scr0 scr)
    (hgat : M6GateAt F_cur cv scr0 g_len g.toNat)
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
    (bkt_64 + bs.setWidth 64).toNat = bkt_off + bs.toNat ∧
    occ_s.toNat + 2 ≤ co ∧
    (occ_s + 1#64).toNat = occ_s.toNat + 1 ∧
    (occ_s + 2#64).toNat = occ_s.toNat + 2 ∧
    (s_i + 1#32).toNat = s_i.toNat + 1 ∧
    occ_s.setWidth 32 = BitVec.ofNat 32 occ_s.toNat ∧
    scr_ps.length = c.scratch_cap ∧
    M8CtrlLayout c scr_ps g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_ps[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv scr0 scr_ps g_len ht_off ht_sz ∧
    M6OccNodesOk F_cur cv g_len (occ_s.toNat + 2) co bkt_off occ_bkt scr0 scr_ps ∧
    ∃ (hbs_arr : (bkt_64 + bs.setWidth 64).toNat < scr.length),
      (occ_s + 1#64).toNat < (scr.set occ_s.toNat entry_s).length ∧
      (bkt_64 + bs.setWidth 64).toNat < ((scr.set occ_s.toNat entry_s).set
        (occ_s + 1#64).toNat (scr[(bkt_64 + bs.setWidth 64).toNat]'hbs_arr)).length ∧
      (∀ (hb_cap : bkt_off + bs.toNat < scr.length),
        ((scr.set occ_s.toNat entry_s).set (occ_s.toNat + 1)
          (scr[bkt_off + bs.toNat]'hb_cap)).set (bkt_off + bs.toNat)
            (occ_s.setWidth 32) = scr_ps) := by
  intro bkt_64 entry_s scr_ps
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hlay' := hlay
  rcases hlay with ⟨hc_cap, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbh, hht_cap, _⟩
  have hgat' := hgat
  obtain ⟨_, mword, _, hg1, _, _, _, har_31, _, _⟩ := hgat
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hs0_g1)
  have har_le31 : (mw1 &&& 0xFF#32).toNat ≤ 31 := hmw ▸ har_31
  have hoes_hi : occ_s.toNat + 2 ≤ co := by omega
  have hbkt64_n : bkt_64.toNat = bkt_off := by
    dsimp only [bkt_64]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs_n : (bkt_64 + bs.setWidth 64).toNat = bkt_off + bs.toNat := by
    rw [bv64_add_zext32_0 (by rw [hbkt64_n]; omega), hbkt64_n]
  have hoes1_n : (occ_s + 1#64).toNat = occ_s.toNat + 1 := bv64_add1_lt (by omega)
  have hoes2_n : (occ_s + 2#64).toNat = occ_s.toNat + 2 :=
    bv64_add_nat_lt 2 (by decide) (by omega)
  have hs1_n : (s_i + 1#32).toNat = s_i.toNat + 1 := bv32_add1_lt_of (by omega)
  have hoes_32 : occ_s.setWidth 32 = BitVec.ofNat 32 occ_s.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs1_32 : s_i + 1#32 = BitVec.ofNat 32 (s_i.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [hs1_n, bv32_ofNat_toNat (by omega)]
  have hentry_eq : entry_s =
      (BitVec.ofNat 32 (s_i.toNat + 1) <<< 24) ||| BitVec.ofNat 32 g.toNat := by
    dsimp only [entry_s]; rw [hs1_32, hg_32]
  have hpush := m8Wl_push_pres hlay' hscrl hpref hht hoes_lo hoes_hi hbs (entry := entry_s)
  have hocc_ps := m6OccNodesOk_push hocc hoes_ev (by omega) hoes_hi (by omega) hg_lt (by omega)
    hgat' (by rw [hs0_g1, Option.getD_some]; change s_i.toNat + 1 ≤ (mw1 &&& 0xFF#32).toNat; omega)
    hbs hg_co (by omega)
  have hsn0 : s_i.toNat + 1 ≠ 0 := by omega
  have hocc_ps' : M6OccNodesOk F_cur cv g_len (occ_s.toNat + 2) co bkt_off occ_bkt scr0
      scr_ps := by
    simpa only [scr_ps, ite_eq_right hsn0, ← hentry_eq] using hocc_ps
  have hbs_arr : (bkt_64 + bs.setWidth 64).toNat < scr.length := by rw [hbs_n, hscrl]; omega
  refine ⟨hbs_n, hoes_hi, hoes1_n, hoes2_n, hs1_n, hoes_32,
    by simpa only [scr_ps, List.getElem?_eq_getElem (by rw [hscrl]; omega),
      Option.getD_some] using hpush.1,
    by simpa only [scr_ps, List.getElem?_eq_getElem (by rw [hscrl]; omega),
      Option.getD_some] using hpush.2.1,
    fun idx h => by
      simpa only [scr_ps, List.getElem?_eq_getElem (by rw [hscrl]; omega),
        Option.getD_some] using hpush.2.2.1 idx h,
    by simpa only [scr_ps, List.getElem?_eq_getElem (by rw [hscrl]; omega),
      Option.getD_some] using hpush.2.2.2,
    hocc_ps', hbs_arr, by rw [List.length_set, hoes1_n, hscrl]; omega,
    by simp only [List.length_set]; rw [hbs_n, hscrl]; omega, fun hb_cap => ?_⟩
  dsimp only [scr_ps]; rw [hoes_32, List.getElem?_eq_getElem hb_cap, Option.getD_some]

private theorem m8Wl_stOk_of_eval {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat} {scr0 : List (BitVec 32)} {s s' : FullState} {er : BitVec 64}
    (hok : M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 s)
    (hc_cap : ctrl_off < c.scratch_cap)
    (_he2_0 : (er &&& 2#64) = 0#64)
    (hdw' : FullDenseInvW c F0 F_cur s') (hcv' : s'.core.cur_vars = s.core.cur_vars)
    (hfl' : s'.core.fuel = s.core.fuel)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr)
    (hpref' : ∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?)
    (hht' : M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf g_len ht_off ht_sz)
    (hq' : M8QueueCtx c s'.scratch.scratch_buf g_len ctrl_off ht_off ht_sz)
    (hfr' : ∀ idx < c.scratch_cap, idx < ht_off →
      (ctrl_off = c.scratch_cap → s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
      (∀ o b i q, M8CtrlLayout c s.scratch.scratch_buf g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)) :
    M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 s' := by
  have ⟨_, hcvs, hfls, _, hlays, _, _, hoccs⟩ := hok
  have hlay' : M8CtrlLayout c s'.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz := by
    rcases hq' with hcap | ⟨o', b', i', q', hlo⟩
    · exact absurd hcap (Nat.ne_of_lt hc_cap)
    · exact m8CtrlLayout_eq_of_frame hlays hlo hfr'
  have hocc' := m8OccNodesOk_of_ev_frame hoccs hlays hfr'
  exact ⟨hdw', hcv'.trans hcvs, hfl'.trans hfls, (hcv'.trans hcvs) ▸ hrepr', hlay', hpref',
    (hcv'.trans hcvs) ▸ hht', hocc'⟩


private def m8Wl_relinkExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reprPtr scrPtr : V i64) (occ_u : V i32) (bkt_64 gn : V i64)
    (nd slot_i : V i32) (er : V i64) (Jrel : L []) : Expr V L rs :=
  .let_ ⟨.and i64, (.var er, (.imm 4, ()))⟩ fun p721 =>
  .let_ ⟨.cmp .ne i64 .bool rfl, (.var p721.1, (.imm 0, ()))⟩ fun p722 =>
  .jnz (.var p722.1) (
    .group (sig := [[i32]]) (fun _ =>
      .cons (fun p823 =>
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
        .store (t := i32) (.var nd) (.var p845.1) (
        .jump Jrel ()))
      ) (.nil)
    ) (fun J723 =>
      .let_ ⟨.cmp .eq i32 .bool rfl, (.var slot_i, (.imm 0, ()))⟩ fun p724 =>
      .jnz (.var p724.1) (
        .jump J723.1 (.imm 0, ())
      ) (
        .let_ ⟨.add i32, (.imm 1, (.var slot_i, ()))⟩ fun p725 =>
        .jump J723.1 (.var p725.1, ())
      )
    )
  ) (.jump Jrel ())

private theorem m8Wl_relink_wp (Γ : Env)
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
    (hgn_lt : gn.toNat < g_len) (hgat_gn : M6GateAt F_cur cv0 scr0 g_len gn.toNat)
    (hslot_le : slot_i.toNat ≤ ((scr0[gn.toNat + 1]?.getD 0#32) &&& 0xFF#32).toNat)
    (hokj : M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 sj)
    (hmj : (FullMem c sj ⋆ R) mj)
    (hJrel : ∀ m_nd,
      (∃ snd : FullState,
        M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz occ_end scr0 snd ∧
        (FullMem c snd ⋆ R) m_nd) →
      Jrel () m_nd) :
    wp Γ Q X (m8Wl_relinkExpr c.pRepr c.pScratchBuf (BitVec.ofNat 32 occ_bkt)
      (BitVec.ofNat 64 bkt_off) gn nd slot_i er Jrel) mj := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨hdwj, hcvj, hflj, hreprj, hlay_j, hprefj, hht_j, hocc_j⟩ := hokj
  have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len
  unfold m8Wl_relinkExpr
  m6b_steps; m6b_split
  · clear hc; m6b_to_group
    refine wp_join_group (ts := [i32])
      (fun (r_off, ()) mr => mr = mj ∧
        (gn.toNat + r_off.toNat < g_len ∧
          ∃ v : BitVec 32,
            scr0[gn.toNat + r_off.toNat]? = some v ∧ v.toNat < 2 * cv0))
      (fun _ ⟨r_off, ⟨⟩⟩ mr ⟨hmr, hr_lt, rv0, hrv0_get, hrv0_lt⟩ => by
        subst mr
        have hgnr_n : (gn + r_off.setWidth 64).toNat = gn.toNat + r_off.toNat := by
          rw [BitVec.toNat_add, bv_zext32_toNat r_off, Nat.mod_eq_of_lt (by omega)]
        have hgnr_arr : (gn + r_off.setWidth 64).toNat < sj.scratch.scratch_buf.length := by
          rw [hgnr_n]; omega
        have hgnr_arr' : gn.toNat + r_off.toNat < sj.scratch.scratch_buf.length := by omega
        have hscr_r0 : sj.scratch.scratch_buf[(gn + r_off.setWidth 64).toNat]'hgnr_arr = rv0 :=
          (list_getElem_congr hgnr_n hgnr_arr hgnr_arr').trans
            (scr_eq_of_pref hprefj hr_lt hgnr_arr' hrv0_get)
        m6b_steps; m6b_call hFind
        refine ⟨F_cur, 2 * cv0, sj.core.repr, FullReprRest c sj ⋆ R,
          hcvj ▸ hreprj, ?_, focus_full_repr hmj,
          fun dst repri mi hrl_i hrepr_i _ hdst_lt _ hmi => ?_⟩
        · change (sj.scratch.scratch_buf[(gn + r_off.setWidth 64).toNat]'hgnr_arr).toNat < 2 * cv0
          rw [hscr_r0]; exact hrv0_lt
        let sj_r : FullState := { sj with core := { sj.core with repr := repri } }
        have hscrl_jr : sj_r.scratch.scratch_buf.length = c.scratch_cap := hscrl_j
        have hmi' : (FullMem c sj_r ⋆ R) mi := unfocus_full_repr hmi
        clear hmi
        have hoki := m8WlStOk_with_repr hokj (hrl_i.trans hdwj.1.core_ok.repr_len) hrepr_i
        let b_dst := (dst >>> (1 : Nat)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
        have hbdst_lt : b_dst.toNat < occ_bkt := by
          dsimp only [b_dst]
          rw [show (dst >>> (1 : Nat)) = dst >>> 1#32 from rfl,
            show BitVec.ofNat 32 occ_bkt - (1 : BitVec 32) =
              BitVec.ofNat 32 occ_bkt - 1#32 from rfl,
            m8_and_sub1_u32_eq_mod hopow]
          exact Nat.mod_lt _ ho_pos
        obtain ⟨hb_idx_n, hb_arr, hb_arr_s1, hscrl_rel, hlay_rel,
          hpref_rel, hht_rel, hocc_rel, hrel_eq⟩ :=
          m8Wl_relink_step_prep hlay_j hscrl_j hprefj (hcvj ▸ hht_j) hocc_j hnd_lo hnd_hi
            hnd_ev hnd1_n hbdst_lt
        have hoe_co : occ_end ≤ ctrl_off := hocc_j.2.1
        have hnd1_nat : (nd.setWidth 64 + (1 : BitVec 64)).toNat = nd.toNat + 1 := hnd1_n
        have hb_dst_arr0 :
            (BitVec.ofNat 64 bkt_off + b_dst.setWidth 64).toNat <
              sj_r.scratch.scratch_buf.length := by
          rw [hscrl_jr, hb_idx_n]; omega
        have hnd1_arr0 :
            (nd.setWidth 64 + (1 : BitVec 64)).toNat < sj_r.scratch.scratch_buf.length := by
          rw [hscrl_jr, hnd1_nat]; omega
        have hb_dst_arr1 :
            (BitVec.ofNat 64 bkt_off + b_dst.setWidth 64).toNat <
              (sj_r.scratch.scratch_buf.set (nd.setWidth 64 + (1 : BitVec 64)).toNat
                (sj_r.scratch.scratch_buf[(BitVec.ofNat 64 bkt_off +
                  b_dst.setWidth 64).toNat]'hb_dst_arr0)).length := by
          rw [List.length_set]; exact hb_dst_arr0
        have hfs_r := focus_full_scratch8 hmi'; clear hmi'
        generalize hRs_r : FullScratchRest8 c sj_r ⋆ R = Rs_r at hfs_r
        m6b_steps
        have hrel_val :
            sj_r.scratch.scratch_buf[
                (BitVec.ofNat 64 bkt_off + b_dst.setWidth 64).toNat]'hb_dst_arr0 =
              sj.scratch.scratch_buf[bkt_off + b_dst.toNat]'(by rw [hscrl_j]; omega) :=
          list_getElem_congr hb_idx_n hb_dst_arr0 (by rw [hscrl_j]; omega)
        rw [hrel_val, show (1 : BitVec 64) = 1#64 from rfl, hb_idx_n, hnd1_n] at hm
        rw [hrel_eq _ (by rw [hscrl_j]; omega)] at hm
        subst hRs_r
        have hm_rel := unfocus_full_scratch88 hm
        refine hJrel m ⟨_, ?_, hm_rel⟩
        exact m8WlStOk_with_scr hoki hscrl_rel hlay_rel hpref_rel hht_rel hocc_rel)
      (fun Jr hJr => by
        obtain ⟨lhs_g, mw_g, hg0_g, hg1_g, hl_lt_g, _, _, _, hrhs_g, _⟩ := hgat_gn
        rw [hg1_g, Option.getD_some] at hslot_le
        m6b_split
        · have hs0 : slot_i.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
          m6b_let
          exact hJr (0, ()) mj ⟨rfl, by simp [hgn_lt], lhs_g, by simpa using hg0_g, hl_lt_g⟩
        · have hsne : slot_i.toNat ≠ 0 := fun h =>
            (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
          have hs_pos : 0 < slot_i.toNat := Nat.pos_of_ne_zero hsne
          have h1s : (1#32 + slot_i).toNat = 2 + (slot_i.toNat - 1) := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega
          obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_g (slot_i.toNat - 1) (by omega)
          m6b_let
          rw [show (1 : BitVec 32) + slot_i = 1#32 + slot_i from rfl]
          refine hJr (1#32 + slot_i, ()) mj ⟨rfl, ?_, rv, ?_, hrv_lt⟩
          · rw [h1s]; omega
          · rw [h1s, ← Nat.add_assoc]; exact hrv_get)
  · m6b_let; exact hJrel mj ⟨sj, hokj, hmj⟩

private def m8Wl_rehashExpr {V : Ty → Type} {L : List Ty → Type}
    (h scrPtr tlim ht_off_64 ht_sz_64 g_len ctrl_off i_o rehashes g_o : V i64)
    (ep : V i32) (ticks_n : V i64) (Jreh : L [i64, i64, i64, i64]) : Expr V L [i64] :=
  .let_ ⟨.add i64, (.var h, (.imm 1144, ()))⟩ fun p799 =>
  .load i64 (.var p799.1) fun v800 =>
  .let_ ⟨.mul i64, (.var v800, (.imm 4, ()))⟩ fun p801 =>
  .let_ ⟨.mul i64, (.var ht_sz_64, (.imm 3, ()))⟩ fun p802 =>
  .let_ ⟨.cmp .uge i64 .bool rfl, (.var p801.1, (.var p802.1, ()))⟩ fun p803 =>
  .jnz (.var p803.1) (
    .let_ ⟨.cmp .ult i64 .bool rfl, (.var rehashes, (.imm 4, ()))⟩ fun p804 =>
    .jnz (.var p804.1) (
      .let_ ⟨.cmp .ult i64 .bool rfl, (.var ticks_n, (.var tlim, ()))⟩ fun p805 =>
      .jnz (.var p805.1) (
        .group (sig := [[i64]]) (fun J806 =>
          .cons (fun p906 =>
            .let_ ⟨.cmp .ult i64 .bool rfl, (.var p906.1, (.var ht_sz_64, ()))⟩
              fun p907 =>
            .jnz (.var p907.1) (
              .let_ ⟨.add i64, (.var ht_off_64, (.var p906.1, ()))⟩ fun p908 =>
              .let_ ⟨.mul i64, (.var p908.1, (.imm 4, ()))⟩ fun p909 =>
              .let_ ⟨.add i64, (.var scrPtr, (.var p909.1, ()))⟩ fun p910 =>
              .store (t := i32) (.imm 4294967295) (.var p910.1) (
              .let_ ⟨.add i64, (.var p906.1, (.imm 1, ()))⟩ fun p911 =>
              .jump J806.1 (.var p911.1, ()))
            ) (
              .let_ ⟨.add i64, (.var h, (.imm 1144, ()))⟩ fun p908 =>
              .store (t := i64) (.imm 0) (.var p908.1) (
              .let_ ⟨.add i64, (.var rehashes, (.imm 1, ()))⟩ fun p909 =>
              .group (sig := [[i64, i64]]) (fun J910 =>
                .cons (fun p1010 =>
                  .let_ ⟨.cmp .ult i64 .bool rfl, (.var p1010.2.1, (.var g_len, ()))⟩
                    fun p1012 =>
                  .jnz (.var p1012.1) (
                    .let_ ⟨.add i64, (.var h, (.imm 1024, ()))⟩ fun p1013 =>
                    .load i64 (.var p1013.1) fun v1014 =>
                    .let_ ⟨.cmp .eq i64 .bool rfl, (.var v1014, (.imm 0, ()))⟩
                      fun p1015 =>
                    .jnz (.var p1015.1) (
                      .let_ ⟨.cmp .ult i64 .bool rfl, (.var p1010.1, (.var tlim, ()))⟩
                        fun p1016 =>
                      .jnz (.var p1016.1) (
                        .let_ ⟨.add i64, (.var p1010.2.1, (.imm 1, ()))⟩ fun p1017 =>
                        .let_ ⟨.mul i64, (.var p1017.1, (.imm 4, ()))⟩ fun p1018 =>
                        .let_ ⟨.add i64, (.var scrPtr, (.var p1018.1, ()))⟩
                          fun p1019 =>
                        .load i32 (.var p1019.1) fun v1020 =>
                        .let_ ⟨.and i32, (.var v1020, (.imm 255, ()))⟩
                          fun p1021 =>
                        .let_ ⟨.add i64, (.var p1010.1, (.imm 1, ()))⟩ fun p1022 =>
                        .call (as := [i64, i64, i64, i64, i32, i64]) (bs := [i64])
                          "full_cong_eval_gate"
                          (.var h, (.var p1010.2.1, (.var ht_off_64, (.var ht_sz_64, (.var ep,
                            (.var ctrl_off, ()))))))
                          fun p1023 =>
                        .let_ ⟨.and i64, (.var p1023.1, (.imm 2, ()))⟩ fun p1024 =>
                        .let_ ⟨.cmp .ne i64 .bool rfl, (.var p1024.1, (.imm 0, ()))⟩
                          fun p1025 =>
                        .jnz (.var p1025.1) (
                          .ret (.imm 20, ())
                        ) (
                          .let_ ⟨.add i64, (.var p1010.2.1, (.imm 2, ()))⟩
                            fun p1026 =>
                          .let_ ⟨.zext 32 64, (.var p1021.1, ())⟩ fun p1027 =>
                          .let_ ⟨.add i64, (.var p1026.1, (.var p1027.1, ()))⟩
                            fun p1028 =>
                          .jump J910.1 (.var p1022.1, (.var p1028.1, ()))
                        )
                      ) (
                        .jump Jreh
                          (.var p906.1, (.var p1010.1, (.var p909.1, (.var p1010.2.1, ()))))
                      )
                    ) (
                      .jump Jreh
                        (.var p906.1, (.var p1010.1, (.var p909.1, (.var p1010.2.1, ()))))
                    )
                  ) (
                    .jump Jreh
                      (.var p906.1, (.var p1010.1, (.var p909.1, (.var p1010.2.1, ()))))
                  )
                ) (.nil)
              ) (fun J910 =>
                .jump J910.1 (.var ticks_n, (.imm 0, ()))
              ))
            )
          ) (.nil)
        ) (fun J806 =>
          .jump J806.1 (.imm 0, ())
        )
      ) (
        .jump Jreh (.var i_o, (.var ticks_n, (.var rehashes, (.var g_o, ()))))
      )
    ) (
      .jump Jreh (.var i_o, (.var ticks_n, (.var rehashes, (.var g_o, ()))))
    )
  ) (
    .jump Jreh (.var i_o, (.var ticks_n, (.var rehashes, (.var g_o, ()))))
  )

private theorem m8Wl_rehash_wp (Γ : Env)
    (hEval : ∀ a m Q X, m8CongEvalGateSpec a m Q X →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {g_len ctrl_off tlim i_o ticks_o rehashes g_o ticks_n : BitVec 64} {ql ep : BitVec 32}
    {scr0 : List (BitVec 32)} {sa : FullState} {ma : Mem 64} {R : Mem 64 → Prop}
    {Q : Post [i64]} {X : XPost} {Jreh : Cont [i64, i64, i64, i64]}
    (hg_pos : 0 < g_len.toNat) (hht_pos : 0 < ht_sz) (hht_bnd : ht_sz < 2 ^ 30)
    (hg_ht_le : g_len.toNat ≤ ht_off) (hht_cap : ht_off + ht_sz ≤ c.scratch_cap)
    (hc_cap : ctrl_off.toNat < c.scratch_cap)
    (htlim_le : tlim.toNat ≤ 2 ^ 63 - 1) (hreh_le : rehashes.toNat ≤ 4)
    (hta_lo : ticks_o.toNat ≤ ticks_n.toNat) (hta_hi : ticks_n.toNat ≤ tlim.toNat + 2)
    (hta_eq : ticks_n.toNat = ticks_o.toNat →
      sa.core.inconsistent = 0#64 ∧
      (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat)
    (hseq0 : M6GateSeqOk F_cur cv0 scr0 g_len.toNat 0)
    (hoka : M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
      q_off ht_off ht_sz occ_end scr0 sa)
    (hma : (FullMem c sa ⋆ R) ma)
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = cv0 → s'.core.fuel = fuel0 →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJreh : ∀ ys mb,
      (match ys with
        | (_i_b, ticks_b, reh_b, _g_b, ()) => ∃ sb : FullState,
          reh_b.toNat ≤ 4 ∧ ticks_o.toNat ≤ ticks_b.toNat ∧
          ticks_b.toNat ≤ tlim.toNat + 3 ∧
          (ticks_o.toNat < ticks_b.toNat ∨
            (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
          M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz occ_end scr0 sb ∧
          (FullMem c sb ⋆ R) mb) →
      Jreh ys mb) :
    wp Γ Q X (m8Wl_rehashExpr c.hdr c.pScratchBuf tlim
      (BitVec.ofNat 64 ht_off) (BitVec.ofNat 64 ht_sz) g_len ctrl_off i_o rehashes g_o ep
      ticks_n Jreh) ma := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨hdw_a, hcv_a, hfl_a, hrepr_a, hlay_a, hpref_a, hht_a, hocc_a⟩ := hoka
  have hscrl_a := hdw_a.1.scratch_ok.scratch_buf_len
  have hho_n : (BitVec.ofNat 64 ht_off).toNat = ht_off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hhs_n : (BitVec.ofNat 64 ht_sz).toNat = ht_sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstep_a : ticks_o.toNat < ticks_n.toNat ∨
      (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat := by
    by_cases hteq : ticks_n.toNat = ticks_o.toNat
    · exact Or.inr (hta_eq hteq).2
    · exact Or.inl (by omega)
  have hjreh_sa : Jreh (i_o, ticks_n, rehashes, g_o, ()) ma :=
    hJreh (i_o, ticks_n, rehashes, g_o, ()) ma
      ⟨sa, hreh_le, hta_lo, by omega, hstep_a, hoka, hma⟩
  unfold m8Wl_rehashExpr
  m6b_steps; m6b_split
  · clear hc; m6b_split
    · have hreh_lt : rehashes.toNat < 4 := bv64_ult_lt hc
      clear hc; m6b_steps; m6b_split
      · have hta_lt : ticks_n.toNat < tlim.toNat := bv64_ult_lt hc
        clear hc; m6b_steps
        have hfs_a := focus_full_scratch8 hma; clear hma
        generalize hRs_a : FullScratchRest8 c sa ⋆ R = Rs_a at hfs_a
        refine wp_loop_inv (ts := [i64])
          (fun (ih, ()) mh => ∃ scrh : List (BitVec 32),
            scrh.length = c.scratch_cap ∧ ih.toNat ≤ ht_sz ∧
            M8CtrlLayout c scrh g_len.toNat ctrl_off.toNat occ_bkt bkt_off
              inq_off q_off ht_off ht_sz ∧
            (∀ idx < g_len.toNat, scrh[idx]? = scr0[idx]?) ∧
            (∀ k < ih.toNat, scrh[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
            M6OccNodesOk F_cur cv0 g_len.toNat occ_end ctrl_off.toNat
              bkt_off occ_bkt scr0 scrh ∧
            (array (t := i32) c.pScratchBuf scrh ⋆ Rs_a) mh)
          (fun (ih, ()) _ => ht_sz - ih.toNat)
          (fun Jh hJh => by
            m6b_steps; exact hJh (0#64, ()) ma ⟨sa.scratch.scratch_buf, hscrl_a,
              Nat.zero_le _, hlay_a, hpref_a, fun _ h => absurd h (Nat.not_lt_zero _),
              hocc_a, hfs_a⟩)
          (fun Jh (ih, ()) mh ⟨scrh, hscrl_h, hih_le, hlay_h, hpref_h, hht_h,
            hocc_h, hmh⟩ ihh => ?_)
        m6b_split
        · have hih_lt : ih.toNat < ht_sz := by
            have hlt := bv64_ult_lt hc
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
            exact hlt
          obtain ⟨hhti_n, hhti_arr, hih1, hscrl_h', hlay_h', hpref_h',
            hht_h', hocc_h'⟩ :=
            m8Wl_rehash_clear_step hlay_h hscrl_h hpref_h hht_h hocc_h hih_lt
          clear hc; m6b_steps
          rw [hhti_n] at hm
          exact ihh (ih + 1#64, ()) m (by dsimp only; omega)
            ⟨_, hscrl_h', by rw [hih1]; omega, hlay_h', hpref_h',
             fun k hk => hht_h' k (hih1 ▸ hk), hocc_h', hm⟩
        · have hih_eq : ih.toNat = ht_sz := by
            have hnot := bv64_ult_not_lt hc
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnot
            omega
          rw [hih_eq] at hht_h
          have hht_clr : M6CongHtInv F_cur cv0 scr0 scrh g_len.toNat ht_off ht_sz :=
            fun k hk => Or.inl (hht_h k hk)
          subst hRs_a
          have hmh_u := unfocus_full_scratch88 hmh
          clear hc; m6b_steps
          let sa_r : FullState :=
            { sa with scratch := { sa.scratch with scratch_buf := scrh, res_sz := 0#64 } }
          have hok_r : M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat
              occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end scr0 sa_r :=
            m8WlStOk_with_scr hoka hscrl_h hlay_h hpref_h hht_clr hocc_h 0#64
          have hr1_n : (rehashes + 1#64).toNat = rehashes.toNat + 1 :=
            bv64_add1_toNat (n := 4) hreh_lt (by decide)
          m6b_to_group
          refine wp_loop_inv (ts := [i64, i64])
            (fun (ticks_r, gr, ()) mr => ∃ sr : FullState,
              gr.toNat ≤ g_len.toNat ∧ ticks_n.toNat ≤ ticks_r.toNat ∧
              ticks_r.toNat ≤ tlim.toNat + 1 ∧
              (0 < gr.toNat → ticks_n.toNat < ticks_r.toNat) ∧
              (ticks_n.toNat = ticks_o.toNat → gr.toNat = 0 → sr.core.inconsistent = 0#64) ∧
              M6GateSeqOk F_cur cv0 scr0 g_len.toNat gr.toNat ∧
              M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                bkt_off inq_off q_off ht_off ht_sz occ_end scr0 sr ∧
              (FullMem c sr ⋆ R) mr)
            (fun (_, gr, ()) _ => g_len.toNat - gr.toNat)
            (fun Jr hJr => by
              m6b_steps; exact hJr (ticks_n, 0#64, ()) m
                ⟨sa_r, Nat.zero_le _, Nat.le_refl _, by omega,
                 fun h => absurd h (by decide), fun h _ => (hta_eq h).1,
                 hseq0, hok_r, hm⟩)
            (fun Jr (ticks_r, gr, ()) mr
              ⟨sr, hgr_le, htr_lo, htr_hi, hgr_lt, htr_inc, hseq_r, hok_r, hmr⟩ ihr => ?_)
          have ⟨hdw_r, hcv_r, hfl_r, hrepr_r, hlay_r, hpref_r, hht_r, hocc_r⟩ := hok_r
          have hscrl_r := hdw_r.1.scratch_ok.scratch_buf_len
          have hreh_exit :
              (¬ gr.toNat < g_len.toNat ∨ sr.core.inconsistent ≠ 0#64 ∨
                ¬ ticks_r.toNat < tlim.toNat) →
              ticks_o.toNat < ticks_r.toNat := by
            intro hwhy
            rcases Nat.eq_or_lt_of_le hta_lo with hteq | htlt
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
                obtain ⟨hgat_r, hseq_r'⟩ := m6GateSeqOk_inv_lt hseq_r hgr_lt_g
                have ⟨_, mword_r, _, hscr_r1, _, hbd_r, _, _, _, _⟩ := hgat_r
                have hgr1_n : (gr + 1#64).toNat = gr.toNat + 1 :=
                  bv64_add1_toNat (by omega) (by omega)
                have hgr1_arr : (gr + 1#64).toNat < sr.scratch.scratch_buf.length := by
                  rw [hgr1_n]; omega
                have hsr_g1 : sr.scratch.scratch_buf[(gr + 1#64).toNat]'hgr1_arr = mword_r :=
                  scr_eq_of_pref hpref_r (by omega) hgr1_arr (by rw [hgr1_n]; exact hscr_r1)
                let ar_r := mword_r &&& 0xFF#32
                have hnext_gr : (gr + 2#64 + ar_r.setWidth 64).toNat =
                    gr.toNat + 2 + ar_r.toNat := bv64_add_zext32 (k := 2) (by omega)
                have hseq_r'' : M6GateSeqOk F_cur cv0 scr0 g_len.toNat
                    (gr + 2#64 + ar_r.setWidth 64).toNat := by
                  rw [hnext_gr]
                  simpa only [hscr_r1, Option.getD_some, ar_r] using hseq_r'
                clear hc; m6b_steps; m6b_call hEval
                dsimp only [m8CongEvalGateSpec]
                rw [hho_n, hhs_n]
                refine ⟨c, F0, F_cur, sr, scr0, g_len.toNat, R, rfl, hdw_r,
                  hcv_r ▸ hrepr_r, hht_pos, hht_bnd, hgr_lt_g,
                  by omega, by omega, hpref_r, hcv_r ▸ hgat_r, hcv_r ▸ hht_r,
                  Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay_r⟩, hmr,
                  fun er su mu hdwu hcvu hflu haru haleu hrepru hprefu hhtu hqu
                    hfru he2_u hmu => ?_⟩
                m6b_split
                · m6b_steps
                  exact hQ 20#64 su mu hdwu (hcvu.trans hcv_r)
                    (hflu.trans hfl_r) ((hcvu.trans hcv_r) ▸ hrepru)
                    (Or.inr rfl) (fun _ => he2_u (bne_iff_ne.mp hc)) hmu
                · have he2_0 : (er &&& 2#64) = 0#64 := by simpa using hc
                  have hoku := m8Wl_stOk_of_eval hok_r hc_cap he2_0 hdwu hcvu hflu
                    hrepru hprefu hhtu hqu (hfru he2_0)
                  have htr1 : (ticks_r + 1#64).toNat = ticks_r.toNat + 1 :=
                    bv64_add1_lt (by omega)
                  have hsr_g1_any : ∀ h,
                      sr.scratch.scratch_buf[(gr + (1 : BitVec 64)).toNat]'h =
                      mword_r := fun _ => hsr_g1
                  m6b_steps
                  rw [show ticks_r + (1 : BitVec 64) = ticks_r + 1#64 from rfl,
                    hsr_g1_any _, show (255 : BitVec 32) = 0xFF#32 from rfl,
                    show (2 : BitVec 64) = 2#64 from rfl]
                  exact ihr (ticks_r + 1#64, gr + 2#64 + ar_r.setWidth 64, ()) mu
                    (by dsimp only; rw [hnext_gr]; omega)
                    ⟨su, by rw [hnext_gr]; exact hbd_r, by rw [htr1]; omega,
                     by rw [htr1]; omega, fun _ => by rw [htr1]; omega,
                     fun _ hg0 => by rw [hnext_gr] at hg0; omega,
                     hseq_r'', hoku, hmu⟩
              · m6b_let; exact hJreh (ih, ticks_r, rehashes + 1#64, gr, ()) mr
                  ⟨sr, by omega, by omega, by omega,
                   Or.inl (hreh_exit (Or.inr (Or.inr (bv64_ult_not_lt hc)))), hok_r, hmr⟩
            · m6b_let; exact hJreh (ih, ticks_r, rehashes + 1#64, gr, ()) mr
                ⟨sr, by omega, by omega, by omega,
                 Or.inl (hreh_exit (Or.inr (Or.inl (beq_eq_false_iff_ne.mp hc)))), hok_r, hmr⟩
          · m6b_let; exact hJreh (ih, ticks_r, rehashes + 1#64, gr, ()) mr
              ⟨sr, by omega, by omega, by omega,
               Or.inl (hreh_exit (Or.inl (bv64_ult_not_lt hc))), hok_r, hmr⟩
      · m6b_let; exact hjreh_sa
    · m6b_let; exact hjreh_sa
  · m6b_let; exact hjreh_sa

private def m8Wl_pushsExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reprPtr scrPtr : V i64) (occ_u : V i32) (bkt_64 occ_s_init g : V i64)
    (arity : V i32) (Jocc : L [i64]) : Expr V L rs :=
  .group (sig := [[i64, i32]]) (fun J395 =>
    .cons (fun p495 =>
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
        .jump J395.1 (.var p527.1, (.var p528.1, ()))
        )))
      ) (
        .jump Jocc (.var p495.1, ())
      )
    ) (.nil)
  ) (fun J395 =>
    .jump J395.1 (.var occ_s_init, (.imm 0, ()))
  )

private theorem m8Wl_pushs_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st_p0 : FullState} {m_p0 : Mem 64} {occ_end g : BitVec 64}
    {mw1 : BitVec 32} {R : Mem 64 → Prop} {Jocc : Cont [i64]} {Q : Post [i64]} {X : XPost}
    (hg_co : g_len ≤ ctrl_off) (_hht_cap : ht_off + ht_sz ≤ c.scratch_cap)
    (hc_cap : ctrl_off < c.scratch_cap)
    (ho_pos : 0 < occ_bkt) (hopow : ∃ p, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p)
    (hg_lt : g.toNat < g_len) (hgat_1 : M6GateAt F_cur cv0 scr0 g_len g.toNat)
    (hscr0_g1 : scr0[g.toNat + 1]? = some mw1)
    (hocc_fit : occ_end.toNat + (1 + (mw1 &&& 0xFF#32).toNat) * 2 ≤ ctrl_off)
    (hoe_lo : g_len ≤ occ_end.toNat) (hoe_ev : (occ_end.toNat - g_len) % 2 = 0)
    (hoe2_n : (occ_end + 2#64).toNat = occ_end.toNat + 2)
    (hg_32 : g.setWidth 32 = BitVec.ofNat 32 g.toNat)
    (hok_p0 : M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz (occ_end.toNat + 2) scr0 st_p0)
    (hm_p0 : (FullMem c st_p0 ⋆ R) m_p0)
    (hJocc : ∀ (occ_e' : BitVec 64) me,
      (∃ se : FullState, g_len ≤ occ_e'.toNat ∧ occ_e'.toNat ≤ ctrl_off ∧
        (occ_e'.toNat - g_len) % 2 = 0 ∧
        M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz occ_e'.toNat scr0 se ∧
        (FullMem c se ⋆ R) me) →
      Jocc (occ_e', ()) me) :
    wp Γ Q X (m8Wl_pushsExpr c.pRepr c.pScratchBuf (BitVec.ofNat 32 occ_bkt)
      (BitVec.ofNat 64 bkt_off) (occ_end + 2#64) g (mw1 &&& 0xFF#32) Jocc) m_p0 := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  let arity := mw1 &&& 0xFF#32
  have ⟨_, mword, _, hg1, _, _, _, _, hrhs_1, _⟩ := hgat_1
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hscr0_g1)
  unfold m8Wl_pushsExpr
  m6b_to_group
  refine wp_loop_inv (ts := [i64, i32])
    (fun (occ_s, s_i, ()) ms => ∃ st_s : FullState,
      s_i.toNat ≤ arity.toNat ∧ g_len ≤ occ_s.toNat ∧
      occ_s.toNat + 2 * (arity.toNat - s_i.toNat) ≤ ctrl_off ∧
      (occ_s.toNat - g_len) % 2 = 0 ∧
      M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
        ht_off ht_sz occ_s.toNat scr0 st_s ∧
      (FullMem c st_s ⋆ R) ms)
    (fun (_, s_i, ()) _ => arity.toNat - s_i.toNat)
    (fun Js hJs => by
      m6b_steps
      refine hJs (occ_end + 2#64, 0#32, ()) m_p0 ⟨_, Nat.zero_le _,
        by rw [hoe2_n]; omega, by rw [hoe2_n]; dsimp only [arity]; omega,
        by rw [hoe2_n]; omega, ?_, hm_p0⟩
      exact hoe2_n ▸ hok_p0)
    (fun Js (occ_s, s_i, ()) ms ⟨st_s, hs_le, hoes_lo, hoes_cap, hoes_ev, hok_s, hms⟩ ihs => ?_)
  have ⟨hdw_s, hcv_s, hfl_s, hrepr_s, hlay_s, hpref_s, hht_s, hocc_s⟩ := hok_s
  have hscrl_s := hdw_s.1.scratch_ok.scratch_buf_len
  m6b_split
  · have hs_lt : s_i.toNat < arity.toNat := bv32_ult_lt hc
    have hs_lt_mw : s_i.toNat < (mword &&& 0xFF#32).toNat := by
      simpa only [arity, ← hmw] using hs_lt
    obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_1 s_i.toNat hs_lt_mw
    have hg2s_n : (g + 2#64 + s_i.setWidth 64).toNat = g.toNat + 2 + s_i.toNat :=
      bv64_add_zext32 (k := 2) (by omega)
    have hg2s_arr : (g + 2#64 + s_i.setWidth 64).toNat < st_s.scratch.scratch_buf.length := by
      rw [hg2s_n]; omega
    have hs_g2s : st_s.scratch.scratch_buf[(g + 2#64 + s_i.setWidth 64).toNat]'hg2s_arr = rv :=
      scr_eq_of_pref hpref_s (by omega) hg2s_arr (by rw [hg2s_n]; exact hrv_get)
    clear hc; m6b_steps; m6b_call hFind
    refine ⟨F_cur, 2 * cv0, st_s.core.repr, FullReprRest c st_s ⋆ R,
      hcv_s ▸ hrepr_s,
      (congrArg BitVec.toNat (hs_g2s : st_s.scratch.scratch_buf[(g + (2 : BitVec 64) +
        s_i.setWidth 64).toNat]'hg2s_arr = rv)) ▸ hrv_lt,
      focus_full_repr hms,
      fun rr repr_r mr hrl_r hrepr_r _ hrr_lt _ hmr => ?_⟩
    let st_r : FullState := { st_s with core := { st_s.core with repr := repr_r } }
    have hscrl_sr : st_r.scratch.scratch_buf.length = c.scratch_cap := hscrl_s
    have hmr' : (FullMem c st_r ⋆ R) mr := unfocus_full_repr hmr
    clear hmr
    have hokr := m8WlStOk_with_repr hok_s (hrl_r.trans hdw_s.1.core_ok.repr_len) hrepr_r
    let bs := (rr >>> (1 : Nat)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
    have hbs_lt : bs.toNat < occ_bkt := by
      dsimp only [bs]
      rw [show (rr >>> (1 : Nat)) = rr >>> 1#32 from rfl,
        show BitVec.ofNat 32 occ_bkt - (1 : BitVec 32) = BitVec.ofNat 32 occ_bkt - 1#32 from rfl,
        m8_and_sub1_u32_eq_mod hopow]
      exact Nat.mod_lt _ ho_pos
    obtain ⟨hbs_n, hoes_hi, hoes1_n, hoes2_n, hs1_n, hoes_32,
      hscrl_ps, hlay_ps, hpref_ps, hht_ps, hocc_ps,
      hbs_arr_s, hoes1_arr_s, hbs_arr_s2, hps_eq⟩ :=
      m8Wl_pushs_step_prep hlay_s hscrl_s hpref_s (hcv_s ▸ hht_s) hocc_s
        hgat_1 hscr0_g1 hg_co hg_lt hs_lt hoes_lo hoes_cap hoes_ev hbs_lt hg_32
    have hco_bkt : ctrl_off < bkt_off := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hq1, hq2, hq3, _⟩ := hlay_s; omega
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
        ((st_r.scratch.scratch_buf.set occ_s.toNat entry_s).set
          (occ_s + 1#64).toNat
          ((st_r.scratch.scratch_buf.set occ_s.toNat entry_s)[
            (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1)).length := by
      simp only [List.length_set]; rw [hscrl_sr, hbs_n]; omega
    have hfs_ps := focus_full_scratch8 hmr'; clear hmr'
    generalize hRs_ps : FullScratchRest8 c st_r ⋆ R = Rs_ps at hfs_ps
    m6b_steps
    let scr_ps := ((st_s.scratch.scratch_buf.set occ_s.toNat entry_s).set (occ_s.toNat + 1)
      (st_s.scratch.scratch_buf[bkt_off + bs.toNat]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + bs.toNat) (BitVec.ofNat 32 occ_s.toNat)
    have hbs_val :
        (st_r.scratch.scratch_buf.set occ_s.toNat entry_s)[
          (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1 =
        st_s.scratch.scratch_buf[bkt_off + bs.toNat]'(by rw [hscrl_s]; omega) := by
      rw [List.getElem_set_ne (by change _ ≠ _; rw [hbs_n]; omega)]
      exact list_getElem_congr hbs_n _ _
    have hmem_scr :
        ((st_r.scratch.scratch_buf.set occ_s.toNat
            (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32)).set
          (occ_s + (1 : BitVec 64)).toNat
          ((st_r.scratch.scratch_buf.set occ_s.toNat
              (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32))[
            (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1)).set
          (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat (occ_s.setWidth 32) = scr_ps := by
      have he : (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32) =
          entry_s := rfl
      have h1 : st_r.scratch.scratch_buf.set occ_s.toNat
          (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32) =
          st_r.scratch.scratch_buf.set occ_s.toNat entry_s := congrArg _ he
      have h2 :
          (st_r.scratch.scratch_buf.set occ_s.toNat
            (((s_i + (1 : BitVec 32)) <<< (24 : BitVec 32)) ||| g.setWidth 32))[
            (BitVec.ofNat 64 bkt_off + bs.setWidth 64).toNat]'hbs_arr1 =
          st_s.scratch.scratch_buf[bkt_off + bs.toNat]'(by rw [hscrl_s]; omega) :=
        (list_getElem_congr rfl _ hbs_arr1).trans hbs_val
      rw [h2, he, show (occ_s + (1 : BitVec 64)).toNat = occ_s.toNat + 1 from hoes1_n, hbs_n]
      exact hps_eq (by rw [hscrl_s]; omega)
    dsimp only [bs] at hmem_scr
    have hm_ps_arr : (array (t := i32) c.pScratchBuf scr_ps ⋆ Rs_ps) m :=
      (congrArg (fun (xs : List (BitVec 32)) =>
        (array (t := i32) c.pScratchBuf xs ⋆ Rs_ps) m) hmem_scr).mp hm
    subst hRs_ps
    have hm_ps' := unfocus_full_scratch88 hm_ps_arr
    let st_ps : FullState :=
      { st_r with scratch := { st_r.scratch with scratch_buf := scr_ps } }
    have hok_ps' : M8WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
        ht_off ht_sz (occ_s.toNat + 2) scr0 st_ps :=
      ⟨⟨⟨hokr.1.1.core_ok, { hokr.1.1.scratch_ok with scratch_buf_len := hscrl_ps }⟩,
        hokr.1.2.1, hokr.1.2.2.1, hokr.1.2.2.2.1,
        fullExtScratchOk_of_eq hokr.1.2.2.2.2.1 rfl rfl rfl rfl,
        hokr.1.2.2.2.2.2.1, hokr.1.2.2.2.2.2.2⟩,
       hokr.2.1, hokr.2.2.1, hokr.2.2.2.1, hlay_ps, hpref_ps, hht_ps, hocc_ps⟩
    refine ihs (occ_s + 2#64, s_i + 1#32, ()) m (by dsimp only; omega)
      ⟨st_ps, by rw [hs1_n]; omega, by rw [hoes2_n]; omega,
       by rw [hoes2_n, hs1_n]; omega, by rw [hoes2_n]; omega,
       hoes2_n ▸ hok_ps', hm_ps'⟩
  · clear hc; m6b_let
    exact hJocc occ_s ms ⟨st_s, hoes_lo, by omega, hoes_ev, hok_s, hms⟩


theorem full_cong_worklist_m8_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hEval : ∀ a m Q X, m8CongEvalGateSpec a m Q X →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, m8CongWorklistSpec a m Q X → Func.wp Γ full_cong_worklist_body a m Q X := by
  rintro ⟨h, g_len, ctrl_off, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, occ_bkt, bkt_off, inq_off, q_off, ht_off, ht_sz, R,
     rfl, hdw0, hrepr0, hg_pos, hht_bnd, hlay0, hseq0, hpref0, hht0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have ⟨hc_cap, _hc_8, hg_co, hg_24, _, _, _, _, _, _,
    ho_pos, ho_8192, hopow, hht_pos, hcq, hqi, hib, hbh, hht_cap, _, _, _⟩ := hlay0
  have hg_ht_le : g_len.toNat ≤ ht_off := by omega
  have hscrl0 := hdw0.1.scratch_ok.scratch_buf_len
  have hg_lt_64 : g_len.toNat < 2 ^ 64 := by omega
  m6b_to_group
  refine wp_join_group (ts := [i64]) (fun (tlim, ()) mt => mt = m0 ∧ tlim.toNat ≤ 2 ^ 63 - 1)
    ?_ ?_
  · rintro _ ⟨tlim, ⟨⟩⟩ mt ⟨hmt, htlim_le⟩; subst mt
    have hcf := m8Wl_ctrl_arith hht_bnd hscrl0 hlay0
    rcases hcf with ⟨hc1_n, hc2_n, hc3_n, hc4_n, hc5_n, hc6_n, hc7_n,
      hco0_arr, hco1_arr, hco2_arr, hco3_arr, hco4_arr, hco5_arr, hco6_arr, hco7_arr,
      heq_co0, heq_co1, heq_co2, heq_co3, heq_co6, heq_co7,
      hbkt32, hinq32, hq32, hho32, hhs32, hocc32, hho_n, hhs_n, hbkt64_n, hinq64_n, hq64_n⟩
    let occ_u := BitVec.ofNat 32 occ_bkt
    let bkt_64 := BitVec.ofNat 64 bkt_off
    let inq_64 := BitVec.ofNat 64 inq_off
    let q_64 := BitVec.ofNat 64 q_off
    let ht_off_64 := BitVec.ofNat 64 ht_off
    let ht_sz_64 := BitVec.ofNat 64 ht_sz
    m6b_steps
    have hfs0 := focus_full_scratch8 hm0; clear hm0
    generalize hRs0 : FullScratchRest8 c s0 ⋆ R = Rs0 at hfs0
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) mi => ∃ scri : List (BitVec 32),
        scri.length = c.scratch_cap ∧ i.toNat ≤ occ_bkt ∧
        M8CtrlLayout c scri g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
        (∀ idx < g_len.toNat, scri[idx]? = scr0[idx]?) ∧
        M6CongHtInv F_cur cv0 scr0 scri g_len.toNat ht_off ht_sz ∧
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
        m8Wl_phase0_clear_step hlay_i hscrl_i hpref_i hht_i hbkt_i hi_lt
      clear hc; rw [heq_co1, hbkt32, heq_co2, hinq32]; m6b_steps
      rw [hbkt_i_n, hinq_i_n] at hm
      exact ihi (i + 1#64, ()) m (by dsimp only; omega)
        ⟨_, hscrl', by omega, hlay', hpref', hht', fun b hb => hbkt' b (hi1_n ▸ hb), hm⟩
    · have hi_eq : i.toNat = occ_bkt := by
        have hnot : ¬ i.toNat < occ_bkt := by
          have := bv64_ult_not_lt hc
          rw [heq_co0, hocc32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact this
        omega
      rw [hi_eq] at hbkt_i
      have hc4_arr : (ctrl_off + 4).toNat < scri.length := by rw [hc4_n, hscrl_i]; omega
      have hc5_arr : (ctrl_off + 5).toNat < (scri.set (ctrl_off + 4).toNat 0#32).length := by
        rw [List.length_set, hc5_n, hscrl_i]; omega
      clear hc; m6b_steps; rw [hc4_n, hc5_n] at hm
      subst hRs0
      have hm_p0 := unfocus_full_scratch88 hm
      obtain ⟨hscrl_p0, hlay_p0, hpref_p0, hht_p0, hocc_p0⟩ :=
        m8Wl_phase0_finalize hlay_i hscrl_i hpref_i hht_i hbkt_i rfl
      let st_p0 : FullState :=
        { s0 with scratch := { s0.scratch with
          scratch_buf := (scri.set (ctrl_off.toNat + 4) 0#32).set (ctrl_off.toNat + 5) 0#32 } }
      have hok_p0 : M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
          inq_off q_off ht_off ht_sz g_len.toNat scr0 st_p0 :=
        ⟨⟨⟨hdw0.1.core_ok, { hdw0.1.scratch_ok with scratch_buf_len := hscrl_p0 }⟩,
          hdw0.2.1, hdw0.2.2.1, hdw0.2.2.2.1,
          fullExtScratchOk_of_eq hdw0.2.2.2.2.1 rfl rfl rfl rfl,
          hdw0.2.2.2.2.2.1, hdw0.2.2.2.2.2.2⟩,
         rfl, rfl, hrepr0, hlay_p0, hpref_p0, hht_p0, hocc_p0⟩
      m6b_to_group
      refine wp_loop_inv (ts := [i64, i64, i64])
        (fun (occ_end, ticks, g, ()) m1 => ∃ s1 : FullState,
          g.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ occ_end.toNat ∧ occ_end.toNat ≤ ctrl_off.toNat ∧
          (occ_end.toNat - g_len.toNat) % 2 = 0 ∧ ticks.toNat ≤ tlim.toNat + 2 ∧
          M6GateSeqOk F_cur cv0 scr0 g_len.toNat g.toNat ∧
          M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz occ_end.toNat scr0 s1 ∧
          (FullMem c s1 ⋆ R) m1)
        (fun (_, _, g, ()) _ => g_len.toNat - g.toNat)
        (fun J1 hJ1 => by
          m6b_steps; exact hJ1 (g_len, 0#64, 0#64, ()) m
            ⟨st_p0, Nat.zero_le _, Nat.le_refl _, hg_co, by simp, Nat.zero_le _, hseq0,
             hok_p0, hm_p0⟩)
        (fun J1 (occ_end, ticks, g, ()) m1
            ⟨s1, hg_le, hoe_lo, hoe_hi, hoe_ev, htk_le, hseq_1, hok_1, hm1⟩ ih1 => ?_)
      have ⟨hdw_1, hcv_1, hfl_1, hrepr_1, hlay_1, hpref_1, hht_1, hocc_1⟩ := hok_1
      have hscrl_1 := hdw_1.1.scratch_ok.scratch_buf_len
      m6b_to_group
      refine wp_join_group (ts := []) (fun () mp2 => mp2 = m1) ?_ ?_
      · rintro _ ⟨⟩ mp2 hmp2; subst mp2
        let p5Addr := c.pScratchBuf + BitVec.ofNat 64 (4 * (ctrl_off.toNat + 5))
        have m8Wl_v_eq : ∀ {st : FullState} {m : Mem 64}
            (h : ctrl_off.toNat + 5 < st.scratch.scratch_buf.length),
            (FullMem c st ⋆ R) m →
            ((loadVal m i32 p5Addr).getD 0#32).toNat =
              (st.scratch.scratch_buf[ctrl_off.toNat + 5]'h).toNat := fun h hm => by
          dsimp only [p5Addr]
          rw [FullArenaTactics.load_full_scratch_buf h hm, Option.getD_some]
        m6b_to_group
        refine wp_loop_inv (ts := [i64, i64, i64, i64, i32])
          (fun (_i, ticks_o, rehashes, _g, _ep, ()) mo => ∃ so : FullState,
            rehashes.toNat ≤ 4 ∧ ticks_o.toNat ≤ tlim.toNat + 3 ∧
            M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
              q_off ht_off ht_sz occ_end.toNat scr0 so ∧
            (FullMem c so ⋆ R) mo)
          (fun (_, ticks_o, _, _, _, ()) mo =>
            (tlim.toNat - ticks_o.toNat) * (occ_bkt + 1) +
              ((loadVal mo i32 p5Addr).getD 0#32).toNat)
          ?_ ?_
        · intro Jo hJo
          m6b_steps; exact hJo (i, ticks, 0#64, g, 3#32, ()) m1
            ⟨s1, Nat.zero_le _, by omega, hok_1, hm1⟩
        rintro Jo ⟨_i_o, ticks_o, rehashes, _g_o, ep, ⟨⟩⟩ mo
          ⟨so, hreh_le, hto_le, hok_o, hmo⟩ iho
        have ⟨hdw_o, hcv_o, hfl_o, hrepr_o, hlay_o, hpref_o, hht_o, hocc_o⟩ := hok_o
        have hscrl_o := hdw_o.1.scratch_ok.scratch_buf_len
        have hc5_o : ctrl_off.toNat + 5 < so.scratch.scratch_buf.length := by
          have := hlay_o.1; omega
        have hp5_o : ((loadVal mo i32 p5Addr).getD 0#32).toNat =
            (so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
          rw [m8Wl_v_eq hc5_o hmo, List.getElem?_eq_getElem hc5_o, Option.getD_some]
        m6b_to_group
        refine wp_join_group (ts := [])
          (fun () m_out => ∃ sx : FullState,
            FullDenseInvW c F0 F_cur sx ∧ sx.core.cur_vars = cv0 ∧ sx.core.fuel = fuel0 ∧
            FullCongReprInv F_cur (2 * cv0) sx.core.repr ∧ (FullMem c sx ⋆ R) m_out)
          ?_ ?_
        · rintro _ ⟨⟩ m_out ⟨sx, hdwx, hcvx, hflx, hreprx, hmx⟩
          m6b_to_group
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mr => ∃ sx' : FullState,
              FullDenseInvW c F0 F_cur sx' ∧ sx'.core.cur_vars = cv0 ∧
              sx'.core.fuel = fuel0 ∧ FullCongReprInv F_cur (2 * cv0) sx'.core.repr ∧
              (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullMem c sx' ⋆ R) mr)
            (fun _ ⟨r, ⟨⟩⟩ mr ⟨sx', hdwx', hcvx', hflx', hreprx', hr, huns, hmx'⟩ => by
              m6b_steps
              exact hQ r sx' mr hdwx' hcvx' hflx' (hcvx' ▸ hreprx') hr huns hmx')
            (fun Jret hJret => by
              m6b_steps; m6b_split
              · have hne0 : sx.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
                m6b_steps
                exact hJret (20#64, ()) m_out ⟨sx, hdwx, hcvx, hflx, hreprx, Or.inr rfl,
                  (fun _ => unsat_of_inconsistent_w hdwx.2.1 hne0), hmx⟩
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
            have hget5 : so.scratch.scratch_buf[(ctrl_off + 5).toNat]'hco5' =
                so.scratch.scratch_buf[ctrl_off.toNat + 5]'(by omega) :=
              list_getElem_congr hc5_n hco5' (by omega)
            change 0 < (so.scratch.scratch_buf[(ctrl_off + 5).toNat]'hco5').toNat at hlt
            rw [hget5, ← Option.getD_some
              (a := so.scratch.scratch_buf[ctrl_off.toNat + 5]'(by omega)) (b := 0#32),
              ← List.getElem?_eq_getElem (by omega)] at hlt
            exact hlt
          clear hc; m6b_split
          · have hinc_0 : so.core.inconsistent = 0#64 := beq_iff_eq.mp hc
            clear hc; m6b_split
            · have hto_lt : ticks_o.toNat < tlim.toNat := bv64_ult_lt hc
              let qh := so.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32
              let ql := so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32
              let b := so.scratch.scratch_buf[q_off + qh.toNat]?.getD 0#32
              let nqh := (qh + 1#32) &&& (occ_u - 1#32)
              obtain ⟨hco4_o, hco5_o, hq_ld_arr, hb_lt, hnqh_lt, hscrl_pop, hlay_pop,
                hpref_pop, hht_pop, hnd0_ptr, hocc_pop, hqh_u, hql_u, hb_raw_eq, hco5_s4,
                hinq_s45_arr, hbkt_s45i_arr, hinqb_n, hbktb_n, hnd0_scr3, hscr_pop_eq,
                hql_pop_lt⟩ :=
                m8Wl_pop_step_prep hlay_o hscrl_o hpref_o hht_o hocc_o hql_pos hc4_n hc5_n
              clear hc
              have hfs_o := focus_full_scratch8 hmo; clear hmo
              generalize hRs_o : FullScratchRest8 c so ⋆ R = Rs_o at hfs_o
              rw [heq_co0, heq_co1, hbkt32, heq_co2, hinq32, heq_co3, hq32]
              m6b_steps
              rw [hnd0_scr3 _]
              rw [hscr_pop_eq] at hm
              subst hRs_o
              have hm_pop := unfocus_full_scratch88 hm
              let scr_pop := (((so.scratch.scratch_buf.set (ctrl_off.toNat + 4) nqh).set
                (ctrl_off.toNat + 5) (ql - 1#32)).set (inq_off + b.toNat) 0#32).set
                (bkt_off + b.toNat) 0xFFFFFFFF#32
              let st_pop : FullState :=
                { so with scratch := { so.scratch with scratch_buf := scr_pop } }
              have hok_pop : M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                  bkt_off inq_off q_off ht_off ht_sz occ_end.toNat scr0 st_pop :=
                m8WlStOk_with_scr hok_o hscrl_pop hlay_pop hpref_pop hht_pop hocc_pop
              let nd0 := so.scratch.scratch_buf[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32
              clear hco4_o hco5_o hq_ld_arr hb_lt hnqh_lt hco5_s4 hinq_s45_arr hbkt_s45i_arr
                hinqb_n hbktb_n hnd0_scr3 hscr_pop_eq hqh_u hql_u hb_raw_eq
                hscrl_pop hlay_pop hpref_pop hht_pop hocc_pop
              m6b_to_group
              refine wp_loop_inv (ts := [i64, i32])
                (fun (ticks_n, nd, ()) mn => ∃ sn : FullState,
                  ticks_o.toNat ≤ ticks_n.toNat ∧ ticks_n.toNat ≤ tlim.toNat + 2 ∧
                  (ticks_n.toNat = ticks_o.toNat →
                    sn.core.inconsistent = 0#64 ∧
                    (sn.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
                  M6OccNodePtrOk g_len.toNat occ_end.toNat nd ∧
                  M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
                    inq_off q_off ht_off ht_sz occ_end.toNat scr0 sn ∧
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
                (ticks_n.toNat = ticks_o.toNat →
                  sa.core.inconsistent = 0#64 ∧
                  (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
                M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
                  q_off ht_off ht_sz occ_end.toNat scr0 sa ∧
                (FullMem c sa ⋆ R) ma)
                (fun _ ⟨⟩ ma ⟨sa, hta_lo, hta_hi, hta_eq, hok_a, hma⟩ => by
                  have ⟨hdw_a, hcv_a, hfl_a, hrepr_a, hlay_a, hpref_a, hht_a, hocc_a⟩ := hok_a
                  have hscrl_a := hdw_a.1.scratch_ok.scratch_buf_len
                  m6b_to_group
                  refine wp_join_group (ts := [i64, i64, i64, i64])
                    (fun (_i_b, ticks_b, reh_b, _g_b, ()) mb => ∃ sb : FullState,
                      reh_b.toNat ≤ 4 ∧ ticks_o.toNat ≤ ticks_b.toNat ∧
                      ticks_b.toNat ≤ tlim.toNat + 3 ∧
                      (ticks_o.toNat < ticks_b.toNat ∨
                        (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat <
                          ql.toNat) ∧
                      M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
                        inq_off q_off ht_off ht_sz occ_end.toNat scr0 sb ∧
                      (FullMem c sb ⋆ R) mb)
                    (fun _ ⟨_i_b, ticks_b, reh_b, _g_b, ⟨⟩⟩ mb
                      ⟨sb, hreh_b, htb_lo, htb_hi, hstep_b, hok_b, hmb⟩ => by
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
                        rw [m8Wl_v_eq hc5_b hmb, hp5_o]
                        have heq_b : (sb.scratch.scratch_buf[ctrl_off.toNat + 5]'hc5_b).toNat =
                            (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
                          rw [List.getElem?_eq_getElem hc5_b, Option.getD_some]
                        rw [heq_b]
                        exact m6Wl_outer_dec hto_lt htb_lo hstep_b hql_b_le
                      m6b_steps
                      rw [show ep + (1 : BitVec 32) = ep + 1#32 from rfl]
                      exact iho (_i_b, ticks_b, reh_b, _g_b, ep + 1#32, ()) mb hdec
                        ⟨sb, hreh_b, htb_hi, hok_b, hmb⟩)
                    ?_
                  intro Jreh hJreh
                  rw [heq_co6, hho32, heq_co7, hhs32]
                  exact m8Wl_rehash_wp Γ hEval hg_pos hht_pos hht_bnd hg_ht_le hht_cap hc_cap
                    htlim_le hreh_le hta_lo hta_hi hta_eq hseq0 hok_a hma hQ hJreh)
                ?_
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
                        show (1#64 : BitVec 64).toNat = 1 from rfl]
                      exact Nat.mod_eq_of_lt (by omega)
                    have hnd1_arr : (nd.setWidth 64 + 1#64).toNat <
                        sn.scratch.scratch_buf.length := by
                      rw [hnd1_n]; omega
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
                    rw [hentry_eq] at hgn_lt hgat_gn hslot_le
                    rw [hnxt_eq] at hnxt_ptr
                    let gn := (entry &&& 0x00FFFFFF#32).setWidth 64
                    have hgn_n : gn.toNat = (entry &&& 0x00FFFFFF#32).toNat := bv_zext32_toNat _
                    let slot_i := entry >>> 24
                    have htn2 : (ticks_n + 2#64).toNat = ticks_n.toNat + 2 := by
                      rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    clear hc; m6b_steps
                    rw [heq_co6, hho32, heq_co7, hhs32]
                    m6b_call hEval
                    dsimp only [m8CongEvalGateSpec]
                    rw [hho_n, hhs_n]
                    refine ⟨c, F0, F_cur, sn, scr0, g_len.toNat, R, rfl, hdw_n,
                      hcv_n ▸ hrepr_n, hht_pos, hht_bnd, hgn_n ▸ hgn_lt, hg_ht_le, hht_cap,
                      hpref_n, hcv_n ▸ hgn_n ▸ hgat_gn, hcv_n ▸ hht_n,
                      Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay_n⟩, hmn,
                      fun er sj mj hdwj hcvj hflj harj halej hreprj hprefj hhtj hqj hfrj he2_u
                        hmj => ?_⟩
                    m6b_split
                    · m6b_steps
                      exact hQ 20#64 sj mj hdwj (hcvj.trans hcv_n) (hflj.trans hfl_n)
                        ((hcvj.trans hcv_n) ▸ hreprj) (Or.inr rfl)
                        (fun _ => he2_u (bne_iff_ne.mp hc)) hmj
                    · have he2_0 : (er &&& 2#64) = 0#64 := by simpa using hc
                      have hokj := m8Wl_stOk_of_eval hok_n hc_cap he2_0 hdwj hcvj hflj hreprj
                        hprefj hhtj hqj (fun idx h1 h2 => hfrj he2_0 idx h1 h2)
                      have hlay_j := hokj.2.2.2.2.1
                      have hocc_j := hokj.2.2.2.2.2.2.2
                      clear hc; m6b_to_group
                      refine wp_join_group (ts := [])
                        (fun () m_nd => ∃ snd : FullState,
                          M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                            bkt_off inq_off q_off ht_off ht_sz occ_end.toNat scr0 snd ∧
                          (FullMem c snd ⋆ R) m_nd)
                        (fun _ ⟨⟩ m_nd ⟨snd, hok_nd, hm_nd⟩ => by
                          m6b_let
                          rw [show ticks_n + (2 : BitVec 64) = ticks_n + 2#64 from rfl]
                          exact ihn (ticks_n + 2#64, nxt, ()) m_nd
                            (by dsimp only; rw [htn2]; omega)
                            ⟨snd, by rw [htn2]; omega, by rw [htn2]; omega,
                             fun h => by rw [htn2] at h; omega, hnxt_ptr, hok_nd, hm_nd⟩)
                        (fun Jrel hJrel =>
                          have hslot_gn :
                              slot_i.toNat ≤ (scr0[gn.toNat + 1]?.getD 0#32 &&& 0xFF#32).toNat := by
                            dsimp only [gn, slot_i]; rw [bv_zext32_toNat]; exact hslot_le
                          m8Wl_relink_wp Γ hFind hg_co hht_cap hc_cap ho_pos hopow
                            hnd_lo hnd_hi hnd_ev hnd1_n (hgn_n ▸ hgn_lt) (hgn_n ▸ hgat_gn)
                            hslot_gn hokj hmj (fun m_nd h => hJrel () m_nd h))
                  · m6b_let; exact hJnd () mn
                      ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩
                · m6b_let; exact hJnd () mn
                    ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩
              · m6b_let; exact hJnd () mn
                  ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩
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
              obtain ⟨hgat_1, hseq_next⟩ := m6GateSeqOk_inv_lt hseq_1 hg_lt
              have ⟨lhs0, mw1, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, _, _, hrhs_1, _⟩ := hgat_1
              have hg_arr : g.toNat < s1.scratch.scratch_buf.length := by omega
              have hg1_n : (g + 1).toNat = g.toNat + 1 := bv64_add1_lt (by omega)
              have hg1_arr : (g + 1).toNat < s1.scratch.scratch_buf.length := by
                rw [hg1_n]; omega
              have hs1_g1 : s1.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mw1 :=
                scr_eq_of_pref hpref_1 (by omega) hg1_arr (by rw [hg1_n]; exact hscr0_g1)
              let arity := mw1 &&& 0xFF#32
              have hnext_g : (g + 2#64 + arity.setWidth 64).toNat =
                  g.toNat + 2 + arity.toNat := bv64_add_zext32 (k := 2) (by omega)
              have hseq_next' : M6GateSeqOk F_cur cv0 scr0 g_len.toNat
                  (g + 2#64 + arity.setWidth 64).toNat := by
                rw [hnext_g]; simpa [hscr0_g1, arity] using hseq_next
              have htk2 : (ticks + 2#64).toNat = ticks.toNat + 2 := by
                rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              clear hc; m6b_steps
              rw [heq_co6, hho32, heq_co7, hhs32]
              m6b_call hEval
              dsimp only [m8CongEvalGateSpec]
              rw [hho_n, hhs_n]
              refine ⟨c, F0, F_cur, s1, scr0, g_len.toNat, R, rfl, hdw_1, hcv_1 ▸ hrepr_1,
                hht_pos, hht_bnd, hg_lt, hg_ht_le, hht_cap, hpref_1, hcv_1 ▸ hgat_1,
                hcv_1 ▸ hht_1, Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay_1⟩, hm1,
                fun er sj mj hdwj hcvj hflj harj halej hreprj hprefj hhtj hqj hfrj he2_u
                  hmj => ?_⟩
              m6b_split
              · m6b_steps
                exact hQ 20#64 sj mj hdwj (hcvj.trans hcv_1) (hflj.trans hfl_1)
                  ((hcvj.trans hcv_1) ▸ hreprj) (Or.inr rfl)
                  (fun _ => he2_u (bne_iff_ne.mp hc)) hmj
              · have he2_0 : (er &&& 2#64) = 0#64 := by simpa using hc
                have hokj := m8Wl_stOk_of_eval hok_1 hc_cap he2_0 hdwj hcvj hflj hreprj hprefj hhtj
                  hqj (fun idx h1 h2 => hfrj he2_0 idx h1 h2)
                have hlay_j := hokj.2.2.2.2.1
                have hocc_j := hokj.2.2.2.2.2.2.2
                clear hc; m6b_to_group
                refine wp_join_group (ts := [i64])
                  (fun (occ_e', ()) me => ∃ se : FullState,
                    g_len.toNat ≤ occ_e'.toNat ∧ occ_e'.toNat ≤ ctrl_off.toNat ∧
                    (occ_e'.toNat - g_len.toNat) % 2 = 0 ∧
                    M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
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
                       by rw [htk2]; omega, hseq_next', hoke', hme'⟩)
                  ?_
                intro Jocc hJocc
                m6b_steps; m6b_split
                · clear hc; m6b_split
                  · have hle_raw := bv64_ule_true_le hc
                    rw [hs1_g1] at hle_raw
                    have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len
                    have hg_j_arr : g.toNat < sj.scratch.scratch_buf.length := by omega
                    have hscr_j_g : sj.scratch.scratch_buf[g.toNat]'hg_j_arr = lhs0 :=
                      scr_eq_of_pref hprefj hg_lt hg_j_arr hscr0_g
                    clear hc; m6b_steps; m6b_call hFind
                    refine ⟨F_cur, 2 * cv0, sj.core.repr, FullReprRest c sj ⋆ R,
                      (hcvj.trans hcv_1) ▸ hreprj, by rw [hscr_j_g]; exact hlhs0_lt,
                      focus_full_repr hmj,
                      fun rl repri mi hrl_i hrepr_i _ hrl_lt _ hmi => ?_⟩
                    let sj_r : FullState := { sj with core := { sj.core with repr := repri } }
                    have hscrl_jr : sj_r.scratch.scratch_buf.length = c.scratch_cap := hscrl_j
                    have hmi' : (FullMem c sj_r ⋆ R) mi := unfocus_full_repr hmi
                    clear hmi
                    have hoki := m8WlStOk_with_repr hokj
                      (hrl_i.trans hdwj.1.core_ok.repr_len) hrepr_i
                    let b0 := (rl >>> (1 : Nat)) &&& (occ_u - (1 : BitVec 32))
                    have hb0_lt : b0.toNat < occ_bkt := by
                      dsimp only [b0, occ_u]
                      rw [show (rl >>> (1 : Nat)) = rl >>> 1#32 from rfl,
                        show occ_u - (1 : BitVec 32) = BitVec.ofNat 32 occ_bkt - 1#32 from rfl,
                        m8_and_sub1_u32_eq_mod hopow]
                      exact Nat.mod_lt _ ho_pos
                    obtain ⟨hoe_fit, hb0_n, hoe1_n, hoe2_n, hg_32, hoe_32,
                      hscrl_p0, hlay_p0, hpref_p0, hht_p0, hocc_p0,
                      hb0_arr_j, hoe1_arr_j, hb0_arr_j2, hp0_eq⟩ :=
                      m8Wl_push0_step_prep hlay_j hscrl_j hprefj ((hcvj.trans hcv_1) ▸ hhtj) hocc_j
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
                      by simp only [List.length_set]; rw [hscrl_jr]; rw [hb0_n]; omega
                    have hfs_p0 := focus_full_scratch8 hmi'; clear hmi'
                    generalize hRs_p0 : FullScratchRest8 c sj_r ⋆ R = Rs_p0 at hfs_p0
                    rw [heq_co0, heq_co1, hbkt32]
                    m6b_steps
                    have hb0_val :
                        (sj_r.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32))[
                          (BitVec.ofNat 64 bkt_off + b0.setWidth 64).toNat]'hb0_arr1 =
                        sj.scratch.scratch_buf[bkt_off + b0.toNat]'(by rw [hscrl_j]; omega) := by
                      rw [List.getElem_set_ne (by change _ ≠ _; rw [hb0_n]; omega)]
                      exact list_getElem_congr hb0_n _ _
                    rw [hb0_val, show (1 : BitVec 64) = 1#64 from rfl, hb0_n, hoe1_n] at hm
                    rw [hp0_eq _] at hm
                    subst hRs_p0
                    have hm_p0' := unfocus_full_scratch88 hm
                    let scr_p0 := ((sj.scratch.scratch_buf.set occ_end.toNat (g.setWidth 32)).set
                      (occ_end.toNat + 1)
                      (sj.scratch.scratch_buf[bkt_off + b0.toNat]?.getD 0xFFFFFFFF#32)).set
                      (bkt_off + b0.toNat) (BitVec.ofNat 32 occ_end.toNat)
                    let st_p0' : FullState :=
                      { sj_r with scratch := { sj_r.scratch with scratch_buf := scr_p0 } }
                    have hok_p0' : M8WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt
                        bkt_off inq_off q_off ht_off ht_sz (occ_end.toNat + 2) scr0 st_p0' :=
                      ⟨⟨⟨hoki.1.1.core_ok,
                        { hoki.1.1.scratch_ok with scratch_buf_len := hscrl_p0 }⟩,
                        hoki.1.2.1, hoki.1.2.2.1, hoki.1.2.2.2.1,
                        fullExtScratchOk_of_eq hoki.1.2.2.2.2.1 rfl rfl rfl rfl,
                        hoki.1.2.2.2.2.2.1, hoki.1.2.2.2.2.2.2⟩,
                       hoki.2.1, hoki.2.2.1, hoki.2.2.2.1, hlay_p0, hpref_p0, hht_p0, hocc_p0⟩
                    m6b_to_group
                    have hs1_g1_any :
                        ∀ h, s1.scratch.scratch_buf[(g + (1 : BitVec 64)).toNat]'h = mw1 :=
                      fun _ => hs1_g1
                    rw [hs1_g1_any _, show (255 : BitVec 32) = 0xFF#32 from rfl,
                      show occ_end + (2 : BitVec 64) = occ_end + 2#64 from rfl]
                    exact m8Wl_pushs_wp Γ hFind hg_co hht_cap hc_cap ho_pos hopow hg_lt
                      hgat_1 hscr0_g1 hoe_fit hoe_lo hoe_ev hoe2_n hg_32
                      hok_p0' hm_p0' (fun occ_e' me h => hJocc (occ_e', ()) me h)
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
        rw [show (9223372036854775807 : BitVec 64).toNat = 2 ^ 63 - 1 from rfl] at h
        omega
      m6b_let; exact hJt (tick_lim, ()) m0 ⟨rfl, ht_le⟩


end WorklistM8

section CongDenseM8


private theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem bv64_setWidth32_eq {x : BitVec 64} {n : Nat} (hx : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  subst hx; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem m8_denseInvW_with_antsz_ressz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩, hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m8_denseInvW_with_tmk_ar {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch :=
        { s.scratch with tarjan_mark := tmk', ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with tarjan_mark_len := ht }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m8_denseInvW_with_scr_res0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hsl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := 0#64 } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hsl }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m8_denseInvW_after_iteAll {c : FullCfg} {F0 : CNF Nat}
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

private theorem m8_cd_ht_pow_step {ht_sz : BitVec 64} {k cap : Nat}
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

private theorem m8_cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * 268435456)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem m8_cd_ht_clear_inv {F_cur : List (List Nat)} {cv0 g_len ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinit : ∀ k < ht_sz, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    (∀ idx < g_len, scri[idx]? = scr0[idx]?) ∧
    M6CongHtInv F_cur cv0 scr0 scri g_len ht_off ht_sz :=
  ⟨hpref, fun k hk => Or.inl (hinit k hk)⟩

private theorem m8_cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
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



private theorem m8_cd_layout_params {ht_off ht_sz cap : Nat}
    (h256 : 256 ≤ cap) (hht_pos : 0 < ht_sz) (hht_le : ht_sz ≤ cap)
    (hmul : ht_sz = 64 ∨ ht_sz * 4 ≤ cap) (hcap : cap < 2 ^ 28) (hho : ht_off = cap - ht_sz) :
    let occ_bkt :=
      if 262144 ≤ ht_off then 8192
      else if 65536 ≤ ht_off then 2048
      else if 16384 ≤ ht_off then 512
      else if 2048 ≤ ht_off then 256
      else if 256 ≤ ht_off then 32 else 16
    let bkt_off := ht_off - occ_bkt
    let inq_off := bkt_off - occ_bkt
    let q_off := inq_off - occ_bkt
    let ctrl_off := q_off - 8
    0 < occ_bkt ∧ occ_bkt ≤ 8192 ∧
    (∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) ∧
    occ_bkt * 3 + 8 ≤ ht_off ∧
    ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
    inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
    ctrl_off < cap ∧ ctrl_off + 8 ≤ cap ∧ ht_off + ht_sz ≤ cap := by
  intro occ_bkt bkt_off inq_off q_off ctrl_off
  have hht_off_ge : 192 ≤ ht_off := by
    rcases hmul with rfl | h4 <;> omega
  have hpow : 0 < occ_bkt ∧ occ_bkt ≤ 8192 ∧
      (∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) ∧ occ_bkt * 3 + 8 ≤ ht_off := by
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
    by omega, by omega, by omega⟩


private theorem m8_cd_gcap_le {ctrl_off : Nat} (hcap : ctrl_off < 2 ^ 28) :
    ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64).toNat ≤ ctrl_off := by
  have hmul : (BitVec.ofNat 64 ctrl_off * 3#64).toNat = ctrl_off * 3 := by
    rw [BitVec.toNat_mul, bv64_ofNat_toNat_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [show ((BitVec.ofNat 64 ctrl_off * 3#64) >>> 2#64 : BitVec 64) =
      (BitVec.ofNat 64 ctrl_off * 3#64) >>> (2 : Nat) from rfl,
    BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow]
  omega

private theorem m8_cd_ctrl_off_toNat {cap : Nat} {ht_sz occ : BitVec 64}
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


private theorem m8_cd_ctrl_store_layout {c : FullCfg} {F_cur : List (List Nat)} {cv0 : Nat}
    {scr0 scri : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hg_co : g_len ≤ ctrl_off) (hg_24 : g_len ≤ 0x01000000)
    (ho_pos : 0 < occ_bkt) (ho_8192 : occ_bkt ≤ 8192)
    (hopow : ∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p)
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
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
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
  have hlay : M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz :=
    ⟨hc_cap, hc8, hg_co, hg_24, hs0, hs1, hs2, hs3, hs6, hs7,
     ho_pos, ho_8192, hopow, hht_pos, hcq, hqi, hib, hbh, hhc,
     by have := hg 4 (by decide); rw [this]; simpa using ho_pos,
     by rw [h5]; exact Nat.zero_le _,
     fun k hk => by
       rw [h5', show (0#32 : BitVec 32).toNat = 0 from rfl] at hk
       omega⟩
  exact ⟨hsl, hlay, hpref', hht'⟩


theorem m8_congruence_dense_wp (Γ : Env)
    (hExtBin : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m6CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hIteAll : ∀ a m Q X, FullM7CongIte.m7ExtractIteAllM6Spec a m Q X →
      Γ "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X)
    (hWork : ∀ a m Q X, m8CongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ m8_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, hm0, hQ⟩
  have hsc : c.scratch_cap < 2 ^ 28 := Nat.lt_of_lt_of_le c.hscr (by decide)
  have hmx : c.max_vars < 2 * 268435456 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
  obtain ⟨hlen0, ⟨F_cur, hw0⟩⟩ := hden0.1
  have hdw0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hlen0, hw0, hden0.2.1, hden0.2.2.1, hden0.2.2.2.1, hden0.2.2.2.2.1, hden0.2.2.2.2.2⟩
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have hcv_le : cv0 ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  unfold Func.wp m8_congruence_dense_body
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
        m8_denseInvW_with_antsz_ressz hdw0 0#64 s0.scratch.res_sz
      m6b_call hExtBin
      refine ⟨c, F0, F_cur, s0a, R, rfl, hdw0a, hm,
        fun r1 s1 m1 hdw1 hcv1 hfl1 _hr1_dom hr1_uns hm1 => ?_⟩
      have hcv10 : s1.core.cur_vars = cv0 := hcv1
      m6b_split
      · m6b_steps
        exact hQ 20#64 _ m (m8_denseInvW_with_antsz_ressz hdw1 0#64 s1.scratch.res_sz).toDense
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
            exact m8_cd_repr_init_inv hrl hcv_le hmx hinit
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
              exact hQ 20#64 _ m (m8_denseInvW_with_tmk_ar hdw3 htlt 0#64 0#64).toDense
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
                    obtain ⟨hk1, hpow1, h128k1, hsc1⟩ := m8_cd_ht_pow_step hk_le hpow hlt hmul_le
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
                occ_bkt_bv.toNat =
                  (if 262144 ≤ ht_off.toNat then 8192
                   else if 65536 ≤ ht_off.toNat then 2048
                   else if 16384 ≤ ht_off.toNat then 512
                   else if 2048 ≤ ht_off.toNat then 256
                   else if 256 ≤ ht_off.toNat then 32 else 16))
              ?_
              (fun Jocc hJocc => by
                m6b_split
                · have h262k : 262144 ≤ ht_off.toNat := by
                    have h := bv64_ule_true_le hc
                    rw [show (262144 : BitVec 64).toNat = 262144 from rfl] at h
                    exact h
                  m6b_let; exact hJocc (8192#64, ()) me ⟨hme, by simp [h262k]⟩
                · have hlt262k : ¬ 262144 ≤ ht_off.toNat := by
                    have h := bv64_ule_false_lt hc
                    rw [show (262144 : BitVec 64).toNat = 262144 from rfl] at h
                    dsimp only [ht_off]; omega
                  clear hc; m6b_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (o1, ()) mo1 => mo1 = m3 ∧
                      o1.toNat =
                        (if 65536 ≤ ht_off.toNat then 2048
                         else if 16384 ≤ ht_off.toNat then 512
                         else if 2048 ≤ ht_off.toNat then 256
                         else if 256 ≤ ht_off.toNat then 32 else 16))
                    (fun _ ⟨o1, ⟨⟩⟩ mo1 ⟨hmo1, ho1⟩ =>
                      hJocc (o1, ()) mo1 ⟨hmo1, by simp [hlt262k, ho1]⟩)
                    (fun Jocc1 hJocc1 => by
                      m6b_split
                      · have h65k : 65536 ≤ ht_off.toNat := by
                          have h := bv64_ule_true_le hc
                          rw [show (65536 : BitVec 64).toNat = 65536 from rfl] at h
                          exact h
                        m6b_let; exact hJocc1 (2048#64, ()) me ⟨hme, by simp [h65k]⟩
                      · have hlt65k : ¬ 65536 ≤ ht_off.toNat := by
                          have h := bv64_ule_false_lt hc
                          rw [show (65536 : BitVec 64).toNat = 65536 from rfl] at h
                          dsimp only [ht_off]; omega
                        clear hc; m6b_to_group
                        refine wp_join_group (ts := [i64])
                          (fun (o2, ()) mo2 => mo2 = m3 ∧
                            o2.toNat =
                              (if 16384 ≤ ht_off.toNat then 512
                               else if 2048 ≤ ht_off.toNat then 256
                               else if 256 ≤ ht_off.toNat then 32 else 16))
                          (fun _ ⟨o2, ⟨⟩⟩ mo2 ⟨hmo2, ho2⟩ =>
                            hJocc1 (o2, ()) mo2 ⟨hmo2, by simp [hlt65k, ho2]⟩)
                          (fun Jocc2 hJocc2 => by
                            m6b_split
                            · have h16k : 16384 ≤ ht_off.toNat := by
                                have h := bv64_ule_true_le hc
                                rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                                exact h
                              m6b_let; exact hJocc2 (512#64, ()) me ⟨hme, by simp [h16k]⟩
                            · have hlt16k : ¬ 16384 ≤ ht_off.toNat := by
                                have h := bv64_ule_false_lt hc
                                rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                                dsimp only [ht_off]; omega
                              clear hc; m6b_to_group
                              refine wp_join_group (ts := [i64])
                                (fun (o3, ()) mo3 => mo3 = m3 ∧
                                  o3.toNat =
                                    (if 2048 ≤ ht_off.toNat then 256
                                     else if 256 ≤ ht_off.toNat then 32 else 16))
                                (fun _ ⟨o3, ⟨⟩⟩ mo3 ⟨hmo3, ho3⟩ =>
                                  hJocc2 (o3, ()) mo3 ⟨hmo3, by simp [hlt16k, ho3]⟩)
                                (fun Jocc3 hJocc3 => by
                                  m6b_split
                                  · have h2k : 2048 ≤ ht_off.toNat := by
                                      have h := bv64_ule_true_le hc
                                      rw [show (2048 : BitVec 64).toNat = 2048 from rfl] at h
                                      exact h
                                    m6b_let; exact hJocc3 (256#64, ()) me ⟨hme, by simp [h2k]⟩
                                  · have hlt2k : ¬ 2048 ≤ ht_off.toNat := by
                                      have h := bv64_ule_false_lt hc
                                      rw [show (2048 : BitVec 64).toNat = 2048 from rfl] at h
                                      dsimp only [ht_off]; omega
                                    clear hc; m6b_to_group
                                    refine wp_join_group (ts := [i64])
                                      (fun (o4, ()) mo4 => mo4 = m3 ∧
                                        o4.toNat = (if 256 ≤ ht_off.toNat then 32 else 16))
                                      (fun _ ⟨o4, ⟨⟩⟩ mo4 ⟨hmo4, ho4⟩ =>
                                        hJocc3 (o4, ()) mo4 ⟨hmo4, by simp [hlt2k, ho4]⟩)
                                      (fun Jocc4 hJocc4 => by
                                        m6b_split
                                        · have h256o : 256 ≤ ht_off.toNat := by
                                            have h := bv64_ule_true_le hc
                                            rw [show (256 : BitVec 64).toNat = 256 from rfl] at h
                                            exact h
                                          m6b_let; exact hJocc4 (32#64, ()) me ⟨hme, by simp [h256o]⟩
                                        · have hlt256o : ¬ 256 ≤ ht_off.toNat := by
                                            have h := bv64_ule_false_lt hc
                                            rw [show (256 : BitVec 64).toNat = 256 from rfl] at h
                                            dsimp only [ht_off]; omega
                                          m6b_let; exact hJocc4 (16#64, ()) me ⟨hme, by simp [hlt256o]⟩)))))
            rintro _ ⟨occ_bkt_bv, ⟨⟩⟩ mo ⟨hmo, hocc_eq⟩
            let occ_bkt := occ_bkt_bv.toNat
            have hmul4' : ht_sz.toNat = 64 ∨ ht_sz.toNat * 4 ≤ c.scratch_cap :=
              hmul4.elim (fun h => Or.inl (by subst h; rfl)) Or.inr
            have ⟨ho_pos, ho_8192, hopow, hocc38, hcq, hqi, hib, hbh, hc_cap, hc8, hhc⟩ :=
              m8_cd_layout_params h256 hht_pos hsc_le hmul4' hsc hht_off_n
            rw [← hocc_eq] at ho_pos ho_8192 hopow hocc38 hcq hqi hib hbh hc_cap hc8
            let bkt_off := ht_off.toNat - occ_bkt
            let inq_off := bkt_off - occ_bkt
            let q_off := inq_off - occ_bkt
            let ctrl_off := q_off - 8
            have hco_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz - occ_bkt_bv -
                occ_bkt_bv - occ_bkt_bv - 8#64).toNat = ctrl_off := by
              dsimp only [ctrl_off, q_off, inq_off, bkt_off]
              rw [hht_off_n]
              exact m8_cd_ctrl_off_toNat hsc_le (hht_off_n ▸ hocc38) hsc
            have hco_le_fn := m8_cd_gcap_le (by omega : ctrl_off < 2 ^ 28)
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
                        exact hQ 20#64 _ m (m8_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64).toDense
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
                        have hdwf := m8_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64
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
                        m8_cd_ht_set_step (by omega) hpref_i hinit_i (by omega)
                      exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                        ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i],
                         by rw [hi3_1]; omega, hpref_i', hi3_1 ▸ hinit_i', hm⟩
                    · have hi3_eq : i3.toNat = ht_sz.toNat := by
                        have := bv64_ult_not_lt hc; omega
                      rw [hi3_eq] at hinit_i
                      obtain ⟨hpref4, hht4⟩ :=
                        m8_cd_ht_clear_inv (F_cur := F_cur) (cv0 := cv0) hpref_i hinit_i
                      have hctrl_st := m8_cd_ctrl_store_layout hg_le_co (by omega) ho_pos
                        ho_8192 hopow hht_pos (by omega) hc_cap hc8 hcq hqi hib hbh hhc
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
                        m8_denseInvW_with_scr_res0 hdw4 hctrl_st.1,
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
                            (m8_denseInvW_with_tmk_ar hdw4w htlt 0#64 0#64).toDense
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
              have hdw4b := m8_denseInvW_after_iteAll hdw4a hlen4b hcore4b hll4b hel4b
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


end CongDenseM8

end LeanQbe.T.Examples.Kissat.FullM8FidV12

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Worklist Helpers & Invariants (`WpWorklist0`)

3-word occurrence node invariants, control-block layout preservation, measure-decrease, and
phase/push/pop/rehash preservation lemmas shared with
`LeanQbe.T.Examples.Kissat.Proof.Congruence.WpWorklist1`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

public section

/-! ## 1. 3-Word Occurrence Node Invariants & Helpers -/

@[expose] def WlNodePtrOk (g_len occ_end : Nat) (p : BitVec 32) : Prop :=
  p = 0xFFFFFFFF#32 ∨ (g_len ≤ p.toNat ∧ p.toNat + 2 < occ_end ∧ (p.toNat - g_len) % 3 = 0)

@[expose] def CongOccNodesOk (F_cur : List (List Nat)) (cv g_len occ_end ctrl_off
    bkt_off occ_bkt : Nat) (scr0 scr : List (BitVec 32)) : Prop :=
  g_len ≤ occ_end ∧ occ_end ≤ ctrl_off ∧ (occ_end - g_len) % 3 = 0 ∧
  (∀ b < occ_bkt, WlNodePtrOk g_len occ_end (scr[bkt_off + b]?.getD 0xFFFFFFFF#32)) ∧
  ∀ nd, g_len ≤ nd → nd + 2 < occ_end → (nd - g_len) % 3 = 0 →
    let gn := scr[nd]?.getD 0#32; let raw_lit := scr[nd + 1]?.getD 0#32
    let nxt := scr[nd + 2]?.getD 0xFFFFFFFF#32
    gn.toNat < g_len ∧ CongGateAt congAndArityMax F_cur cv scr0 g_len gn.toNat ∧
    raw_lit.toNat < 2 * cv ∧ WlNodePtrOk g_len occ_end nxt

@[expose] def WlStOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat) (scr0 : List (BitVec 32)) (st : FullState) : Prop :=
  FullDenseInvW c F0 F_cur st ∧ st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  CongCtrlLayout c st.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off q_off
    ht_off ht_sz ∧
  (∀ idx < g_len, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  CongHtInv congAndArityMax F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz ∧
  CongOccNodesOk F_cur cv0 g_len occ_end ctrl_off bkt_off occ_bkt scr0 st.scratch.scratch_buf

theorem wlStOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat} {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 st) {r : List (BitVec 32)} (hr : r.length = 2 * c.max_vars)
    (hrepr : FullCongReprInv F_cur (2 * cv0) r) :
    WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 { st with core := { st.core with repr := r } } :=
  ⟨fullDenseInvW_with_repr hok.1 hr, hok.2.1, hok.2.2.1, hrepr, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2⟩

theorem wlStOk_with_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ht_sz'
      occ_end occ_end' : Nat} {scr0 scr' : List (BitVec 32)} {st : FullState}
    (hok : WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 st) (hl : scr'.length = c.scratch_cap)
    (hlay' : CongCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz')
    (hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]?)
    (hht' : CongHtInv congAndArityMax F_cur cv0 scr0 scr' g_len ht_off ht_sz')
    (hocc' : CongOccNodesOk F_cur cv0 g_len occ_end' ctrl_off bkt_off occ_bkt scr0 scr')
    (rs' : BitVec 64 := st.scratch.res_sz) :
    WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz' occ_end'
      scr0 { st with scratch := { st.scratch with scratch_buf := scr', res_sz := rs' } } :=
  ⟨fullDenseInvW_with_scr (fullDenseInvW_with_rsz hok.1 rs') hl,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hlay', hpref', hht', hocc'⟩

theorem wl_ctrl_same_of_agree {c : FullCfg} {g_len co occ_bkt bkt_off inq_off q_off
    ht_off ht_sz : Nat} {scr scr' : List (BitVec 32)}
    (hlay : CongCtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen : scr'.length = scr.length)
    (hag : ∀ idx, (co ≤ idx ∧ idx < q_off + occ_bkt) → scr'[idx]? = scr[idx]?) :
    CongCtrlLayout c scr' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, ho_pos, _, _, _, hcq, hqi, _, _, _, _, hql, hqok⟩
  refine congCtrlLayout_same_tail hlay' hlen (by rw [hag (co + 5) ⟨by omega, by omega⟩]; exact hql)
    (fun j hj _ => hag (co + j) ⟨by omega, by omega⟩) (fun k hk => by
      rw [hag (co + 5) ⟨by omega, by omega⟩] at hk; rw [hag (co + 4) ⟨by omega, by omega⟩]
      have hslot := Nat.mod_lt ((scr[co + 4]?.getD 0#32).toNat + k) ho_pos
      rw [hag (q_off + ((scr[co + 4]?.getD 0#32).toNat + k) % occ_bkt) ⟨by omega, by omega⟩]
      exact hqok k hk)

theorem congOccNodesOk_of_ev_frame {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len occ_end ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scr scr' : List (BitVec 32)}
    (hocc : CongOccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr)
    (hlay : CongCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hfr : ∀ idx < c.scratch_cap, idx < ht_off →
      (ctrl_off = c.scratch_cap → scr'[idx]? = scr[idx]?) ∧
      (∀ o b i q, CongCtrlLayout c scr g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        scr'[idx]? = scr[idx]?)) :
    CongOccNodesOk F_cur cv g_len occ_end ctrl_off bkt_off occ_bkt scr0 scr' := by
  have hlay' := hlay; have h_occ1 := hocc.1; have h_occ2 := hocc.2.1
  rcases hlay with ⟨_, _, hgc, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hkeep : ∀ idx, (g_len ≤ idx ∧ idx < occ_end) ∨ (bkt_off ≤ idx ∧ idx < bkt_off + occ_bkt) →
      scr'[idx]? = scr[idx]? := fun idx hi => by
    have ha : idx < c.scratch_cap ∧ idx < ht_off ∧ idx ≠ ctrl_off + 5 ∧
        ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) ∧ ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) := by
      rcases hi with ⟨_, _⟩ | ⟨_, _⟩ <;> refine ⟨by omega, by omega, by omega, by omega, by omega⟩
    exact (hfr idx ha.1 ha.2.1).2 occ_bkt bkt_off inq_off q_off hlay' ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2
  refine ⟨hocc.1, hocc.2.1, hocc.2.2.1, fun b hb => ?_, fun nd hn1 hn2 hm3 => ?_⟩
  · rw [hkeep (bkt_off + b) (Or.inr ⟨by omega, by omega⟩)]; exact hocc.2.2.2.1 b hb
  · rw [hkeep nd (Or.inl ⟨hn1, by omega⟩), hkeep (nd + 1) (Or.inl ⟨by omega, by omega⟩),
      hkeep (nd + 2) (Or.inl ⟨by omega, by omega⟩)]; exact hocc.2.2.2.2 nd hn1 hn2 hm3

theorem wlStOk_of_eval {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end : Nat} {scr0 : List (BitVec 32)} {s s' : FullState}
    (hok : WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 s) (hc_cap : ctrl_off < c.scratch_cap)
    (hdw' : FullDenseInvW c F0 F_cur s') (hcv' : s'.core.cur_vars = s.core.cur_vars)
    (hfl' : s'.core.fuel = s.core.fuel)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr)
    (hpref' : ∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?)
    (hht' : CongHtInv congAndArityMax F_cur s'.core.cur_vars scr0
      s'.scratch.scratch_buf g_len ht_off ht_sz)
    (hq' : CongQueueCtx c s'.scratch.scratch_buf g_len ctrl_off ht_off ht_sz)
    (hfr' : ∀ idx < c.scratch_cap, idx < ht_off →
      (ctrl_off = c.scratch_cap → s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
      (∀ o b i q, CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)) :
    WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz
      occ_end scr0 s' := by
  have ⟨_, hcvs, hfls, _, hlays, _, _, hoccs⟩ := hok
  have hlay' : CongCtrlLayout c s'.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off
      inq_off q_off ht_off ht_sz := by
    rcases hq' with hcap | ⟨o', b', i', q', hlo⟩
    · exact absurd hcap (Nat.ne_of_lt hc_cap)
    · have hkeep : ∀ j < 4,
          s'.scratch.scratch_buf[ctrl_off + j]? = s.scratch.scratch_buf[ctrl_off + j]? :=
        fun j hj => (hfr' (ctrl_off + j) (by have := hlays.2.1; omega)
          (by rcases hlays with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4, _⟩
              omega)).2 occ_bkt bkt_off inq_off q_off hlays (by omega)
          (by have := hlays.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)
          (by rcases hlays with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, _⟩; omega)
      have heq : ∀ a b : Nat, a < 2 ^ 32 → b < 2 ^ 32 →
          BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun a b ha hb h => by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using
          congrArg BitVec.toNat h
      have hsc := c.hscr; unfold dimacsBound at hsc
      have h0e := hkeep 0 (by omega); simp only [Nat.add_zero] at h0e
      rcases hlo with ⟨hc1, hc8, hgc, hgm, hlo0, hlo1, hlo2, hlo3, hlo_rest⟩
      rcases hlays with ⟨_, _, _, _, hls0, hls1, hls2, hls3, _, _, _, hls_max, _, _, _, hlsqi,
        hlsib, hlsbh, hlsht⟩
      unfold congOccBktMax at hlo_rest hls_max
      have h0 : o' = occ_bkt := heq _ _ (by omega) (by omega) (by rw [← hlo0, h0e, hls0])
      have h1 : b' = bkt_off :=
        heq _ _ (by omega) (by omega) (by rw [← hlo1, hkeep 1 (by omega), hls1])
      have h2 : i' = inq_off :=
        heq _ _ (by omega) (by omega) (by rw [← hlo2, hkeep 2 (by omega), hls2])
      have h3 : q' = q_off :=
        heq _ _ (by omega) (by omega) (by rw [← hlo3, hkeep 3 (by omega), hls3])
      subst h0 h1 h2 h3; exact ⟨hc1, hc8, hgc, hgm, hlo0, hlo1, hlo2, hlo3, hlo_rest⟩
  exact ⟨hdw', hcv'.trans hcvs, hfl'.trans hfls, (hcv'.trans hcvs) ▸ hrepr', hlay', hpref',
    (hcv'.trans hcvs) ▸ hht', congOccNodesOk_of_ev_frame hoccs hlays hfr'⟩

theorem wl_ctrl_arith {c : FullCfg} {scr : List (BitVec 32)} {g_len : Nat}
    {ctrl_off : BitVec 64} {occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hht_bnd : ht_sz < 2 ^ 30) (hscrl : scr.length = c.scratch_cap)
    (hlay : CongCtrlLayout c scr g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    (ctrl_off + 1#64).toNat = ctrl_off.toNat + 1 ∧ (ctrl_off + 2#64).toNat = ctrl_off.toNat + 2 ∧
    (ctrl_off + 3#64).toNat = ctrl_off.toNat + 3 ∧ (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4 ∧
    (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5 ∧ (ctrl_off + 6#64).toNat = ctrl_off.toNat + 6 ∧
    (ctrl_off + 7#64).toNat = ctrl_off.toNat + 7 ∧
    scr[ctrl_off.toNat]?.getD 0#32 = BitVec.ofNat 32 occ_bkt ∧
    scr[(ctrl_off + 1#64).toNat]?.getD 0#32 = BitVec.ofNat 32 bkt_off ∧
    scr[(ctrl_off + 2#64).toNat]?.getD 0#32 = BitVec.ofNat 32 inq_off ∧
    scr[(ctrl_off + 3#64).toNat]?.getD 0#32 = BitVec.ofNat 32 q_off ∧
    scr[(ctrl_off + 6#64).toNat]?.getD 0#32 = BitVec.ofNat 32 ht_off ∧
    scr[(ctrl_off + 7#64).toNat]?.getD 0#32 = BitVec.ofNat 32 ht_sz ∧
    (BitVec.ofNat 32 bkt_off).setWidth 64 = BitVec.ofNat 64 bkt_off ∧
    (BitVec.ofNat 32 inq_off).setWidth 64 = BitVec.ofNat 64 inq_off ∧
    (BitVec.ofNat 32 q_off).setWidth 64 = BitVec.ofNat 64 q_off ∧
    (BitVec.ofNat 32 ht_off).setWidth 64 = BitVec.ofNat 64 ht_off ∧
    (BitVec.ofNat 32 ht_sz).setWidth 64 = BitVec.ofNat 64 ht_sz ∧
    (BitVec.ofNat 64 ht_off).toNat = ht_off ∧ (BitVec.ofNat 64 ht_sz).toNat = ht_sz ∧
    (BitVec.ofNat 64 bkt_off).toNat = bkt_off ∧ (BitVec.ofNat 64 inq_off).toNat = inq_off ∧
    (BitVec.ofNat 64 q_off).toNat = q_off := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  rcases hlay with ⟨hc_cap, hc_8, _, _, hs0, hs1, hs2, hs3, hs6, hs7,
    _, ho_max, _, _, hcq, hqi, hib, hbh, hht_cap, _⟩
  unfold congOccBktMax at ho_max
  have h1 : (ctrl_off + 1#64).toNat = ctrl_off.toNat + 1 := by bv_omega
  have h2 : (ctrl_off + 2#64).toNat = ctrl_off.toNat + 2 := by bv_omega
  have h3 : (ctrl_off + 3#64).toNat = ctrl_off.toNat + 3 := by bv_omega
  have h4 : (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4 := by bv_omega
  have h5 : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5 := by bv_omega
  have h6 : (ctrl_off + 6#64).toNat = ctrl_off.toNat + 6 := by bv_omega
  have h7 : (ctrl_off + 7#64).toNat = ctrl_off.toNat + 7 := by bv_omega
  refine ⟨h1, h2, h3, h4, h5, h6, h7, hs0, h1 ▸ hs1, h2 ▸ hs2, h3 ▸ hs3, h6 ▸ hs6, h7 ▸ hs7,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem wl_phase0_clear_step {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} {i : BitVec 64}
    (hlay : CongCtrlLayout c scri g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scri.length = c.scratch_cap) (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : CongHtInv congAndArityMax F_cur cv scr0 scri g_len ht_off ht_sz)
    (hbkt : ∀ b < i.toNat, scri[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_lt : i.toNat < occ_bkt) :
    let scri' := (scri.set (bkt_off + i.toNat) 0xFFFFFFFF#32).set (inq_off + i.toNat) 0#32
    (BitVec.ofNat 64 bkt_off + i).toNat = bkt_off + i.toNat ∧
    (BitVec.ofNat 64 inq_off + i).toNat = inq_off + i.toNat ∧
    (i + 1#64).toNat = i.toNat + 1 ∧ scri'.length = c.scratch_cap ∧
    CongCtrlLayout c scri' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scri'[idx]? = scr0[idx]?) ∧
    CongHtInv congAndArityMax F_cur cv scr0 scri' g_len ht_off ht_sz ∧
    (∀ b < i.toNat + 1, scri'[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
  intro scri'; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, ho_max, _, _, hcq, hqi, hib, hbh, hht_cap, _⟩
  unfold congOccBktMax at ho_max
  have hlen' : scri'.length = c.scratch_cap := by simp [scri', hscrl]
  have hno : ∀ idx, (co ≤ idx ∧ idx < q_off + occ_bkt) ∨ idx < g_len ∨ ht_off ≤ idx →
      scri'[idx]? = scri[idx]? := fun idx hidx => by dsimp only [scri']; rw [
    List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega),
    List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega)]
  refine ⟨by bv_omega, by bv_omega, by bv_omega, hlen',
    wl_ctrl_same_of_agree hlay' (by rw [hlen', hscrl]) fun idx h => hno idx (Or.inl h),
    fun idx hidx => by rw [hno idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx,
    fun k hk => by
      rw [hno (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk,
    fun b hb => ?_⟩
  by_cases hbi : b = i.toNat
  · subst hbi; dsimp only [scri']; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
  · dsimp only [scri']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hbkt b (by omega)

theorem wl_phase0_finalize {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat} {scr0 scri : List (BitVec 32)}
    (hlay : CongCtrlLayout c scri g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scri.length = c.scratch_cap) (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : CongHtInv congAndArityMax F_cur cv scr0 scri g_len ht_off ht_sz)
    (hbkt : ∀ b < occ_bkt, scri[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    let scr_f := (scri.set (co + 4) 0#32).set (co + 5) 0#32
    scr_f.length = c.scratch_cap ∧
    CongCtrlLayout c scr_f g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr_f[idx]? = scr0[idx]?) ∧
    CongHtInv congAndArityMax F_cur cv scr0 scr_f g_len ht_off ht_sz ∧
    CongOccNodesOk F_cur cv g_len g_len co bkt_off occ_bkt scr0 scr_f := by
  intro scr_f; have hlay' := hlay
  rcases hlay with ⟨hc1, hc8, hgc, _, _, _, _, _, _, _, ho_pos, _, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hq4 : scr_f[co + 4]?.getD 0#32 = 0#32 := by dsimp only [scr_f]; rw [
    List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega),
    Option.getD_some]
  have hq5 : scr_f[co + 5]?.getD 0#32 = 0#32 := by
    dsimp only [scr_f]; rw [List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
  have hno : ∀ idx, idx < co ∨ co + 8 ≤ idx → scr_f[idx]? = scri[idx]? := fun idx h => by
    dsimp only [scr_f]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨by simp [scr_f, hscrl], congCtrlLayout_set_q hlay' (by simp [scr_f])
      (fun i _ h4 h5 => by
        dsimp only [scr_f]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
      (by rw [hq4]; exact ho_pos) (by rw [hq5]; exact Nat.zero_le _)
      (fun k hk => by rw [hq5] at hk; cases hk),
    fun idx hidx => by rw [hno idx (Or.inl (by omega))]; exact hpref idx hidx,
    fun k hk => by rw [hno (ht_off + k) (Or.inr (by omega))]; exact hht k hk,
    ⟨Nat.le_refl _, hgc, by simp, fun b hb =>
      Or.inl (by rw [hno (bkt_off + b) (Or.inr (by omega))]; exact hbkt b hb), fun _ => by omega⟩⟩

theorem wl_push3_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end b : Nat}
    {scr0 scr : List (BitVec 32)} {gn raw_lit : BitVec 32}
    (hlay : CongCtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap) (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : CongHtInv congAndArityMax F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr)
    (hocc3 : occ_end + 3 ≤ co) (hb : b < occ_bkt) (hgn : gn.toNat < g_len)
    (hgat : CongGateAt congAndArityMax F_cur cv scr0 g_len gn.toNat)
    (hlit : raw_lit.toNat < 2 * cv) :
    let head := scr[bkt_off + b]?.getD 0xFFFFFFFF#32
    let scr' := (((scr.set occ_end gn).set (occ_end + 1) raw_lit).set
      (occ_end + 2) head).set (bkt_off + b) (BitVec.ofNat 32 occ_end)
    scr'.length = c.scratch_cap ∧
    CongCtrlLayout c scr' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    CongHtInv congAndArityMax F_cur cv scr0 scr' g_len ht_off ht_sz ∧
    CongOccNodesOk F_cur cv g_len (occ_end + 3) co bkt_off occ_bkt scr0 scr' := by
  intro head scr'; have hlay' := hlay; have hsc := c.hscr; unfold dimacsBound at hsc
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hge := hocc.1; have hev := hocc.2.2.1
  have hlen' : scr'.length = c.scratch_cap := by simp [scr', hscrl]
  have hno : ∀ idx, (co ≤ idx ∧ idx < inq_off) ∨ idx < g_len ∨ ht_off ≤ idx →
      scr'[idx]? = scr[idx]? := fun idx hidx => by dsimp only [scr']; rw [
    List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega),
    List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega),
    List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega),
    List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega)]
  have hptr_w : ∀ {p : BitVec 32},
      WlNodePtrOk g_len occ_end p → WlNodePtrOk g_len (occ_end + 3) p := fun hp => by
    rcases hp with rfl | ⟨h1, h2, h3⟩; exact Or.inl rfl; exact Or.inr ⟨h1, by omega, h3⟩
  have hkeep : ∀ idx, g_len ≤ idx → idx < occ_end → scr'[idx]? = scr[idx]? := fun idx h1 h2 => by
    dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hlen', wl_ctrl_same_of_agree hlay' (by rw [hlen', hscrl])
      fun idx h => hno idx (Or.inl ⟨h.1, by omega⟩),
    fun idx hidx => by rw [hno idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx,
    fun k hk => by rw [hno (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk,
    ⟨by omega, by omega, by omega, fun b' hb' => ?_, fun nd hn1 hn2 hm3 => ?_⟩⟩
  · by_cases hbb : b' = b
    · subst hbb; dsimp only [scr']
      have hoe_32 : (BitVec.ofNat 32 occ_end).toNat = occ_end := by bv_omega
      rw [List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
      exact Or.inr ⟨by rw [hoe_32]; exact hge, by rw [hoe_32]; omega, by rw [hoe_32]; exact hev⟩
    · dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hptr_w (hocc.2.2.2.1 b' hb')
  · by_cases hnd : nd = occ_end
    · subst nd
      have hg0 : scr'[occ_end]? = some gn := by dsimp only [scr']; rw [
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega)]
      have hg1 : scr'[occ_end + 1]? = some raw_lit := by dsimp only [scr']; rw [
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hscrl]; omega)]
      have hg2 : scr'[occ_end + 2]? = some head := by dsimp only [scr']; rw [
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega)]
      rw [hg0, hg1, hg2, Option.getD_some, Option.getD_some, Option.getD_some]
      exact ⟨hgn, hgat, hlit, hptr_w (hocc.2.2.2.1 b hb)⟩
    · have hnd_lt : nd + 2 < occ_end := by omega
      rw [hkeep nd hn1 (by omega), hkeep (nd + 1) (by omega) (by omega),
        hkeep (nd + 2) (by omega) hnd_lt]
      obtain ⟨g1, g2, g3, g4⟩ := hocc.2.2.2.2 nd hn1 hnd_lt hm3; exact ⟨g1, g2, g3, hptr_w g4⟩

theorem wl_relink_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end nd b_dst : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : CongCtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap) (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : CongHtInv congAndArityMax F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr)
    (hge : g_len ≤ nd) (hnd2 : nd + 2 < occ_end) (hm3 : (nd - g_len) % 3 = 0)
    (hb : b_dst < occ_bkt) :
    let scr' := (scr.set (nd + 2) (scr[bkt_off + b_dst]?.getD 0xFFFFFFFF#32)).set
      (bkt_off + b_dst) (BitVec.ofNat 32 nd)
    scr'.length = c.scratch_cap ∧
    CongCtrlLayout c scr' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    CongHtInv congAndArityMax F_cur cv scr0 scr' g_len ht_off ht_sz ∧
    CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr' := by
  intro scr'; have hlay' := hlay; have hsc := c.hscr; unfold dimacsBound at hsc
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hocc_c := hocc.2.1; have hlen' : scr'.length = c.scratch_cap := by simp [scr', hscrl]
  have hno : ∀ idx, (co ≤ idx ∧ idx < inq_off) ∨ idx < g_len ∨ ht_off ≤ idx →
      scr'[idx]? = scr[idx]? := fun idx hidx => by
    dsimp only [scr']; rw [List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega),
      List.getElem?_set_ne (by rcases hidx with ⟨_, _⟩ | _ | _ <;> omega)]
  refine ⟨hlen', wl_ctrl_same_of_agree hlay' (by rw [hlen', hscrl])
      fun idx h => hno idx (Or.inl ⟨h.1, by omega⟩),
    fun idx hidx => by rw [hno idx (Or.inr (Or.inl hidx))]; exact hpref idx hidx,
    fun k hk => by rw [hno (ht_off + k) (Or.inr (Or.inr (by omega)))]; exact hht k hk,
    ⟨hocc.1, hocc.2.1, hocc.2.2.1, fun b' hb' => ?_, fun nd' hn1 hn2 hm3' => ?_⟩⟩
  · by_cases hbb : b' = b_dst
    · subst hbb; dsimp only [scr']
      have hnd_32 : (BitVec.ofNat 32 nd).toNat = nd := by bv_omega
      rw [List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
      exact Or.inr ⟨by rw [hnd_32]; exact hge,
        by rw [hnd_32]; exact hnd2, by rw [hnd_32]; exact hm3⟩
    · dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hocc.2.2.2.1 b' hb'
  · have e0 : scr'[nd']? = scr[nd']? := by
      dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    have e1 : scr'[nd' + 1]? = scr[nd' + 1]? := by
      dsimp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    have e2 : scr'[nd' + 2]? = if nd' = nd then
        some (scr[bkt_off + b_dst]?.getD 0xFFFFFFFF#32) else scr[nd' + 2]? := by
      dsimp only [scr']; split
      · rename_i heq; subst heq
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega)]
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    obtain ⟨g1, g2, g3, g4⟩ := hocc.2.2.2.2 nd' hn1 hn2 hm3'
    rw [e0, e1]; refine ⟨g1, g2, g3, ?_⟩; rw [e2]; split
    · rw [Option.getD_some]; exact hocc.2.2.2.1 b_dst hb
    · exact g4

theorem wl_pop_pres {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scr : List (BitVec 32)}
    (hlay : CongCtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scr.length = c.scratch_cap) (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hht : CongHtInv congAndArityMax F_cur cv scr0 scr g_len ht_off ht_sz)
    (hocc : CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr)
    (hpos : 0 < (scr[co + 5]?.getD 0#32).toNat) :
    let qh := scr[co + 4]?.getD 0#32; let ql := scr[co + 5]?.getD 0#32
    let b := scr[q_off + qh.toNat]?.getD 0#32
    let nqh := (qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
    let scr1 := (((scr.set (co + 4) nqh).set (co + 5) (ql - 1#32)).set
      (inq_off + b.toNat) 0#32).set (bkt_off + b.toNat) 0xFFFFFFFF#32
    b.toNat < occ_bkt ∧ nqh.toNat < occ_bkt ∧ scr1.length = c.scratch_cap ∧
    CongCtrlLayout c scr1 g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr1[idx]? = scr0[idx]?) ∧
    CongHtInv congAndArityMax F_cur cv scr0 scr1 g_len ht_off ht_sz ∧
    WlNodePtrOk g_len occ_end (scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32) ∧
    CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scr1 ∧
    (scr1[co + 5]?.getD 0#32).toNat < ql.toNat := by
  intro qh ql b nqh scr1
  have ⟨hb_lt, hnqh_lt, hlay_pop⟩ := congCtrlLayout_pop_q hlay hscrl hpos
  change b.toNat < occ_bkt at hb_lt
  let scr_pop := ((scr.set (co + 4) nqh).set (co + 5) (ql - 1#32)).set (inq_off + b.toNat) 0#32
  have hscrl_pop : scr_pop.length = c.scratch_cap := by simp [scr_pop, hscrl]
  have hlay_pop' := hlay_pop
  rcases hlay_pop with ⟨hc1, hc8, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hhc, _⟩
  have hlen1 : scr1.length = c.scratch_cap := by simp [scr1, hscrl]
  have hdisj : ∀ idx, idx < co ∨ ht_off ≤ idx → scr1[idx]? = scr[idx]? := fun idx hidx => by
    dsimp only [scr1]; rw [List.getElem?_set_ne (by rcases hidx with _ | _ <;> omega),
      List.getElem?_set_ne (by rcases hidx with _ | _ <;> omega),
      List.getElem?_set_ne (by rcases hidx with _ | _ <;> omega),
      List.getElem?_set_ne (by rcases hidx with _ | _ <;> omega)]
  have hql_dec : (scr1[co + 5]?.getD 0#32).toNat < ql.toNat := by
    dsimp only [scr1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
    change 0 < ql.toNat at hpos; bv_omega
  refine ⟨hb_lt, hnqh_lt, hlen1, wl_ctrl_same_of_agree hlay_pop' (by rw [hlen1, hscrl_pop])
      fun idx h => by dsimp only [scr1]; exact List.getElem?_set_ne (by omega),
    fun idx hidx => by rw [hdisj idx (Or.inl (by omega))]; exact hpref idx hidx,
    fun k hk => by rw [hdisj (ht_off + k) (Or.inr (by omega))]; exact hht k hk,
    hocc.2.2.2.1 b.toNat hb_lt,
    ⟨hocc.1, hocc.2.1, hocc.2.2.1, fun b' hb' => ?_, fun nd hn1 hn2 hm3 => ?_⟩, hql_dec⟩
  · by_cases hbb : b' = b.toNat
    · subst hbb; dsimp only [scr1]
      rw [List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]; exact Or.inl rfl
    · dsimp only [scr1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hocc.2.2.2.1 b' hb'
  · have hocc_c := hocc.2.1; rw [hdisj nd (Or.inl (by omega)), hdisj (nd + 1) (Or.inl (by omega)),
      hdisj (nd + 2) (Or.inl (by omega))]; exact hocc.2.2.2.2 nd hn1 hn2 hm3

theorem wl_rehash_clear_step {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 scrh : List (BitVec 32)} {ih : BitVec 64}
    (hlay : CongCtrlLayout c scrh g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hscrl : scrh.length = c.scratch_cap) (hpref : ∀ idx < g_len, scrh[idx]? = scr0[idx]?)
    (hht : ∀ k < ih.toNat, scrh[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hocc : CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh)
    (hih_lt : ih.toNat < ht_sz) :
    let scrh' := scrh.set (ht_off + ih.toNat) 0xFFFFFFFF#32
    (BitVec.ofNat 64 ht_off + ih).toNat = ht_off + ih.toNat ∧
    (BitVec.ofNat 64 ht_off + ih).toNat < scrh.length ∧
    (ih + 1#64).toNat = ih.toNat + 1 ∧ scrh'.length = c.scratch_cap ∧
    CongCtrlLayout c scrh' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scrh'[idx]? = scr0[idx]?) ∧
    (∀ k < ih.toNat + 1, scrh'[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
    CongOccNodesOk F_cur cv g_len occ_end co bkt_off occ_bkt scr0 scrh' := by
  intro scrh'; have hsc := c.hscr; unfold dimacsBound at hsc; have hlay' := hlay
  rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hht_cap, _⟩
  have hhti_n : (BitVec.ofNat 64 ht_off + ih).toNat = ht_off + ih.toNat := by bv_omega
  have hlen' : scrh'.length = c.scratch_cap := by simp [scrh', hscrl]
  have hno : ∀ idx, idx < ht_off → scrh'[idx]? = scrh[idx]? :=
    fun idx hidx => List.getElem?_set_ne (by omega)
  refine ⟨hhti_n, by rw [hhti_n]; omega, by bv_omega, hlen',
    wl_ctrl_same_of_agree hlay' (by rw [hlen', hscrl]) fun idx h => hno idx (by omega),
    fun idx hidx => by rw [hno idx (by omega)]; exact hpref idx hidx, fun k hk => ?_,
    ⟨hocc.1, hocc.2.1, hocc.2.2.1, fun b' hb' => by
       rw [hno (bkt_off + b') (by omega)]; exact hocc.2.2.2.1 b' hb',
     fun nd hn1 hn2 hm3 => by
       have hocc_c := hocc.2.1
       rw [hno nd (by omega), hno (nd + 1) (by omega), hno (nd + 2) (by omega)]
       exact hocc.2.2.2.2 nd hn1 hn2 hm3⟩⟩
  by_cases hki : k = ih.toNat
  · subst hki; dsimp only [scrh']
    rw [List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
  · dsimp only [scrh']; rw [List.getElem?_set_ne (by omega)]; exact hht k (by omega)

theorem wl_do_grow_ctrl {c : FullCfg} {scr : List (BitVec 32)}
    {g_len co occ_bkt bkt_off inq_off q_off ht_off : Nat} {ht_sz : BitVec 64}
    (hlay : CongCtrlLayout c scr g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz.toNat)
    (hscrl : scr.length = c.scratch_cap)
    (hpre : ht_sz.toNat < 1048576 ∧ ht_off + (ht_sz <<< 1#64).toNat ≤ c.scratch_cap) :
    let ht_sz2 := ht_sz <<< 1#64; let scr' := scr.set (co + 7) (BitVec.setWidth 32 ht_sz2)
    0 < ht_sz2.toNat ∧ ht_sz2.toNat ≤ 2 * congHashMaxSz ∧ ht_sz2.toNat < 2 ^ 30 ∧
    ht_off + ht_sz2.toNat ≤ c.scratch_cap ∧ scr'.length = c.scratch_cap ∧
    CongCtrlLayout c scr' g_len co occ_bkt bkt_off inq_off q_off ht_off ht_sz2.toNat := by
  intro ht_sz2 scr'; have hsc := c.hscr; unfold dimacsBound at hsc; unfold congHashMaxSz
  have hsh : ht_sz2.toNat = 2 * ht_sz.toNat := bv64_shl1_lt (by omega); have hlay' := hlay
  rcases hlay with ⟨hc1, hc8, hgc, hgm, s0, s1, s2, s3, s6, _, ho_pos, ho_max, hpow, hht_pos,
    hcq, hqi, hib, hbh, hht_cap, hqh, hql, hqok⟩
  have hno : ∀ idx, idx ≠ co + 7 → scr'[idx]? = scr[idx]? :=
    fun idx hne => List.getElem?_set_ne (Ne.symm hne)
  have h7 : scr'[co + 7]?.getD 0#32 = BitVec.ofNat 32 ht_sz2.toNat := by
    dsimp only [scr']
    rw [List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]; bv_omega
  refine ⟨by omega, by omega, by omega, hpre.2, by simp [scr', hscrl],
    ⟨hc1, hc8, hgc, hgm, by rw [hno co (by omega)]; exact s0,
     by rw [hno (co + 1) (by omega)]; exact s1, by rw [hno (co + 2) (by omega)]; exact s2,
     by rw [hno (co + 3) (by omega)]; exact s3, by rw [hno (co + 6) (by omega)]; exact s6, h7,
     ho_pos, ho_max, hpow, by omega, hcq, hqi, hib, hbh, hpre.2,
     by rw [hno (co + 4) (by omega)]; exact hqh, by rw [hno (co + 5) (by omega)]; exact hql,
     fun k hk => by
       rw [hno (co + 5) (by omega)] at hk; rw [hno (co + 4) (by omega)]
       have hslot := Nat.mod_lt ((scr[co + 4]?.getD 0#32).toNat + k) ho_pos
       rw [hno (q_off + ((scr[co + 4]?.getD 0#32).toNat + k) % occ_bkt) (by omega)]
       exact hqok k hk⟩⟩

theorem wl_load_c5 {c : FullCfg} {ctrl_off : BitVec 64} {so : FullState} {mo : Mem 64}
    {R : Mem 64 → Prop} (hc5_n : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5)
    (hco5_o : (ctrl_off + 5#64).toNat < so.scratch.scratch_buf.length)
    (hmo : (FullMem c so ⋆ R) mo) :
    (loadVal mo i32 (c.pScratchBuf + ctrl_off * 4 + 20)).getD 0#32 =
      so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32 := by
  have ha_c5 : c.pScratchBuf + ctrl_off * 4 + 20 = c.pScratchBuf + (ctrl_off + 5#64) * 4 := by
    bv_omega
  rw [ha_c5, c0_load_array (focus_full_scratch_buf hmo) hco5_o (by decide) (by decide),
    Option.getD_some, list_getElem_congr hc5_n hco5_o (by rw [← hc5_n]; exact hco5_o),
    List.getElem?_eq_getElem (by rw [← hc5_n]; exact hco5_o), Option.getD_some]

theorem wl_measure_dec {c : FullCfg} {ctrl_off tlim ticks_o ticks_b : BitVec 64}
    {occ_bkt : Nat} {ql : BitVec 32} {sb : FullState} {mo mb : Mem 64} {R : Mem 64 → Prop}
    (hc5_n : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5)
    (hco5_b : (ctrl_off + 5#64).toNat < sb.scratch.scratch_buf.length)
    (hld_o : (loadVal mo i32 (c.pScratchBuf + ctrl_off * 4 + 20)).getD 0#32 = ql)
    (hmb : (FullMem c sb ⋆ R) mb)
    (hto_lt : ticks_o.toNat < tlim.toNat)
    (hq_lt : (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hstep_b : ticks_o.toNat < ticks_b.toNat ∨ (sb.core.inconsistent = 0#64 ∧
      (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat))
    (htb_lo : ticks_o.toNat ≤ ticks_b.toNat) :
    (tlim.toNat - ticks_b.toNat) * (occ_bkt + 1) +
      ((loadVal mb i32 (c.pScratchBuf + ctrl_off * 4 + 20)).getD 0#32).toNat <
    (tlim.toNat - ticks_o.toNat) * (occ_bkt + 1) +
      ((loadVal mo i32 (c.pScratchBuf + ctrl_off * 4 + 20)).getD 0#32).toNat := by
  have hld_b := wl_load_c5 hc5_n hco5_b hmb
  rw [hld_b, hld_o]; rcases Nat.lt_or_eq_of_le htb_lo with hlt | heq
  · have h1 : tlim.toNat - ticks_b.toNat + 1 ≤ tlim.toNat - ticks_o.toNat := by omega
    have h2 := Nat.mul_le_mul_right (occ_bkt + 1) h1
    have h3 : (tlim.toNat - ticks_b.toNat) * (occ_bkt + 1) + occ_bkt <
        (tlim.toNat - ticks_b.toNat + 1) * (occ_bkt + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
    omega
  · have hql_lt := (hstep_b.resolve_left (by omega)).2; rw [← heq]; omega

theorem wl_ctrl_eqs {c : FullCfg} {scr : List (BitVec 32)} {g_len : Nat}
    {ctrl_off : BitVec 64} {occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hht_bnd : ht_sz < 2 ^ 30) (hscrl : scr.length = c.scratch_cap)
    (hlay : CongCtrlLayout c scr g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    ∃ (hc0 : ctrl_off.toNat < scr.length) (hc1 : (ctrl_off + 1#64).toNat < scr.length)
      (hc2 : (ctrl_off + 2#64).toNat < scr.length) (hc3 : (ctrl_off + 3#64).toNat < scr.length)
      (hc6 : (ctrl_off + 6#64).toNat < scr.length) (hc7 : (ctrl_off + 7#64).toNat < scr.length),
      (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4 ∧ (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5 ∧
      (BitVec.ofNat 64 ht_off).toNat = ht_off ∧ (BitVec.ofNat 64 ht_sz).toNat = ht_sz ∧
      (BitVec.ofNat 64 bkt_off).toNat = bkt_off ∧ (BitVec.ofNat 64 inq_off).toNat = inq_off ∧
      (BitVec.ofNat 64 q_off).toNat = q_off ∧ scr[ctrl_off.toNat]'hc0 = BitVec.ofNat 32 occ_bkt ∧
      BitVec.setWidth 64 (scr[(ctrl_off + 1#64).toNat]'hc1) = BitVec.ofNat 64 bkt_off ∧
      BitVec.setWidth 64 (scr[(ctrl_off + 2#64).toNat]'hc2) = BitVec.ofNat 64 inq_off ∧
      BitVec.setWidth 64 (scr[(ctrl_off + 3#64).toNat]'hc3) = BitVec.ofNat 64 q_off ∧
      BitVec.setWidth 64 (scr[(ctrl_off + 6#64).toNat]'hc6) = BitVec.ofNat 64 ht_off ∧
      BitVec.setWidth 64 (scr[(ctrl_off + 7#64).toNat]'hc7) = BitVec.ofNat 64 ht_sz := by
  have ⟨hc1_n, hc2_n, hc3_n, hc4_n, hc5_n, hc6_n, hc7_n, hs0_c, hs1_c, hs2_c, hs3_c, hs6_c, hs7_c,
    hb32, hi32, hq32, hho32, hhs32, hho_n, hhs_n, hb64, hi64, hq64⟩ :=
    wl_ctrl_arith hht_bnd hscrl hlay
  have hc_cap := hlay.1; have hc_8 := hlay.2.1
  have hc0 : ctrl_off.toNat < scr.length := by rw [hscrl]; exact hc_cap
  have hc1 : (ctrl_off + 1#64).toNat < scr.length := by rw [hscrl, hc1_n]; omega
  have hc2 : (ctrl_off + 2#64).toNat < scr.length := by rw [hscrl, hc2_n]; omega
  have hc3 : (ctrl_off + 3#64).toNat < scr.length := by rw [hscrl, hc3_n]; omega
  have hc6 : (ctrl_off + 6#64).toNat < scr.length := by rw [hscrl, hc6_n]; omega
  have hc7 : (ctrl_off + 7#64).toNat < scr.length := by rw [hscrl, hc7_n]; omega
  rw [List.getElem?_eq_getElem hc0, Option.getD_some] at hs0_c
  rw [List.getElem?_eq_getElem hc1, Option.getD_some] at hs1_c
  rw [List.getElem?_eq_getElem hc2, Option.getD_some] at hs2_c
  rw [List.getElem?_eq_getElem hc3, Option.getD_some] at hs3_c
  rw [List.getElem?_eq_getElem hc6, Option.getD_some] at hs6_c
  rw [List.getElem?_eq_getElem hc7, Option.getD_some] at hs7_c
  exact ⟨hc0, hc1, hc2, hc3, hc6, hc7, hc4_n, hc5_n, hho_n, hhs_n, hb64, hi64, hq64, hs0_c,
    hs1_c ▸ hb32, hs2_c ▸ hi32, hs3_c ▸ hq32, hs6_c ▸ hho32, hs7_c ▸ hhs32⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Spec
public import LeanQbe.T.Examples.Arisca.Proof.Poly2Sp0
public import LeanQbe.T.Examples.Arisca.Proof.Poly2R
public import LeanQbe.T.Examples.Arisca.Proof.Poly2ApplySubst
public import LeanQbe.T.Examples.Arisca.Proof.Poly2ApplyLoop
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Poly2 Entry & `ar_apply` Loop 4 WP (`Arisca.Proof.Poly2`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for `ar_apply_wp` (chaining
`apply_bx_loop_wp`, `apply_slR_loop_wp`, `apply_vq_loop_wp`, and Loop 4 `apply_outer_loop_wp`),
and public re-export of all `Poly2` proofs (`ar_add_q_wp`, `ar_load_rule_wp`, `ar_store_rule_wp`,
`ar_build_sp0_wp`, `ar_build_R_wp`, `ar_apply_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly


public section

private theorem apply_post_vq_wp (Γ : T.Env)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    (hMun : ∀ xs m Q X, arMunionSpec xs m Q X →
      Γ "ar_munion" [i64, i64, i32, i64] [i64] xs m Q X)
    (hCmul : ∀ xs m Q X, arCmulSpec xs m Q X →
      Γ "ar_cmul" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s s1 : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 tm0_1 tm1_1 pool0_1 pool1_1 qm : List (BitVec 32)}
    {qs ql qh : List (BitVec 64)}
    {ix ix2 bxL vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {vqOff' vq' : List (BitVec 32)} {vqSkip' : List (BitVec 8)}
    {partnerArr curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop}
    {nb : BitVec 32} {slB slR : BitVec 64} {qFin : Nat} {mV : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hs1 : s1 = { s with pc := s1.pc, ptop := s1.ptop })
    (hpc1 : s1.pc.toNat < 2) (htc1 : s1.tc.toNat < 2)
    (htn : s.tn.toNat ≤ s.tcap.toNat) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnb_pos : 0 < nb.toNat) (hnb_tn : nb.toNat ≤ s.tn.toNat)
    (hbx_t : s.tcap.toNat ≤ bxL.length) (hinc : strictIncBelow bxL nb.toNat s.tn.toNat)
    (hnb_nr_q : nb.toNat * s.cur_nr.toNat ≤ s.qcap.toNat)
    (hnb_nr_t : (s.tn.toNat - nb.toNat) + nb.toNat * s.cur_nr.toNat ≤ s.tcap.toNat)
    (hslR : slR.toNat = rSymLenSum curRp curRm s.cur_nr.toNat)
    (hslB1 : slB.toNat = bxSymLenSum (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
      (if s1.tc.toNat = 0 then tm0_1 else tm1_1) bxL nb.toNat)
    (hpt_cap : s1.ptop.toNat + (s.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat) ≤ s.pcap.toNat)
    (htm0 : s.tcap.toNat ≤ tm0.length) (htm1 : s.tcap.toNat ≤ tm1.length)
    (hts0 : s.tcap.toNat ≤ ts0.length) (htl0 : s.tcap.toNat ≤ tl0.length)
    (hth0 : s.tcap.toNat ≤ th0.length)
    (hts1 : s.tcap.toNat ≤ ts1.length) (htl1 : s.tcap.toNat ≤ tl1.length)
    (hth1 : s.tcap.toNat ≤ th1.length)
    (hp0 : s.pcap.toNat ≤ pool0.length) (hp1 : s.pcap.toNat ≤ pool1.length)
    (hqm : s.qcap.toNat ≤ qm.length) (hqs : s.qcap.toNat ≤ qs.length)
    (hql : s.qcap.toNat ≤ ql.length) (hqh : s.qcap.toNat ≤ qh.length)
    (hix : s.qcap.toNat ≤ ix.length) (hix2 : s.qcap.toNat ≤ ix2.length)
    (hvqOff : s.qcap.toNat + 1 ≤ vqOff.length) (hvq : s.pcap.toNat ≤ vq.length)
    (hvqSkip : s.qcap.toNat ≤ vqSkip.length)
    (htm0_1 : tm0_1.length = tm0.length) (htm1_1 : tm1_1.length = tm1.length)
    (hp0_1 : pool0_1.length = pool0.length) (hp1_1 : pool1_1.length = pool1.length)
    (hvqo : vqOff'.length = vqOff.length) (hvq' : vq'.length = vq.length)
    (hvqs : vqSkip'.length = vqSkip.length) (hqFin : qFin ≤ s1.pcap.toNat)
    (hcurNr_rm : s.cur_nr.toNat ≤ curRm.length) (hcurNr_rl : s.cur_nr.toNat ≤ curRl.length)
    (hcurNr_rh : s.cur_nr.toNat ≤ curRh.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hPart : ∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr)
    (hCurR : ∀ σ, Valid σ →
      CurRRep s.modW σ s.cur_nr.toNat sym.toNat curRm curRl curRh curRp)
    (hcurSl : ∀ r < s.cur_nr.toNat, MonoSliceOk curRp (curRm.getD r 0#32).toNat curRp.length)
    (hcurSo : ∀ r < s.cur_nr.toNat, MonoSorted curRp (curRm.getD r 0#32).toNat)
    (hcurMr32 : ∀ r < s.cur_nr.toNat,
      (curRp.getD (curRm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hVqOk : ∀ r < s1.cur_nr.toNat,
      VqRowOk s1.n_nets.toNat sym.toNat partnerArr curRp curRm vqOff' vq' vqSkip' Valid r qFin)
    (hSl1 : ∀ i < s.tn.toNat,
      MonoSliceOk (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
        ((if s1.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat s1.ptop.toNat ∧
      ((if s1.pc.toNat = 0 then pool0_1 else pool1_1).getD
        ((if s1.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSo1 : ∀ i < s.tn.toNat, MonoSorted (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
      ((if s1.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat)
    (hSi1 : SigOk (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
      (if s1.tc.toNat = 0 then tm0_1 else tm1_1) (if s.tc.toNat = 0 then ts0 else ts1) s.tn.toNat)
    (hTot1 : monoTotalWords (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
      (if s1.tc.toNat = 0 then tm0_1 else tm1_1) s.tn.toNat ≤ s1.ptop.toNat)
    (hbxM1 : ∀ b < nb.toNat, sym.toNat ∈ symListAt (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
      ((if s1.tc.toNat = 0 then tm0_1 else tm1_1).getD (bxL.getD b 0#32).toNat 0#32).toNat)
    (hSyEq1 : ∀ i < s.tn.toNat,
      symListAt (if s1.pc.toNat = 0 then pool0_1 else pool1_1)
        ((if s1.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat =
      symListAt (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat)
    (hmV : (arCtxMem cx s1 ⋆ array (t := i32) s1.partner partnerArr ⋆
      array (t := i32) s1.cur_rm curRm ⋆ array64 s1.cur_rl curRl ⋆
      array64 s1.cur_rh curRh ⋆ array (t := i32) s1.cur_rp curRp ⋆
      tMem s1 tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
      qMem s1 qm qs ql qh ix ix2 bxL vqOff' vq' vqSkip' ⋆ R) mV)
    (hOk : ∀ (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' bx' vqOff'' vq'' : List (BitVec 32)) (vqSkip'' : List (BitVec 8))
        (m' : Mem 64),
      let srcPool0 := if s.pc.toNat = 0 then pool0 else pool1
      let srcTm0 := if s.tc.toNat = 0 then tm0 else tm1
      let srcTl0 := if s.tc.toNat = 0 then tl0 else tl1
      let srcTh0 := if s.tc.toNat = 0 then th0 else th1
      let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
      let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
      let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
      let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
      let dstTh := if s'.tc.toNat = 0 then th0' else th1'
      s'.pc.toNat < 2 → s'.tc.toNat < 2 →
      s'.ptop.toNat ≤ s.pcap.toNat → s'.tn.toNat ≤ s.tcap.toNat →
      s' = { s with
        tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop,
        qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      bx'.length = bxL.length → vqOff''.length = vqOff'.length →
      vq''.length = vq'.length → vqSkip''.length = vqSkip'.length →
      (∀ i < s'.tn.toNat,
        MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
        (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) →
      SigOk dstPool dstTm dstTs s'.tn.toNat →
      monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat →
      (∀ bd : Nat, SymsBound srcPool0 srcTm0 s.tn.toNat bd →
        SymsBound curRp curRm s.cur_nr.toNat bd →
        SymsBound dstPool dstTm s'.tn.toNat bd) →
      (∀ σ, Valid σ →
        polyEval s.modW σ dstPool dstTm dstTl dstTh s'.tn.toNat =
          polyEval s.modW σ srcPool0 srcTm0 srcTl0 srcTh0 s.tn.toNat) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
        array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
        array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx' vqOff'' vq'' vqSkip'' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (applyLoop4Expr cx sym s1.cur_rm s1.cur_rl s1.cur_rh s1.cur_rp s1.cur_nr s1.tn
      s1.bx nb slB slR (s1.pool.getD s1.pc.toNat 0#64) (s1.tm.getD s1.tc.toNat 0#64)
      (s1.tl.getD s1.tc.toNat 0#64) (s1.th.getD s1.tc.toNat 0#64) s1.ptop) mV := by
  have hpcap1 : s1.pcap = s.pcap := by rw [hs1]
  have hcurNr1 : s1.cur_nr = s.cur_nr := by rw [hs1]
  have hnn1 : s1.n_nets = s.n_nets := by rw [hs1]
  obtain ⟨restTQ1, hFocTQ1, htqBack1⟩ := tqMem_apply_focus s1 tm0_1 tm1_1 ts0 tl0 th0
    ts1 tl1 th1 pool0_1 pool1_1 qm qs ql qh ix ix2 bxL vqOff' vq' vqSkip' hpc1 htc1
  have hCtx : ApplyLoopCtx cx sym s s1 tm0 tm1 pool0 pool1 ts0 tl0 th0 ts1 tl1 th1
      tm0_1 tm1_1 pool0_1 pool1_1 qm qs ql qh ix ix2 bxL vqOff' vq' vqSkip'
      partnerArr curRm curRl curRh curRp Valid R
      (array (t := i32) (s1.tm.getD s1.tc.toNat 0#64)
         (if s1.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s1.ts.getD s1.tc.toNat 0#64) (if s1.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s1.tl.getD s1.tc.toNat 0#64) (if s1.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s1.th.getD s1.tc.toNat 0#64) (if s1.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s1.bx bxL ⋆ array (t := i32) s1.vq_off vqOff' ⋆
       array (t := i32) s1.vq vq' ⋆ array (t := i8) s1.vq_skip vqSkip' ⋆ restTQ1)
      nb slB slR qFin :=
    { hs1 := hs1, hpc := hpc1, htc := htc1, htn := htn, htcap30 := htcap30,
      hqcap32 := hqcap32, hpcap32 := hpcap32, hnb_pos := hnb_pos, hnb_tn := hnb_tn,
      hnb_bx := le_trans hnb_tn (le_trans htn hbx_t),
      hinc := hinc, hnb_nr_q := hnb_nr_q, hnb_nr_t := hnb_nr_t, hslR := hslR, hslB := hslB1,
      hpt_cap := hpt_cap,
      htm0_len := by rw [htm0_1]; exact htm0, htm1_len := by rw [htm1_1]; exact htm1,
      hts0_len := hts0, htl0_len := htl0, hth0_len := hth0,
      hts1_len := hts1, htl1_len := htl1, hth1_len := hth1,
      hp0_len := by rw [hp0_1]; exact hp0, hp1_len := by rw [hp1_1]; exact hp1,
      hqm_len := hqm, hqs_len := hqs, hql_len := hql, hqh_len := hqh,
      hix_len := hix, hix2_len := hix2,
      hvqOff_len := by rw [hvqo]; exact hvqOff, hvq_len := by rw [hvq']; exact hvq,
      hvqSkip_len := by rw [hvqs]; exact hvqSkip,
      hqFin_le := by rw [← hpcap1]; exact hqFin,
      hcurNr_rm := hcurNr_rm, hcurNr_rl := hcurNr_rl, hcurNr_rh := hcurNr_rh,
      hMasks := hMasks, hPart := hPart, hCurR := hCurR, hcurSl := hcurSl,
      hcurSo := hcurSo, hcurMr32 := hcurMr32,
      hVqOk := by rw [← hnn1, ← hcurNr1]; exact hVqOk,
      hSl1 := hSl1, hSo1 := hSo1,
      hSi1 := by
        have htc_eq : s1.tc = s.tc := by rw [hs1]
        simpa only [htc_eq] using hSi1,
      hTot1 := hTot1, hbxMem := hbxM1, hSym1 := hSyEq1,
      htm0_eq := htm0_1, htm1_eq := htm1_1, hp0_eq := hp0_1, hp1_eq := hp1_1,
      htqPack := fun s' pool' qm' qs' ql' qh' htm' hts' htl' hth' hpool'
          hqm' hqs' hql' hqh' hix' hix2' hbx' hvqo' hvq'' hvqs'
          lpool lqm lqs lql lqh => by
        have hback := htqBack1 s' pool' qm' qs' ql' qh' bxL vqOff' vq' vqSkip'
          htm' hts' htl' hth' hpool' hqm' hqs' hql' hqh' hix' hix2' hbx' hvqo' hvq'' hvqs'
          lpool lqm lqs lql lqh rfl rfl rfl rfl
        rw [hback]; ac_rfl }
  exact apply_outer_loop_wp Γ hMhas hMun hCmul hMerge hFocTQ1 hCtx hmV hOk

private theorem apply_post_bx_wp (Γ : T.Env)
    (hComp : ∀ xs m Q X, arCompactSpec xs m Q X →
      Γ "ar_compact" [i64] [] xs m Q X)
    (hMvan : ∀ xs m Q X, arMvanishSpec xs m Q X →
      Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    (hMun : ∀ xs m Q X, arMunionSpec xs m Q X →
      Γ "ar_munion" [i64, i64, i32, i64] [i64] xs m Q X)
    (hCmul : ∀ xs m Q X, arCmulSpec xs m Q X →
      Γ "ar_cmul" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bxL vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {partnerArr curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop}
    {nb : BitVec 32} {slB : BitVec 64} {mL : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (htn : s.tn.toNat ≤ s.tcap.toNat) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hptop : s.ptop.toNat ≤ s.pcap.toNat)
    (hpcap32 : s.pcap.toNat < 2 ^ 32) (hnn32 : 2 * s.n_nets.toNat < 2 ^ 32)
    (htm0 : s.tcap.toNat ≤ tm0.length) (htm1 : s.tcap.toNat ≤ tm1.length)
    (hts0 : s.tcap.toNat ≤ ts0.length) (htl0 : s.tcap.toNat ≤ tl0.length)
    (hth0 : s.tcap.toNat ≤ th0.length)
    (hts1 : s.tcap.toNat ≤ ts1.length) (htl1 : s.tcap.toNat ≤ tl1.length)
    (hth1 : s.tcap.toNat ≤ th1.length)
    (hp0 : s.pcap.toNat ≤ pool0.length) (hp1 : s.pcap.toNat ≤ pool1.length)
    (hqm : s.qcap.toNat ≤ qm.length) (hqs : s.qcap.toNat ≤ qs.length)
    (hql : s.qcap.toNat ≤ ql.length) (hqh : s.qcap.toNat ≤ qh.length)
    (hix : s.qcap.toNat ≤ ix.length) (hix2 : s.qcap.toNat ≤ ix2.length)
    (hbx_t : s.tcap.toNat ≤ bxL.length)
    (hvqOff : s.qcap.toNat + 1 ≤ vqOff.length) (hvq : s.pcap.toNat ≤ vq.length)
    (hvqSkip : s.qcap.toNat ≤ vqSkip.length)
    (hnb_pos : 0 < nb.toNat) (hnb_tn : nb.toNat ≤ s.tn.toNat)
    (hinc : strictIncBelow bxL nb.toNat s.tn.toNat)
    (hslB : slB.toNat = bxSymLenSum (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) bxL nb.toNat)
    (hNonEmpty : ∃ σ₀, Valid σ₀)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hPart : ∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr)
    (hCurR : ∀ σ, Valid σ →
      CurRRep s.modW σ s.cur_nr.toNat sym.toNat curRm curRl curRh curRp)
    (hcurNr_rm : s.cur_nr.toNat ≤ curRm.length) (hcurNr_rl : s.cur_nr.toNat ≤ curRl.length)
    (hcurNr_rh : s.cur_nr.toNat ≤ curRh.length)
    (hcurSl : ∀ r < s.cur_nr.toNat, MonoSliceOk curRp (curRm.getD r 0#32).toNat curRp.length)
    (hcurSo : ∀ r < s.cur_nr.toNat, MonoSorted curRp (curRm.getD r 0#32).toNat)
    (hcurMr32 : ∀ r < s.cur_nr.toNat,
      (curRp.getD (curRm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hcurTot : monoTotalWords curRp curRm s.cur_nr.toNat ≤ 4000000000)
    (hSlices : ∀ i < s.tn.toNat,
      MonoSliceOk (if s.pc.toNat = 0 then pool0 else pool1)
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat s.ptop.toNat ∧
      ((if s.pc.toNat = 0 then pool0 else pool1).getD
        ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ i < s.tn.toNat, MonoSorted (if s.pc.toNat = 0 then pool0 else pool1)
      ((if s.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat)
    (hSig : SigOk (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) (if s.tc.toNat = 0 then ts0 else ts1) s.tn.toNat)
    (hTot : monoTotalWords (if s.pc.toNat = 0 then pool0 else pool1)
      (if s.tc.toNat = 0 then tm0 else tm1) s.tn.toNat ≤ s.ptop.toNat)
    (hbxMem : ∀ b < nb.toNat, sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0 else pool1)
      ((if s.tc.toNat = 0 then tm0 else tm1).getD (bxL.getD b 0#32).toNat 0#32).toNat)
    (hmL' : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bxL vqOff vq vqSkip ⋆ R) mL)
    (hPost : ∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' bx' vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8))
        (m' : Mem 64),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      let srcTm := if s.tc.toNat = 0 then tm0 else tm1
      let srcTl := if s.tc.toNat = 0 then tl0 else tl1
      let srcTh := if s.tc.toNat = 0 then th0 else th1
      let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
      let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
      let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
      let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
      let dstTh := if s'.tc.toNat = 0 then th0' else th1'
      s'.pc.toNat < 2 → s'.tc.toNat < 2 →
      s'.ptop.toNat ≤ s.pcap.toNat → s'.tn.toNat ≤ s.tcap.toNat →
      s' = { s with
        tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop,
        qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      bx'.length = bxL.length → vqOff'.length = vqOff.length →
      vq'.length = vq.length → vqSkip'.length = vqSkip.length →
      (ok = true →
        (∀ i < s'.tn.toNat,
          MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
          (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) ∧
        SigOk dstPool dstTm dstTs s'.tn.toNat ∧
        monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat ∧
        (∀ bd : Nat, SymsBound srcPool srcTm s.tn.toNat bd →
          SymsBound curRp curRm s.cur_nr.toNat bd →
          SymsBound dstPool dstTm s'.tn.toNat bd) ∧
        (∀ σ, Valid σ →
          polyEval s.modW σ dstPool dstTm dstTl dstTh s'.tn.toNat =
            polyEval s.modW σ srcPool srcTm srcTl srcTh s.tn.toNat)) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
        array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
        array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx' vqOff' vq' vqSkip' ⋆ R) m' →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (applyLoop2Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
      s.bx nb slB) mL := by
  refine apply_slR_loop_wp Γ hComp hpc htc htn htcap30 hqcap32 hptop hpcap32
    htm0 htm1 hp0 hp1 hnb_pos hnb_tn hinc hslB hNonEmpty hcurNr_rm hcurSl hcurTot
    hSlices hSorted hSig hTot hbxMem hmL' ?_ ?_
  · intro s1 tm0_1 tm1_1 pool0_1 pool1_1 m1 hpc1 hpt1 hs1 htm0_1 htm1_1 hp0_1 hp1_1 hm1
    have htn1 : s1.tn.toNat ≤ s.tcap.toNat := by rw [hs1]; exact htn
    have htc1 : s1.tc.toNat < 2 := by rw [hs1]; exact htc
    refine hPost false s1 tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1
      qm qs ql qh ix ix2 bxL vqOff vq vqSkip m1 hpc1 htc1 hpt1 htn1
      (by rw [hs1]) htm0_1 htm1_1 rfl rfl rfl rfl rfl rfl hp0_1 hp1_1
      rfl rfl rfl rfl (Or.inl ⟨by rw [hs1], by rw [hs1], rfl, rfl⟩)
      rfl rfl rfl rfl (fun h => by cases h) hm1
  · intro s1 tm0_1 tm1_1 pool0_1 pool1_1 slR m1 dstPool1 dstTm1
      hpc1 hpt1 hs1 htm0_1 htm1_1 hp0_1 hp1_1
      hcurNr_qcap hnb_nr_q hnb_nr_t hslR hpt_cap hslB1 hSl1 hSo1 hSi1 hTot1 hbxM1 hSyEq1 hm1
    dsimp only [dstPool1, dstTm1] at hslB1 hSl1 hSo1 hSi1 hTot1 hbxM1 hSyEq1
    have htc1 : s1.tc.toNat < 2 := by rw [hs1]; exact htc
    have hcurNr1 : s1.cur_nr = s.cur_nr := by rw [hs1]
    have hqcap1 : s1.qcap = s.qcap := by rw [hs1]
    have hpcap1 : s1.pcap = s.pcap := by rw [hs1]
    have hnn1 : s1.n_nets = s.n_nets := by rw [hs1]
    rw [show applyLoop3Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
          s.bx nb slB slR =
        applyLoop3Expr cx sym s1.cur_rm s1.cur_rl s1.cur_rh s1.cur_rp s1.cur_nr s1.tn
          s1.bx nb slB slR by rw [hs1]]
    refine apply_vq_loop_wp Γ hMvan hpc1 htc1 (by rw [hcurNr1, hqcap1]; exact hcurNr_qcap)
      (by rw [hqcap1]; exact hqcap32) (by rw [hpcap1]; exact hpcap32)
      (by rw [hnn1]; exact hnn32) (by rw [hcurNr1]; exact hcurNr_rm)
      (by rw [hqcap1]; exact hvqOff) (by rw [hpcap1]; exact hvq)
      (by rw [hqcap1]; exact hvqSkip) (by rw [hcurNr1]; exact hcurSl)
      (by rw [hcurNr1]; exact hcurMr32) hNonEmpty (by rw [hnn1]; exact hPart) hm1 ?_ ?_
    · intro vqOff' vq' vqSkip' mF hvqo hvq' hvqs hmF
      have htn1 : s1.tn.toNat ≤ s.tcap.toNat := by rw [hs1]; exact htn
      refine hPost false s1 tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1
        qm qs ql qh ix ix2 bxL vqOff' vq' vqSkip' mF hpc1 htc1 hpt1 htn1
        (by rw [hs1]) htm0_1 htm1_1 rfl rfl rfl rfl rfl rfl hp0_1 hp1_1
        rfl rfl rfl rfl (Or.inl ⟨by rw [hs1], by rw [hs1], rfl, rfl⟩)
        rfl hvqo hvq' hvqs (fun h => by cases h) hmF
    · intro vqOff' vq' vqSkip' qFin mV hvqo hvq' hvqs hqFin hVqOk hmV
      refine apply_post_vq_wp (bxL := bxL) Γ hMhas hMun hCmul hMerge hs1 hpc1 htc1 htn
        htcap30 hqcap32 hpcap32 hnb_pos hnb_tn hbx_t hinc hnb_nr_q hnb_nr_t hslR hslB1 hpt_cap
        htm0 htm1 hts0 htl0 hth0 hts1 htl1 hth1 hp0 hp1 hqm hqs hql hqh hix hix2
        hvqOff hvq hvqSkip htm0_1 htm1_1 hp0_1 hp1_1 hvqo hvq' hvqs hqFin
        hcurNr_rm hcurNr_rl hcurNr_rh hMasks hPart hCurR hcurSl hcurSo hcurMr32
        hVqOk hSl1 hSo1 hSi1 hTot1 hbxM1 hSyEq1 hmV ?_
      intro s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh'
        ix' ix2' bx' vqOff'' vq'' vqSkip'' m'
        srcPool0 srcTm0 srcTl0 srcTh0 dstPool dstTm dstTs dstTl dstTh
        hpc' htc' hpt' htn' hs' htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1'
        hp0' hp1' hqm' hqs' hql' hqh' hixs hbx' hvqo'' hvq'' hvqs''
        hSl' hSo' hSi' hW' hSy' hEv' hm'
      dsimp only [srcPool0, srcTm0, srcTl0, srcTh0] at hSl' hSo' hSi' hW' hSy' hEv'
      dsimp only [dstPool, dstTm, dstTs, dstTl, dstTh] at hSl' hSo' hSi' hW' hSy' hEv'
      exact hPost true s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh'
        ix' ix2' bx' vqOff'' vq'' vqSkip'' m' hpc' htc' hpt' htn' hs'
        htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1' hp0' hp1' hqm' hqs' hql' hqh'
        hixs hbx' (hvqo''.trans hvqo) (hvq''.trans hvq') (hvqs''.trans hvqs)
        (fun _ => ⟨hSl', hSo', hSi', hW', hSy', hEv'⟩) hm'

/-! ## 2. Entry Theorem: `ar_apply_wp` -/

/-- `XPost`-polymorphic WP soundness for `ar_apply(cx, s)`. -/
public theorem ar_apply_wp (Γ : T.Env)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    (hSigbit : ∀ xs m Q X, arSigbitSpec xs m Q X →
      Γ "ar_sigbit" [i32] [i64] xs m Q X)
    (hComp : ∀ xs m Q X, arCompactSpec xs m Q X →
      Γ "ar_compact" [i64] [] xs m Q X)
    (hMvan : ∀ xs m Q X, arMvanishSpec xs m Q X →
      Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X)
    (hMun : ∀ xs m Q X, arMunionSpec xs m Q X →
      Γ "ar_munion" [i64, i64, i32, i64] [i64] xs m Q X)
    (hCmul : ∀ xs m Q X, arCmulSpec xs m Q X →
      Γ "ar_cmul" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X) :
    ∀ xs m Q X, arApplySpec xs m Q X → Func.wp Γ ar_apply_body xs m Q X := by
  rintro ⟨cx, sym, ⟨⟩⟩ m0 Q X
    ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
     qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip,
     partnerArr, curRm, curRl, curRh, curRp, Valid, R,
     hpc, htc, htn, htcap30, _hqcap16, hqcap32, hptop, hpcap32, _hnn30, hnn32,
     htm0, htm1, hts0, htl0, hth0, hts1, htl1, hth1, hp0, hp1,
     hqm, hqs, hql, hqh, hix, hix2, hbx_t, _hbx_q, hvqOff, hvq, hvqSkip,
     hMasks, hNonEmpty, hPart, hCurR, hcurSo, hcurMr32, hcurTot,
     hSlices, hSorted, hSig, hTot, hm0, hPost⟩
  have hm0_cx : (arCtxMem cx s ⋆ (array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R)) m0 := sep_cast hm0 (by ac_rfl)
  have hl_ok : ArCtxLengthsOk s := arCtxMem_lengthsOk hm0_cx
  obtain ⟨σ₀, hV₀⟩ := hNonEmpty
  have hcurR0 := hCurR σ₀ hV₀
  have hcurNr_rm : s.cur_nr.toNat ≤ curRm.length := hcurR0.1
  have hcurNr_rl : s.cur_nr.toNat ≤ curRl.length := hcurR0.2.1
  have hcurNr_rh : s.cur_nr.toNat ≤ curRh.length := hcurR0.2.2.1
  have hcurSl : ∀ r < s.cur_nr.toNat, MonoSliceOk curRp (curRm.getD r 0#32).toNat curRp.length :=
    hcurR0.2.2.2.1
  have hhtm_len : s.tcap.toNat ≤ (if s.tc.toNat = 0 then tm0 else tm1).length := by
    split <;> assumption
  have hhts_len : s.tcap.toNat ≤ (if s.tc.toNat = 0 then ts0 else ts1).length := by
    split <;> assumption
  have hhp_len : s.pcap.toNat ≤ (if s.pc.toNat = 0 then pool0 else pool1).length := by
    split <;> assumption
  dsimp only [Func.wp, ar_apply_body]
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hSigbit ⟨sym, ⟨⟩⟩ m0 _ X fun bit hbit => ?_)
  subst hbit
  c0_hsteps_nogrp
  obtain ⟨restTQ0, hFocTQ0, htqBack0⟩ := tqMem_apply_focus s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
    pool0 pool1 qm qs ql qh ix ix2 bx vqOff vq vqSkip hpc htc
  let restBx : Mem 64 → Prop :=
    array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
    array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
    array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
    array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
    array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
    array (t := i32) s.vq_off vqOff ⋆ array (t := i32) s.vq vq ⋆
    array (t := i8) s.vq_skip vqSkip ⋆ restTQ0
  have hm0_bx : (arCtxMem cx s ⋆
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
      array (t := i32) s.bx bx ⋆ restBx ⋆ R) m0 := by
    have hm' : (arCtxMem cx s ⋆
        (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
         qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip) ⋆
        array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
        array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
        R) m0 := sep_cast hm0 (by ac_rfl)
    rw [hFocTQ0] at hm'
    dsimp only [restBx]; exact sep_cast hm' (by ac_rfl)
  rw [← getD_eq_getElem s.tm 0#64 (by rw [hl_ok.tm]; exact htc),
      ← getD_eq_getElem s.pool 0#64 (by rw [hl_ok.pool]; exact hpc),
      ← getD_eq_getElem s.ts 0#64 (by rw [hl_ok.ts]; exact htc)]
  change wp Γ Q X (applyLoop1Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
    (sigBit sym) (s.tm.getD s.tc.toNat 0#64) (s.pool.getD s.pc.toNat 0#64)
    (s.ts.getD s.tc.toNat 0#64) s.bx) m0
  refine apply_bx_loop_wp (Γ := Γ) (_tl0 := tl0) (_th0 := th0) (_tl1 := tl1) (_th1 := th1)
    hMhas hpc htc htn htcap30 hptop hpcap32 hhtm_len hhts_len hhp_len hbx_t hSlices hSorted hTot
    hm0_bx ?_ ?_
  · intro bxL mL hbxL hmL
    have hmL' : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
        array (t := i32) s.cur_rp curRp ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bxL vqOff vq vqSkip ⋆ R) mL := by
      have hm1 : (arCtxMem cx s ⋆
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
             (if s.pc.toNat = 0 then pool0 else pool1) ⋆
           array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
           array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
           array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
           array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
           array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
           array (t := i32) s.bx bxL ⋆ array (t := i32) s.vq_off vqOff ⋆
           array (t := i32) s.vq vq ⋆ array (t := i8) s.vq_skip vqSkip ⋆ restTQ0) ⋆
          array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
          array (t := i32) s.cur_rp curRp ⋆ R) mL := by
        dsimp only [restBx] at hmL; exact sep_cast hmL (by ac_rfl)
      rw [← htqBack0 s (if s.pc.toNat = 0 then pool0 else pool1) qm qs ql qh bxL vqOff vq vqSkip
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl hbxL rfl rfl rfl] at hm1
      rcases bv32_lt2_cases hpc with h0 | h1
      · simp only [h0] at hm1; exact sep_cast hm1 (by ac_rfl)
      · simp only [h1] at hm1; exact sep_cast hm1 (by ac_rfl)
    refine hPost true s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 qm qs ql qh
      ix ix2 bxL vqOff vq vqSkip mL hpc htc hptop htn rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hbxL rfl rfl rfl
      (fun _ => ⟨hSlices, hSorted, hSig, hTot, fun _ hSb _ => hSb, fun _ _ => rfl⟩) hmL'
  · intro nb slB bxL mL hbxL hnb_pos hnb_tn hinc hslB hbxMem hmL
    have hmL' : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
        array (t := i32) s.cur_rp curRp ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bxL vqOff vq vqSkip ⋆ R) mL := by
      have hm1 : (arCtxMem cx s ⋆
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
             (if s.pc.toNat = 0 then pool0 else pool1) ⋆
           array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
           array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
           array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
           array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
           array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
           array (t := i32) s.bx bxL ⋆ array (t := i32) s.vq_off vqOff ⋆
           array (t := i32) s.vq vq ⋆ array (t := i8) s.vq_skip vqSkip ⋆ restTQ0) ⋆
          array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
          array (t := i32) s.cur_rp curRp ⋆ R) mL := by
        dsimp only [restBx] at hmL; exact sep_cast hmL (by ac_rfl)
      rw [← htqBack0 s (if s.pc.toNat = 0 then pool0 else pool1) qm qs ql qh bxL vqOff vq vqSkip
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl hbxL rfl rfl rfl] at hm1
      rcases bv32_lt2_cases hpc with h0 | h1
      · simp only [h0] at hm1; exact sep_cast hm1 (by ac_rfl)
      · simp only [h1] at hm1; exact sep_cast hm1 (by ac_rfl)
    refine apply_post_bx_wp Γ hComp hMvan hMhas hMun hCmul hMerge hpc htc htn htcap30 hqcap32
      hptop hpcap32 hnn32 htm0 htm1 hts0 htl0 hth0 hts1 htl1 hth1 hp0 hp1 hqm hqs hql hqh hix hix2
      (by rw [hbxL]; exact hbx_t) hvqOff hvq hvqSkip hnb_pos hnb_tn hinc hslB ⟨σ₀, hV₀⟩ hMasks
      hPart hCurR hcurNr_rm hcurNr_rl hcurNr_rh hcurSl hcurSo hcurMr32 hcurTot
      hSlices hSorted hSig hTot hbxMem hmL' ?_
    intro ok s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh'
      ix' ix2' bx' vqOff' vq' vqSkip' m'
      srcPool srcTm srcTl srcTh dstPool dstTm dstTs dstTl dstTh
      hpc' htc' hpt' htn' hs' htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1'
      hp0' hp1' hqm' hqs' hql' hqh' hixs hbx' hvqo' hvq' hvqs' hOk' hm'
    dsimp only [srcPool, srcTm, srcTl, srcTh, dstPool, dstTm, dstTs, dstTl, dstTh] at hOk'
    exact hPost ok s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh'
      ix' ix2' bx' vqOff' vq' vqSkip' m' hpc' htc' hpt' htn' hs'
      htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1' hp0' hp1' hqm' hqs' hql' hqh'
      hixs (by rw [hbx', hbxL]) hvqo' hvq' hvqs' hOk' hm'

end

end LeanQbe.T.Examples.Arisca.Proof

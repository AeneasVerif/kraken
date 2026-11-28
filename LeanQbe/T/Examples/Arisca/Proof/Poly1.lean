/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly1Merge
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Merge Products WP (`Arisca.Proof.Poly1`)

`XPost`-polymorphic `Mem 64` WP proof for `ar_merge_products` (`ar_merge_products_wp`),
re-exporting `ar_sort_combine_wp`, `ar_gallop_wp`, and specs from `Poly1Merge` / `Poly1Sort` /
`Poly1Base`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

/-! ## 2. Emit Phase & `ar_merge_products_wp` (`Arisca.Src.Poly`) -/

private theorem merge_products_emit_phase (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx sm ss sl sh dm ds dl dh pool bxPtr qmPtr : Val i64}
    {nb k sidx didx n o cur bp pi a curC bpC oC : Val i32}
    {Q : Post []} {X : XPost} {s sSort : ArCtxState}
    {srcPool srcTm qm ixS bx dstTm0 : List (BitVec 32)}
    {qs srcTs srcTl srcTh qlS qhS dstTs0 dstTl0 dstTh0 : List (BitVec 64)}
    {dTmC : List (BitVec 32)} {dTsC dTlC dThC : List (BitVec 64)}
    {restM R Rro : Mem 64 → Prop}
    {JExit JL : Cont [i32, i32, i32, i32]} {JA : Cont [i32, i32, i64]}
    {JC : Cont [i32, i32, i32]} {mC : Mem 64}
    (hrecL : ∀ (prem' : Nat) (ys : Tup Val [i32, i32, i32, i32]) (m' : Mem 64),
      prem' < (k.toNat + 1) - pi.toNat →
      (prem' = (k.toNat + 1) - ys.2.2.2.1.toNat ∧
        MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat s.ptop.toNat
          srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
          (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
          (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
          dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
          ys.2.2.2.1.toNat ys.2.1.toNat ys.2.2.1.toNat ys.1.toNat m') →
      JL ys m')
    (hsm : sm = s.tm.getD s.tc.toNat 0#64) (hss : ss = s.ts.getD s.tc.toNat 0#64)
    (hsl : sl = s.tl.getD s.tc.toNat 0#64) (hsh : sh = s.th.getD s.tc.toNat 0#64)
    (hdm : dm = s.tm.getD (1 - s.tc.toNat) 0#64)
    (hds : ds = s.ts.getD (1 - s.tc.toNat) 0#64)
    (hdl : dl = s.tl.getD (1 - s.tc.toNat) 0#64)
    (hdh : dh = s.th.getD (1 - s.tc.toNat) 0#64)
    (hpool_val : pool = s.pool.getD s.pc.toNat 0#64) (hbxPtr : bxPtr = s.bx)
    (hn : n = s.tn)
    (hSort_qm : sSort.qm = s.qm) (hSort_qs : sSort.qs = s.qs)
    (hSort_ql : sSort.ql = s.ql) (hSort_qh : sSort.qh = s.qh)
    (hSort_nout : sSort.n_out = s.n_out) (hSort_mlo : sSort.mlo = s.mlo)
    (hSort_mhi : sSort.mhi = s.mhi)
    (hRro : Rro = arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
      array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R)
    (hptop_le : s.ptop.toNat ≤ srcPool.length)
    (hk_qn : k.toNat ≤ s.qn.toNat) (htn_le : s.tn.toNat ≤ s.tcap.toNat)
    (hqn_le : s.qn.toNat ≤ s.qcap.toNat)
    (hcap_sum : (s.tn.toNat - nb.toNat) + s.qn.toNat ≤ s.tcap.toNat)
    (hnb_bx : nb.toNat ≤ bx.length) (hinc : strictIncBelow bx nb.toNat s.tn.toNat)
    (hsrcTm_len : s.tcap.toNat ≤ srcTm.length) (hsrcTs_len : s.tcap.toNat ≤ srcTs.length)
    (hsrcTl_len : s.tcap.toNat ≤ srcTl.length) (hsrcTh_len : s.tcap.toNat ≤ srcTh.length)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hqs_len : s.qcap.toNat ≤ qs.length)
    (hqlS_len : s.qcap.toNat ≤ qlS.length) (hqhS_len : s.qcap.toNat ≤ qhS.length)
    (hMasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hTmOk : ∀ t < s.tn.toNat, MonoSliceOk srcPool (srcTm.getD t 0#32).toNat s.ptop.toNat ∧
      (srcPool.getD (srcTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hQmOk : ∀ t < s.qn.toNat, MonoSliceOk srcPool (qm.getD t 0#32).toNat s.ptop.toNat ∧
      (srcPool.getD (qm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hTmSorted : ∀ t < s.tn.toNat, MonoSorted srcPool (srcTm.getD t 0#32).toNat)
    (hQmSorted : ∀ t < s.qn.toNat, MonoSorted srcPool (qm.getD t 0#32).toNat)
    (hTmSig : SigOk srcPool srcTm srcTs s.tn.toNat)
    (hQmSig : SigOk srcPool qm qs s.qn.toNat)
    (hpi_lt : pi.toNat < k.toNat) (ha_eq : a = ixS.getD pi.toNat 0#32)
    (ha_lt : a.toNat < s.qn.toNat)
    (hqmPtr : qmPtr = s.pool.getD s.pc.toNat 0#64 +
      BitVec.ofNat 64 (4 * (qm.getD a.toNat 0#32).toNat))
    (hdC1 : dTmC.length = dstTm0.length) (hdC2 : dTsC.length = dstTs0.length)
    (hdC3 : dTlC.length = dstTl0.length) (hdC4 : dThC.length = dstTh0.length)
    (hdstTm_len : s.tcap.toNat ≤ dstTm0.length) (hdstTs_len : s.tcap.toNat ≤ dstTs0.length)
    (hdstTl_len : s.tcap.toNat ≤ dstTl0.length) (hdstTh_len : s.tcap.toNat ≤ dstTh0.length)
    (hbpC_nb : bpC.toNat ≤ nb.toNat) (hcurC_tn : curC.toNat ≤ s.tn.toNat)
    (hoC_le : oC.toNat ≤ curC.toNat - bpC.toNat + pi.toNat)
    (hloC : ∀ p < bpC.toNat, (bx.getD p 0#32).toNat < curC.toNat)
    (hhiC : bpC.toNat < nb.toNat → curC.toNat ≤ (bx.getD bpC.toNat 0#32).toNat)
    (hOkC : ∀ t < oC.toNat, MonoSliceOk srcPool (dTmC.getD t 0#32).toNat s.ptop.toNat ∧
      (srcPool.getD (dTmC.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortedC : ∀ t < oC.toNat, MonoSorted srcPool (dTmC.getD t 0#32).toNat)
    (hSigC : SigOk srcPool dTmC dTsC oC.toNat)
    (hwordsC : monoTotalWords srcPool dTmC oC.toNat +
        tailWordSum srcPool srcTm curC.toNat s.tn.toNat +
        tailQWordSum srcPool qm ixS pi.toNat k.toNat ≤
      monoTotalWords srcPool srcTm s.tn.toNat + tailQWordSum srcPool qm ixS 0 k.toNat)
    (hSrcTC : ∀ t < oC.toNat,
      (∃ idx < s.tn.toNat, dTmC.getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < s.qn.toNat, dTmC.getD t 0#32 = qm.getD qidx 0#32))
    (hevalC : ∀ σ : Nat → Bool,
      polyEval s.n_out.toNat σ srcPool dTmC dTlC dThC oC.toNat =
        nonBxRangeSum s.n_out.toNat σ srcPool srcTm srcTl srcTh bx nb.toNat 0 curC.toNat +
          polyEvalIdxOf s.n_out.toNat σ srcPool qm qlS qhS ixS 0 pi.toNat)
    (hmC : (array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
      array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
      array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
      array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC ⋆ Rro) mC) :
    wp Γ Q X (mergeEmitExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n
      JExit JL o cur bp pi JA a curC qmPtr JC oC curC bpC) mC := by
  rw [hsm, hss, hsl, hsh, hdm, hds, hdl, hdh, hpool_val, hbxPtr, hn]
  dsimp only [mergeEmitExpr, mergeCopyStepExpr, mergeCopyLoopExpr, mergeLoopThenExpr,
    mergeOuterExpr, skip4L64]
  have hpip1 : (pi + 1#32).toNat = pi.toNat + 1 := bv32_succ_toNat (by omega)
  refine wp_join_group (fun (v : Tup Val [i32, i32]) mN =>
      MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat s.ptop.toNat
        srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
        (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
        (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
        dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
        (pi + 1#32).toNat v.2.1.toNat bpC.toNat v.1.toNat mN) ?_ ?_
  · rintro JN ⟨oN, curN, ⟨⟩⟩ mN hinvN
    c0_hfast
    exact hrecL ((k.toNat + 1) - (pi + 1#32).toNat)
      (oN, curN, bpC, pi + 1#32, ⟨⟩) mN (by rw [hpip1]; omega) ⟨rfl, hinvN⟩
  · intro JN hJN
    refine wp_join_group (fun (_ : Tup Val []) mQ => mQ = mC) ?_ ?_
    · rintro JQ ⟨⟩ mQ hmQ
      subst mQ
      have hsubQ := strictIncBelow_cur_sub_bp hinc hbpC_nb hcurC_tn hloC hhiC
      have hoC_lt : oC.toNat < s.tcap.toNat := by omega
      have hoC_p1 : (oC + 1#32).toNat = oC.toNat + 1 := bv32_succ_toNat (by omega)
      have hmC0 : (arCtxMem cx sSort ⋆ array (t := i32) sSort.qm qm ⋆
          array64 sSort.qs qs ⋆ array64 sSort.ql qlS ⋆ array64 sSort.qh qhS ⋆
          array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
          array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
          array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
          array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC ⋆
          array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
          array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R) mC := by
        rw [hRro] at hmC
        rw [← hSort_qm, ← hSort_qs, ← hSort_ql, ← hSort_qh] at hmC
        exact sep_cast hmC (by ac_rfl)
      have ha64 : (BitVec.setWidth 64 a).toNat = a.toNat := by c0_bv_omega
      have hoC64 : (BitVec.setWidth 64 oC).toNat = oC.toNat := by c0_bv_omega
      c0_hfast_nogrp
      refine hJN (oC + 1#32, curC, ⟨⟩) _ ?_
      rw [hpip1, hoC_p1]
      exact merge_push_q_step (qs_a := qs.getD a.toNat 0#64) (ql_a := qlS.getD a.toNat 0#64)
        (qh_a := qhS.getD a.toNat 0#64) hQmOk hQmSorted hQmSig ha_eq ha_lt rfl rfl rfl
        hdC1 hdC2 hdC3 hdC4 hpi_lt hbpC_nb hcurC_tn hoC_le (by omega) (by omega) (by omega)
        (by omega) hloC hhiC hOkC hSortedC hSigC
        hwordsC hSrcTC hevalC (by
          simp only [ha64, hoC64] at hm
          rw [hSort_qm, hSort_qs, hSort_ql, hSort_qh] at hm
          rw [getD_eq_getElem qm 0#32 (by omega), getD_eq_getElem qs 0#64 (by omega),
            getD_eq_getElem qlS 0#64 (by omega), getD_eq_getElem qhS 0#64 (by omega)]
          exact sep_cast hm (by rw [hRro]; ac_rfl))
    · intro JQ hJQ
      c0_hsplit
      · have hcur_lt_tn : curC.toNat < s.tn.toNat := hc; clear hc
        have hcur_tm : curC.toNat < srcTm.length := by omega
        have hcur64 : (BitVec.setWidth 64 curC).toNat = curC.toNat := by c0_bv_omega
        let Rmc := array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
          array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
          array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
          array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC ⋆
          arCtxMem cx sSort ⋆ array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
          array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
          array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R
        have hmC_u := hmC; rw [hRro] at hmC_u
        c0_hstraight
        refine wp_call_of_spec _ _ ?_
        refine hMcmp _ _ _ _ ⟨s.pool.getD s.pc.toNat 0#64, srcPool,
          (srcTm.getD curC.toNat 0#32).toNat, (qm.getD a.toNat 0#32).toNat, Rmc,
          ?_, ?_,
          ⟨Nat.lt_of_lt_of_le (hTmOk curC.toNat hcur_lt_tn).1.1 hptop_le,
            le_trans (hTmOk curC.toNat hcur_lt_tn).1.2 hptop_le⟩,
          ⟨Nat.lt_of_lt_of_le (hQmOk a.toNat ha_lt).1.1 hptop_le,
            le_trans (hQmOk a.toNat ha_lt).1.2 hptop_le⟩,
          (hTmOk curC.toNat hcur_lt_tn).2,
          (by dsimp only [Rmc]; rw [hRro] at hmC; exact sep_cast hmC (by ac_rfl)),
          fun cmp hcmp => ?_⟩
        · simp only [Arg.val, hcur64]
          simpa [getD_eq_getElem srcTm 0#32 hcur_tm] using
            qm_pool_ptr_eq (s.pool.getD s.pc.toNat 0#64)
              (s.pool.getD s.pc.toNat 0#64) srcTm hcur_tm rfl
        · simp only [Arg.val]; exact hqmPtr
        · c0_hsplit
          · have hsym : symListAt srcPool (srcTm.getD curC.toNat 0#32).toNat =
                symListAt srcPool (qm.getD (ixS.getD pi.toNat 0#32).toNat 0#32).toNat := by
              rw [← ha_eq]; exact hcmp hc
            clear hc
            refine wp_join_group (fun (_ : Tup Val []) mK =>
                mK = mC ∧ ¬(bpC.toNat < nb.toNat ∧
                  (bx.getD bpC.toNat 0#32).toNat = curC.toNat)) ?_ ?_
            · rintro JK ⟨⟩ mK ⟨hmK_eq, hne⟩
              subst hmK_eq
              let Rcadd := array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
                array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
                array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
                array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆
                array64 s.qh qhS ⋆ array (t := i32) sSort.ix ixS ⋆
                array (t := i32) s.bx bx ⋆ restM ⋆ R ⋆
                array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
                array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
                array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
                array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC
              have hmC_cadd : (arCtxMem cx sSort ⋆ Rcadd) mK := by
                dsimp only [Rcadd]; rw [hRro] at hmC; exact sep_cast hmC (by ac_rfl)
              have hmC_q := hmC
              rw [hRro, ← hSort_ql, ← hSort_qh] at hmC_q
              c0_hfast
              refine wp_call_of_spec _ _ ?_
              refine hCadd _ _ _ _ ⟨sSort, Rcadd,
                (by rw [hSort_nout, hSort_mlo, hSort_mhi]; exact hMasks), hmC_cadd,
                fun nl nh hcadd => ?_⟩
              have ha64 : (BitVec.setWidth 64 a).toNat = a.toNat := by c0_bv_omega
              have hoC64 : (BitVec.setWidth 64 oC).toNat = oC.toNat := by c0_bv_omega
              have hcadd' : coeff128 s.n_out.toNat nl nh =
                  coeff128 s.n_out.toNat (srcTl.getD curC.toNat 0#64)
                    (srcTh.getD curC.toNat 0#64) +
                  coeff128 s.n_out.toNat (qlS.getD (ixS.getD pi.toNat 0#32).toNat 0#64)
                    (qhS.getD (ixS.getD pi.toNat 0#32).toNat 0#64) := by
                have ha_ql : a.toNat < qlS.length := by omega
                have ha_qh : a.toNat < qhS.length := by omega
                rw [hSort_nout] at hcadd
                simp only [Arg.val, hcur64, ha64] at hcadd
                rw [getD_eq_getElem srcTl 0#64 (by omega),
                  getD_eq_getElem srcTh 0#64 (by omega), ← ha_eq,
                  getD_eq_getElem qlS 0#64 ha_ql,
                  getD_eq_getElem qhS 0#64 ha_qh]
                exact hcadd
              have hcur_p1 : (curC + 1#32).toNat = curC.toNat + 1 :=
                bv32_succ_toNat (by have := htn_le; have := s.tcap.isLt; omega)
              have hsubC := strictIncBelow_cur_sub_bp hinc hbpC_nb hcurC_tn hloC hhiC
              have hoC_lt : oC.toNat < s.tcap.toNat := by omega
              have hoC_p1 : (oC + 1#32).toNat = oC.toNat + 1 := bv32_succ_toNat (by omega)
              refine wp_join_group (fun (v : Tup Val [i32]) mO =>
                  let o' := if nl ≠ 0#64 ∨ nh ≠ 0#64 then oC.toNat + 1 else oC.toNat
                  v.1.toNat = o' ∧
                  (if nl ≠ 0#64 ∨ nh ≠ 0#64 then
                    array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64)
                      (dTmC.set oC.toNat (srcTm.getD curC.toNat 0#32)) ⋆
                    array64 (s.ts.getD (1 - s.tc.toNat) 0#64)
                      (dTsC.set oC.toNat (srcTs.getD curC.toNat 0#64)) ⋆
                    array64 (s.tl.getD (1 - s.tc.toNat) 0#64) (dTlC.set oC.toNat nl) ⋆
                    array64 (s.th.getD (1 - s.tc.toNat) 0#64) (dThC.set oC.toNat nh) ⋆
                    Rro
                  else array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
                    array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
                    array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
                    array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC ⋆ Rro) mO) ?_ ?_
              · rintro JO ⟨oO, ⟨⟩⟩ mO ⟨hoO, hmO⟩
                c0_hfast
                refine hJN (oO, curC + 1#32, ⟨⟩) mO ?_
                rw [hpip1, hcur_p1, hoO]
                exact merge_cadd_step hinc hnb_bx hTmOk hTmSorted hTmSig hsym hcadd' hne hdC1 hdC2
                  hdC3 hdC4 hpi_lt hbpC_nb hcur_lt_tn hoC_le (by omega) (by omega) (by omega)
                  (by omega) rfl hloC hhiC hOkC hSortedC hSigC hwordsC hSrcTC hevalC hmO
              · intro JO hJO
                refine wp_join_group (fun (_ : Tup Val []) mS =>
                    (nl ≠ 0#64 ∨ nh ≠ 0#64) ∧ mS = mK) ?_ ?_
                · rintro Js ⟨⟩ mS ⟨hnz, rfl⟩
                  have hmC_u2 := hmC
                  rw [hRro] at hmC_u2
                  c0_hfast
                  refine hJO (oC + 1#32, ⟨⟩) _ ⟨by simp [hnz, hoC_p1], ?_⟩
                  simp only [hnz, ↓reduceIte, hoC64, hcur64] at *
                  rw [getD_eq_getElem srcTm 0#32 (by omega),
                    getD_eq_getElem srcTs 0#64 (by omega)]
                  exact sep_cast hm (by rw [hRro]; ac_rfl)
                · intro Js hJs
                  c0_hsplit
                  · exact hJs ⟨⟩ mK ⟨Or.inl hc, rfl⟩
                  · c0_hsplit
                    · exact hJs ⟨⟩ mK ⟨Or.inr hc, rfl⟩
                    · have hzero : ¬(nl ≠ 0#64 ∨ nh ≠ 0#64) := by
                        rintro (h1 | h2) <;> c0_bv_omega
                      c0_hfast
                      refine hJO (oC, ⟨⟩) mK ⟨by simp [hzero], ?_⟩
                      simp only [hzero, ↓reduceIte]; exact hmC
            · intro JK hJK
              have hbp64 : (BitVec.setWidth 64 bpC).toNat = bpC.toNat := by c0_bv_omega
              c0_hsplit
              · have hbp_lt : bpC.toNat < nb.toNat := hc
                c0_hsplit
                · c0_hfast; exact hJQ ⟨⟩ mC rfl
                · have hne' : (bx.getD bpC.toNat 0#32).toNat ≠ curC.toNat := by
                    have hbx_get : bx[bpC.toNat]'(by omega) = bx.getD bpC.toNat 0#32 :=
                      (getD_eq_getElem bx 0#32 (by omega)).symm
                    intro h2; apply hc; rw [hbx_get]; exact BitVec.eq_of_toNat_eq h2
                  c0_hfast
                  exact hJK ⟨⟩ mC ⟨rfl, fun ⟨_, heq⟩ => hne' heq⟩
              · have hbp_ge : ¬ bpC.toNat < nb.toNat := by c0_bv_omega
                c0_hfast
                exact hJK ⟨⟩ mC ⟨rfl, by simp [hbp_ge]⟩
          · exact hJQ ⟨⟩ mC rfl
      · exact hJQ ⟨⟩ mC rfl

private theorem merge_products_outer_loop (Γ : T.Env)
    (hGallop : ∀ xs m Q X, arGallopSpec xs m Q X →
      Γ "ar_gallop" [i64, i64, i32, i32, i64] [i32] xs m Q X)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx sm ss sl sh dm ds dl dh pool bxPtr : Val i64} {nb k sidx didx n : Val i32}
    {Q : Post []} {X : XPost} {s sSort : ArCtxState}
    {srcPool srcTm qm ixS ix2S bx dstTm0 : List (BitVec 32)}
    {qs srcTs srcTl srcTh qlS qhS dstTs0 dstTl0 dstTh0 : List (BitVec 64)}
    {restM R Rro : Mem 64 → Prop}
    {JExit : Cont [i32, i32, i32, i32]} {mS : Mem 64}
    (hExit : ∀ (ys : Tup Val [i32, i32, i32, i32]) (mE : Mem 64),
      (ys.2.2.2.1 = k ∧ ys.2.1 = s.tn ∧
        MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat s.ptop.toNat
          srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
          (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
          (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
          dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
          ys.2.2.2.1.toNat ys.2.1.toNat ys.2.2.1.toNat ys.1.toNat mE) →
      JExit ys mE)
    (hsm : sm = s.tm.getD s.tc.toNat 0#64) (hss : ss = s.ts.getD s.tc.toNat 0#64)
    (hsl : sl = s.tl.getD s.tc.toNat 0#64) (hsh : sh = s.th.getD s.tc.toNat 0#64)
    (hdm : dm = s.tm.getD (1 - s.tc.toNat) 0#64)
    (hds : ds = s.ts.getD (1 - s.tc.toNat) 0#64)
    (hdl : dl = s.tl.getD (1 - s.tc.toNat) 0#64)
    (hdh : dh = s.th.getD (1 - s.tc.toNat) 0#64)
    (hpool_val : pool = s.pool.getD s.pc.toNat 0#64)
    (hbxPtr : bxPtr = s.bx) (hn : n = s.tn)
    (_hSort_tn : sSort.tn = s.tn) (_hSort_bx : sSort.bx = s.bx)
    (hSort_qm : sSort.qm = s.qm) (hSort_qs : sSort.qs = s.qs)
    (hSort_ql : sSort.ql = s.ql) (hSort_qh : sSort.qh = s.qh)
    (hSort_nout : sSort.n_out = s.n_out) (hSort_mlo : sSort.mlo = s.mlo)
    (hSort_mhi : sSort.mhi = s.mhi)
    (hRro : Rro = arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
      array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R)
    (hptop_le : s.ptop.toNat ≤ srcPool.length)
    (hk_qn : k.toNat ≤ s.qn.toNat) (htn_le : s.tn.toNat ≤ s.tcap.toNat)
    (hqn_le : s.qn.toNat ≤ s.qcap.toNat)
    (hcap_sum : (s.tn.toNat - nb.toNat) + s.qn.toNat ≤ s.tcap.toNat)
    (hnb_bx : nb.toNat ≤ bx.length) (hinc : strictIncBelow bx nb.toNat s.tn.toNat)
    (hsrcTm_len : s.tcap.toNat ≤ srcTm.length) (hsrcTs_len : s.tcap.toNat ≤ srcTs.length)
    (hsrcTl_len : s.tcap.toNat ≤ srcTl.length) (hsrcTh_len : s.tcap.toNat ≤ srcTh.length)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hqs_len : s.qcap.toNat ≤ qs.length)
    (hqlS_len : s.qcap.toNat ≤ qlS.length) (hqhS_len : s.qcap.toNat ≤ qhS.length)
    (hdstTm_len : s.tcap.toNat ≤ dstTm0.length) (hdstTs_len : s.tcap.toNat ≤ dstTs0.length)
    (hdstTl_len : s.tcap.toNat ≤ dstTl0.length) (hdstTh_len : s.tcap.toNat ≤ dstTh0.length)
    (hMasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hTmOk : ∀ t < s.tn.toNat, MonoSliceOk srcPool (srcTm.getD t 0#32).toNat s.ptop.toNat ∧
      (srcPool.getD (srcTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hQmOk : ∀ t < s.qn.toNat, MonoSliceOk srcPool (qm.getD t 0#32).toNat s.ptop.toNat ∧
      (srcPool.getD (qm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hTmSorted : ∀ t < s.tn.toNat, MonoSorted srcPool (srcTm.getD t 0#32).toNat)
    (hQmSorted : ∀ t < s.qn.toNat, MonoSorted srcPool (qm.getD t 0#32).toNat)
    (hTmSig : SigOk srcPool srcTm srcTs s.tn.toNat)
    (hQmSig : SigOk srcPool qm qs s.qn.toNat)
    (hix_lt : ∀ p < k.toNat, (ixS.getD p 0#32).toNat < s.qn.toNat)
    (hix_len : s.qcap.toNat ≤ ixS.length) (_hix2_len : s.qcap.toNat ≤ ix2S.length)
    (hmS0 : (arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dstTm0 ⋆
      array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dstTs0 ⋆
      array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dstTl0 ⋆
      array64 (s.th.getD (1 - s.tc.toNat) 0#64) dstTh0 ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
      array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R) mS) :
    wp Γ Q X (mergeOuterExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n
      JExit) mS := by
  dsimp only [mergeOuterExpr, skip4L64]
  refine wp_loop_group (fun prem (v : Tup Val [i32, i32, i32, i32]) mL =>
      let (o, cur, bp, pi, _) := v
      prem = (k.toNat + 1) - pi.toNat ∧
      MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat s.ptop.toNat
        srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
        (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
        (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
        dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
        pi.toNat cur.toNat bp.toNat o.toNat mL) ?_ ?_
  · intro JL prem ⟨o, cur, bp, pi, ⟨⟩⟩ mL hrecL ⟨hprem, dTm, dTs, dTl, dTh,
        hd1, hd2, hd3, hd4, hpi_k, hbp_nb, hcur_tn, ho_le, hlo, hhi,
        hOk, hSorted, hSig, hwords, hSrcT, heval, hmL⟩
    c0_hsplit
    · clear hc
      refine wp_join_group (fun (v : Tup Val [i32, i32, i64]) mA =>
          let (a, j, qmPtr, _) := v
          mA = mL ∧ cur.toNat ≤ j.toNat ∧ j.toNat ≤ s.tn.toNat ∧
          (pi.toNat < k.toNat →
            a = ixS.getD pi.toNat 0#32 ∧ a.toNat < s.qn.toNat ∧
            qmPtr = s.pool.getD s.pc.toNat 0#64 +
              BitVec.ofNat 64 (4 * (qm.getD a.toNat 0#32).toNat)) ∧
          (pi.toNat = k.toNat → j = s.tn)) ?_ ?_
      · rintro JA ⟨a, j, qmPtr, ⟨⟩⟩ mA ⟨hmA, hcur_j, hj_tn, ha_spec, hjk_spec⟩
        subst mA
        refine wp_loop_group (fun crem (v : Tup Val [i32, i32, i32]) mC =>
            let (oC, curC, bpC, _) := v
            crem = j.toNat - curC.toNat ∧ cur.toNat ≤ curC.toNat ∧ curC.toNat ≤ j.toNat ∧
            MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat
              s.ptop.toNat srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
              (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
              (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
              dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
              pi.toNat curC.toNat bpC.toNat oC.toNat mC) ?_ ?_
        · intro JC crem ⟨oC, curC, bpC, ⟨⟩⟩ mC hrecC
            ⟨hcrem, hcur_C, hC_j, dTmC, dTsC, dTlC, dThC, hdC1, hdC2, hdC3, hdC4,
              _, hbpC_nb, hcurC_tn, hoC_le, hloC, hhiC,
              hOkC, hSortedC, hSigC, hwordsC, hSrcTC, hevalC, hmC⟩
          c0_hsplit
          · have hcurC_lt : curC.toNat < j.toNat := hc; clear hc
            have hrecC' : ∀ (crem' : Nat) (ys : Tup Val [i32, i32, i32]) (m' : Mem 64),
                crem' < j.toNat - curC.toNat →
                crem' = j.toNat - ys.2.1.toNat ∧ cur.toNat ≤ ys.2.1.toNat ∧
                  ys.2.1.toNat ≤ j.toNat ∧
                  MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat
                    s.ptop.toNat srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
                    (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
                    (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
                    dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
                    pi.toNat ys.2.1.toNat ys.2.2.1.toNat ys.1.toNat m' →
                JC ys m' := by
              intro crem' ⟨o', cur', bp', ⟨⟩⟩ m' hlt hinv
              rw [← hcrem] at hlt
              exact hrecC crem' _ m' hlt hinv
            change wp Γ Q X (mergeCopyStepExpr cx nb k sidx didx sm ss sl sh dm ds dl dh
              pool bxPtr n JExit JL o cur bp pi JA a j qmPtr JC oC curC bpC) mC
            exact merge_products_copy_step Γ hrecC' hsm hss hsl hsh hdm hds hdl hdh
              hbxPtr hRro htn_le hk_qn hcap_sum hnb_bx hinc
              hsrcTm_len hsrcTs_len hsrcTl_len hsrcTh_len hTmOk hTmSorted hTmSig hcur_C hcurC_lt
              hj_tn hdC1 hdC2 hdC3 hdC4 hdstTm_len hdstTs_len hdstTl_len hdstTh_len
              hpi_k hbpC_nb hcurC_tn hoC_le hloC hhiC hOkC hSortedC hSigC
              hwordsC hSrcTC hevalC hmC
          · have hC_eq : curC = j := BitVec.eq_of_toNat_eq
              (by have := BitVec.not_lt.mp hc; omega)
            subst hC_eq; clear hc
            c0_hsplit
            · have hpi_eq : pi = k := BitVec.eq_of_toNat_eq (by c0_bv_omega)
              have hjk_eq : curC = s.tn := hjk_spec (by rw [hpi_eq])
              c0_hfast
              exact hExit (oC, curC, bpC, pi, ⟨⟩) mC ⟨hpi_eq, hjk_eq,
                dTmC, dTsC, dTlC, dThC, hdC1, hdC2, hdC3, hdC4,
                hpi_k, hbpC_nb, hcurC_tn, hoC_le, hloC, hhiC,
                hOkC, hSortedC, hSigC, hwordsC, hSrcTC, hevalC, hmC⟩
            · have hpi_lt : pi.toNat < k.toNat :=
                Nat.lt_of_le_of_ne hpi_k (fun h => hc (BitVec.eq_of_toNat_eq h))
              clear hc
              obtain ⟨ha_eq, ha_lt, hqm_ptr⟩ := ha_spec hpi_lt
              have hrecL' : ∀ (prem' : Nat) (ys : Tup Val [i32, i32, i32, i32]) (m' : Mem 64),
                  prem' < k.toNat + 1 - pi.toNat →
                  prem' = k.toNat + 1 - ys.2.2.2.1.toNat ∧
                  MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat
                    s.ptop.toNat srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
                    (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
                    (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
                    dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
                    ys.2.2.2.1.toNat ys.2.1.toNat ys.2.2.1.toNat ys.1.toNat m' →
                  JL ys m' := by
                intro prem' ⟨o', cur', bp', pi', ⟨⟩⟩ m' hlt hinv
                rw [← hprem] at hlt
                exact hrecL prem' _ m' hlt hinv
              change wp Γ Q X (mergeEmitExpr cx nb k sidx didx sm ss sl sh dm ds dl dh
                pool bxPtr n JExit JL o cur bp pi JA a curC qmPtr JC oC curC bpC) mC
              exact merge_products_emit_phase Γ hMcmp hCadd hrecL' hsm hss hsl hsh
                hdm hds hdl hdh hpool_val hbxPtr hn hSort_qm hSort_qs hSort_ql hSort_qh
                hSort_nout hSort_mlo hSort_mhi hRro hptop_le hk_qn htn_le hqn_le hcap_sum hnb_bx
                hinc hsrcTm_len hsrcTs_len hsrcTl_len hsrcTh_len hqm_len hqs_len hqlS_len hqhS_len
                hMasks hTmOk hQmOk hTmSorted hQmSorted hTmSig hQmSig hpi_lt ha_eq ha_lt hqm_ptr
                hdC1 hdC2 hdC3 hdC4 hdstTm_len hdstTs_len hdstTl_len hdstTh_len hbpC_nb hcurC_tn
                hoC_le hloC hhiC hOkC hSortedC hSigC hwordsC hSrcTC hevalC hmC
        · intro JC hJC
          c0_hfast
          exact hJC (j.toNat - cur.toNat) (o, cur, bp, ⟨⟩) mL
            ⟨rfl, le_refl _, hcur_j, dTm, dTs, dTl, dTh, hd1, hd2, hd3, hd4,
              hpi_k, hbp_nb, hcur_tn, ho_le, hlo, hhi, hOk, hSorted, hSig,
              hwords, hSrcT, heval, hmL⟩
      · intro JA hJA
        c0_hsplit
        · have hpi_lt : pi.toNat < k.toNat := hc; clear hc
          have ha_lt : (ixS[pi.toNat]'(by omega)).toNat < s.qn.toNat := by
            rw [← getD_eq_getElem ixS 0#32 (by omega)]; exact hix_lt pi.toNat hpi_lt
          have ha_qm : (ixS[pi.toNat]'(by omega)).toNat < qm.length := by omega
          let Rgal := arCtxMem cx sSort ⋆ array (t := i32) s.qm qm ⋆
            array (t := i32) sSort.ix ixS ⋆
            array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTm ⋆
            array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTs ⋆
            array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTl ⋆
            array64 (s.th.getD (1 - s.tc.toNat) 0#64) dTh ⋆
            array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
            array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
            array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
            array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
            array (t := i32) s.bx bx ⋆ restM ⋆ R
          have hmL_gal : (array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
              array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆ Rgal) mL := by
            rw [hRro] at hmL; dsimp only [Rgal]; exact sep_cast hmL (by ac_rfl)
          have hpi64 : (BitVec.setWidth 64 pi).toNat = pi.toNat := by c0_bv_omega
          rw [hsm, hpool_val, hn]
          have hmL_u := hmL; rw [hRro, ← hSort_qm] at hmL_u
          c0_hstraight
          refine wp_call_of_spec _ _ ?_
          refine hGallop _ _ _ _
            ⟨srcTm, srcPool, (qm.getD (ixS.getD pi.toNat 0#32).toNat 0#32).toNat, Rgal,
              hcur_tn, (by simpa only [Arg.val] using Nat.le_trans htn_le hsrcTm_len), ?_,
              by rw [getD_eq_getElem ixS 0#32 (by omega)]
                 exact ⟨Nat.lt_of_lt_of_le (hQmOk _ ha_lt).1.1 hptop_le,
                   le_trans (hQmOk _ ha_lt).1.2 hptop_le⟩,
              by rw [getD_eq_getElem ixS 0#32 (by omega)]; exact (hQmOk _ ha_lt).2,
              fun i hi => ⟨⟨Nat.lt_of_lt_of_le (hTmOk i hi).1.1 hptop_le,
                le_trans (hTmOk i hi).1.2 hptop_le⟩, (hTmOk i hi).2⟩,
              hmL_gal, fun j hcur_j hj_tn => ?_⟩
          · have hix_sw : (BitVec.setWidth 64 (ixS[pi.toNat]'(by omega))).toNat =
                (ixS[pi.toNat]'(by omega)).toNat := by c0_bv_omega
            simp only [Arg.val, hpi64, hix_sw]
            rw [getD_eq_getElem ixS 0#32 (by omega), getD_eq_getElem qm 0#32 ha_qm]
            congr 1; c0_bv_omega
          c0_hfast
          simp only [Arg.val] at hcur_j hj_tn
          refine hJA (_, j, _, ⟨⟩) mL ⟨rfl, hcur_j, hj_tn,
            fun _ => ⟨(by simp only [hpi64]
                          exact (getD_eq_getElem ixS 0#32 (by omega)).symm),
              by simp only [hpi64]; exact ha_lt,
              by have hix_sw : (BitVec.setWidth 64 (ixS[pi.toNat]'(by omega))).toNat =
                     (ixS[pi.toNat]'(by omega)).toNat := by c0_bv_omega
                 simp only [hpi64, hix_sw]
                 rw [getD_eq_getElem qm 0#32 ha_qm]
                 congr 1; c0_bv_omega⟩,
            fun h => absurd hpi_lt (by rw [h]; exact Nat.lt_irrefl _)⟩
        · have hpi_eq : pi.toNat = k.toNat := by
            have hnot : ¬ pi.toNat < k.toNat := by c0_bv_omega
            omega
          c0_hfast
          exact hJA (0#32, n, 0#64, ⟨⟩) mL
            ⟨rfl, by rw [hn]; exact hcur_tn, by rw [hn]; exact le_refl _,
              fun h => absurd h (by omega), fun _ => hn⟩
    · exfalso; exact absurd hpi_k hc
  · intro JL hJL
    c0_hfast
    exact hJL (k.toNat + 1) (0#32, 0#32, 0#32, 0#32, ⟨⟩) mS ⟨rfl, dstTm0,
      dstTs0, dstTl0, dstTh0, rfl, rfl, rfl, rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _, fun _ hp => by rw [BitVec.toNat_zero] at hp; omega,
      fun _ => Nat.zero_le _, fun _ ht => by rw [BitVec.toNat_zero] at ht; omega,
      fun _ ht => by rw [BitVec.toNat_zero] at ht; omega, sigOk_empty _ _ _,
      (by simp only [BitVec.toNat_zero, tailWordSum_zero, monoTotalWords, List.range_zero,
        List.foldl_nil, Nat.zero_add]; exact le_refl _),
      (fun _ h0 => absurd h0 (Nat.not_lt_zero _)),
      (fun _ => by simp [nonBxRangeSum, polyEval, polyEvalRange, polyEvalIdxOf]),
      sep_cast hmS0 (by rw [hRro]; ac_rfl)⟩

public theorem ar_merge_products_wp (Γ : T.Env)
    (hSort : ∀ xs m Q X, arSortCombineSpec xs m Q X → Γ "ar_sort_combine" [i64] [i32] xs m Q X)
    (hGallop : ∀ xs m Q X, arGallopSpec xs m Q X →
      Γ "ar_gallop" [i64, i64, i32, i32, i64] [i32] xs m Q X)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X) :
    ∀ xs m Q X, arMergeProductsSpec xs m Q X → Func.wp Γ ar_merge_products_body xs m Q X := by
  rintro ⟨cx, nb, ⟨⟩⟩ m Q X
    ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
      qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, R,
      hpc, htc, htn_le, hqn_le, hptop_cap, htcap30, hqcap32, hcap_sum, hnb_tn, hnb_bx, hinc,
      htm0_len, htm1_len, hts0_len, htl0_len, hth0_len, hts1_len, htl1_len, hth1_len,
      hp0_len, hp1_len, hqm_len, hqs_len, hql_len, hqh_len, hix_len, hix2_len,
      hMasks, hTmOk, hQmOk, hTmSorted, hQmSorted, hTmSig, hQmSig, hm, hQ⟩
  have hptop_le : s.ptop.toNat ≤ (if s.pc.toNat = 0 then pool0 else pool1).length := by
    split <;> omega
  c0_hsteps
  refine wp_call_of_spec _ _ (hSort ⟨cx, ⟨⟩⟩ m _ X
    ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
      qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, R,
      hpc, hqn_le, hqcap32, hp0_len, hp1_len, hqm_len, hqs_len, hql_len, hqh_len,
      hix_len, hix2_len, hMasks,
      (fun i hi => ⟨⟨Nat.lt_of_lt_of_le (hQmOk i hi).1.1 hptop_le,
        le_trans (hQmOk i hi).1.2 hptop_le⟩, (hQmOk i hi).2⟩),
      hm,
      fun k sSort qlS qhS ixS ix2S mS hk_qn hqlS_len hqhS_len hixS_len hix2S_len
        hix_ptrs hsSort hix_lt hix_nd hq_eval hmS => ?_⟩)
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  let srcTm := if s.tc.toNat = 0 then tm0 else tm1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  let dstTm0 := if s.tc.toNat = 0 then tm1 else tm0
  let dstTs0 := if s.tc.toNat = 0 then ts1 else ts0
  let dstTl0 := if s.tc.toNat = 0 then tl1 else tl0
  let dstTh0 := if s.tc.toNat = 0 then th1 else th0
  have hSort_pc : sSort.pc = s.pc := by rw [hsSort]
  have hSort_tc : sSort.tc = s.tc := by rw [hsSort]
  have hSort_tn : sSort.tn = s.tn := by rw [hsSort]
  have hSort_pool : sSort.pool = s.pool := by rw [hsSort]
  have hSort_tm : sSort.tm = s.tm := by rw [hsSort]
  have hSort_ts : sSort.ts = s.ts := by rw [hsSort]
  have hSort_tl : sSort.tl = s.tl := by rw [hsSort]
  have hSort_th : sSort.th = s.th := by rw [hsSort]
  obtain ⟨restM, hmS_eq, hfocM⟩ := tqMem_merge_focus sSort tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
    pool0 pool1 qm qs qlS qhS ixS ix2S bx vqOff vq vqSkip
    (by rw [hSort_pc]; exact hpc) (by rw [hSort_tc]; exact htc)
  have hl_sS : ArCtxLengthsOk sSort := arCtxMem_lengths4 hmS
  have hmS0 : (arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dstTm0 ⋆
      array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dstTs0 ⋆
      array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dstTl0 ⋆
      array64 (s.th.getD (1 - s.tc.toNat) 0#64) dstTh0 ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
      array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R) mS := by
    have h' : ((tMem sSort tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem sSort qm qs qlS qhS ixS ix2S bx vqOff vq vqSkip) ⋆ (arCtxMem cx sSort ⋆ R)) mS :=
      sep_cast hmS (by ac_rfl)
    rw [hmS_eq] at h'
    simp only [hSort_pc, hSort_tc, hSort_pool, hSort_tm, hSort_ts, hSort_tl, hSort_th,
      show sSort.qm = s.qm by rw [hsSort], show sSort.qs = s.qs by rw [hsSort],
      show sSort.ql = s.ql by rw [hsSort], show sSort.qh = s.qh by rw [hsSort],
      show sSort.bx = s.bx by rw [hsSort]] at h'
    exact sep_cast h' (by ac_rfl)
  have hdstTm_len : s.tcap.toNat ≤ dstTm0.length := by dsimp only [dstTm0]; split <;> assumption
  have hdstTs_len : s.tcap.toNat ≤ dstTs0.length := by dsimp only [dstTs0]; split <;> assumption
  have hdstTl_len : s.tcap.toNat ≤ dstTl0.length := by dsimp only [dstTl0]; split <;> assumption
  have hdstTh_len : s.tcap.toNat ≤ dstTh0.length := by dsimp only [dstTh0]; split <;> assumption
  have hsrcTm_len : s.tcap.toNat ≤ srcTm.length := by dsimp only [srcTm]; split <;> assumption
  have hsrcTl_len : s.tcap.toNat ≤ srcTl.length := by dsimp only [srcTl]; split <;> assumption
  have hsrcTh_len : s.tcap.toNat ≤ srcTh.length := by dsimp only [srcTh]; split <;> assumption
  have hdidx : (s.tc ^^^ 1#32).toNat = 1 - s.tc.toNat := by
    rcases bv32_lt2_cases htc with h0 | h0 <;> simp [h0]
  have hpool_pc : sSort.pool[sSort.pc.toNat]'(by rw [hl_sS.pool, hSort_pc]; exact hpc) =
      s.pool.getD s.pc.toNat 0#64 := by
    rw [← getD_eq_getElem sSort.pool 0#64 (by rw [hl_sS.pool, hSort_pc]; exact hpc),
      hSort_pool, hSort_pc]
  let Rro := arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
    array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
    array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
    array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
    array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R
  clear hmS
  have hSort_didx : (sSort.tc ^^^ 1#32).toNat = 1 - s.tc.toNat := by
    rw [hSort_tc]; exact hdidx
  have hs_pc_lt : sSort.pc.toNat < 2 := by rw [hSort_pc]; exact hpc
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  c0_hfast_nogrp
  refine wp_join_group (fun (v : Tup Val [i32, i32, i32, i32]) mE =>
      let (o, cur, bp, pi, _) := v
      pi = k ∧ cur = s.tn ∧
      MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.n_out.toNat s.ptop.toNat
        srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
        (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
        (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
        dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
        pi.toNat cur.toNat bp.toNat o.toNat mE)
    ?_ ?_
  · rintro JExit ⟨o, cur, bp, pi, ⟨⟩⟩ mE ⟨rfl, rfl, dTm, dTs, dTl, dTh,
        hd1, hd2, hd3, hd4, _, hbp, _, ho_le, _, hhi,
        hOk, hSorted, hSig, hwords, hSrcT, heval, hmE⟩
    have hbp_eq : bp.toNat = nb.toNat := merge_bx_all_visited hinc hbp hhi
    have ho_sum : o.toNat ≤ (s.tn.toNat - nb.toNat) + s.qn.toNat := by omega
    have hmE0 : (array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTm ⋆
        array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTs ⋆
        array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTl ⋆
        array64 (s.th.getD (1 - s.tc.toNat) 0#64) dTh ⋆
        arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
        array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R) mE := by
      dsimp only [Rro, srcTs] at hmE; exact sep_cast hmE (by ac_rfl)
    c0_hfast
    let sF : ArCtxState := { sSort with tc := sSort.tc ^^^ 1#32, tn := o }
    have hmF : (arCtxMem cx sF ⋆
        tMem sF (if s.tc.toNat = 0 then tm0 else dTm) (if s.tc.toNat = 0 then dTm else tm1)
          (if s.tc.toNat = 0 then ts0 else dTs) (if s.tc.toNat = 0 then tl0 else dTl)
          (if s.tc.toNat = 0 then th0 else dTh) (if s.tc.toNat = 0 then dTs else ts1)
          (if s.tc.toNat = 0 then dTl else tl1) (if s.tc.toNat = 0 then dTh else th1) pool0 pool1 ⋆
        qMem sF qm qs qlS qhS ixS ix2S bx vqOff vq vqSkip ⋆ R) m := by
      have hfoc' := hfocM sF dTm dTs dTl dTh rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl
        (by dsimp only [dstTm0] at hd1; rw [hSort_tc]; exact hd1)
        (by dsimp only [dstTs0] at hd2; rw [hSort_tc]; exact hd2)
        (by dsimp only [dstTl0] at hd3; rw [hSort_tc]; exact hd3)
        (by dsimp only [dstTh0] at hd4; rw [hSort_tc]; exact hd4)
      simp only [hSort_pc, hSort_tc, hSort_pool, hSort_tm, hSort_ts, hSort_tl, hSort_th,
        show sSort.qm = s.qm by rw [hsSort], show sSort.qs = s.qs by rw [hsSort],
        show sSort.ql = s.ql by rw [hsSort], show sSort.qh = s.qh by rw [hsSort],
        show sSort.bx = s.bx by rw [hsSort]] at hfoc'
      have h' : (arCtxMem cx sF ⋆ (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
          array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTm ⋆
          array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTs ⋆
          array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTl ⋆
          array64 (s.th.getD (1 - s.tc.toNat) 0#64) dTh ⋆
          array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆
          array64 s.qh qhS ⋆ array (t := i32) sSort.ix ixS ⋆
          array (t := i32) s.bx bx ⋆ restM) ⋆ R) m :=
        sep_cast hm (by dsimp only [sF, srcTs]; ac_rfl)
      rw [← hfoc'] at h'; exact sep_cast h' (by ac_rfl)
    have hwords_done : monoTotalWords srcPool dTm o.toNat ≤
        monoTotalWords srcPool srcTm s.tn.toNat + monoTotalWords srcPool qm s.qn.toNat := by
      simp only [tailWordSum_nil, tailQWordSum_nil, Nat.add_zero] at hwords
      exact le_trans hwords (Nat.add_le_add_left (tailQWordSum_zero_le hix_nd hix_lt) _)
    have hSb_done : ∀ bd : Nat, SymsBound srcPool srcTm s.tn.toNat bd →
        SymsBound srcPool qm s.qn.toNat bd → SymsBound srcPool dTm o.toNat bd := by
      intro bd hSbT hSbQ i hi x hx
      rcases hSrcT i hi with ⟨idx, hidx, heq⟩ | ⟨qidx, hqidx, heq⟩
      · rw [heq] at hx; exact hSbT idx hidx x hx
      · rw [heq] at hx; exact hSbQ qidx hqidx x hx
    have heval_done : ∀ σ : Nat → Bool,
        polyEval s.n_out.toNat σ srcPool dTm dTl dTh o.toNat =
          nonBxTermSum s.n_out.toNat σ srcPool srcTm srcTl srcTh bx nb.toNat s.tn.toNat +
            polyEval s.n_out.toNat σ srcPool qm ql qh s.qn.toNat := fun σ => by
      rw [heval σ, hq_eval σ]; rfl
    have hsF_tc : sF.tc.toNat = 1 - s.tc.toNat := by dsimp only [sF]; rw [hSort_tc]; exact hdidx
    have hsF_eq : sF = { s with tc := sF.tc, tn := sF.tn, ix := sF.ix, ix2 := sF.ix2 } := by
      dsimp only [sF]; rw [hsSort]
    have hixS_swap : (sF.ix = s.ix ∧ sF.ix2 = s.ix2 ∧
          ixS.length = ix.length ∧ ix2S.length = ix2.length) ∨
        (sF.ix = s.ix2 ∧ sF.ix2 = s.ix ∧
          ixS.length = ix2.length ∧ ix2S.length = ix.length) := by
      simpa [sF] using hix_ptrs
    refine hQ sF _ _ _ _ _ _ _ _ qlS qhS ixS ix2S _ hsF_tc ho_sum
      (by exact le_trans ho_sum hcap_sum) hsF_eq ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ hqlS_len hqhS_len hixS_swap hixS_len hix2S_len ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmF
    · split <;> simp only [dstTm0, *, ↓reduceIte] at hd1 ⊢ <;> first | rfl | exact hd1
    · split <;> simp only [dstTm0, *, ↓reduceIte] at hd1 ⊢ <;> first | rfl | exact hd1
    · split <;> simp only [dstTs0, *, ↓reduceIte] at hd2 ⊢ <;> first | rfl | exact hd2
    · split <;> simp only [dstTl0, *, ↓reduceIte] at hd3 ⊢ <;> first | rfl | exact hd3
    · split <;> simp only [dstTh0, *, ↓reduceIte] at hd4 ⊢ <;> first | rfl | exact hd4
    · split <;> simp only [dstTs0, *, ↓reduceIte] at hd2 ⊢ <;> first | rfl | exact hd2
    · split <;> simp only [dstTl0, *, ↓reduceIte] at hd3 ⊢ <;> first | rfl | exact hd3
    · split <;> simp only [dstTh0, *, ↓reduceIte] at hd4 ⊢ <;> first | rfl | exact hd4
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · intro i hi
      rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool] using hOk i hi
    · intro i hi
      rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool] using hSorted i hi
    · rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool] using hSig
    · rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool, srcTm] using hwords_done
    · intro bd hSbT hSbQ i hi x hx
      rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool, srcTm] using
          hSb_done bd (by simpa [hp, ht, srcPool, srcTm] using hSbT)
            (by simpa [hp, ht, srcPool] using hSbQ) i hi x
            (by simpa [hp, ht, srcPool] using hx)
    · rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool, srcTm, srcTl, srcTh] using heval_done
  · intro JExit hExit
    have hSort_qm : sSort.qm = s.qm := by rw [hsSort]
    have hSort_qs : sSort.qs = s.qs := by rw [hsSort]
    have hSort_ql : sSort.ql = s.ql := by rw [hsSort]
    have hSort_qh : sSort.qh = s.qh := by rw [hsSort]
    have hSort_nout : sSort.n_out = s.n_out := by rw [hsSort]
    have hSort_mlo : sSort.mlo = s.mlo := by rw [hsSort]
    have hSort_mhi : sSort.mhi = s.mhi := by rw [hsSort]
    have hSort_bx : sSort.bx = s.bx := by rw [hsSort]
    have hRro_eq : Rro = arCtxMem cx sSort ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
        array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆
        array64 s.qh qhS ⋆ array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆
        restM ⋆ R := rfl
    have hs_ts_len : s.tcap.toNat ≤ srcTs.length := by dsimp only [srcTs]; split <;> assumption
    have hsm : sSort.tm[sSort.tc.toNat]'(by rw [hl_sS.tm, hSort_tc]; omega) =
        s.tm.getD s.tc.toNat 0#64 := by
      rw [← getD_eq_getElem sSort.tm 0#64 (by rw [hl_sS.tm, hSort_tc]; omega), hSort_tm, hSort_tc]
    have hss : sSort.ts[sSort.tc.toNat]'(by rw [hl_sS.ts, hSort_tc]; omega) =
        s.ts.getD s.tc.toNat 0#64 := by
      rw [← getD_eq_getElem sSort.ts 0#64 (by rw [hl_sS.ts, hSort_tc]; omega), hSort_ts, hSort_tc]
    have hsl : sSort.tl[sSort.tc.toNat]'(by rw [hl_sS.tl, hSort_tc]; omega) =
        s.tl.getD s.tc.toNat 0#64 := by
      rw [← getD_eq_getElem sSort.tl 0#64 (by rw [hl_sS.tl, hSort_tc]; omega), hSort_tl, hSort_tc]
    have hsh : sSort.th[sSort.tc.toNat]'(by rw [hl_sS.th, hSort_tc]; omega) =
        s.th.getD s.tc.toNat 0#64 := by
      rw [← getD_eq_getElem sSort.th 0#64 (by rw [hl_sS.th, hSort_tc]; omega), hSort_th, hSort_tc]
    have hdm : sSort.tm[(sSort.tc ^^^ 1#32).toNat]'(by rw [hl_sS.tm, hSort_didx]; omega) =
        s.tm.getD (1 - s.tc.toNat) 0#64 := by
      rw [← getD_eq_getElem sSort.tm 0#64 (by rw [hl_sS.tm, hSort_didx]; omega),
        hSort_tm, hSort_didx]
    have hds : sSort.ts[(sSort.tc ^^^ 1#32).toNat]'(by rw [hl_sS.ts, hSort_didx]; omega) =
        s.ts.getD (1 - s.tc.toNat) 0#64 := by
      rw [← getD_eq_getElem sSort.ts 0#64 (by rw [hl_sS.ts, hSort_didx]; omega),
        hSort_ts, hSort_didx]
    have hdl : sSort.tl[(sSort.tc ^^^ 1#32).toNat]'(by rw [hl_sS.tl, hSort_didx]; omega) =
        s.tl.getD (1 - s.tc.toNat) 0#64 := by
      rw [← getD_eq_getElem sSort.tl 0#64 (by rw [hl_sS.tl, hSort_didx]; omega),
        hSort_tl, hSort_didx]
    have hdh : sSort.th[(sSort.tc ^^^ 1#32).toNat]'(by rw [hl_sS.th, hSort_didx]; omega) =
        s.th.getD (1 - s.tc.toNat) 0#64 := by
      rw [← getD_eq_getElem sSort.th 0#64 (by rw [hl_sS.th, hSort_didx]; omega),
        hSort_th, hSort_didx]
    change wp Γ Q X (mergeOuterExpr cx nb k sSort.tc (sSort.tc ^^^ 1#32)
      (sSort.tm[sSort.tc.toNat]'_) (sSort.ts[sSort.tc.toNat]'_)
      (sSort.tl[sSort.tc.toNat]'_) (sSort.th[sSort.tc.toNat]'_)
      (sSort.tm[(sSort.tc ^^^ 1#32).toNat]'_) (sSort.ts[(sSort.tc ^^^ 1#32).toNat]'_)
      (sSort.tl[(sSort.tc ^^^ 1#32).toNat]'_) (sSort.th[(sSort.tc ^^^ 1#32).toNat]'_)
      (sSort.pool[sSort.pc.toNat]'(by rw [hl_sS.pool, hSort_pc]; exact hpc))
        sSort.bx sSort.tn JExit) mS
    exact merge_products_outer_loop Γ hGallop hMcmp hCadd hExit hsm hss hsl hsh hdm hds hdl hdh
      hpool_pc hSort_bx hSort_tn hSort_tn hSort_bx hSort_qm hSort_qs hSort_ql hSort_qh
      hSort_nout hSort_mlo hSort_mhi hRro_eq hptop_le
      hk_qn htn_le hqn_le hcap_sum hnb_bx hinc hsrcTm_len hs_ts_len hsrcTl_len hsrcTh_len
      hqm_len hqs_len (by rw [hqlS_len]; exact hql_len) (by rw [hqhS_len]; exact hqh_len)
      hdstTm_len hdstTs_len hdstTl_len hdstTh_len
      hMasks hTmOk hQmOk hTmSorted hQmSorted
      (by rcases bv32_lt2_cases hpc with hp | hp <;> rcases bv32_lt2_cases htc with ht | ht <;>
        simpa [hp, ht, srcPool, srcTm, srcTs] using hTmSig)
      (by rcases bv32_lt2_cases hpc with hp | hp <;> simpa [hp, srcPool] using hQmSig)
      hix_lt hixS_len hix2S_len hmS0

end LeanQbe.T.Examples.Arisca.Proof

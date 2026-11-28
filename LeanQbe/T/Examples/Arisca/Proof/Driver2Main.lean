/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver2MainBase
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Top-Level `n_main` Loop (`Arisca.Proof.Driver2Main`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for the `n_main` replay/flip loop and
final `pos == nw` / `tn == 0` checks of `ar_check_main` (`main_main_loop_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open LeanQbe.T.Examples.Arisca.Src.Driver

public section

private theorem main_even_apply (Γ : LeanQbe.T.Env)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    {cx aig : Val i64} {sym : BitVec 32} {v : BitVec 32}
    {s0 s1 s2 s1' sR : ArCtxState} {g : Aig} {top0 : Nat}
    {aigBytes artBytes : List UInt8} {t : CmTabArrs} {flL : List (BitVec 8)}
    {d0 dL dR : CmDynArrs} {R : Mem 64 → Prop} {mR : Mem 64}
    {Q : Post [.bool]} {X : XPost} {kNext : Expr Val Cont [.bool]}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t.LenOk g s0) (hdLenR : dR.LenOk s0.qcap.toNat)
    (lfl : flL.length = t.flippedArr.length)
    (hs1_eq : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs1'_s1 : s1' = { s1 with
      pos := s1'.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s1'.tc, tn := s1'.tn, pc := s1'.pc, ptop := s1'.ptop, qn := s1'.qn,
      ix := s1'.ix, ix2 := s1'.ix2, cur_rm := s1'.cur_rm, cur_rl := s1'.cur_rl,
      cur_rh := s1'.cur_rh, cur_rp := s1'.cur_rp, cur_nr := s1'.cur_nr })
    (hsR : sR = { s1' with
      cur_rm := sR.cur_rm, cur_rl := sR.cur_rl,
      cur_rh := sR.cur_rh, cur_rp := sR.cur_rp, cur_nr := sR.cur_nr })
    (hixSwR : (sR.ix = s0.ix ∧ sR.ix2 = s0.ix2) ∨ (sR.ix = s0.ix2 ∧ sR.ix2 = s0.ix))
    (hsR_s1 : sR = { s1 with
      pos := sR.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := sR.tc, tn := sR.tn, pc := sR.pc, ptop := sR.ptop, qn := sR.qn,
      ix := sR.ix, ix2 := sR.ix2, cur_rm := sR.cur_rm, cur_rl := sR.cur_rl,
      cur_rh := sR.cur_rh, cur_rp := sR.cur_rp, cur_nr := sR.cur_nr })
    (hrsm_eq : dR.rsM = d0.rsM) (hrsl_eq : dR.rsL = d0.rsL)
    (hrsh_eq : dR.rsH = d0.rsH) (hrsp_eq : dR.rsPool = d0.rsPool)
    (hv_lt : v.toNat < s0.n_nets.toNat) (hv_lt2 : v.toNat < s2.n_nets.toNat)
    (hv_ne : t.ruleN.getD v.toNat 0#32 ≠ cNone32)
    (hsym_val : sym.toNat =
      if flL.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
    (hpcR : sR.pc.toNat < 2) (htcR : sR.tc.toNat < 2)
    (htnR : sR.tn.toNat ≤ s0.tcap.toNat) (hptR : sR.ptop.toNat ≤ s0.pcap.toNat)
    (hSortRs : RulesSorted d0.rsPool d0.rsM s2.rs_n.toNat)
    (hOkRs : ∀ j < s2.rs_n.toNat,
      (d0.rsPool.getD (d0.rsM.getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hrs_tot_bd : monoTotalWords d0.rsPool d0.rsM s2.rs_n.toNat ≤ 4000000000)
    (hRep : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ t.bindArr) s0.n_nets.toNat t.partnerArr ∧
      RulesRep s0.modW (cSig g ρ t.bindArr) s2 t.ruleOff t.ruleN
        d0.rsM d0.rsL d0.rsH d0.rsPool)
    (hRep1' : ∀ ρ : Nat → Bool,
      RulesRep s0.modW (cSig g ρ t.bindArr) s1' t.ruleOff t.ruleN
        dL.rsM dL.rsL dL.rsH dL.rsPool)
    (hrsmL : dL.rsM = d0.rsM) (hrslL : dL.rsL = d0.rsL)
    (hrshL : dL.rsH = d0.rsH) (_hrspL : dL.rsPool = d0.rsPool)
    (hSlR : ∀ j < sR.tn.toNat,
      MonoSliceOk (if sR.pc.toNat = 0 then dR.pool0 else dR.pool1)
        ((if sR.tc.toNat = 0 then dR.tm0 else dR.tm1).getD j 0#32).toNat sR.ptop.toNat ∧
      ((if sR.pc.toNat = 0 then dR.pool0 else dR.pool1).getD
        ((if sR.tc.toNat = 0 then dR.tm0 else dR.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
        2 ^ 32)
    (hSortR : ∀ j < sR.tn.toNat,
      MonoSorted (if sR.pc.toNat = 0 then dR.pool0 else dR.pool1)
        ((if sR.tc.toNat = 0 then dR.tm0 else dR.tm1).getD j 0#32).toNat)
    (hSigR : SigOk (if sR.pc.toNat = 0 then dR.pool0 else dR.pool1)
      (if sR.tc.toNat = 0 then dR.tm0 else dR.tm1)
      (if sR.tc.toNat = 0 then dR.ts0 else dR.ts1) sR.tn.toNat)
    (hTotR : monoTotalWords (if sR.pc.toNat = 0 then dR.pool0 else dR.pool1)
      (if sR.tc.toNat = 0 then dR.tm0 else dR.tm1) sR.tn.toNat ≤ sR.ptop.toNat)
    (hEvR : ∀ ρ : Nat → Bool,
      polyEval s0.modW (cSig g ρ t.bindArr)
          (if sR.pc.toNat = 0 then dR.pool0 else dR.pool1)
          (if sR.tc.toNat = 0 then dR.tm0 else dR.tm1)
          (if sR.tc.toNat = 0 then dR.tl0 else dR.tl1)
          (if sR.tc.toNat = 0 then dR.th0 else dR.th1) sR.tn.toNat =
        sp0TargetEval s0.spec s0.modW g ρ)
    (hR_cases :
      (flL.getD v.toNat 0#8 = 0#8 ∧
        sR.cur_rm = s1'.rs_m + BitVec.ofNat 64 (4 * (t.ruleOff.getD v.toNat 0#32).toNat) ∧
        sR.cur_rl = s1'.rs_l + BitVec.ofNat 64 (8 * (t.ruleOff.getD v.toNat 0#32).toNat) ∧
        sR.cur_rh = s1'.rs_h + BitVec.ofNat 64 (8 * (t.ruleOff.getD v.toNat 0#32).toNat) ∧
        sR.cur_rp = s1'.rs_pool ∧ sR.cur_nr = t.ruleN.getD v.toNat 0#32) ∨
      (sR.cur_rm = s1'.rm2 ∧ sR.cur_rl = s1'.rl2 ∧ sR.cur_rh = s1'.rh2 ∧
        sR.cur_rp = s1'.rpool ∧
        (∀ σ : Nat → Bool, (∃ ρ, σ = cSig g ρ t.bindArr) →
          CurRRep s1'.modW σ sR.cur_nr.toNat
            (if flL.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
            dR.rm2 dR.rl2 dR.rh2 dR.rpool) ∧
        (∀ r < sR.cur_nr.toNat, MonoSorted dR.rpool (dR.rm2.getD r 0#32).toNat) ∧
        (∀ r < sR.cur_nr.toNat,
          (dR.rpool.getD (dR.rm2.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        monoTotalWords dR.rpool dR.rm2 sR.cur_nr.toNat ≤ s1'.rpcap.toNat))
    (hmR_ar : (arCtxMem cx sR ⋆ bytes s0.art artBytes ⋆
      cmArenaMem sR s0 top0 { t with flippedArr := flL } dR ⋆ bytes aig aigBytes ⋆ R) mR)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hkDone : ∀ (sB : ArCtxState) (dB : CmDynArrs) (mB : Mem 64),
      dB.LenOk s0.qcap.toNat →
      dB.rsM = d0.rsM → dB.rsL = d0.rsL → dB.rsH = d0.rsH → dB.rsPool = d0.rsPool →
      sB = { s1 with
        pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
        tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
        ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
        cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } →
      ((sB.ix = s0.ix ∧ sB.ix2 = s0.ix2) ∨ (sB.ix = s0.ix2 ∧ sB.ix2 = s0.ix)) →
      sB.pc.toNat < 2 → sB.tc.toNat < 2 →
      sB.tn.toNat ≤ s0.tcap.toNat → sB.ptop.toNat ≤ s0.pcap.toNat → sB.pos = s1'.pos →
      (∀ j < sB.tn.toNat,
        MonoSliceOk (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat sB.ptop.toNat ∧
        ((if sB.pc.toNat = 0 then dB.pool0 else dB.pool1).getD
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
          2 ^ 32) →
      (∀ j < sB.tn.toNat,
        MonoSorted (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat) →
      SigOk (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
        (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
        (if sB.tc.toNat = 0 then dB.ts0 else dB.ts1) sB.tn.toNat →
      monoTotalWords (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
        (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1) sB.tn.toNat ≤ sB.ptop.toNat →
      (∀ ρ : Nat → Bool,
        polyEval s0.modW (cSig g ρ t.bindArr)
            (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
            (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
            (if sB.tc.toNat = 0 then dB.tl0 else dB.tl1)
            (if sB.tc.toNat = 0 then dB.th0 else dB.th1) sB.tn.toNat =
          sp0TargetEval s0.spec s0.modW g ρ) →
      (arCtxMem cx sB ⋆ bytes s0.art artBytes ⋆
        cmArenaMem sB s0 top0 { t with flippedArr := flL } dB ⋆ bytes aig aigBytes ⋆ R) mB →
      wp Γ Q X kNext mB) :
    wp Γ Q X (@Expr.call Val Cont [.bool] "ar_apply" [i64, i32] [.bool]
      (Arg.var cx, Arg.var sym, ()) fun p =>
      Expr.jnz (Arg.var p.fst) kNext (Expr.ret (Arg.imm false, ())) ) mR := by
  rcases hR_cases with ⟨hfl0, hcm, hcl, hch, hcp, hcnr⟩ |
      ⟨hcm, hcl, hch, hcp, hCurR', hCurSort', hCurOk', hCurTot'⟩
  · let off := (t.ruleOff.getD v.toNat 0#32).toNat
    have hRep0 := hRep1' (fun _ => false)
    have hv_lt1' : v.toNat < s1'.n_nets.toNat := by
      rw [show s1'.n_nets = s0.n_nets by rw [hs1'_s1, hs1_eq]]; exact hv_lt
    have hoff_cnt := (hRep0.2.2.2.2.2.2.2.2.2 v.toNat hv_lt1' hv_ne).1
    have hrsn_le : s1'.rs_n.toNat ≤ s1'.rs_cap.toNat := hRep0.2.2.1
    have hoff_m : off ≤ dR.rsM.length := by
      have := hRep0.2.2.2.2.1; rw [hrsmL, ← hrsm_eq] at this; omega
    have hoff_l : off ≤ dR.rsL.length := by
      have := hRep0.2.2.2.2.2.1; rw [hrslL, ← hrsl_eq] at this; omega
    have hoff_h : off ≤ dR.rsH.length := by
      have := hRep0.2.2.2.2.2.2.1; rw [hrshL, ← hrsh_eq] at this; omega
    let Rapply : Mem 64 → Prop :=
      aigArraysMem sR t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 sR.bind t.bindArr ⋆
      arrayPad i32 sR.rule_off t.ruleOff ⋆ arrayPad i32 sR.rule_n t.ruleN ⋆
      u32PadTail sR.partner t.partnerArr.length ⋆ arrayPad i8 sR.flipped flL ⋆
      arrayPad i32 sR.in_net t.inNetArr ⋆ arrayPad i32 sR.out_ref t.outRefArr ⋆
      gateScratchMem sR t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
      region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
      array (t := i32) sR.rs_m (dR.rsM.take off) ⋆
      array64 sR.rs_l (dR.rsL.take off) ⋆ array64 sR.rs_h (dR.rsH.take off) ⋆
      u32PadTail sR.rs_m dR.rsM.length ⋆ u32PadTail sR.rs_pool dR.rsPool.length ⋆
      rMem sR dR.rm dR.rl dR.rh dR.rm2 dR.rl2 dR.rh2 dR.rpool ⋆
      region (sR.w + sR.top) (sR.wlen.toNat - sR.top.toNat)
    have hmR_sp : (arCtxMem cx sR ⋆ array (t := i32) sR.partner t.partnerArr ⋆
        array (t := i32) sR.cur_rm (dR.rsM.drop off) ⋆
        array64 sR.cur_rl (dR.rsL.drop off) ⋆ array64 sR.cur_rh (dR.rsH.drop off) ⋆
        array (t := i32) sR.cur_rp dR.rsPool ⋆
        tMem sR dR.tm0 dR.tm1 dR.ts0 dR.tl0 dR.th0 dR.ts1 dR.tl1 dR.th1 dR.pool0 dR.pool1 ⋆
        qMem sR dR.qm dR.qs dR.ql dR.qh dR.ix dR.ix2 dR.bx dR.vqOff dR.vq dR.vqSkip ⋆
        Rapply ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mR := by
      rw [arena_unpack_apply, rsMem_unpack, rs_split_at hoff_m hoff_l hoff_h] at hmR_ar
      rw [hcm, hcl, hch, hcp,
        show s1'.rs_m = sR.rs_m by rw [hsR], show s1'.rs_l = sR.rs_l by rw [hsR],
        show s1'.rs_h = sR.rs_h by rw [hsR], show s1'.rs_pool = sR.rs_pool by rw [hsR]]
      exact sep_cast hmR_ar (by dsimp only [Rapply]; ac_rfl)
    have hrsn_eq : s1'.rs_n = s2.rs_n := by rw [hs1'_s1]
    refine main_apply_step Γ hApply hb htLen hdLenR
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq])
      (by simp only [ArCtxState.modW, show sR.spec = s0.spec by rw [hsR_s1, hs1_eq],
            show sR.n_out = s0.n_out by rw [hsR_s1, hs1_eq]])
      (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      hpcR htcR htnR hptR hixSwR (fun ρ => (hRep ρ).1)
      (fun ρ => by
        rw [hsym_val, hcnr, hrsm_eq, hrsl_eq, hrsh_eq, hrsp_eq]
        simp only [hfl0, ne_eq, not_true_eq_false, ↓reduceIte]
        exact curRRep_of_rulesRep_drop (hRep ρ).2 hv_lt2 hv_ne)
      (fun r hr => by
        rw [hcnr] at hr
        have hdrop : (dR.rsM.drop off).getD r 0#32 = dR.rsM.getD (off + r) 0#32 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [hdrop, hrsm_eq, hrsp_eq]
        exact hSortRs (off + r) (by rw [← hrsn_eq]; omega))
      (fun r hr => by
        rw [hcnr] at hr
        have hdrop : (dR.rsM.drop off).getD r 0#32 = dR.rsM.getD (off + r) 0#32 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [hdrop, hrsm_eq, hrsp_eq]
        exact hOkRs (off + r) (by rw [← hrsn_eq]; omega))
      (by
        rw [hcnr, hrsm_eq, hrsp_eq]
        have h1 := monoTotalWords_drop_le (pool := d0.rsPool) (rsM := d0.rsM)
          (off := off) (cnt := (t.ruleN.getD v.toNat 0#32).toNat) (n := s2.rs_n.toNat)
          (by rw [← hrsn_eq]; omega)
        omega)
      hSlR hSortR hSigR hTotR hEvR hmR_sp
      (fun sB dB mB hdB hsB hixB hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp hmB => by
        have hsB_s1 : sB = { s1 with
            pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
            tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
            ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
            cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } := by
          rw [hsB, hsR_s1]
        exact main_fail_collapse hb htLen hs1_eq lfl hdB hsB_s1 hixB
          (cmArena_apply_rs_repack hsR hsB hcm hcl hch hcp hoff_m hoff_l hoff_h
            hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp hmB) hFail)
      (fun sB dB mB hdB hsB hixB hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp
        hpcB htcB htnB hptB hSlB hSortB hSigB hTotB hEvB hmB =>
        have hsB_s1 : sB = { s1 with
            pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
            tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
            ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
            cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } := by
          rw [hsB, hsR_s1]
        hkDone sB dB mB hdB (hrsM.trans hrsm_eq) (hrsL.trans hrsl_eq) (hrsH.trans hrsh_eq)
          (hrsP.trans hrsp_eq) hsB_s1 hixB hpcB htcB htnB hptB
          (by rw [show sB.pos = sR.pos by rw [hsB], show sR.pos = s1'.pos by rw [hsR]])
          hSlB hSortB hSigB hTotB hEvB
          (cmArena_apply_rs_repack hsR hsB hcm hcl hch hcp hoff_m hoff_l hoff_h
            hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp hmB))
  · let Rapply : Mem 64 → Prop :=
      aigArraysMem sR t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 sR.bind t.bindArr ⋆
      arrayPad i32 sR.rule_off t.ruleOff ⋆ arrayPad i32 sR.rule_n t.ruleN ⋆
      u32PadTail sR.partner t.partnerArr.length ⋆ arrayPad i8 sR.flipped flL ⋆
      arrayPad i32 sR.in_net t.inNetArr ⋆ arrayPad i32 sR.out_ref t.outRefArr ⋆
      gateScratchMem sR t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
      region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
      rsMem sR dR.rsM dR.rsL dR.rsH dR.rsPool ⋆
      arrayPad i32 sR.rm dR.rm ⋆ array64 sR.rl dR.rl ⋆ array64 sR.rh dR.rh ⋆
      u32PadTail sR.rm2 dR.rm2.length ⋆ u32PadTail sR.rpool dR.rpool.length ⋆
      region (sR.w + sR.top) (sR.wlen.toNat - sR.top.toNat)
    have hmR_sp : (arCtxMem cx sR ⋆ array (t := i32) sR.partner t.partnerArr ⋆
        array (t := i32) sR.cur_rm dR.rm2 ⋆ array64 sR.cur_rl dR.rl2 ⋆
        array64 sR.cur_rh dR.rh2 ⋆ array (t := i32) sR.cur_rp dR.rpool ⋆
        tMem sR dR.tm0 dR.tm1 dR.ts0 dR.tl0 dR.th0 dR.ts1 dR.tl1 dR.th1 dR.pool0 dR.pool1 ⋆
        qMem sR dR.qm dR.qs dR.ql dR.qh dR.ix dR.ix2 dR.bx dR.vqOff dR.vq dR.vqSkip ⋆
        Rapply ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mR := by
      rw [arena_unpack_apply] at hmR_ar
      dsimp only [rMem] at hmR_ar
      rw [arrayPad_u32_unfold sR.rm2 dR.rm2, arrayPad_u32_unfold sR.rpool dR.rpool] at hmR_ar
      rw [hcm, hcl, hch, hcp,
        show s1'.rm2 = sR.rm2 by rw [hsR], show s1'.rl2 = sR.rl2 by rw [hsR],
        show s1'.rh2 = sR.rh2 by rw [hsR], show s1'.rpool = sR.rpool by rw [hsR]]
      exact sep_cast hmR_ar (by dsimp only [Rapply]; ac_rfl)
    refine main_apply_step Γ hApply hb htLen hdLenR
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq])
      (by simp only [ArCtxState.modW, show sR.spec = s0.spec by rw [hsR_s1, hs1_eq],
            show sR.n_out = s0.n_out by rw [hsR_s1, hs1_eq]])
      (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq]) (by rw [hsR_s1, hs1_eq])
      hpcR htcR htnR hptR hixSwR (fun ρ => (hRep ρ).1)
      (fun ρ => by
        rw [hsym_val]
        have h1 := hCurR' (cSig g ρ t.bindArr) ⟨ρ, rfl⟩
        rw [show s1'.modW = s0.modW by
          simp only [ArCtxState.modW, show s1'.spec = s0.spec by rw [hs1'_s1, hs1_eq],
            show s1'.n_out = s0.n_out by rw [hs1'_s1, hs1_eq]]] at h1
        exact h1)
      hCurSort' hCurOk'
      (by
        have h1 : s1'.rpcap.toNat ≤ 4000000000 := by
          rw [show s1'.rpcap = s0.rpcap by rw [hs1'_s1, hs1_eq], hb.rpcap_eq, hb.pcap_eq]
          have := hb.cap_hi; omega
        omega)
      hSlR hSortR hSigR hTotR hEvR hmR_sp
      (fun sB dB mB hdB hsB hixB hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp hmB => by
        have hsB_s1 : sB = { s1 with
            pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
            tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
            ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
            cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } := by
          rw [hsB, hsR_s1]
        exact main_fail_collapse hb htLen hs1_eq lfl hdB hsB_s1 hixB
          (cmArena_apply_r2_repack hsR hsB hcm hcl hch hcp
            hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp hmB) hFail)
      (fun sB dB mB hdB hsB hixB hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp
        hpcB htcB htnB hptB hSlB hSortB hSigB hTotB hEvB hmB =>
        have hsB_s1 : sB = { s1 with
            pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
            tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
            ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
            cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } := by
          rw [hsB, hsR_s1]
        hkDone sB dB mB hdB (hrsM.trans hrsm_eq) (hrsL.trans hrsl_eq) (hrsH.trans hrsh_eq)
          (hrsP.trans hrsp_eq) hsB_s1 hixB hpcB htcB htnB hptB
          (by rw [show sB.pos = sR.pos by rw [hsB], show sR.pos = s1'.pos by rw [hsR]])
          hSlB hSortB hSigB hTotB hEvB
          (cmArena_apply_r2_repack hsR hsB hcm hcl hch hcp
            hrsM hrsL hrsH hrsP hrm hrl hrh hrm2 hrl2 hrh2 hrp hmB))

private theorem flip_cur_bundle {nOut : Nat} {g : Aig} {bindArr : List (BitVec 32)}
    {v : BitVec 32} {mlo mhi nl nh : BitVec 64}
    {rpool rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    (hm : MasksOk nOut mlo mhi)
    (hrm_len : 16 ≤ rm.length) (hrl_len : 16 ≤ rl.length) (hrh_len : 16 ≤ rh.length)
    (hrp_len : 192 ≤ rpool.length) (h2v1 : 2 * v.toNat + 1 < 2 ^ 32)
    (hcneg : coeff128 nOut nl nh = -coeff128 nOut 1#64 0#64) :
    let rpF := ((rpool.set 0 0#32).set 1 1#32).set 2 (2#32 * v + 1#32)
    let rmF := (rm.set 0 0#32).set 1 1#32
    let rlF := (rl.set 0 (1#64 &&& mlo)).set 1 nl
    let rhF := (rh.set 0 0#64).set 1 nh
    (∀ ρ, CurRRep nOut (cSig g ρ bindArr) 2 (2 * v.toNat) rmF rlF rhF rpF) ∧
    (∀ r < 2, MonoSorted rpF (rmF.getD r 0#32).toNat) ∧
    (∀ r < 2, (rpF.getD (rmF.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    monoTotalWords rpF rmF 2 ≤ 4000000000 := by
  intro rpF rmF rlF rhF
  have hrp0 : rpF.getD 0 0#32 = 0#32 := by
    dsimp only [rpF]
    rw [getD_set_ne _ 0#32 _ (by omega), getD_set_ne _ 0#32 _ (by omega),
      d_getD_set_eq _ 0#32 _ (by omega)]
  have hrp1 : rpF.getD 1 0#32 = 1#32 := by
    dsimp only [rpF]
    rw [getD_set_ne _ 0#32 _ (by omega),
      d_getD_set_eq _ 0#32 _ (by simp only [List.length_set]; omega)]
  have hrp2 : rpF.getD 2 0#32 = BitVec.ofNat 32 (2 * v.toNat + 1) := by
    dsimp only [rpF]
    rw [d_getD_set_eq _ 0#32 _ (by simp only [List.length_set]; omega)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 32), Nat.mod_eq_of_lt h2v1]
  have hrm0 : rmF.getD 0 0#32 = 0#32 := by
    dsimp only [rmF]; rw [getD_set_ne _ 0#32 _ (by omega), d_getD_set_eq _ 0#32 _ (by omega)]
  have hrm1 : rmF.getD 1 0#32 = 1#32 := by
    dsimp only [rmF]; rw [d_getD_set_eq _ 0#32 _ (by simp only [List.length_set]; omega)]
  have hrl0 : rlF.getD 0 0#64 = 1#64 &&& mlo := by
    dsimp only [rlF]; rw [getD_set_ne _ 0#64 _ (by omega), d_getD_set_eq _ 0#64 _ (by omega)]
  have hrh0 : rhF.getD 0 0#64 = 0#64 := by
    dsimp only [rhF]; rw [getD_set_ne _ 0#64 _ (by omega), d_getD_set_eq _ 0#64 _ (by omega)]
  have hrl1 : rlF.getD 1 0#64 = nl := by
    dsimp only [rlF]; rw [d_getD_set_eq _ 0#64 _ (by simp only [List.length_set]; omega)]
  have hrh1 : rhF.getD 1 0#64 = nh := by
    dsimp only [rhF]; rw [d_getD_set_eq _ 0#64 _ (by simp only [List.length_set]; omega)]
  refine ⟨fun ρ => flip_curRRep hm (cSig_odd g ρ bindArr v.toNat)
      (by simpa [rmF] using hrm_len) (by simpa [rlF] using hrl_len)
      (by simpa [rhF] using hrh_len) (by simpa [rpF] using hrp_len)
      hrp0 hrp1 hrp2 h2v1 hrm0 hrm1 hrl0 hrh0 hrl1 hrh1 hcneg,
    fun r hr => ?_, fun r hr => ?_, ?_⟩
  · rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · rw [hrm0, show (0#32 : BitVec 32).toNat = 0 from rfl]
      exact monoSorted_of_le1 (by rw [hrp0]; decide)
    · rw [hrm1, show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact monoSorted_of_le1 (by rw [hrp1]; decide)
  · rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · rw [hrm0, show (0#32 : BitVec 32).toNat = 0 from rfl, hrp0]; simp only [BitVec.toNat_ofNat]
      omega
    · rw [hrm1, show (1#32 : BitVec 32).toNat = 1 from rfl, hrp1]; simp only [BitVec.toNat_ofNat]
      omega
  · rw [monoTotalWords, show List.range 2 = [0, 1] from rfl]
    simp only [List.getD_eq_getElem?_getD] at hrm0 hrm1 hrp0 hrp1
    simp [hrm0, hrm1, hrp0, hrp1]

private theorem wp_store_arr64_abs {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i64} {a : Arg Val i64} {val : BitVec 64} {k : Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 64)} {idx : BitVec 64} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + idx * 8)
    (hi : idx.toNat < xs.length) (hm : (array64 base xs ⋆ R) m)
    (hk : ∀ m', (array64 base (xs.set idx.toNat val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (8 * idx.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm idx.toNat 8]
  exact head_wp_store hv ha' (store_array64 val hi hm) hk

private theorem main_odd_flip_apply (Γ : LeanQbe.T.Env)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    {cx aig : Val i64} {v : BitVec 32} {nl nh : BitVec 64}
    {s0 s1 s2 s1' : ArCtxState} {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t : CmTabArrs} {flL : List (BitVec 8)} {d0 dL : CmDynArrs}
    {Rflip0 R : Mem 64 → Prop} {mF : Mem 64}
    {Q : Post [.bool]} {X : XPost} {J : Cont []}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t.LenOk g s0) (hdL : dL.LenOk s0.qcap.toNat) (lfl : flL.length = t.flippedArr.length)
    (hrsm_eq : dL.rsM = d0.rsM) (hrsl_eq : dL.rsL = d0.rsL)
    (hrsh_eq : dL.rsH = d0.rsH) (hrsp_eq : dL.rsPool = d0.rsPool)
    (hs1_eq : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs1'_s1 : s1' = { s1 with
      pos := s1'.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s1'.tc, tn := s1'.tn, pc := s1'.pc, ptop := s1'.ptop, qn := s1'.qn,
      ix := s1'.ix, ix2 := s1'.ix2, cur_rm := s1'.cur_rm, cur_rl := s1'.cur_rl,
      cur_rh := s1'.cur_rh, cur_rp := s1'.cur_rp, cur_nr := s1'.cur_nr })
    (hixSw1' : (s1'.ix = s0.ix ∧ s1'.ix2 = s0.ix2) ∨ (s1'.ix = s0.ix2 ∧ s1'.ix2 = s0.ix))
    (hpcL : s1'.pc.toNat < 2) (htcL : s1'.tc.toNat < 2)
    (htnL : s1'.tn.toNat ≤ s0.tcap.toNat) (hptL : s1'.ptop.toNat ≤ s0.pcap.toNat)
    (_hs1'_pos : s1'.pos.toNat ≤ s0.nw.toNat)
    (hv_fl : (BitVec.setWidth 64 v).toNat < flL.length)
    (h2v1_lt : 2 * v.toNat + 1 < 2 ^ 32)
    (hcneg : coeff128 s1'.modW nl nh = -coeff128 s1'.modW 1#64 0#64)
    (hRflip0 : Rflip0 =
      (aigArraysMem s1' t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 s1'.bind t.bindArr ⋆
       arrayPad i32 s1'.rule_off t.ruleOff ⋆ arrayPad i32 s1'.rule_n t.ruleN ⋆
       u32PadTail s1'.partner t.partnerArr.length ⋆ u8PadTail s1'.flipped flL.length ⋆
       arrayPad i32 s1'.in_net t.inNetArr ⋆ arrayPad i32 s1'.out_ref t.outRefArr ⋆
       gateScratchMem s1' t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
       region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
       rsMem s1' dL.rsM dL.rsL dL.rsH dL.rsPool ⋆
       u32PadTail s1'.rm dL.rm.length ⋆
       arrayPad i32 s1'.rm2 dL.rm2 ⋆ array64 s1'.rl2 dL.rl2 ⋆ array64 s1'.rh2 dL.rh2 ⋆
       u32PadTail s1'.rpool dL.rpool.length ⋆
       region (s1'.w + s1'.top) (s1'.wlen.toNat - s1'.top.toNat)))
    (hRep : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ t.bindArr) s0.n_nets.toNat t.partnerArr ∧
      RulesRep s0.modW (cSig g ρ t.bindArr) s2 t.ruleOff t.ruleN
        d0.rsM d0.rsL d0.rsH d0.rsPool)
    (hSlL : ∀ j < s1'.tn.toNat,
      MonoSliceOk (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
        ((if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat s1'.ptop.toNat ∧
      ((if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1).getD
        ((if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
        2 ^ 32)
    (hSortL : ∀ j < s1'.tn.toNat,
      MonoSorted (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
        ((if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat)
    (hSigL : SigOk (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
      (if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1)
      (if s1'.tc.toNat = 0 then dL.ts0 else dL.ts1) s1'.tn.toNat)
    (hTotL : monoTotalWords (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
      (if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1) s1'.tn.toNat ≤ s1'.ptop.toNat)
    (hEvL : ∀ ρ : Nat → Bool,
      polyEval s0.modW (cSig g ρ t.bindArr)
          (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
          (if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1)
          (if s1'.tc.toNat = 0 then dL.tl0 else dL.tl1)
          (if s1'.tc.toNat = 0 then dL.th0 else dL.th1) s1'.tn.toNat =
        sp0TargetEval s0.spec s0.modW g ρ)
    (hmF : let rpF := ((dL.rpool.set 0 0#32).set 1 1#32).set 2 (2#32 * v + 1#32)
      let rmF := (dL.rm.set 0 0#32).set 1 1#32
      let rlF := (dL.rl.set 0 (1#64 &&& s1'.mlo)).set 1 nl
      let rhF := (dL.rh.set 0 0#64).set 1 nh
      let sF : ArCtxState := { s1' with
        cur_rm := s1'.rm, cur_rl := s1'.rl, cur_rh := s1'.rh,
        cur_rp := s1'.rpool, cur_nr := 2#32 }
      (arCtxMem cx sF ⋆ array (t := i8) sF.flipped flL ⋆ array (t := i32) sF.rm rmF ⋆
        array64 sF.rl rlF ⋆ array64 sF.rh rhF ⋆ array (t := i32) sF.rpool rpF ⋆
        array (t := i32) sF.partner t.partnerArr ⋆
        tMem sF dL.tm0 dL.tm1 dL.ts0 dL.tl0 dL.th0 dL.ts1 dL.tl1 dL.th1 dL.pool0 dL.pool1 ⋆
        qMem sF dL.qm dL.qs dL.ql dL.qh dL.ix dL.ix2 dL.bx dL.vqOff dL.vq dL.vqSkip ⋆
        Rflip0 ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mF)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hkJ : ∀ (sB : ArCtxState) (flB : List (BitVec 8)) (dB : CmDynArrs) (mB : Mem 64),
      flB.length = t.flippedArr.length → dB.LenOk s0.qcap.toNat →
      dB.rsM = d0.rsM → dB.rsL = d0.rsL → dB.rsH = d0.rsH → dB.rsPool = d0.rsPool →
      sB = { s1 with
        pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
        tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
        ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
        cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } →
      ((sB.ix = s0.ix ∧ sB.ix2 = s0.ix2) ∨ (sB.ix = s0.ix2 ∧ sB.ix2 = s0.ix)) →
      sB.pc.toNat < 2 → sB.tc.toNat < 2 →
      sB.tn.toNat ≤ s0.tcap.toNat → sB.ptop.toNat ≤ s0.pcap.toNat → sB.pos = s1'.pos →
      (∀ j < sB.tn.toNat,
        MonoSliceOk (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat sB.ptop.toNat ∧
        ((if sB.pc.toNat = 0 then dB.pool0 else dB.pool1).getD
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
          2 ^ 32) →
      (∀ j < sB.tn.toNat,
        MonoSorted (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat) →
      SigOk (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
        (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
        (if sB.tc.toNat = 0 then dB.ts0 else dB.ts1) sB.tn.toNat →
      monoTotalWords (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
        (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1) sB.tn.toNat ≤ sB.ptop.toNat →
      (∀ ρ : Nat → Bool,
        polyEval s0.modW (cSig g ρ t.bindArr)
            (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
            (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
            (if sB.tc.toNat = 0 then dB.tl0 else dB.tl1)
            (if sB.tc.toNat = 0 then dB.th0 else dB.th1) sB.tn.toNat =
          sp0TargetEval s0.spec s0.modW g ρ) →
      (arCtxMem cx sB ⋆ bytes s0.art artBytes ⋆
        cmArenaMem sB s0 top0 { t with flippedArr := flB } dB ⋆ bytes aig aigBytes ⋆ R) mB →
      wp Γ Q X (Expr.jump J ()) mB) :
    let kTrue := Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var cx, Arg.imm 136, ()) } fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
        Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) } fun p =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var ld, Arg.var p.fst, ()) } fun p =>
            Expr.let_
              { sig := [i32], code := OpCode.trunc 32 8,
                args := (Arg.imm 1, ()) } fun pv =>
              Expr.store (Arg.var pv.fst) (Arg.var p.fst) (Expr.jump J ())
    wp Γ Q X (@Expr.call Val Cont [.bool] "ar_apply" [i64, i32] [.bool]
      (Arg.var cx, Arg.var (2#32 * v), ()) fun p =>
      Expr.jnz (Arg.var p.fst) kTrue (Expr.ret (Arg.imm false, ())) ) mF := by
  have hrm_l16 : 16 ≤ dL.rm.length := by rw [CmDynArrs.len_rm hdL]; exact hb.cap_lo
  have hrl_l16 : 16 ≤ dL.rl.length := by rw [CmDynArrs.len_rl hdL]; exact hb.cap_lo
  have hrh_l16 : 16 ≤ dL.rh.length := by rw [CmDynArrs.len_rh hdL]; exact hb.cap_lo
  have hrp_l192 : 192 ≤ dL.rpool.length := by
    rw [CmDynArrs.len_rpool hdL]; have := hb.cap_lo; omega
  let rpF := ((dL.rpool.set 0 0#32).set 1 1#32).set 2 (2#32 * v + 1#32)
  let rmF := (dL.rm.set 0 0#32).set 1 1#32
  let rlF := (dL.rl.set 0 (1#64 &&& s1'.mlo)).set 1 nl
  let rhF := (dL.rh.set 0 0#64).set 1 nh
  let sF : ArCtxState := { s1' with
    cur_rm := s1'.rm, cur_rl := s1'.rl, cur_rh := s1'.rh,
    cur_rp := s1'.rpool, cur_nr := 2#32 }
  have hsF_1 : sF = { s1' with
      cur_rm := s1'.rm, cur_rl := s1'.rl, cur_rh := s1'.rh,
      cur_rp := s1'.rpool, cur_nr := 2#32 } := rfl
  have hsF_s1 : sF = { s1 with
      pos := sF.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := sF.tc, tn := sF.tn, pc := sF.pc, ptop := sF.ptop, qn := sF.qn,
      ix := sF.ix, ix2 := sF.ix2, cur_rm := sF.cur_rm, cur_rl := sF.cur_rl,
      cur_rh := sF.cur_rh, cur_rp := sF.cur_rp, cur_nr := sF.cur_nr } := by
    dsimp only [sF]; rw [hs1'_s1]
  let dF : CmDynArrs := { dL with rm := rmF, rl := rlF, rh := rhF, rpool := rpF }
  have lrmF : rmF.length = dL.rm.length := by simp [rmF]
  have lrlF : rlF.length = dL.rl.length := by simp [rlF]
  have lrhF : rhF.length = dL.rh.length := by simp [rhF]
  have lrpF : rpF.length = dL.rpool.length := by simp [rpF]
  have hdLenF : dF.LenOk s0.qcap.toNat := d_LenOk_flip hdL lrmF lrlF lrhF lrpF
  have h2v_eq : (2#32 * v).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hcneg' : coeff128 s0.modW nl nh = -coeff128 s0.modW 1#64 0#64 := by
    rw [show s1'.modW = s0.modW by
      simp only [ArCtxState.modW, show s1'.spec = s0.spec by rw [hs1'_s1, hs1_eq],
        show s1'.n_out = s0.n_out by rw [hs1'_s1, hs1_eq]]] at hcneg
    exact hcneg
  have ⟨hCurRF, hCurSortF, hCurOkF, hCurTotF⟩ := flip_cur_bundle (g := g)
    (bindArr := t.bindArr) (v := v) hb.masks hrm_l16 hrl_l16 hrh_l16 hrp_l192
    h2v1_lt hcneg'
  let RcurF : Mem 64 → Prop := array (t := i8) sF.flipped flL ⋆ Rflip0
  have hmF_sp : (arCtxMem cx sF ⋆ array (t := i32) sF.partner t.partnerArr ⋆
      array (t := i32) sF.cur_rm rmF ⋆ array64 sF.cur_rl rlF ⋆
      array64 sF.cur_rh rhF ⋆ array (t := i32) sF.cur_rp rpF ⋆
      tMem sF dF.tm0 dF.tm1 dF.ts0 dF.tl0 dF.th0 dF.ts1 dF.tl1 dF.th1 dF.pool0 dF.pool1 ⋆
      qMem sF dF.qm dF.qs dF.ql dF.qh dF.ix dF.ix2 dF.bx dF.vqOff dF.vq dF.vqSkip ⋆
      RcurF ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mF := by
    dsimp only [RcurF, sF, dF, rmF, rlF, rhF, rpF] at hmF ⊢
    exact sep_cast hmF (by ac_rfl)
  refine main_apply_step Γ hApply hb htLen hdLenF (sA := sF)
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq])
    (by simp only [ArCtxState.modW, show sF.spec = s0.spec by rw [hsF_s1, hs1_eq],
          show sF.n_out = s0.n_out by rw [hsF_s1, hs1_eq]])
    (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq]) (by rw [hsF_s1, hs1_eq])
    hpcL htcL htnL hptL hixSw1' (fun ρ => (hRep ρ).1)
    (fun ρ => by
      dsimp only [rmF, rlF, rhF, rpF]
      rw [h2v_eq, show sF.cur_nr.toNat = 2 from rfl, show s1'.mlo = s0.mlo by rw [hs1'_s1, hs1_eq]]
      exact hCurRF ρ)
    (by dsimp only [rpF, rmF]; rw [show sF.cur_nr.toNat = 2 from rfl]; exact hCurSortF)
    (by dsimp only [rpF, rmF]; rw [show sF.cur_nr.toNat = 2 from rfl]; exact hCurOkF)
    (by dsimp only [rpF, rmF]; rw [show sF.cur_nr.toNat = 2 from rfl]; exact hCurTotF)
    (by dsimp only [dF]; exact hSlL) (by dsimp only [dF]; exact hSortL)
    (by dsimp only [dF]; exact hSigL) (by dsimp only [dF]; exact hTotL)
    (fun ρ => by dsimp only [dF]; exact hEvL ρ) hmF_sp
    (fun sB dB mB hdB hsB hixB hrsM hrsL hrsH hrsP hrmB hrlB hrhB
      hrm2B hrl2B hrh2B hrpB hmB => by
      have hsB_s1 : sB = { s1 with
          pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
          tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
          ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
          cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } := by
        rw [hsB, hsF_s1]
      have hmB_ar := cmArena_apply_r1_repack (cx := cx) (aig := aig) (s0 := s0) (top0 := top0)
        (aigBytes := aigBytes) (artBytes := artBytes) (t := t)
        (flL := flL) (flB := flL) (dF := dF) (dB := dB) (R := R)
        hsF_1 hsB rfl hrsM hrsL hrsH hrsP hrmB hrlB hrhB hrm2B hrl2B hrh2B hrpB
        (by
          dsimp only [RcurF] at hmB
          rw [hRflip0] at hmB
          dsimp only [dF]
          rw [lrmF, lrpF]
          exact sep_cast hmB (by ac_rfl))
      exact main_fail_collapse hb htLen hs1_eq lfl hdB hsB_s1 hixB hmB_ar hFail)
    (fun sB dB mB hdB hsB hixB hrsM hrsL hrsH hrsP hrmB hrlB hrhB
      hrm2B hrl2B hrh2B hrpB hpcB htcB htnB hptB hSlB hSortB hSigB hTotB hEvB hmB => by
      have hmB_fl : (arCtxMem cx sB ⋆ array (t := i8) sB.flipped flL ⋆
          (array (t := i32) sB.partner t.partnerArr ⋆
           array (t := i32) sB.cur_rm rmF ⋆ array64 sB.cur_rl rlF ⋆
           array64 sB.cur_rh rhF ⋆ array (t := i32) sB.cur_rp rpF ⋆
           tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1
             dB.pool0 dB.pool1 ⋆
           qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq
             dB.vqSkip ⋆
           Rflip0 ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R)) mB := by
        dsimp only [RcurF] at hmB
        rw [show sF.flipped = sB.flipped by rw [hsB]] at hmB
        exact sep_cast hmB (by ac_rfl)
      c0_hsteps_nogrp
      let flB := flL.set (BitVec.setWidth 64 v).toNat 1#8
      have lflB : flB.length = t.flippedArr.length := by simp [flB, lfl]
      have hsB_s1 : sB = { s1 with
          pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
          tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
          ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
          cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } := by
        rw [hsB, hsF_s1]
      have hmB_ar := cmArena_apply_r1_repack (cx := cx) (aig := aig) (s0 := s0) (top0 := top0)
        (aigBytes := aigBytes) (artBytes := artBytes) (t := t)
        (flL := flL) (flB := flB) (dF := dF) (dB := dB) (R := R)
        hsF_1 hsB (lflB.trans lfl.symm)
        hrsM hrsL hrsH hrsP hrmB hrlB hrhB hrm2B hrl2B hrh2B hrpB
        (by
          have hmB_next : (array (t := i8) sB.flipped
              (flL.set (BitVec.setWidth 64 v).toNat 1#8) ⋆ _) _ := ‹_›
          rw [hRflip0, show sB.flipped = sF.flipped by rw [hsB]] at hmB_next
          dsimp only [dF, flB]
          rw [lrmF, lrpF]
          exact sep_cast hmB_next (by ac_rfl))
      exact hkJ sB flB dB _ lflB hdB (hrsM.trans hrsm_eq) (hrsL.trans hrsl_eq)
        (hrsH.trans hrsh_eq) (hrsP.trans hrsp_eq) hsB_s1 hixB hpcB htcB htnB hptB
        (by rw [show sB.pos = sF.pos by rw [hsB]]) hSlB hSortB hSigB hTotB hEvB hmB_ar)

private theorem main_even_buildR_call (Γ : LeanQbe.T.Env)
    (hBuildR : ∀ xs m Q X, arBuildRSpec xs m Q X → Γ "ar_build_R" [i64, i32] [.bool] xs m Q X)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    {cx aig : Val i64} {v : BitVec 32} {Q : Post [.bool]} {X : XPost} {J : Cont []}
    {s0 s1 s2 s1' : ArCtxState} {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t : CmTabArrs} {flL : List (BitVec 8)} {d0 dL : CmDynArrs}
    {Rbr R : Mem 64 → Prop} {m1' : Mem 64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t.LenOk g s0) (hdL : dL.LenOk s0.qcap.toNat) (lfl : flL.length = t.flippedArr.length)
    (hrsm_eq : dL.rsM = d0.rsM) (hrsl_eq : dL.rsL = d0.rsL)
    (hrsh_eq : dL.rsH = d0.rsH) (hrsp_eq : dL.rsPool = d0.rsPool)
    (hs1_eq : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs1'_s1 : s1' = { s1 with
      pos := s1'.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s1'.tc, tn := s1'.tn, pc := s1'.pc, ptop := s1'.ptop, qn := s1'.qn,
      ix := s1'.ix, ix2 := s1'.ix2, cur_rm := s1'.cur_rm, cur_rl := s1'.cur_rl,
      cur_rh := s1'.cur_rh, cur_rp := s1'.cur_rp, cur_nr := s1'.cur_nr })
    (hixSw1' : (s1'.ix = s0.ix ∧ s1'.ix2 = s0.ix2) ∨ (s1'.ix = s0.ix2 ∧ s1'.ix2 = s0.ix))
    (hpcL : s1'.pc.toNat < 2) (htcL : s1'.tc.toNat < 2)
    (htnL : s1'.tn.toNat ≤ s0.tcap.toNat) (hptL : s1'.ptop.toNat ≤ s0.pcap.toNat)
    (_hs1'_pos : s1'.pos.toNat ≤ s0.nw.toNat)
    (hv_lt : v.toNat < s0.n_nets.toNat) (hs2_nn : s2.n_nets = s0.n_nets)
    (hv_ne : t.ruleN.getD v.toNat 0#32 ≠ cNone32)
    (_hv_fl : (BitVec.setWidth 64 v).toNat < flL.length) (h2v1_lt : 2 * v.toNat + 1 < 2 ^ 32)
    (hSortRs : RulesSorted d0.rsPool d0.rsM s2.rs_n.toNat)
    (hOkRs : ∀ j < s2.rs_n.toNat,
      (d0.rsPool.getD (d0.rsM.getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hTotRs : monoTotalWords d0.rsPool d0.rsM s2.rs_n.toNat ≤ s2.rs_ptop.toNat)
    (hSyRs : SymsBound d0.rsPool d0.rsM s2.rs_n.toNat s0.n_nets.toNat)
    (hRep : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ t.bindArr) s0.n_nets.toNat t.partnerArr ∧
      RulesRep s0.modW (cSig g ρ t.bindArr) s2 t.ruleOff t.ruleN
        d0.rsM d0.rsL d0.rsH d0.rsPool)
    (hRep1' : ∀ ρ : Nat → Bool,
      RulesRep s0.modW (cSig g ρ t.bindArr) s1' t.ruleOff t.ruleN
        dL.rsM dL.rsL dL.rsH dL.rsPool)
    (hSlL : ∀ j < s1'.tn.toNat,
      MonoSliceOk (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
        ((if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat s1'.ptop.toNat ∧
      ((if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1).getD
        ((if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
        2 ^ 32)
    (hSortL : ∀ j < s1'.tn.toNat,
      MonoSorted (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
        ((if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat)
    (hSigL : SigOk (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
      (if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1)
      (if s1'.tc.toNat = 0 then dL.ts0 else dL.ts1) s1'.tn.toNat)
    (hTotL : monoTotalWords (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
      (if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1) s1'.tn.toNat ≤ s1'.ptop.toNat)
    (hEvL : ∀ ρ : Nat → Bool,
      polyEval s0.modW (cSig g ρ t.bindArr)
          (if s1'.pc.toNat = 0 then dL.pool0 else dL.pool1)
          (if s1'.tc.toNat = 0 then dL.tm0 else dL.tm1)
          (if s1'.tc.toNat = 0 then dL.tl0 else dL.tl1)
          (if s1'.tc.toNat = 0 then dL.th0 else dL.th1) s1'.tn.toNat =
        sp0TargetEval s0.spec s0.modW g ρ)
    (hRbr : Rbr =
      (aigArraysMem s1' t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 s1'.bind t.bindArr ⋆
       u32PadTail s1'.rule_off t.ruleOff.length ⋆ u32PadTail s1'.rule_n t.ruleN.length ⋆
       arrayPad i32 s1'.partner t.partnerArr ⋆ u8PadTail s1'.flipped flL.length ⋆
       arrayPad i32 s1'.in_net t.inNetArr ⋆ arrayPad i32 s1'.out_ref t.outRefArr ⋆
       gateScratchMem s1' t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
       region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
       tMem s1' dL.tm0 dL.tm1 dL.ts0 dL.tl0 dL.th0 dL.ts1 dL.tl1 dL.th1 dL.pool0 dL.pool1 ⋆
       arrayPad i32 s1'.qm dL.qm ⋆ array64 s1'.qs dL.qs ⋆ array64 s1'.ql dL.ql ⋆
       array64 s1'.qh dL.qh ⋆ u32PadTail s1'.ix dL.ix.length ⋆
       u32PadTail s1'.ix2 dL.ix2.length ⋆ arrayPad i32 s1'.bx dL.bx ⋆
       arrayPad i32 s1'.vq_off dL.vqOff ⋆ arrayPad i32 s1'.vq dL.vq ⋆
       arrayPad i8 s1'.vq_skip dL.vqSkip ⋆
       region (s1'.w + s1'.top) (s1'.wlen.toNat - s1'.top.toNat) ⋆
       bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R))
    (hm_br : (arCtxMem cx s1' ⋆ array (t := i32) s1'.rule_off t.ruleOff ⋆
      array (t := i32) s1'.rule_n t.ruleN ⋆ array (t := i8) s1'.flipped flL ⋆
      rsMem s1' dL.rsM dL.rsL dL.rsH dL.rsPool ⋆
      rMem s1' dL.rm dL.rl dL.rh dL.rm2 dL.rl2 dL.rh2 dL.rpool ⋆
      array (t := i32) s1'.ix dL.ix ⋆ array (t := i32) s1'.ix2 dL.ix2 ⋆ Rbr) m1')
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hkJ : ∀ (sB : ArCtxState) (dB : CmDynArrs) (mB : Mem 64),
      dB.LenOk s0.qcap.toNat →
      dB.rsM = d0.rsM → dB.rsL = d0.rsL → dB.rsH = d0.rsH → dB.rsPool = d0.rsPool →
      sB = { s1 with
        pos := sB.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
        tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop, qn := sB.qn,
        ix := sB.ix, ix2 := sB.ix2, cur_rm := sB.cur_rm, cur_rl := sB.cur_rl,
        cur_rh := sB.cur_rh, cur_rp := sB.cur_rp, cur_nr := sB.cur_nr } →
      ((sB.ix = s0.ix ∧ sB.ix2 = s0.ix2) ∨ (sB.ix = s0.ix2 ∧ sB.ix2 = s0.ix)) →
      sB.pc.toNat < 2 → sB.tc.toNat < 2 →
      sB.tn.toNat ≤ s0.tcap.toNat → sB.ptop.toNat ≤ s0.pcap.toNat → sB.pos = s1'.pos →
      (∀ j < sB.tn.toNat,
        MonoSliceOk (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat sB.ptop.toNat ∧
        ((if sB.pc.toNat = 0 then dB.pool0 else dB.pool1).getD
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
          2 ^ 32) →
      (∀ j < sB.tn.toNat,
        MonoSorted (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
          ((if sB.tc.toNat = 0 then dB.tm0 else dB.tm1).getD j 0#32).toNat) →
      SigOk (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
        (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
        (if sB.tc.toNat = 0 then dB.ts0 else dB.ts1) sB.tn.toNat →
      monoTotalWords (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
        (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1) sB.tn.toNat ≤ sB.ptop.toNat →
      (∀ ρ : Nat → Bool,
        polyEval s0.modW (cSig g ρ t.bindArr)
            (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
            (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
            (if sB.tc.toNat = 0 then dB.tl0 else dB.tl1)
            (if sB.tc.toNat = 0 then dB.th0 else dB.th1) sB.tn.toNat =
          sp0TargetEval s0.spec s0.modW g ρ) →
      (arCtxMem cx sB ⋆ bytes s0.art artBytes ⋆
        cmArenaMem sB s0 top0 { t with flippedArr := flL } dB ⋆ bytes aig aigBytes ⋆ R) mB →
      wp Γ Q X (Expr.jump J ()) mB) :
    let kOk := @Expr.group Val Cont [.bool] [[i32]]
      (fun _Js =>
        Blocks.cons
          (fun p =>
            @Expr.call Val Cont [.bool] "ar_apply" [i64, i32] [.bool]
              (Arg.var cx, Arg.var p.fst, ()) fun p =>
              Expr.jnz (Arg.var p.fst) (Expr.jump J ()) (Expr.ret (Arg.imm false, ())))
          Blocks.nil)
      fun Js =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var cx, Arg.imm 136, ()) } fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) } fun p =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var ld, Arg.var p.fst, ()) } fun p =>
              Expr.load i8 (Arg.var p.fst) fun ld =>
                Expr.let_
                  { sig := [i32], code := OpCode.trunc 32 8,
                    args := (Arg.imm 0, ()) } fun p =>
                  Expr.let_
                    { sig := [i8], code := OpCode.zext 8 32,
                      args := (Arg.var ld, ()) } fun p_1 =>
                    Expr.let_
                      { sig := [i8], code := OpCode.zext 8 32,
                        args := (Arg.var p.fst, ()) } fun p =>
                      Expr.let_
                        { sig := [i32, i32],
                          code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
                          args := (Arg.var p_1.fst, Arg.var p.fst, ()) } fun p =>
                        Expr.jnz (Arg.var p.fst)
                          (Expr.let_
                            { sig := [i32, i32], code := OpCode.mul i32,
                              args := (Arg.imm 2, Arg.var v, ()) } fun p =>
                            Expr.let_
                              { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                              Expr.jump Js.fst (Arg.var p.fst, ()))
                          (Expr.let_
                            { sig := [i32, i32], code := OpCode.mul i32,
                              args := (Arg.imm 2, Arg.var v, ()) } fun p =>
                            Expr.jump Js.fst (Arg.var p.fst, ()))
    wp Γ Q X (@Expr.call Val Cont [.bool] "ar_build_R" [i64, i32] [.bool]
      (Arg.var cx, Arg.var v, ()) fun p =>
      Expr.jnz (Arg.var p.fst) kOk (Expr.ret (Arg.imm false, ())) ) m1' := by
  have hqcap32 : s0.qcap.toNat + 16 < 2 ^ 32 := by have := hb.cap_hi; omega
  have hpcap32 : s0.pcap.toNat < 2 ^ 32 := by rw [hb.pcap_eq]; have := hb.cap_hi; omega
  have hrcap30 : s0.rs_cap.toNat < 2 ^ 30 := by rw [hb.rs_cap_eq]; have := hb.cap_hi; omega
  have hrpcap32 : s0.rs_pcap.toNat < 2 ^ 32 := by
    rw [hb.rs_pcap_eq, hb.pcap_eq]; have := hb.cap_hi; omega
  apply wp_call_of_spec
  refine hBuildR _ _ _ _ ⟨s1', t.ruleOff, t.ruleN, dL.rsM, dL.rsL, dL.rsH, dL.rsPool,
    flL, dL.rm, dL.rl, dL.rh, dL.rm2, dL.rl2, dL.rh2, dL.rpool, dL.ix, dL.ix2,
    fun σ => ∃ ρ : Nat → Bool, σ = cSig g ρ t.bindArr, Rbr,
    by rw [show s1'.n_nets = s0.n_nets by rw [hs1'_s1, hs1_eq]]; exact hv_lt, hv_ne,
    by rw [show s1'.n_nets = s0.n_nets by rw [hs1'_s1, hs1_eq]]; exact hb.nnets_bd,
    by rw [show s1'.n_nets = s0.n_nets by rw [hs1'_s1, hs1_eq], lfl]
       have := htLen.2.2.2.2.2.2.2.1; omega,
    by rw [show s1'.qcap = s0.qcap by rw [hs1'_s1, hs1_eq]]; exact hb.cap_lo,
    by rw [show s1'.qcap = s0.qcap by rw [hs1'_s1, hs1_eq]]; exact hqcap32,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq],
           show s1'.qcap = s0.qcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq]
       exact Nat.le_refl _,
    by rw [show s1'.rpcap = s0.rpcap by rw [hs1'_s1, hs1_eq], hb.rpcap_eq]
       exact hpcap32,
    by rw [show s1'.rs_cap = s0.rs_cap by rw [hs1'_s1, hs1_eq]]; exact hrcap30,
    by rw [show s1'.rs_pcap = s0.rs_pcap by rw [hs1'_s1, hs1_eq]]; exact hrpcap32,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq, CmDynArrs.len_rm hdL]
       exact Nat.le_refl _,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq, CmDynArrs.len_rl hdL]
       exact Nat.le_refl _,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq, CmDynArrs.len_rh hdL]
       exact Nat.le_refl _,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq, CmDynArrs.len_rm2 hdL]
       exact Nat.le_refl _,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq, CmDynArrs.len_rl2 hdL]
       exact Nat.le_refl _,
    by rw [show s1'.rcap = s0.rcap by rw [hs1'_s1, hs1_eq], hb.rcap_eq, CmDynArrs.len_rh2 hdL]
       exact Nat.le_refl _,
    by rw [show s1'.rpcap = s0.rpcap by rw [hs1'_s1, hs1_eq], hb.rpcap_eq, hb.pcap_eq,
           CmDynArrs.len_rpool hdL]
       exact Nat.le_refl _,
    by rw [show s1'.qcap = s0.qcap by rw [hs1'_s1, hs1_eq], CmDynArrs.len_ix hdL]
       exact Nat.le_refl _,
    by rw [show s1'.qcap = s0.qcap by rw [hs1'_s1, hs1_eq], CmDynArrs.len_ix2 hdL]
       exact Nat.le_refl _,
    by rw [CmDynArrs.len_ix hdL, CmDynArrs.len_ix2 hdL],
    by rw [show s1'.modW = s0.modW by
             simp only [ArCtxState.modW, show s1'.spec = s0.spec by rw [hs1'_s1, hs1_eq],
               show s1'.n_out = s0.n_out by rw [hs1'_s1, hs1_eq]],
           show s1'.mlo = s0.mlo by rw [hs1'_s1, hs1_eq],
           show s1'.mhi = s0.mhi by rw [hs1'_s1, hs1_eq]]; exact hb.masks,
    ⟨cSig g (fun _ => false) t.bindArr, fun _ => false, rfl⟩,
    fun σ ⟨ρ, hρ⟩ => by
      subst hρ
      rw [show s1'.n_nets = s0.n_nets by rw [hs1'_s1, hs1_eq],
          show s1'.modW = s0.modW by
            simp only [ArCtxState.modW, show s1'.spec = s0.spec by rw [hs1'_s1, hs1_eq],
              show s1'.n_out = s0.n_out by rw [hs1'_s1, hs1_eq]]]
      exact ⟨fun w _ => cSig_odd g ρ t.bindArr w, hRep1' ρ⟩,
    by rw [hrsm_eq, hrsp_eq, show s1'.rs_n = s2.rs_n by rw [hs1'_s1]]; exact hSortRs,
    by rw [hrsm_eq, hrsp_eq, show s1'.rs_n = s2.rs_n by rw [hs1'_s1]]; exact hOkRs,
    by rw [hrsm_eq, hrsp_eq, show s1'.rs_n = s2.rs_n by rw [hs1'_s1],
           show s1'.rs_ptop = s2.rs_ptop by rw [hs1'_s1]]; exact hTotRs,
    by rw [hrsm_eq, hrsp_eq, show s1'.rs_n = s2.rs_n by rw [hs1'_s1],
           show s1'.n_nets = s0.n_nets by rw [hs1'_s1, hs1_eq]]; exact hSyRs,
    hm_br,
    fun okR sR rmR rlR rhR rm2R rl2R rh2R rpoolR ixR ix2R mR
      hsR lrmR lrlR lrhR lrm2R lrl2R lrh2R lrpR lixR lix2R hokR hmR => ?_⟩
  let dR : CmDynArrs := { dL with
    rm := rmR, rl := rlR, rh := rhR, rm2 := rm2R, rl2 := rl2R, rh2 := rh2R,
    rpool := rpoolR, ix := ixR, ix2 := ix2R }
  have hdLenR := d_LenOk_buildR hdL lrmR lrlR lrhR lrm2R lrl2R lrh2R lrpR lixR lix2R
  have hsR_s1 : sR = { s1 with
      pos := sR.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := sR.tc, tn := sR.tn, pc := sR.pc, ptop := sR.ptop, qn := sR.qn,
      ix := sR.ix, ix2 := sR.ix2, cur_rm := sR.cur_rm, cur_rl := sR.cur_rl,
      cur_rh := sR.cur_rh, cur_rp := sR.cur_rp, cur_nr := sR.cur_nr } := by
    rw [hsR, hs1'_s1]
  have hixSwR : (sR.ix = s0.ix ∧ sR.ix2 = s0.ix2) ∨ (sR.ix = s0.ix2 ∧ sR.ix2 = s0.ix) := by
    rw [show sR.ix = s1'.ix by rw [hsR], show sR.ix2 = s1'.ix2 by rw [hsR]]; exact hixSw1'
  have hmR_ar := cmArena_buildR_repack (cx := cx) (aig := aig) (s0 := s0) (top0 := top0)
    (aigBytes := aigBytes) (artBytes := artBytes) (tL := { t with flippedArr := flL })
    (dR := dR) (R := R) hsR rfl lixR lix2R
    (by
      have hmR' := hmR
      rw [hRbr] at hmR'
      dsimp only [Arg.val] at hmR'
      dsimp only [dR]
      exact sep_cast hmR' (by ac_rfl))
  cases hokR_v : okR
  · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    exact main_fail_collapse hb htLen hs1_eq lfl hdLenR hsR_s1 hixSwR hmR_ar hFail
  · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    obtain hR_cases := hokR hokR_v
    dsimp only [Arg.val] at hR_cases
    have hsw_v : (BitVec.setWidth 64 v).toNat = v.toNat := by
      have hv32 := v.isLt
      simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)]
    have hv_in : v.toNat < flL.length := by
      rw [lfl]; have := htLen.2.2.2.2.2.2.2.1; have := hv_lt; omega
    have hv_lt2 : v.toNat < s2.n_nets.toNat := by rw [hs2_nn]; exact hv_lt
    have hrs_tot_bd : monoTotalWords d0.rsPool d0.rsM s2.rs_n.toNat ≤ 4000000000 := by
      have hrspt1' : s1'.rs_ptop.toNat ≤ s1'.rs_pcap.toNat := (hRep1' (fun _ => false)).2.2.2.1
      have hrspt2 : s2.rs_ptop.toNat ≤ s0.rs_pcap.toNat := by
        rw [show s2.rs_ptop = s1'.rs_ptop by rw [hs1'_s1],
            show s0.rs_pcap = s1'.rs_pcap by rw [hs1'_s1, hs1_eq]]
        exact hrspt1'
      rw [hb.rs_pcap_eq, hb.pcap_eq] at hrspt2
      have := hTotRs; have := hb.cap_hi; omega
    refine wp_join_state1 (fun sym : BitVec 32 => sym)
      (fun sym mJ => sym.toNat =
          (if flL.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat) ∧ mJ = mR)
      (fun _ sym _ ⟨hsym_val, hmJ⟩ => by
        subst hmJ
        exact main_even_apply Γ hApply hb htLen hdLenR lfl hs1_eq hs1'_s1 hsR hixSwR
          hsR_s1 hrsm_eq hrsl_eq hrsh_eq hrsp_eq hv_lt hv_lt2 hv_ne hsym_val
          (by rw [hsR]; exact hpcL) (by rw [hsR]; exact htcL)
          (by rw [hsR]; exact htnL) (by rw [hsR]; exact hptL)
          hSortRs hOkRs hrs_tot_bd hRep hRep1' hrsm_eq hrsl_eq hrsh_eq hrsp_eq
          (by rw [show sR.pc = s1'.pc by rw [hsR], show sR.tc = s1'.tc by rw [hsR],
                  show sR.ptop = s1'.ptop by rw [hsR], show sR.tn = s1'.tn by rw [hsR]]
              dsimp only [dR]; exact hSlL)
          (by rw [show sR.pc = s1'.pc by rw [hsR], show sR.tc = s1'.tc by rw [hsR],
                  show sR.tn = s1'.tn by rw [hsR]]; dsimp only [dR]; exact hSortL)
          (by rw [show sR.pc = s1'.pc by rw [hsR], show sR.tc = s1'.tc by rw [hsR],
                  show sR.tn = s1'.tn by rw [hsR]]; dsimp only [dR]; exact hSigL)
          (by rw [show sR.pc = s1'.pc by rw [hsR], show sR.tc = s1'.tc by rw [hsR],
                  show sR.ptop = s1'.ptop by rw [hsR], show sR.tn = s1'.tn by rw [hsR]]
              dsimp only [dR]; exact hTotL)
          (fun ρ => by
            rw [show sR.pc = s1'.pc by rw [hsR], show sR.tc = s1'.tc by rw [hsR],
                show sR.tn = s1'.tn by rw [hsR]]; dsimp only [dR]; exact hEvL ρ)
          (hR_cases.imp id (fun ⟨h1, h2, h3, h4, _, h5⟩ => ⟨h1, h2, h3, h4, h5⟩))
          hmR_ar hFail hkJ)
      (fun Js hJs => by
        c0_hsteps_nogrp
        · refine hJs _ mR ⟨?_, rfl⟩
          have hc' : flL.getD v.toNat 0#8 ≠ 0#8 := by
            intro h
            apply hc
            simp only [getD_eq_getElem flL 0#8 hv_in] at h
            rw [h]; rfl
          try rw [show (2 : BitVec 32) = 2#32 from rfl]
          simp only [hc', ↓reduceIte, ne_eq, not_false_eq_true]
          rw [BitVec.toNat_add, BitVec.toNat_mul,
            Nat.mod_eq_of_lt (by simp [BitVec.toNat_ofNat]; omega),
            Nat.mod_eq_of_lt (by rw [BitVec.toNat_ofNat]; omega)]
          rfl
        · refine hJs _ mR ⟨?_, rfl⟩
          have hc' : ¬ (flL.getD v.toNat 0#8 ≠ 0#8) := by
            intro h; apply h
            simp only [getD_eq_getElem flL 0#8 hv_in]
            have h' := congrArg BitVec.toNat hc
            simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
            exact BitVec.eq_of_toNat_eq (by simpa [hsw_v] using h')
          try rw [show (2 : BitVec 32) = 2#32 from rfl]
          simp only [hc', ↓reduceIte]
          rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by simp [BitVec.toNat_ofNat]; omega)]
          rfl)

private theorem main_loop_exit_ok {cx : Val i64} {Q : Post [.bool]}
    {s0 s1 sL : ArCtxState} {rsN : BitVec 32} {rsPtop : BitVec 64}
    {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t : CmTabArrs} {flL : List (BitVec 8)} {dL : CmDynArrs} {R : Mem 64 → Prop} {mL : Mem 64}
    {aig : Val i64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t.LenOk g s0) (lfl : flL.length = t.flippedArr.length)
    (hdL : dL.LenOk s0.qcap.toNat)
    (hs1_eq : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hsL : sL = { s1 with
      pos := sL.pos, rs_n := rsN, rs_ptop := rsPtop,
      tc := sL.tc, tn := sL.tn, pc := sL.pc, ptop := sL.ptop, qn := sL.qn,
      ix := sL.ix, ix2 := sL.ix2, cur_rm := sL.cur_rm, cur_rl := sL.cur_rl,
      cur_rh := sL.cur_rh, cur_rp := sL.cur_rp, cur_nr := sL.cur_nr })
    (hixSw : (sL.ix = s0.ix ∧ sL.ix2 = s0.ix2) ∨ (sL.ix = s0.ix2 ∧ sL.ix2 = s0.ix))
    (htn0 : sL.tn = 0#32)
    (hEvL : ∀ ρ : Nat → Bool,
      polyEval s0.modW (cSig g ρ t.bindArr)
          (if sL.pc.toNat = 0 then dL.pool0 else dL.pool1)
          (if sL.tc.toNat = 0 then dL.tm0 else dL.tm1)
          (if sL.tc.toNat = 0 then dL.tl0 else dL.tl1)
          (if sL.tc.toNat = 0 then dL.th0 else dL.th1) sL.tn.toNat =
        sp0TargetEval s0.spec s0.modW g ρ)
    (hmL : (arCtxMem cx sL ⋆ bytes s0.art artBytes ⋆
      cmArenaMem sL s0 top0 { t with flippedArr := flL } dL ⋆ bytes aig aigBytes ⋆ R) mL)
    (hTrue : ∀ (s' : ArCtxState) (m' : Mem 64),
      (∀ ρ : Nat → Bool,
        0#(s0.modW) = sp0TargetEval s0.spec s0.modW g ρ) →
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (true, ⟨⟩) m') :
    Q (true, ⟨⟩) mL := by
  have htn0_nat : sL.tn.toNat = 0 := by rw [htn0]; rfl
  have htLenL : ({ t with flippedArr := flL } : CmTabArrs).LenOk g s0 :=
    ⟨htLen.1, htLen.2.1, htLen.2.2.1, htLen.2.2.2.1, htLen.2.2.2.2.1,
     htLen.2.2.2.2.2.1, htLen.2.2.2.2.2.2.1, lfl ▸ htLen.2.2.2.2.2.2.2.1,
     htLen.2.2.2.2.2.2.2.2⟩
  have hdGeomL : DynGeom sL top0 s0.qcap.toNat :=
    DynGeom.preserve hb.dgeom (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq]) hixSw (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
      (by rw [hsL, hs1_eq])
  have htGeomL := tgeom_rw (s := sL) hb.tgeom (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
    (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
    (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
    (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
    (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
    (by rw [hsL, hs1_eq])
  have hcol := collapse_dyn_and_tables (t := { t with flippedArr := flL })
    hb htLenL hdL hdGeomL (by rw [hsL, hs1_eq]) (by rw [hsL, hs1_eq])
    (by rw [show sL.top = s0.top by rw [hsL, hs1_eq],
            show sL.wlen = s0.wlen by rw [hsL, hs1_eq]]; exact hb.top_le_wlen)
    htGeomL hmL
  refine hTrue sL mL (fun ρ => ?_) hcol
  have h1 := hEvL ρ; rw [htn0_nat, polyEval_zero] at h1
  exact h1

/-- `n_main` loop and final `pos == nw` / `tn == 0` checks of `ar_check_main`. -/
theorem main_main_loop_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hBuildR : ∀ xs m Q X, arBuildRSpec xs m Q X → Γ "ar_build_R" [i64, i32] [.bool] xs m Q X)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    {cx aig aigLen art artLen : Val i64} {Q : Post [.bool]} {X : XPost}
    {s0 s1 s2 : ArCtxState} {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t : CmTabArrs} {d0 : CmDynArrs} {R : Mem 64 → Prop} {m2 : Mem 64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t.LenOk g s0) (hdLen : d0.LenOk s0.qcap.toNat)
    (hs1_eq : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs2_eq : s2 = { s1 with
      pos := s2.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s2.tc, tn := s2.tn, pc := s2.pc, ptop := s2.ptop, qn := s2.qn,
      ix := s2.ix, ix2 := s2.ix2, cur_rm := s2.cur_rm, cur_rl := s2.cur_rl,
      cur_rh := s2.cur_rh, cur_rp := s2.cur_rp, cur_nr := s2.cur_nr })
    (hixSw2 : (s2.ix = s0.ix ∧ s2.ix2 = s0.ix2) ∨ (s2.ix = s0.ix2 ∧ s2.ix2 = s0.ix))
    (hpc2 : s2.pc.toNat < 2) (htc2 : s2.tc.toNat < 2)
    (htn2 : s2.tn.toNat ≤ s0.tcap.toNat) (hpt2 : s2.ptop.toNat ≤ s0.pcap.toNat)
    (hpos2 : s2.pos.toNat ≤ s0.nw.toNat)
    (_hrsn2 : s2.rs_n.toNat ≤ s0.rs_cap.toNat) (_hrspt2 : s2.rs_ptop.toNat ≤ s0.rs_pcap.toNat)
    (hTotRs : monoTotalWords d0.rsPool d0.rsM s2.rs_n.toNat ≤ s2.rs_ptop.toNat)
    (hSyRs : SymsBound d0.rsPool d0.rsM s2.rs_n.toNat s0.n_nets.toNat)
    (hOkRs : ∀ j < s2.rs_n.toNat,
      (d0.rsPool.getD (d0.rsM.getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortRs : RulesSorted d0.rsPool d0.rsM s2.rs_n.toNat)
    (hRep : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ t.bindArr) s0.n_nets.toNat t.partnerArr ∧
      RulesRep s0.modW (cSig g ρ t.bindArr) s2 t.ruleOff t.ruleN
        d0.rsM d0.rsL d0.rsH d0.rsPool)
    (hSl2 : ∀ j < s2.tn.toNat,
      MonoSliceOk (if s2.pc.toNat = 0 then d0.pool0 else d0.pool1)
        ((if s2.tc.toNat = 0 then d0.tm0 else d0.tm1).getD j 0#32).toNat s2.ptop.toNat ∧
      ((if s2.pc.toNat = 0 then d0.pool0 else d0.pool1).getD
        ((if s2.tc.toNat = 0 then d0.tm0 else d0.tm1).getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSort2 : ∀ j < s2.tn.toNat,
      MonoSorted (if s2.pc.toNat = 0 then d0.pool0 else d0.pool1)
        ((if s2.tc.toNat = 0 then d0.tm0 else d0.tm1).getD j 0#32).toNat)
    (hSig2 : SigOk (if s2.pc.toNat = 0 then d0.pool0 else d0.pool1)
      (if s2.tc.toNat = 0 then d0.tm0 else d0.tm1)
      (if s2.tc.toNat = 0 then d0.ts0 else d0.ts1) s2.tn.toNat)
    (hTot2 : monoTotalWords (if s2.pc.toNat = 0 then d0.pool0 else d0.pool1)
      (if s2.tc.toNat = 0 then d0.tm0 else d0.tm1) s2.tn.toNat ≤ s2.ptop.toNat)
    (hEv2 : ∀ ρ : Nat → Bool,
      polyEval s0.modW (cSig g ρ t.bindArr)
          (if s2.pc.toNat = 0 then d0.pool0 else d0.pool1)
          (if s2.tc.toNat = 0 then d0.tm0 else d0.tm1)
          (if s2.tc.toNat = 0 then d0.tl0 else d0.tl1)
          (if s2.tc.toNat = 0 then d0.th0 else d0.th1) s2.tn.toNat =
        sp0TargetEval s0.spec s0.modW g ρ)
    (hm2 : (arCtxMem cx s2 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s2 s0 top0 t d0 ⋆
      bytes aig aigBytes ⋆ R) m2)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hTrue : ∀ (s' : ArCtxState) (m' : Mem 64),
      (∀ ρ : Nat → Bool,
        0#(s0.modW) = sp0TargetEval s0.spec s0.modW g ρ) →
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (true, ⟨⟩) m') :
    wp Γ Q X (cmMainExpr cx aig aigLen art artLen) m2 := by
  unfold cmMainExpr cmSp0Expr cmConesExpr cmGatesExpr
  have hnw4 : 4 * s0.nw.toNat ≤ artBytes.length := by rw [hb.nw4]; exact Nat.le_refl _
  refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i32]) (mL : Mem 64) =>
      let ⟨i, ⟨⟩⟩ := args
      i.toNat ≤ s0.n_main.toNat ∧ rem = s0.n_main.toNat - i.toNat ∧
      ∃ (sL : ArCtxState) (flL : List (BitVec 8)) (dL : CmDynArrs),
        let tL : CmTabArrs := { t with flippedArr := flL }
        flL.length = t.flippedArr.length ∧ dL.LenOk s0.qcap.toNat ∧
        dL.rsM = d0.rsM ∧ dL.rsL = d0.rsL ∧ dL.rsH = d0.rsH ∧ dL.rsPool = d0.rsPool ∧
        sL = { s1 with
          pos := sL.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
          tc := sL.tc, tn := sL.tn, pc := sL.pc, ptop := sL.ptop, qn := sL.qn,
          ix := sL.ix, ix2 := sL.ix2, cur_rm := sL.cur_rm, cur_rl := sL.cur_rl,
          cur_rh := sL.cur_rh, cur_rp := sL.cur_rp, cur_nr := sL.cur_nr } ∧
        ((sL.ix = s0.ix ∧ sL.ix2 = s0.ix2) ∨ (sL.ix = s0.ix2 ∧ sL.ix2 = s0.ix)) ∧
        sL.pc.toNat < 2 ∧ sL.tc.toNat < 2 ∧
        sL.tn.toNat ≤ s0.tcap.toNat ∧ sL.ptop.toNat ≤ s0.pcap.toNat ∧
        sL.pos.toNat ≤ s0.nw.toNat ∧
        (∀ j < sL.tn.toNat,
          MonoSliceOk (if sL.pc.toNat = 0 then dL.pool0 else dL.pool1)
            ((if sL.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat sL.ptop.toNat ∧
          ((if sL.pc.toNat = 0 then dL.pool0 else dL.pool1).getD
            ((if sL.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat 0#32).toNat + 1 <
            2 ^ 32) ∧
        (∀ j < sL.tn.toNat,
          MonoSorted (if sL.pc.toNat = 0 then dL.pool0 else dL.pool1)
            ((if sL.tc.toNat = 0 then dL.tm0 else dL.tm1).getD j 0#32).toNat) ∧
        SigOk (if sL.pc.toNat = 0 then dL.pool0 else dL.pool1)
          (if sL.tc.toNat = 0 then dL.tm0 else dL.tm1)
          (if sL.tc.toNat = 0 then dL.ts0 else dL.ts1) sL.tn.toNat ∧
        monoTotalWords (if sL.pc.toNat = 0 then dL.pool0 else dL.pool1)
          (if sL.tc.toNat = 0 then dL.tm0 else dL.tm1) sL.tn.toNat ≤ sL.ptop.toNat ∧
        (∀ ρ : Nat → Bool,
          polyEval s0.modW (cSig g ρ t.bindArr)
              (if sL.pc.toNat = 0 then dL.pool0 else dL.pool1)
              (if sL.tc.toNat = 0 then dL.tm0 else dL.tm1)
              (if sL.tc.toNat = 0 then dL.tl0 else dL.tl1)
              (if sL.tc.toNat = 0 then dL.th0 else dL.th1) sL.tn.toNat =
            sp0TargetEval s0.spec s0.modW g ρ) ∧
        (arCtxMem cx sL ⋆ bytes s0.art artBytes ⋆ cmArenaMem sL s0 top0 tL dL ⋆
          bytes aig aigBytes ⋆ R) mL) ?_ ?_
  · intro J rem ⟨i, ⟨⟩⟩ mL hrec
      ⟨hi_le, _, sL, flL, dL, lfl, hdL, hrsm_eq, hrsl_eq, hrsh_eq, hrsp_eq,
       hsL, hixSw, hpcL, htcL, htnL, hptL, hposL, hSlL, hSortL, hSigL, hTotL, hEvL, hmL⟩
    have hnm_eq : sL.n_main = s0.n_main := by rw [hsL, hs1_eq]
    c0_hstraight
    c0_hstep
    · have hi_lt : i.toNat < s0.n_main.toNat := by rw [← hnm_eq]; exact hc
      have hip1 := bv32_add1_lt hi_lt
      let tL : CmTabArrs := { t with flippedArr := flL }
      have hmL_nw : (arCtxMem cx sL ⋆ bytes sL.art artBytes ⋆
          (cmArenaMem sL s0 top0 tL dL ⋆ bytes aig aigBytes ⋆ R)) mL := by
        rw [show sL.art = s0.art by rw [hsL, hs1_eq]]; exact sep_cast hmL (by ac_rfl)
      c0_hsteps_nogrp
      dsimp only [Arg.val]; apply wp_call_of_spec
      refine hNW _ _ _ _ ⟨sL, artBytes, cmArenaMem sL s0 top0 tL dL ⋆ bytes aig aigBytes ⋆ R,
        by rw [show sL.art = s0.art by rw [hsL, hs1_eq]]; exact hb.art_fit,
        by rw [show sL.nw = s0.nw by rw [hsL, hs1_eq]]; exact hnw4, hmL_nw,
        fun ok1 op s1' m1' hif1 hm1' => ?_⟩
      cases hok1 : ok1
      · rw [hok1] at hif1; dsimp only
        refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
        c0_hstraight
        have hs1'_eq : s1' = sL := by
          by_cases hlt : sL.pos.toNat < sL.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif1
          · cases hif1.1
          · exact hif1.2.2
        have hm1_ar : (arCtxMem cx s1' ⋆ bytes s0.art artBytes ⋆
            cmArenaMem s1' s0 top0 tL dL ⋆ bytes aig aigBytes ⋆ R) m1' := by
          rw [show sL.art = s0.art by rw [hsL, hs1_eq], ← hs1'_eq] at hm1'
          exact sep_cast hm1' (by ac_rfl)
        exact main_fail_collapse hb htLen hs1_eq lfl hdL (by rw [hs1'_eq, hsL])
          (by rw [show s1'.ix = sL.ix by rw [hs1'_eq], show s1'.ix2 = sL.ix2 by rw [hs1'_eq]]
              exact hixSw) hm1_ar hFail
      · rw [hok1] at hif1; dsimp only
        refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
        have hpos_lt : sL.pos.toNat < sL.nw.toNat := by
          by_cases hlt : sL.pos.toNat < sL.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif1
          · exact hlt
          · cases hif1.1
        simp only [hpos_lt, ↓reduceIte] at hif1
        rcases hif1 with ⟨_, _, hs1'_eq⟩
        have hs1'_pos : s1'.pos.toNat ≤ s0.nw.toNat := by
          have := s0.nw.isLt; rw [show sL.nw = s0.nw by rw [hsL, hs1_eq]] at hpos_lt
          rw [hs1'_eq, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]; omega
        have hs1'_s1 : s1' = { s1 with
            pos := s1'.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
            tc := s1'.tc, tn := s1'.tn, pc := s1'.pc, ptop := s1'.ptop, qn := s1'.qn,
            ix := s1'.ix, ix2 := s1'.ix2, cur_rm := s1'.cur_rm, cur_rl := s1'.cur_rl,
            cur_rh := s1'.cur_rh, cur_rp := s1'.cur_rp, cur_nr := s1'.cur_nr } := by
          rw [hs1'_eq, hsL]
        have hm1_ar : (arCtxMem cx s1' ⋆ bytes s0.art artBytes ⋆
            cmArenaMem s1' s0 top0 tL dL ⋆ bytes aig aigBytes ⋆ R) m1' := by
          rw [show sL.art = s0.art by rw [hsL, hs1_eq]] at hm1'
          rw [s1'_ar_eq (by rw [hs1'_eq])]; exact sep_cast hm1' (by ac_rfl)
        have hixSw1' : (s1'.ix = s0.ix ∧ s1'.ix2 = s0.ix2) ∨
            (s1'.ix = s0.ix2 ∧ s1'.ix2 = s0.ix) := by
          rw [show s1'.ix = sL.ix by rw [hs1'_eq], show s1'.ix2 = sL.ix2 by rw [hs1'_eq]]
          exact hixSw
        c0_hstraight
        c0_hstep
        · exact main_fail_collapse hb htLen hs1_eq lfl hdL hs1'_s1 hixSw1' hm1_ar hFail
        · let v := op >>> 1#32
          have hv_lt : v.toNat < s0.n_nets.toNat := by
            have h1 : (op >>> 1#32).toNat < s1'.n_nets.toNat := by
              simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using hc
            have h2 : s1'.n_nets = s0.n_nets := by rw [hs1'_s1, hs1_eq]
            rw [← h2]
            exact h1
          have hv_rn : (BitVec.setWidth 64 v).toNat < t.ruleN.length := by
            rw [bv64_sw_toNat]; have := htLen.2.2.2.2.2.1; omega
          have hv_fl : (BitVec.setWidth 64 v).toNat < flL.length := by
            rw [bv64_sw_toNat, lfl]; have := htLen.2.2.2.2.2.2.2.1; omega
          have h2v1_lt : 2 * v.toNat + 1 < 2 ^ 32 := by have := hb.nnets_bd; omega
          have hRep1' := main_rulesRep_step hs2_eq hs1'_s1 hrsm_eq hrsl_eq hrsh_eq hrsp_eq hRep
          have hs1'_L : s1'.pc = sL.pc ∧ s1'.tc = sL.tc ∧ s1'.tn = sL.tn ∧
              s1'.ptop = sL.ptop := by simp [hs1'_eq]
          c0_hstep
          c0_hstraight
          c0_hstep
          · -- Even (`APPLY`) branch (`(op & 1) == 0`)
            let Rbr : Mem 64 → Prop :=
              aigArraysMem s1' tL.rhs0 tL.rhs1 tL.olit ⋆ arrayPad i32 s1'.bind tL.bindArr ⋆
              u32PadTail s1'.rule_off tL.ruleOff.length ⋆ u32PadTail s1'.rule_n tL.ruleN.length ⋆
              arrayPad i32 s1'.partner tL.partnerArr ⋆ u8PadTail s1'.flipped tL.flippedArr.length ⋆
              arrayPad i32 s1'.in_net tL.inNetArr ⋆ arrayPad i32 s1'.out_ref tL.outRefArr ⋆
              gateScratchMem s1' tL.stkN tL.stkP tL.memoN tL.memoV tL.dense tL.gsy tL.gcl tL.gch ⋆
              region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
              tMem s1' dL.tm0 dL.tm1 dL.ts0 dL.tl0 dL.th0 dL.ts1 dL.tl1 dL.th1 dL.pool0 dL.pool1 ⋆
              arrayPad i32 s1'.qm dL.qm ⋆ array64 s1'.qs dL.qs ⋆ array64 s1'.ql dL.ql ⋆
              array64 s1'.qh dL.qh ⋆ u32PadTail s1'.ix dL.ix.length ⋆
              u32PadTail s1'.ix2 dL.ix2.length ⋆ arrayPad i32 s1'.bx dL.bx ⋆
              arrayPad i32 s1'.vq_off dL.vqOff ⋆ arrayPad i32 s1'.vq dL.vq ⋆
              arrayPad i8 s1'.vq_skip dL.vqSkip ⋆
              region (s1'.w + s1'.top) (s1'.wlen.toNat - s1'.top.toNat) ⋆
              bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R
            have hm_br : (arCtxMem cx s1' ⋆ array (t := i32) s1'.rule_off t.ruleOff ⋆
                array (t := i32) s1'.rule_n t.ruleN ⋆ array (t := i8) s1'.flipped flL ⋆
                rsMem s1' dL.rsM dL.rsL dL.rsH dL.rsPool ⋆
                rMem s1' dL.rm dL.rl dL.rh dL.rm2 dL.rl2 dL.rh2 dL.rpool ⋆
                array (t := i32) s1'.ix dL.ix ⋆ array (t := i32) s1'.ix2 dL.ix2 ⋆ Rbr) m1' := by
              rw [arena_unpack_buildR] at hm1_ar
              exact sep_cast hm1_ar (by dsimp only [Rbr]; ac_rfl)
            c0_hstraight
            c0_hstep
            · exact main_fail_collapse hb htLen hs1_eq lfl hdL hs1'_s1 hixSw1' hm1_ar hFail
            · have hv_ne : t.ruleN.getD v.toNat 0#32 ≠ cNone32 := by
                rw [getD_eq_getElem t.ruleN 0#32 (by have := htLen.2.2.2.2.2.1; omega)]
                have h1 : t.ruleN[(BitVec.setWidth 64 v).toNat]'hv_rn ≠ 0xFFFFFFFF#32 := ‹_›
                simpa only [bv64_sw_toNat, cNone32] using h1
              dsimp only [Arg.val]
              refine main_even_buildR_call Γ hBuildR hApply hb htLen hdL lfl
                hrsm_eq hrsl_eq hrsh_eq hrsp_eq hs1_eq hs1'_s1 hixSw1'
                (by rw [hs1'_L.1]; exact hpcL) (by rw [hs1'_L.2.1]; exact htcL)
                (by rw [hs1'_L.2.2.1]; exact htnL) (by rw [hs1'_L.2.2.2]; exact hptL)
                hs1'_pos hv_lt (by rw [hs2_eq, hs1_eq]) hv_ne hv_fl h2v1_lt
                hSortRs hOkRs hTotRs hSyRs hRep hRep1'
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1, hs1'_L.2.2.2]; exact hSlL)
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1]; exact hSortL)
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1]; exact hSigL)
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1, hs1'_L.2.2.2]; exact hTotL)
                (fun ρ => by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1]; exact hEvL ρ)
                rfl hm_br hFail ?_
              intro sB dB mB hdB hrsM hrsL hrsH hrsP hsB_s1 hixB hpcB htcB htnB hptB
                hposB hSlB hSortB hSigB hTotB hEvB hmB_ar
              c0_hstraight
              exact hrec (s0.n_main.toNat - (i + 1#32).toNat) (i + 1#32, ⟨⟩) mB (by omega)
                ⟨by omega, by rw [hip1], sB, flL, dB, lfl, hdB,
                  hrsM, hrsL, hrsH, hrsP, hsB_s1, hixB, hpcB, htcB, htnB, hptB,
                  by rw [hposB]; exact hs1'_pos, hSlB, hSortB, hSigB, hTotB, hEvB, hmB_ar⟩
          · -- Odd (`FLIP`) branch (`(op & 1) != 0`)
            have hrm_l16 : 16 ≤ dL.rm.length := by rw [CmDynArrs.len_rm hdL]; exact hb.cap_lo
            have hrl_l16 : 16 ≤ dL.rl.length := by rw [CmDynArrs.len_rl hdL]; exact hb.cap_lo
            have hrh_l16 : 16 ≤ dL.rh.length := by rw [CmDynArrs.len_rh hdL]; exact hb.cap_lo
            have hrp_l192 : 192 ≤ dL.rpool.length := by
              rw [CmDynArrs.len_rpool hdL]; have := hb.cap_lo; omega
            let Rflip0 : Mem 64 → Prop :=
              aigArraysMem s1' t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 s1'.bind t.bindArr ⋆
              arrayPad i32 s1'.rule_off t.ruleOff ⋆ arrayPad i32 s1'.rule_n t.ruleN ⋆
              u32PadTail s1'.partner t.partnerArr.length ⋆ u8PadTail s1'.flipped flL.length ⋆
              arrayPad i32 s1'.in_net t.inNetArr ⋆ arrayPad i32 s1'.out_ref t.outRefArr ⋆
              gateScratchMem s1' t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
              region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
              rsMem s1' dL.rsM dL.rsL dL.rsH dL.rsPool ⋆
              u32PadTail s1'.rm dL.rm.length ⋆
              arrayPad i32 s1'.rm2 dL.rm2 ⋆ array64 s1'.rl2 dL.rl2 ⋆ array64 s1'.rh2 dL.rh2 ⋆
              u32PadTail s1'.rpool dL.rpool.length ⋆
              region (s1'.w + s1'.top) (s1'.wlen.toNat - s1'.top.toNat)
            have hm_fl0 : (arCtxMem cx s1' ⋆ array (t := i8) s1'.flipped flL ⋆
                array (t := i32) s1'.rm dL.rm ⋆ array64 s1'.rl dL.rl ⋆
                array64 s1'.rh dL.rh ⋆ array (t := i32) s1'.rpool dL.rpool ⋆
                array (t := i32) s1'.partner t.partnerArr ⋆
                tMem s1' dL.tm0 dL.tm1 dL.ts0 dL.tl0 dL.th0 dL.ts1 dL.tl1 dL.th1
                  dL.pool0 dL.pool1 ⋆
                qMem s1' dL.qm dL.qs dL.ql dL.qh dL.ix dL.ix2 dL.bx dL.vqOff dL.vq dL.vqSkip ⋆
                Rflip0 ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) m1' := by
              rw [arena_unpack_apply] at hm1_ar
              dsimp only [rMem] at hm1_ar
              rw [arrayPad_u8_unfold s1'.flipped flL,
                arrayPad_u32_unfold s1'.rm dL.rm, arrayPad_u32_unfold s1'.rpool dL.rpool] at hm1_ar
              exact sep_cast hm1_ar (by dsimp only [Rflip0]; ac_rfl)
            c0_hstraight
            c0_hstep
            · exact main_fail_collapse hb htLen hs1_eq lfl hdL hs1'_s1 hixSw1' hm1_ar hFail
            · let Rbase : Mem 64 → Prop :=
                array (t := i8) s1'.flipped flL ⋆ array (t := i32) s1'.partner t.partnerArr ⋆
                tMem s1' dL.tm0 dL.tm1 dL.ts0 dL.tl0 dL.th0 dL.ts1 dL.tl1 dL.th1
                  dL.pool0 dL.pool1 ⋆
                qMem s1' dL.qm dL.qs dL.ql dL.qh dL.ix dL.ix2 dL.bx dL.vqOff dL.vq dL.vqSkip ⋆
                Rflip0 ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R
              c0_hsteps_nogrp
              refine wp_store_arr32_abs (base := s1'.rpool) (xs := dL.rpool) (idx := 0#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rm dL.rm ⋆ array64 s1'.rl dL.rl ⋆
                  array64 s1'.rh dL.rh ⋆ Rbase)
                rfl rfl (by simp only [BitVec.toNat_ofNat]; omega)
                (sep_cast ‹_› (by dsimp only [Rbase]; ac_rfl)) fun _ _ => ?_
              c0_hstraight; refine wp_store_arr32_abs (base := s1'.rpool)
                (xs := dL.rpool.set 0 0#32) (idx := 1#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rm dL.rm ⋆ array64 s1'.rl dL.rl ⋆
                  array64 s1'.rh dL.rh ⋆ Rbase)
                rfl rfl (by simp only [List.length_set, BitVec.toNat_ofNat]; omega)
                ‹_› fun _ _ => ?_
              c0_hstraight; refine wp_store_arr32_abs (base := s1'.rpool)
                (xs := (dL.rpool.set 0 0#32).set 1 1#32) (idx := 2#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rm dL.rm ⋆ array64 s1'.rl dL.rl ⋆
                  array64 s1'.rh dL.rh ⋆ Rbase)
                rfl rfl (by simp only [List.length_set, BitVec.toNat_ofNat]; omega)
                ‹_› fun _ hm_rp2 => ?_
              c0_hstraight
              let rpF := ((dL.rpool.set 0 0#32).set 1 1#32).set 2 (2#32 * v + 1#32)
              refine wp_store_arr32_abs (base := s1'.rm) (xs := dL.rm) (idx := 0#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rpool rpF ⋆
                  array64 s1'.rl dL.rl ⋆ array64 s1'.rh dL.rh ⋆ Rbase)
                rfl rfl (by simp only [BitVec.toNat_ofNat]; omega)
                (by rw [show ((2#64 : BitVec 64).toNat) = 2 from rfl] at hm_rp2
                    dsimp only [Arg.val, v, rpF] at hm_rp2 ⊢
                    rw [show (2 : BitVec 32) = 2#32 from rfl] at hm_rp2
                    exact sep_cast hm_rp2 (by ac_rfl)) fun _ _ => ?_
              c0_hstraight; refine wp_store_arr64_abs (base := s1'.rl) (xs := dL.rl) (idx := 0#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rpool rpF ⋆
                  array (t := i32) s1'.rm (dL.rm.set 0 0#32) ⋆ array64 s1'.rh dL.rh ⋆ Rbase)
                rfl rfl (by simp only [BitVec.toNat_ofNat]; omega)
                (sep_cast ‹_› (by ac_rfl)) fun _ _ => ?_
              c0_hstraight
              let rlF0 := dL.rl.set 0 (1#64 &&& s1'.mlo)
              refine wp_store_arr64_abs (base := s1'.rh) (xs := dL.rh) (idx := 0#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rpool rpF ⋆
                  array (t := i32) s1'.rm (dL.rm.set 0 0#32) ⋆ array64 s1'.rl rlF0 ⋆ Rbase)
                rfl rfl (by simp only [BitVec.toNat_ofNat]; omega)
                (sep_cast ‹_› (by dsimp only [rlF0]; ac_rfl)) fun _ _ => ?_
              c0_hstraight
              let rhF0 := dL.rh.set 0 0#64
              refine wp_store_arr32_abs (base := s1'.rm) (xs := dL.rm.set 0 0#32) (idx := 1#64)
                (R := arCtxMem cx s1' ⋆ array (t := i32) s1'.rpool rpF ⋆
                  array64 s1'.rl rlF0 ⋆ array64 s1'.rh rhF0 ⋆ Rbase)
                rfl rfl (by simp only [List.length_set, BitVec.toNat_ofNat]; omega)
                (sep_cast ‹_› (by dsimp only [rhF0]; ac_rfl)) fun _ hm_rm1 => ?_
              c0_hstraight
              let rmF := (dL.rm.set 0 0#32).set 1 1#32
              let Rcneg : Mem 64 → Prop := array (t := i32) s1'.rm rmF ⋆ array64 s1'.rl rlF0 ⋆
                array64 s1'.rh rhF0 ⋆ array (t := i32) s1'.rpool rpF ⋆ Rbase
              apply wp_call_of_spec
              refine hCneg _ _ _ _ ⟨s1', Rcneg,
                by rw [show s1'.modW = s0.modW by
                         simp only [ArCtxState.modW,
                           show s1'.spec = s0.spec by rw [hs1'_s1, hs1_eq],
                           show s1'.n_out = s0.n_out by rw [hs1'_s1, hs1_eq]],
                       show s1'.mlo = s0.mlo by rw [hs1'_s1, hs1_eq],
                       show s1'.mhi = s0.mhi by rw [hs1'_s1, hs1_eq]]; exact hb.masks,
                sep_cast ‹_› (by dsimp only [Rbase, Rcneg, rmF]; ac_rfl), fun nl nh hcneg => ?_⟩
              c0_hsteps_nogrp
              let RcnegTail : Mem 64 → Prop :=
                array (t := i32) s1'.rm rmF ⋆ array (t := i32) s1'.rpool rpF ⋆ Rbase
              refine wp_store_arr64_abs (base := s1'.rl) (xs := rlF0) (idx := 1#64)
                (R := arCtxMem cx s1' ⋆ array64 s1'.rh rhF0 ⋆ RcnegTail)
                rfl rfl (by simp only [rlF0, List.length_set, BitVec.toNat_ofNat]; omega)
                (by rw [show ((1#64 : BitVec 64).toNat) = 1 from rfl] at hm_rm1
                    dsimp only [Arg.val] at hm_rm1
                    exact sep_cast hm_rm1 (by dsimp only [Rbase, RcnegTail, rmF]; ac_rfl))
                fun _ _ => ?_
              c0_hstraight
              refine wp_store_arr64_abs (base := s1'.rh) (xs := rhF0) (idx := 1#64)
                (R := arCtxMem cx s1' ⋆ array64 s1'.rl (rlF0.set 1 nl) ⋆ RcnegTail)
                rfl rfl (by simp only [rhF0, List.length_set, BitVec.toNat_ofNat]; omega)
                (sep_cast ‹_› (by ac_rfl)) fun _ hm_rh1 => ?_
              c0_hsteps_nogrp
              dsimp only [Arg.val]
              refine main_odd_flip_apply Γ hApply hb htLen hdL lfl
                hrsm_eq hrsl_eq hrsh_eq hrsp_eq hs1_eq hs1'_s1 hixSw1'
                (by rw [hs1'_L.1]; exact hpcL) (by rw [hs1'_L.2.1]; exact htcL)
                (by rw [hs1'_L.2.2.1]; exact htnL) (by rw [hs1'_L.2.2.2]; exact hptL)
                hs1'_pos hv_fl h2v1_lt hcneg rfl hRep
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1, hs1'_L.2.2.2]; exact hSlL)
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1]; exact hSortL)
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1]; exact hSigL)
                (by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1, hs1'_L.2.2.2]; exact hTotL)
                (fun ρ => by rw [hs1'_L.1, hs1'_L.2.1, hs1'_L.2.2.1]; exact hEvL ρ)
                (by
                  have hm_end : (arCtxMem cx _ ⋆ _) _ := ‹_›
                  rw [show ((1#64 : BitVec 64).toNat) = 1 from rfl] at hm_end
                  dsimp only
                  dsimp only [Arg.val, RcnegTail, Rbase, Rflip0, rmF, rlF0, rhF0, rpF,
                    v, tMem, qMem] at hm_end ⊢
                  have hsh_rl : op >>> (1#32 : BitVec 32) = op >>> (1 : Nat) := by
                    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight]
                  try rw [hsh_rl] at hm_end; try rw [hsh_rl]
                  try rw [show (2 : BitVec 32) = 2#32 from rfl] at hm_end
                  try rw [show (2 : BitVec 32) = 2#32 from rfl]
                  try rw [show (1#32 + 2#32 * (op >>> (1 : Nat)) : BitVec 32) =
                    2#32 * (op >>> (1 : Nat)) + 1#32 from BitVec.add_comm _ _] at hm_end
                  try rw [show (1#32 + 2#32 * (op >>> (1 : Nat)) : BitVec 32) =
                    2#32 * (op >>> (1 : Nat)) + 1#32 from BitVec.add_comm _ _]
                  try rw [show (s1'.mlo &&& 1#64) = (1#64 &&& s1'.mlo) from BitVec.and_comm _ _]
                    at hm_end
                  try rw [show (s1'.mlo &&& 1#64) = (1#64 &&& s1'.mlo) from BitVec.and_comm _ _]
                  try rw [show s1'.top + s1'.w = s1'.w + s1'.top from BitVec.add_comm _ _]
                    at hm_end
                  try rw [show s1'.top + s1'.w = s1'.w + s1'.top from BitVec.add_comm _ _]
                  exact sep_cast hm_end (by ac_rfl))
                hFail ?_
              intro sB flB dB mB lflB hdB hrsM hrsL hrsH hrsP hsB_s1 hixB
                hpcB htcB htnB hptB hposB hSlB hSortB hSigB hTotB hEvB hmB_ar
              c0_hstraight
              exact hrec (s0.n_main.toNat - (i + 1#32).toNat) (i + 1#32, ⟨⟩) mB (by omega)
                ⟨by omega, by rw [hip1], sB, flB, dB, lflB, hdB,
                  hrsM, hrsL, hrsH, hrsP, hsB_s1, hixB, hpcB, htcB, htnB, hptB,
                  by rw [hposB]; exact hs1'_pos, hSlB, hSortB, hSigB, hTotB, hEvB, hmB_ar⟩
    · have hc1 := hc
      c0_hstraight
      refine head_wp_jnz rfl (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        exact main_fail_collapse hb htLen hs1_eq lfl hdL hsL hixSw hmL hFail
      · c0_hstraight
        refine head_wp_jnz rfl (fun _ => ?_) (fun hc_tn => ?_)
        · c0_hstraight
          exact main_fail_collapse hb htLen hs1_eq lfl hdL hsL hixSw hmL hFail
        · c0_hstraight
          have htn0 : sL.tn = 0#32 := by
            dsimp only [Arg.val] at hc_tn
            simp only [Bool.eq_false_iff, bne_iff_ne, ne_eq] at hc_tn
            exact Classical.not_not.mp hc_tn
          exact main_loop_exit_ok hb htLen lfl hdL hs1_eq hsL hixSw htn0 hEvL hmL hTrue
  · intro J hJ; c0_hsteps
    exact hJ s0.n_main.toNat (0#32, ⟨⟩) m2 ⟨Nat.zero_le _, Nat.sub_zero _, s2,
      t.flippedArr, d0, rfl, hdLen, rfl, rfl, rfl, rfl, hs2_eq, hixSw2, hpc2, htc2,
      htn2, hpt2, hpos2, hSl2, hSort2, hSig2, hTot2, hEv2, hm2⟩

end

end LeanQbe.T.Examples.Arisca.Proof

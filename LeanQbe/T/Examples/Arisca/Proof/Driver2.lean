/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver2Main
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Bytes
import Kraken.Separation

/-!
# ARiSCA Top-Level Entry Points (`Arisca.Proof.Driver2`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proofs for the remaining `2` functions of
`LeanQbe.T.Examples.Arisca.Src.Driver`:
- `ar_check_main` (`ar_check_main_wp`)
- `arisca_check_bytes` (`arisca_check_bytes_wp`).
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

private theorem bv64_ult_sub_max_toNat (p cap : BitVec 64)
    (h : ((0xFFFFFFFFFFFFFFFF#64 - p).ult cap) = false) :
    p.toNat + cap.toNat < 2 ^ 64 := by
  have hp := p.isLt; have hc := cap.isLt
  have hsub : (0xFFFFFFFFFFFFFFFF#64 - p).toNat = 2 ^ 64 - 1 - p.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 by decide]; omega)),
      show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 by decide]
  simp only [BitVec.ult, decide_eq_false_iff_not, not_lt, hsub] at h
  omega

private theorem bv64_pad_eq (p : BitVec 64) :
    (((8 : BitVec 64) - (p &&& (7 : BitVec 64)) &&& (7 : BitVec 64))).toNat =
      (8 - p.toNat % 8) % 8 := by
  have h1 : (p &&& (7 : BitVec 64)).toNat = p.toNat % 8 := by
    rw [BitVec.toNat_and, show ((7 : BitVec 64)).toNat = 7 from rfl]
    simpa using Nat.and_two_pow_sub_one_eq_mod p.toNat 3
  have hlt1 : (p &&& (7 : BitVec 64)).toNat < 8 := by rw [h1]; exact Nat.mod_lt _ (by decide)
  have hsub : ((8 : BitVec 64) - (p &&& (7 : BitVec 64))).toNat = 8 - p.toNat % 8 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [show ((8 : BitVec 64)).toNat = 8 from rfl]; omega)),
      show ((8 : BitVec 64)).toNat = 8 from rfl, h1]
  rw [BitVec.toNat_and, show ((7 : BitVec 64)).toNat = 7 from rfl, hsub]
  simpa using Nat.and_two_pow_sub_one_eq_mod (8 - p.toNat % 8) 3

private theorem tablesEndTop_ge776 (A O nNets nIn nOut : Nat) :
    776 ≤ tablesEndTop A O nNets nIn nOut := by
  dsimp only [tablesEndTop]
  omega

private theorem bindRep_rw {s0 s : ArCtxState} {g : Aig}
    {bindArr inNetArr outRefArr : List (BitVec 32)}
    (hb : BindRep s0 g bindArr inNetArr outRefArr)
    (h1 : s.n_nets = s0.n_nets) (h2 : s.n_in = s0.n_in) (h3 : s.n_out = s0.n_out) :
    BindRep s g bindArr inNetArr outRefArr :=
  { bind_len := h1 ▸ hb.bind_len,
    bind_bound := h1 ▸ hb.bind_bound,
    in_len := h2 ▸ hb.in_len,
    in_eq := h2 ▸ hb.in_eq,
    i_even := hb.i_even,
    in_ok := fun i hi => by rw [h2] at hi; rw [h1]; exact hb.in_ok i hi,
    out_len := h3 ▸ hb.out_len,
    out_eq := h3 ▸ hb.out_eq,
    out_bounds := h3 ▸ hb.out_bounds,
    out_ok := fun j hj => by rw [h3] at hj; rw [h1]; exact hb.out_ok j hj }

private theorem arena_unpack_sp0 {s0 s1 s : ArCtxState} {top0 : Nat}
    {t : CmTabArrs} {d : CmDynArrs}
    (hs1 : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs : s = { s1 with
      pos := s.pos, rs_n := s.rs_n, rs_ptop := s.rs_ptop,
      tc := s.tc, tn := s.tn, pc := s.pc, ptop := s.ptop, qn := s.qn,
      ix := s.ix, ix2 := s.ix2, cur_rm := s.cur_rm, cur_rl := s.cur_rl,
      cur_rh := s.cur_rh, cur_rp := s.cur_rp, cur_nr := s.cur_nr }) :
    cmArenaMem s s0 top0 t d =
      (array (t := i32) s.bind t.bindArr ⋆ array (t := i32) s.in_net t.inNetArr ⋆
       array (t := i32) s.out_ref t.outRefArr ⋆ array (t := i32) s.partner t.partnerArr ⋆
       tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
       qMem s d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
       (aigArraysMem s0 t.rhs0 t.rhs1 t.olit ⋆
        u32PadTail s0.bind t.bindArr.length ⋆ arrayPad i32 s0.rule_off t.ruleOff ⋆
        arrayPad i32 s0.rule_n t.ruleN ⋆ u32PadTail s0.partner t.partnerArr.length ⋆
        arrayPad i8 s0.flipped t.flippedArr ⋆ u32PadTail s0.in_net t.inNetArr.length ⋆
        u32PadTail s0.out_ref t.outRefArr.length ⋆
        gateScratchMem s0 t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        rsMem s0 d.rsM d.rsL d.rsH d.rsPool ⋆
        rMem s0 d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
        region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat))) := by
  dsimp only [cmArenaMem]
  have h1 : aigArraysMem s t.rhs0 t.rhs1 t.olit = aigArraysMem s0 t.rhs0 t.rhs1 t.olit := by
    simp only [aigArraysMem, show s.rhs0 = s0.rhs0 by rw [hs, hs1],
      show s.rhs1 = s0.rhs1 by rw [hs, hs1], show s.olit = s0.olit by rw [hs, hs1]]
  have h2 : gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch =
      gateScratchMem s0 t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch := by
    simp only [gateScratchMem, show s.stk_n = s0.stk_n by rw [hs, hs1],
      show s.stk_p = s0.stk_p by rw [hs, hs1], show s.memo_n = s0.memo_n by rw [hs, hs1],
      show s.memo_v = s0.memo_v by rw [hs, hs1], show s.dense = s0.dense by rw [hs, hs1],
      show s.gsy = s0.gsy by rw [hs, hs1], show s.gcl = s0.gcl by rw [hs, hs1],
      show s.gch = s0.gch by rw [hs, hs1]]
  have h3 : rsMem s d.rsM d.rsL d.rsH d.rsPool = rsMem s0 d.rsM d.rsL d.rsH d.rsPool := by
    simp only [rsMem, show s.rs_m = s0.rs_m by rw [hs, hs1], show s.rs_l = s0.rs_l by rw [hs, hs1],
      show s.rs_h = s0.rs_h by rw [hs, hs1], show s.rs_pool = s0.rs_pool by rw [hs, hs1]]
  have h4 : rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool =
      rMem s0 d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool := by
    simp only [rMem, show s.rm = s0.rm by rw [hs, hs1], show s.rl = s0.rl by rw [hs, hs1],
      show s.rh = s0.rh by rw [hs, hs1], show s.rm2 = s0.rm2 by rw [hs, hs1],
      show s.rl2 = s0.rl2 by rw [hs, hs1], show s.rh2 = s0.rh2 by rw [hs, hs1],
      show s.rpool = s0.rpool by rw [hs, hs1]]
  rw [h1, h2, h3, h4, netTablesMem_unpack]
  simp only [arrayPad_u32_unfold,
    show s.bind = s0.bind by rw [hs, hs1], show s.rule_off = s0.rule_off by rw [hs, hs1],
    show s.rule_n = s0.rule_n by rw [hs, hs1], show s.partner = s0.partner by rw [hs, hs1],
    show s.flipped = s0.flipped by rw [hs, hs1], show s.in_net = s0.in_net by rw [hs, hs1],
    show s.out_ref = s0.out_ref by rw [hs, hs1], show s.w = s0.w by rw [hs, hs1],
    show s.top = s0.top by rw [hs, hs1], show s.wlen = s0.wlen by rw [hs, hs1]]
  ac_rfl

private theorem main_sp0_phase (Γ : LeanQbe.T.Env)
    (hBuildSp0 : ∀ xs m Q X, arBuildSp0Spec xs m Q X → Γ "ar_build_sp0" [i64] [.bool] xs m Q X)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hBuildR : ∀ xs m Q X, arBuildRSpec xs m Q X → Γ "ar_build_R" [i64, i32] [.bool] xs m Q X)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    {cx aig aigLen art artLen : Val i64} {Q : Post [.bool]} {X : XPost}
    {s0 s1 s2 : ArCtxState} {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t2 : CmTabArrs} {d2 : CmDynArrs} {R : Mem 64 → Prop} {m2 : Mem 64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t2.LenOk g s0) (hdLen : d2.LenOk s0.qcap.toNat)
    (hBind : BindRep s0 g t2.bindArr t2.inNetArr t2.outRefArr)
    (hs1 : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs2 : s2 = { s1 with
      pos := s2.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s2.tc, tn := s2.tn, pc := s2.pc, ptop := s2.ptop, qn := s2.qn,
      ix := s2.ix, ix2 := s2.ix2, cur_rm := s2.cur_rm, cur_rl := s2.cur_rl,
      cur_rh := s2.cur_rh, cur_rp := s2.cur_rp, cur_nr := s2.cur_nr })
    (hixSw2 : (s2.ix = s0.ix ∧ s2.ix2 = s0.ix2) ∨ (s2.ix = s0.ix2 ∧ s2.ix2 = s0.ix))
    (hpc2 : s2.pc.toNat < 2) (htc2 : s2.tc.toNat < 2) (hpos2 : s2.pos.toNat ≤ s0.nw.toNat)
    (hrsn2 : s2.rs_n.toNat ≤ s0.rs_cap.toNat) (hrspt2 : s2.rs_ptop.toNat ≤ s0.rs_pcap.toNat)
    (hTot2 : monoTotalWords d2.rsPool d2.rsM s2.rs_n.toNat ≤ s2.rs_ptop.toNat)
    (hSy2 : SymsBound d2.rsPool d2.rsM s2.rs_n.toNat s0.n_nets.toNat)
    (hOk2 : ∀ i < s2.rs_n.toNat,
      (d2.rsPool.getD (d2.rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSort2 : RulesSorted d2.rsPool d2.rsM s2.rs_n.toNat)
    (hRep2 : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ t2.bindArr) s0.n_nets.toNat t2.partnerArr ∧
      RulesRep s0.n_out.toNat (cSig g ρ t2.bindArr) s2 t2.ruleOff t2.ruleN
        d2.rsM d2.rsL d2.rsH d2.rsPool)
    (hm2 : (arCtxMem cx s2 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s2 s0 top0 t2 d2 ⋆
      bytes aig aigBytes ⋆ R) m2)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hTrue : ∀ (s' : ArCtxState) (m' : Mem 64),
      (∀ ρ : Nat → Bool,
        BitVec.ofNat s0.n_out.toNat (outWord g ρ) =
          BitVec.ofInt s0.n_out.toNat (inWord (decide (s0.spec = 1#32)) (g.I / 2) ρ 0) *
            BitVec.ofInt s0.n_out.toNat (inWord (decide (s0.spec = 1#32)) (g.I / 2) ρ (g.I / 2))) →
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (true, ⟨⟩) m') :
    wp Γ Q X (cmSp0Expr cx aig aigLen art artLen) m2 := by
  have htcap30 : s0.tcap.toNat < 2 ^ 30 := by rw [hb.tcap_eq]; have := hb.cap_hi; omega
  have hqcap32 : s0.qcap.toNat + 16 < 2 ^ 32 := by have := hb.cap_hi; omega
  have hpcap32 : s0.pcap.toNat < 2 ^ 32 := by rw [hb.pcap_eq]; have := hb.cap_hi; omega
  have h2nn32 : 2 * s0.n_nets.toNat < 2 ^ 32 := by have := hb.nnets_bd; omega
  have hs2_s0 : s2 = { s0 with
      pos := s2.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs,
      tc := s2.tc, tn := s2.tn, pc := s2.pc, ptop := s2.ptop, qn := s2.qn,
      ix := s2.ix, ix2 := s2.ix2, cur_rm := s2.cur_rm, cur_rl := s2.cur_rl,
      cur_rh := s2.cur_rh, cur_rp := s2.cur_rp, cur_nr := s2.cur_nr } := by
    rw [hs2, hs1]
  let Rsp0 : Mem 64 → Prop :=
    aigArraysMem s0 t2.rhs0 t2.rhs1 t2.olit ⋆ u32PadTail s0.bind t2.bindArr.length ⋆
    arrayPad i32 s0.rule_off t2.ruleOff ⋆ arrayPad i32 s0.rule_n t2.ruleN ⋆
    u32PadTail s0.partner t2.partnerArr.length ⋆ arrayPad i8 s0.flipped t2.flippedArr ⋆
    u32PadTail s0.in_net t2.inNetArr.length ⋆ u32PadTail s0.out_ref t2.outRefArr.length ⋆
    gateScratchMem s0 t2.stkN t2.stkP t2.memoN t2.memoV t2.dense t2.gsy t2.gcl t2.gch ⋆
    region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
    rsMem s0 d2.rsM d2.rsL d2.rsH d2.rsPool ⋆
    rMem s0 d2.rm d2.rl d2.rh d2.rm2 d2.rl2 d2.rh2 d2.rpool ⋆
    region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat) ⋆
    bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R
  have hm_sp0 : (arCtxMem cx s2 ⋆ array (t := i32) s2.bind t2.bindArr ⋆
      array (t := i32) s2.in_net t2.inNetArr ⋆ array (t := i32) s2.out_ref t2.outRefArr ⋆
      array (t := i32) s2.partner t2.partnerArr ⋆
      tMem s2 d2.tm0 d2.tm1 d2.ts0 d2.tl0 d2.th0 d2.ts1 d2.tl1 d2.th1 d2.pool0 d2.pool1 ⋆
      qMem s2 d2.qm d2.qs d2.ql d2.qh d2.ix d2.ix2 d2.bx d2.vqOff d2.vq d2.vqSkip ⋆
      Rsp0) m2 := by
    rw [arena_unpack_sp0 hs1 hs2] at hm2
    exact sep_cast hm2 (by dsimp only [Rsp0]; ac_rfl)
  have hBind2 : BindRep s2 g t2.bindArr t2.inNetArr t2.outRefArr :=
    bindRep_rw hBind (by rw [hs2_s0]) (by rw [hs2_s0]) (by rw [hs2_s0])
  dsimp only [cmSp0Expr]
  apply wp_call_of_spec
  refine hBuildSp0 _ _ _ _ ⟨s2, g, t2.bindArr, t2.inNetArr, t2.outRefArr, t2.partnerArr,
    d2.tm0, d2.tm1, d2.ts0, d2.tl0, d2.th0, d2.ts1, d2.tl1, d2.th1, d2.pool0, d2.pool1,
    d2.qm, d2.qs, d2.ql, d2.qh, d2.ix, d2.ix2, d2.bx, d2.vqOff, d2.vq, d2.vqSkip, Rsp0,
    hpc2, htc2,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0]]; exact htcap30,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]; exact hb.cap_lo,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]; exact hqcap32,
    by rw [show s2.pcap = s0.pcap by rw [hs2_s0]]; exact hpcap32,
    by rw [show s2.n_nets = s0.n_nets by rw [hs2_s0]]; exact hb.nnets_bd,
    by rw [show s2.n_nets = s0.n_nets by rw [hs2_s0]]; exact h2nn32,
    by rw [show s2.spec = s0.spec by rw [hs2_s0]]; exact hb.spec_01,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.tcap = s0.tcap by rw [hs2_s0], hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.pcap = s0.pcap by rw [hs2_s0], hb.pcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.pcap = s0.pcap by rw [hs2_s0], hb.pcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [show s2.qcap = s0.qcap by rw [hs2_s0]]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1],
    by rw [show s2.n_out = s0.n_out by rw [hs2_s0], show s2.mlo = s0.mlo by rw [hs2_s0],
           show s2.mhi = s0.mhi by rw [hs2_s0]]; exact hb.masks,
    hBind2, fun ρ => by
      rw [show s2.n_nets = s0.n_nets by rw [hs2_s0]]
      exact (hRep2 ρ).1, hm_sp0,
    fun ok s3 tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh' ix' ix2' m3
      hpc3 htc3 htn3 hpt3 hqn3 hs3_eq ltm0 ltm1 lts0 ltl0 lth0 lts1 ltl1 lth1 lp0 lp1
      lqm lqs lql lqh hixSw3' hok3 hm3 => ?_⟩
  have hs3_s2 : s3 = { s2 with
      pos := s3.pos, rs_n := s3.rs_n, rs_ptop := s3.rs_ptop,
      tc := s3.tc, tn := s3.tn, pc := s3.pc, ptop := s3.ptop, qn := s3.qn,
      ix := s3.ix, ix2 := s3.ix2, cur_rm := s3.cur_rm, cur_rl := s3.cur_rl,
      cur_rh := s3.cur_rh, cur_rp := s3.cur_rp, cur_nr := s3.cur_nr } := by
    rw [hs3_eq]
  have hs3_s1 : s3 = { s1 with
      pos := s3.pos, rs_n := s3.rs_n, rs_ptop := s3.rs_ptop,
      tc := s3.tc, tn := s3.tn, pc := s3.pc, ptop := s3.ptop, qn := s3.qn,
      ix := s3.ix, ix2 := s3.ix2, cur_rm := s3.cur_rm, cur_rl := s3.cur_rl,
      cur_rh := s3.cur_rh, cur_rp := s3.cur_rp, cur_nr := s3.cur_nr } := by
    rw [hs3_eq, hs2]
  have hs3_s0 : s3 = { s0 with
      pos := s3.pos, rs_n := s3.rs_n, rs_ptop := s3.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs,
      tc := s3.tc, tn := s3.tn, pc := s3.pc, ptop := s3.ptop, qn := s3.qn,
      ix := s3.ix, ix2 := s3.ix2, cur_rm := s3.cur_rm, cur_rl := s3.cur_rl,
      cur_rh := s3.cur_rh, cur_rp := s3.cur_rp, cur_nr := s3.cur_nr } := by
    rw [hs3_eq, hs2_s0]
  have hixSw3 : (s3.ix = s0.ix ∧ s3.ix2 = s0.ix2) ∨ (s3.ix = s0.ix2 ∧ s3.ix2 = s0.ix) := by
    rcases hixSw2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hixSw3' with ⟨h3, h4, _⟩ | ⟨h3, h4, _⟩
    · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inr ⟨h3.trans h2, h4.trans h1⟩
    · exact Or.inr ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inl ⟨h3.trans h2, h4.trans h1⟩
  have lix3 : ix'.length = s0.qcap.toNat ∧ ix2'.length = s0.qcap.toNat := by
    rcases hixSw3' with ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2⟩
    · exact ⟨h1.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        h2.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    · exact ⟨h1.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        h2.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  let d3 : CmDynArrs := { d2 with
    tm0 := tm0', tm1 := tm1', ts0 := ts0', tl0 := tl0', th0 := th0',
    ts1 := ts1', tl1 := tl1', th1 := th1', pool0 := pool0', pool1 := pool1',
    qm := qm', qs := qs', ql := ql', qh := qh', ix := ix', ix2 := ix2' }
  have hdLen3 : d3.LenOk s0.qcap.toNat :=
    ⟨hdLen.1, hdLen.2.1, hdLen.2.2.1, hdLen.2.2.2.1,
     ltm0.trans hdLen.2.2.2.2.1, ltm1.trans hdLen.2.2.2.2.2.1, lts0.trans hdLen.2.2.2.2.2.2.1,
     ltl0.trans hdLen.2.2.2.2.2.2.2.1, lth0.trans hdLen.2.2.2.2.2.2.2.2.1,
     lts1.trans hdLen.2.2.2.2.2.2.2.2.2.1, ltl1.trans hdLen.2.2.2.2.2.2.2.2.2.2.1,
     lth1.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.1, lp0.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lp1.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1, lqm.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lqs.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lql.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lqh.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lix3.1, lix3.2, hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hm3_ar : (arCtxMem cx s3 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s3 s0 top0 t2 d3 ⋆
      bytes aig aigBytes ⋆ R) m3 := by
    rw [arena_unpack_sp0 hs1 hs3_s1]
    dsimp only [Arg.val] at hm3
    exact sep_cast hm3 (by dsimp only [Rsp0, d3]; ac_rfl)
  cases ok
  · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    have hdGeom3 : DynGeom s3 top0 s0.qcap.toNat :=
      DynGeom.preserve hb.dgeom (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
        (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
        (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
        (by rw [hs3_s0]) (by rw [hs3_s0]) hixSw3 (by rw [hs3_s0]) (by rw [hs3_s0])
        (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
        (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
    have htGeom3 := tgeom_rw (s := s3) hb.tgeom (by rw [hs3_s0]) (by rw [hs3_s0])
      (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
      (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
      (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0]) (by rw [hs3_s0])
      (by rw [hs3_s0]) (by rw [hs3_s0])
    exact hFail s3 m3 (collapse_dyn_and_tables hb htLen hdLen3 hdGeom3
      (by rw [hs3_s0]) (by rw [hs3_s0])
      (by rw [show s3.top = s0.top by rw [hs3_s0], show s3.wlen = s0.wlen by rw [hs3_s0]]
          exact hb.top_le_wlen)
      htGeom3 hm3_ar)
  · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    c0_hsteps_nogrp
    obtain ⟨hSl3, hSort3, hSig3, hTot3, hEv3⟩ := hok3 rfl
    change wp Γ Q X (cmMainExpr cx aig aigLen art artLen) m3
    refine main_main_loop_wp Γ hNW hBuildR hApply hCneg hb htLen hdLen3 hs1 hs3_s1 hixSw3
      hpc3 htc3
      (by rw [show s0.tcap = s2.tcap by rw [hs2_s0]]; exact htn3)
      (by rw [show s0.pcap = s2.pcap by rw [hs2_s0]]; exact hpt3)
      (by rw [show s3.pos = s2.pos by rw [hs3_eq]]; exact hpos2)
      (by rw [show s3.rs_n = s2.rs_n by rw [hs3_eq]]; exact hrsn2)
      (by rw [show s3.rs_ptop = s2.rs_ptop by rw [hs3_eq]]; exact hrspt2)
      (by rw [show s3.rs_n = s2.rs_n by rw [hs3_eq], show s3.rs_ptop = s2.rs_ptop by rw [hs3_eq]]
          exact hTot2)
      (by rw [show s3.rs_n = s2.rs_n by rw [hs3_eq]]; exact hSy2)
      (by rw [show s3.rs_n = s2.rs_n by rw [hs3_eq]]; exact hOk2)
      (by rw [show s3.rs_n = s2.rs_n by rw [hs3_eq]]; exact hSort2)
      (fun ρ => by
        obtain ⟨hp, hr⟩ := hRep2 ρ
        refine ⟨hp, ?_⟩
        dsimp only [RulesRep, d3] at hr ⊢
        rw [show s3.n_nets = s2.n_nets by rw [hs3_s2], show s3.rs_n = s2.rs_n by rw [hs3_eq],
            show s3.rs_cap = s2.rs_cap by rw [hs3_s2], show s3.rs_ptop = s2.rs_ptop by rw [hs3_eq],
            show s3.rs_pcap = s2.rs_pcap by rw [hs3_s2]]
        exact hr)
      hSl3 hSort3 hSig3 hTot3
      (fun ρ => by
        rw [show s0.n_out = s2.n_out by rw [hs2_s0], show s0.spec = s2.spec by rw [hs2_s0]]
        exact hEv3 ρ)
      hm3_ar hFail hTrue

/-- WP soundness for `ar_check_main(cx, aig, aig_len, art, art_len)`. -/
theorem ar_check_main_wp (Γ : LeanQbe.T.Env)
    (hParseAig : ∀ xs m Q X, arParseAigSpec xs m Q X →
      Γ "ar_parse_aig" [i64, i64, i64] [.bool] xs m Q X)
    (hParseArt : ∀ xs m Q X, arParseArtHeaderAndTablesSpec xs m Q X →
      Γ "ar_parse_art_header_and_tables" [i64, i64, i64] [.bool] xs m Q X)
    (hSetupDyn : ∀ xs m Q X, arSetupDynamicSpec xs m Q X →
      Γ "ar_setup_dynamic" [i64] [.bool] xs m Q X)
    (hGate : ∀ xs m Q X, arDoGateSpec xs m Q X → Γ "ar_do_gate" [i64] [.bool] xs m Q X)
    (hCone : ∀ xs m Q X, arDoConeSpec xs m Q X → Γ "ar_do_cone" [i64] [.bool] xs m Q X)
    (hBuildSp0 : ∀ xs m Q X, arBuildSp0Spec xs m Q X → Γ "ar_build_sp0" [i64] [.bool] xs m Q X)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hBuildR : ∀ xs m Q X, arBuildRSpec xs m Q X → Γ "ar_build_R" [i64, i32] [.bool] xs m Q X)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X) :
    ∀ xs m Q X, arCheckMainSpec xs m Q X → Func.wp Γ ar_check_main_body xs m Q X := by
  rintro ⟨cx, aig, aigLen, art, artLen, ⟨⟩⟩ m Q X ⟨s, aigBytes, artBytes, R,
    hwPos, htop, hwlenGe, hwFit, haigLen, hartLen, hartFit,
    hrsn, hrspt, hrscap, hrspcap, hptop, htn, hqn, hpc, htc, hcnr, hm, hQ⟩
  c0_hstraight
  apply wp_call_of_spec
  refine hParseAig (cx, aig, aigLen, ()) _ _ _ ⟨s, aigBytes, bytes art artBytes ⋆ R,
    hwPos, htop, hwlenGe, hwFit, haigLen, sep_cast hm (by ac_rfl),
    fun okA m1 hA => ?_⟩
  rcases hA with ⟨rfl, s', hs'w, hs'wl, _, _, _, _, _, _, _, hm1⟩ |
    ⟨rfl, g, rhs0, rhs1, olit, s1, hParseG, hAig, hMg, hs1w, hs1wl, _, _, _,
      hs1rsn, hs1rspt, hs1rscap, hs1rspcap, hs1ptop, hs1tn, hs1qn, hs1pc, hs1tc, hs1cnr,
      hs1M, hs1I, hs1A, hs1O, hs1r0, hs1r1, hs1ol, hs1top, hs1tlen, hm1⟩
  · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    exact hQ false m1 (fun h => by cases h) ⟨s', sep_cast hm1 (by ac_rfl)⟩
  · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    c0_hstraight
    have hpos1 : 0 < s1.w.toNat := by rw [hs1w]; exact hwPos
    have hfit1 : s1.w.toNat + s1.wlen.toNat < 2 ^ 64 := by rw [hs1w, hs1wl]; exact hwFit
    have hm1' : (arCtxMem cx s1 ⋆ arrayPad i32 s1.rhs0 rhs0 ⋆ arrayPad i32 s1.rhs1 rhs1 ⋆
        array (t := i32) s1.olit olit ⋆ region (s1.w + s1.top) (s1.wlen.toNat - s1.top.toNat) ⋆
        bytes art artBytes ⋆ (bytes aig aigBytes ⋆ R)) m1 :=
      sep_cast hm1 (by ac_rfl)
    apply wp_call_of_spec
    refine hParseArt (cx, art, artLen, ()) _ _ _ ⟨s1, g, rhs0, rhs1, olit, artBytes,
      bytes aig aigBytes ⋆ R, hpos1, hfit1, hs1top, hs1tlen,
      by rw [hs1w]; exact hs1r0, by rw [hs1w]; exact hs1r1, by rw [hs1w]; exact hs1ol,
      hAig, hMg, hs1M, hs1I, hs1A, hs1O,
      hs1rsn.trans hrsn, hs1rspt.trans hrspt, hs1rscap.trans hrscap, hs1rspcap.trans hrspcap,
      hartLen, hartFit, hm1',
      fun okP m2 hP => ?_⟩
    rcases hP with ⟨rfl, s', hs'w, hs'wl, hm2⟩ |
      ⟨rfl, s2, bindArr, ruleOff, ruleN, partnerArr, flippedArr, inNetArr, outRefArr,
        stkN, stkP, memoN, memoV, dense, gsy, gcl, gch,
        hs2w, hs2wl, hs2art, hs2nw, hs2pos, hs2pos_nw, hs2M, hs2I, hs2A, hs2O,
        hs2nn, hs2spec, hs2rsn, hs2rspt, hs2rscap, hs2rspcap, hs2ptop, hs2tn, hs2qn,
        hs2pc, hs2tc, hs2cnr, hs2top, hs2tlen, hs2tg, hs2masks, hBind2,
        lbd, lro, lrn, lpa, lfl, lin, lou, lsn, lsp, lmn, lmv, ldn, lgy, lgl, lgh,
        hfl0, hRep2, hm2⟩
    · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
      c0_hstraight
      rw [hs1w, hs1wl] at hm2
      exact hQ false m2 (fun h => by cases h) ⟨s', sep_cast hm2 (by ac_rfl)⟩
    · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
      c0_hstraight
      let Rsetup : Mem 64 → Prop :=
        aigArraysMem s2 rhs0 rhs1 olit ⋆
        netTablesMem s2 bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
        gateScratchMem s2 stkN stkP memoN memoV dense gsy gcl gch ⋆
        bytes aig aigBytes ⋆ bytes s2.art artBytes ⋆ R
      have hm2_setup : (arCtxMem cx s2 ⋆
          region (s2.w + BitVec.ofNat 64 s2.top.toNat) (s2.top.toNat - s2.top.toNat) ⋆
          region (s2.w + s2.top) (s2.wlen.toNat - s2.top.toNat) ⋆ Rsetup) m2 := by
        rw [Nat.sub_self, region_zero]
        exact sep_cast hm2 (by dsimp only [Rsetup]; rw [hs2art]; ac_rfl)
      dsimp only [Arg.val]
      apply wp_call_of_spec
      refine hSetupDyn (cx, ()) _ _ _ ⟨s2, s2.top.toNat, Rsetup,
        by rw [hs2w, hs1w]; exact hwPos, by rw [hs2w, hs2wl, hs1w, hs1wl]; exact hwFit,
        le_refl _, hs2tlen,
        hs2rsn, hs2rspt, hs2ptop.trans (hs1ptop.trans hptop), hs2tn.trans (hs1tn.trans htn),
        hs2qn.trans (hs1qn.trans hqn), hs2pc.trans (hs1pc.trans hpc),
        hs2tc.trans (hs1tc.trans htc), hs2cnr.trans (hs1cnr.trans hcnr),
        hm2_setup, fun okD m3 hD => ?_⟩
      rcases hD with ⟨rfl, s', hs'w, hs'wl, hm3⟩ |
        ⟨rfl, s3, rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1,
          pool0, pool1, qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip,
          rm, rl, rh, rm2, rl2, rh2, rpool,
          hcap_lo, hcap_hi, hpcap, hrscap, htcap, hrcap, hrspcap, hrpcap,
          hs3tlen, hs3dg, hs3_eq,
          lrm, lrl, lrh, lrp, ltm0, ltm1, lts0, ltl0, lth0, lts1, ltl1, lth1,
          lp0, lp1, lqm, lqs, lql, lqh, lix, lix2, lbx, lvqo, lvq, lvqs,
          lrm_, lrl_, lrh_, lrm2, lrl2, lrh2, lrp_, hm3⟩
      · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
        c0_hstraight
        have hm3_col : (aigArraysMem s2 rhs0 rhs1 olit ⋆
            netTablesMem s2 bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
            gateScratchMem s2 stkN stkP memoN memoV dense gsy gcl gch ⋆
            region (s2.w + BitVec.ofNat 64 s2.top.toNat) (s2.wlen.toNat - s2.top.toNat) ⋆
            (arCtxMem cx s' ⋆ bytes aig aigBytes ⋆ bytes s2.art artBytes ⋆ R)) m3 :=
          sep_cast hm3 (by dsimp only [Rsetup]; ac_rfl)
        have hm3_t := tables_collapse_avail hs2tg
          (hs2top ▸ tablesEndTop_ge776 _ _ _ _ _) hs2tlen
          (by rw [hs2w, hs2wl, hs1w, hs1wl]; exact hwFit)
          hAig.rhs0_len hAig.rhs1_len hAig.olit_len lbd lro lrn lpa lfl lin lou
          lsn lsp lmn lmv ldn lgy lgl lgh hm3_col
        rw [hs2w, hs1w, hs2wl, hs1wl, hs2art] at hm3_t
        exact hQ false m3 (fun h => by cases h) ⟨s', sep_cast hm3_t (by ac_rfl)⟩
      · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
        c0_hsteps_nogrp
        have hs3w : s3.w = s.w := by rw [hs3_eq, hs2w, hs1w]
        have hs3wl : s3.wlen = s.wlen := by rw [hs3_eq, hs2wl, hs1wl]
        have hs3_no : s3.n_out = s2.n_out := by rw [hs3_eq]
        have hs3_art : s3.art = art := by rw [hs3_eq, hs2art]
        have htop0_le : s2.top.toNat ≤ s3.top.toNat := by
          rw [hs3dg.top_eq, hs2top]
          refine le_trans (align8_ge _) ?_
          dsimp only [dynEndTop]
          simp only [Nat.add_assoc]
          exact Nat.le_add_right _ _
        have hM3 : s3.M.toNat = g.M := by rw [show s3.M = s2.M by rw [hs3_eq], hs2M, hs1M]
        have hI3 : s3.I.toNat = g.I := by rw [show s3.I = s2.I by rw [hs3_eq], hs2I, hs1I]
        have hA3 : s3.A.toNat = g.ands.length := by rw [show s3.A = s2.A by rw [hs3_eq], hs2A, hs1A]
        have hO3 : s3.O.toNat = g.outs.length := by rw [show s3.O = s2.O by rw [hs3_eq], hs2O, hs1O]
        have hnw3 : 4 * s3.nw.toNat = artBytes.length := by
          rw [show s3.nw = s2.nw by rw [hs3_eq], hs2nw]
        have hnn3 : s3.n_nets.toNat ≤ 0x3FFFFFFF := by
          rw [show s3.n_nets = s2.n_nets by rw [hs3_eq]]; exact hs2nn
        have hspec3 : s3.spec = 0#32 ∨ s3.spec = 1#32 := by
          rw [show s3.spec = s2.spec by rw [hs3_eq]]; exact hs2spec
        have htg3 : TablesGeom s3 g.ands.length g.outs.length
            s3.n_nets.toNat s3.n_in.toNat s3.n_out.toNat s2.top.toNat := by
          rw [show s3.n_nets = s2.n_nets by rw [hs3_eq],
              show s3.n_in = s2.n_in by rw [hs3_eq], hs3_no]
          exact tgeom_rw (s := s3) hs2tg (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq])
            (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq])
            (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq])
            (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq])
            (by rw [hs3_eq])
        have hmasks3 : MasksOk s3.n_out.toNat s3.mlo s3.mhi := by
          rw [hs3_no, show s3.mlo = s2.mlo by rw [hs3_eq], show s3.mhi = s2.mhi by rw [hs3_eq]]
          exact hs2masks
        let hb : CmBase s3 g s2.top.toNat aigBytes artBytes :=
          { w_pos := by rw [hs3w]; exact hwPos,
            w_fit := by rw [hs3w, hs3wl]; exact hwFit,
            top0_ge := hs2top ▸ tablesEndTop_ge776 _ _ _ _ _,
            top0_le_top := htop0_le,
            top_le_wlen := hs3tlen, cap_lo := hcap_lo, cap_hi := hcap_hi, pcap_eq := hpcap,
            rs_cap_eq := hrscap, tcap_eq := htcap, rcap_eq := hrcap,
            rs_pcap_eq := hrspcap, rpcap_eq := hrpcap, parse_aig := hParseG, g_M_le := hMg,
            s_M := hM3, s_I := hI3, s_A := hA3, s_O := hO3,
            art_fit := by rw [hs3_art]; exact hartFit,
            nw4 := hnw3, nnets_bd := hnn3, spec_01 := hspec3,
            tgeom := htg3, dgeom := hs3dg, masks := hmasks3 }
        let t0 : CmTabArrs :=
          { rhs0, rhs1, olit, bindArr, ruleOff, ruleN, partnerArr, flippedArr,
            inNetArr, outRefArr, stkN, stkP, memoN, memoV, dense, gsy, gcl, gch }
        let d0 : CmDynArrs :=
          { rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
            qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip,
            rm, rl, rh, rm2, rl2, rh2, rpool }
        have htLen : t0.LenOk g s3 :=
          ⟨hAig.rhs0_len, hAig.rhs1_len, hAig.olit_len,
           by rw [show s3.n_nets = s2.n_nets by rw [hs3_eq]]; exact lbd,
           by rw [show s3.n_nets = s2.n_nets by rw [hs3_eq]]; exact lro,
           by rw [show s3.n_nets = s2.n_nets by rw [hs3_eq]]; exact lrn,
           by rw [show s3.n_nets = s2.n_nets by rw [hs3_eq]]; exact lpa,
           by rw [show s3.n_nets = s2.n_nets by rw [hs3_eq]]; exact lfl,
           by rw [show s3.n_in = s2.n_in by rw [hs3_eq]]; exact lin,
           by rw [show s3.n_out = s2.n_out by rw [hs3_eq]]; exact lou,
           lsn, lsp, lmn, lmv, ldn, lgy, lgl, lgh⟩
        have hdLen : d0.LenOk s3.qcap.toNat :=
          ⟨lrm, lrl, lrh, hpcap ▸ lrp, ltm0, ltm1, lts0, ltl0, lth0, lts1, ltl1, lth1,
           hpcap ▸ lp0, hpcap ▸ lp1, lqm, lqs, lql, lqh, lix, lix2, lbx, lvqo, hpcap ▸ lvq, lvqs,
           lrm_, lrl_, lrh_, lrm2, lrl2, lrh2, hpcap ▸ lrp_⟩
        have hBind3 : BindRep s3 g t0.bindArr t0.inNetArr t0.outRefArr :=
          bindRep_rw hBind2 (by rw [hs3_eq]) (by rw [hs3_eq]) (by rw [hs3_eq])
        have hrsn3 : s3.rs_n = 0#32 := by rw [hs3_eq]; exact hs2rsn
        have hrsn3_n : s3.rs_n.toNat = 0 := by rw [hrsn3]; rfl
        have hm3_ar : (arCtxMem cx s3 ⋆ bytes s3.art artBytes ⋆
            cmArenaMem s3 s3 s2.top.toNat t0 d0 ⋆ bytes aig aigBytes ⋆ R) m3 := by
          have haig_eq : aigArraysMem s3 rhs0 rhs1 olit = aigArraysMem s2 rhs0 rhs1 olit := by
            simp only [aigArraysMem, show s3.rhs0 = s2.rhs0 by rw [hs3_eq],
              show s3.rhs1 = s2.rhs1 by rw [hs3_eq], show s3.olit = s2.olit by rw [hs3_eq]]
          have hnet_eq : netTablesMem s3 bindArr ruleOff ruleN partnerArr flippedArr
              inNetArr outRefArr = netTablesMem s2 bindArr ruleOff ruleN partnerArr flippedArr
              inNetArr outRefArr := by
            simp only [netTablesMem, show s3.bind = s2.bind by rw [hs3_eq],
              show s3.rule_off = s2.rule_off by rw [hs3_eq],
              show s3.rule_n = s2.rule_n by rw [hs3_eq],
              show s3.partner = s2.partner by rw [hs3_eq],
              show s3.flipped = s2.flipped by rw [hs3_eq],
              show s3.in_net = s2.in_net by rw [hs3_eq],
              show s3.out_ref = s2.out_ref by rw [hs3_eq]]
          have hgs_eq : gateScratchMem s3 stkN stkP memoN memoV dense gsy gcl gch =
              gateScratchMem s2 stkN stkP memoN memoV dense gsy gcl gch := by
            simp only [gateScratchMem, show s3.stk_n = s2.stk_n by rw [hs3_eq],
              show s3.stk_p = s2.stk_p by rw [hs3_eq],
              show s3.memo_n = s2.memo_n by rw [hs3_eq],
              show s3.memo_v = s2.memo_v by rw [hs3_eq],
              show s3.dense = s2.dense by rw [hs3_eq],
              show s3.gsy = s2.gsy by rw [hs3_eq],
              show s3.gcl = s2.gcl by rw [hs3_eq],
              show s3.gch = s2.gch by rw [hs3_eq]]
          dsimp only [cmArenaMem, t0, d0]
          rw [haig_eq, hnet_eq, hgs_eq, show s3.art = s2.art by rw [hs3_eq]]
          have hs2w3 : s2.w = s3.w := by rw [hs3_eq]
          rw [hs2w3] at hm3
          exact sep_cast hm3 (by dsimp only [Rsetup]; ac_rfl)
        have hFail' : ∀ (s' : ArCtxState) (m' : Mem 64),
            (arCtxMem cx s' ⋆ region (s3.w + 776#64) (s3.wlen.toNat - 776) ⋆
              bytes aig aigBytes ⋆ bytes s3.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m' := by
          intro s' m' hm'
          rw [hs3w, hs3wl, hs3_art] at hm'
          exact hQ false m' (fun h => by cases h) ⟨s', hm'⟩
        have hTrue' : ∀ (s' : ArCtxState) (m' : Mem 64),
            (∀ ρ : Nat → Bool,
              BitVec.ofNat s3.n_out.toNat (outWord g ρ) =
                BitVec.ofInt s3.n_out.toNat (inWord (decide (s3.spec = 1#32)) (g.I / 2) ρ 0) *
                  BitVec.ofInt s3.n_out.toNat
                    (inWord (decide (s3.spec = 1#32)) (g.I / 2) ρ (g.I / 2))) →
            (arCtxMem cx s' ⋆ region (s3.w + 776#64) (s3.wlen.toNat - 776) ⋆
              bytes aig aigBytes ⋆ bytes s3.art artBytes ⋆ R) m' → Q (true, ⟨⟩) m' := by
          intro s' m' heq hm'
          rw [hs3w, hs3wl, hs3_art] at hm'
          refine hQ true m'
            (fun _ => ⟨g, decide (s3.spec = 1#32), hParseG, fun ρ => ?_⟩) ⟨s', hm'⟩
          rw [← hBind3.out_eq]
          exact heq ρ
        change wp Γ Q X (cmGatesExpr cx aig aigLen art artLen) m3
        refine main_gates_loop_wp Γ hGate hb htLen hdLen hAig hBind3
          (by rw [show s3.pos = s2.pos by rw [hs3_eq], show s3.nw = s2.nw by rw [hs3_eq]]
              exact hs2pos_nw)
          (by rw [hrsn3_n]; exact Nat.zero_le _)
          (by rw [show s3.rs_ptop = s2.rs_ptop by rw [hs3_eq], hs2rspt]; exact Nat.zero_le _)
          (by rw [hrsn3_n, monoTotalWords_zero]; exact Nat.zero_le _)
          (fun _ hi => by rw [hrsn3_n] at hi; omega)
          (fun _ hi => by rw [hrsn3_n] at hi; omega)
          (fun _ hi => by rw [hrsn3_n] at hi; omega)
          (fun ρ => by
            obtain ⟨hp2, hr2⟩ := hRep2 (cSig g ρ bindArr)
            have hnn_eq : s3.n_nets = s2.n_nets := by rw [hs3_eq]
            refine ⟨by rw [hnn_eq]; exact hp2, ?_⟩
            dsimp only [RulesRep, t0, d0] at hr2 ⊢
            refine ⟨by rw [hnn_eq]; exact Nat.le_of_eq lro.symm,
              by rw [hnn_eq]; exact Nat.le_of_eq lrn.symm,
              by rw [hrsn3_n]; exact Nat.zero_le _,
              by rw [show s3.rs_ptop = 0#64 by rw [hs3_eq, hs2rspt]]; exact Nat.zero_le _,
              by rw [hrscap]; exact Nat.le_of_eq lrm.symm,
              by rw [hrscap]; exact Nat.le_of_eq lrl.symm,
              by rw [hrscap]; exact Nat.le_of_eq lrh.symm,
              by rw [hrspcap]; exact Nat.le_of_eq lrp.symm,
              fun _ hi => by rw [hrsn3_n] at hi; omega,
              fun v hv hne => ?_⟩
            rw [hnn_eq] at hv
            obtain ⟨hoff0, hev0⟩ := hr2.2.2.2.2.2.2.2.2.2 v hv hne
            rw [show s2.rs_n = 0#32 from hs2rsn,
              show (0#32 : BitVec 32).toNat = 0 from rfl] at hoff0
            have hcnt0 : (ruleN.getD v 0#32).toNat = 0 := by omega
            refine ⟨by rw [hrsn3_n]; omega, ?_⟩
            simp only [hcnt0, polyEvalRange, List.range_zero, List.foldl_nil] at hev0 ⊢
            rwa [hs3_no])
          hm3_ar hFail' ?_
        intro sG tG dG mG htLenG hdLenG hsG_eq hposG hrsnG hrsptG hTotG hSyG hOkG hSortG hRepG
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmG
        have hpcG : sG.pc.toNat < 2 := by
          rw [show sG.pc = s3.pc by rw [hsG_eq], show s3.pc = s2.pc by rw [hs3_eq],
              hs2pc.trans hs1pc, hpc]; decide
        have htcG : sG.tc.toNat < 2 := by
          rw [show sG.tc = s3.tc by rw [hsG_eq], show s3.tc = s2.tc by rw [hs3_eq],
              hs2tc.trans hs1tc, htc]; decide
        have hBindG : BindRep s3 g tG.bindArr tG.inNetArr tG.outRefArr := by
          rw [‹tG.bindArr = t0.bindArr›, ‹tG.inNetArr = t0.inNetArr›,
              ‹tG.outRefArr = t0.outRefArr›]
          exact hBind3
        refine main_cones_loop_wp Γ hCone hb htLenG hdLenG hsG_eq hpcG htcG
          hposG hrsnG hrsptG hTotG hSyG hOkG hSortG
          (fun ρ => by rw [← ‹tG.bindArr = t0.bindArr›] at hRepG; exact hRepG ρ)
          hmG hFail' ?_
        intro sC tC dC mC htLenC hdLenC hsC_eq hixC hpcC htcC hposC hrsnC hrsptC
          hTotC hSyC hOkC hSortC hRepC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmC
        have hBindC : BindRep s3 g tC.bindArr tC.inNetArr tC.outRefArr := by
          rw [‹tC.bindArr = tG.bindArr›, ‹tC.inNetArr = tG.inNetArr›,
              ‹tC.outRefArr = tG.outRefArr›]
          exact hBindG
        refine main_sp0_phase Γ hBuildSp0 hNW hBuildR hApply hCneg hb htLenC hdLenC hBindC
          hsG_eq hsC_eq hixC hpcC htcC hposC hrsnC hrsptC hTotC hSyC hOkC hSortC
          (fun ρ => by rw [← ‹tC.bindArr = tG.bindArr›] at hRepC; exact hRepC ρ)
          hmC hFail' hTrue'

/-- WP soundness for `arisca_check_bytes(aig_ptr, aig_len, art_ptr, art_len, work_ptr,
work_len)`. -/
theorem arisca_check_bytes_wp (Γ : LeanQbe.T.Env)
    (hMain : ∀ xs m Q X, arCheckMainSpec xs m Q X →
      Γ "ar_check_main" [i64, i64, i64, i64, i64] [.bool] xs m Q X) :
    ∀ xs m Q X, ariscaCheckBytesSpec xs m Q X →
      Func.wp Γ arisca_check_bytes_body xs m Q X := by
  rintro ⟨aigPtr, aigLen, artPtr, artLen, workPtr, workLen, ⟨⟩⟩ m Q X
    ⟨aigBytes, artBytes, R, haigLen, hartLen, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
  · clear hc; c0_hstraight
    c0_hsplit
    · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
    · clear hc; c0_hstraight
      c0_hsplit
      · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
      · have hw_ne0 : workPtr ≠ 0#64 := hc; clear hc
        have hw_pos : 0 < workPtr.toNat :=
          Nat.pos_of_ne_zero fun h0 => hw_ne0 (BitVec.eq_of_toNat_eq (by simp [h0]))
        c0_hstraight
        refine head_wp_jnz rfl (fun hc => ?_) (fun _ => ?_)
        · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
        · c0_hstraight
          refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
          · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
          · have hartFit : artPtr.toNat + artBytes.length < 2 ^ 64 := by
              rw [← hartLen]; exact bv64_ult_sub_max_toNat artPtr artLen hc
            c0_hstraight
            refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
            · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
            · have hw_fit : workPtr.toNat + workLen.toNat < 2 ^ 64 :=
                bv64_ult_sub_max_toNat workPtr workLen hc
              c0_hstraight
              let padNat := (8 - workPtr.toNat % 8) % 8
              have hpad_lt8 : padNat < 8 := Nat.mod_lt _ (by decide)
              have hpad_eq :
                  (((8 : BitVec 64) - (workPtr &&& (7 : BitVec 64)) &&&
                    (7 : BitVec 64))).toNat = padNat :=
                bv64_pad_eq workPtr
              have hpad_bv :
                  (((8 : BitVec 64) - (workPtr &&& (7 : BitVec 64)) &&&
                    (7 : BitVec 64))) = BitVec.ofNat 64 padNat :=
                BitVec.eq_of_toNat_eq (by
                  rw [hpad_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
              have hpad776 :
                  (((8 : BitVec 64) - (workPtr &&& (7 : BitVec 64)) &&&
                    (7 : BitVec 64)).toNat + 776) % 2 ^ 64 = padNat + 776 := by
                rw [hpad_eq, Nat.mod_eq_of_lt (by omega)]
              c0_hsplit
              · c0_hstraight; exact hQ 0#64 m (fun h => absurd h (by decide)) hm
              · have hlen_ge : padNat + 776 ≤ workLen.toNat := by
                  have h776 :
                      (((8 : BitVec 64) - (workPtr &&& (7 : BitVec 64)) &&&
                        (7 : BitVec 64)) + 776#64).toNat = padNat + 776 := by
                    rw [BitVec.toNat_add, show (776#64 : BitVec 64).toNat = 776 from rfl,
                      hpad_eq, Nat.mod_eq_of_lt (by omega)]
                  have hnc : ¬ workLen.toNat < padNat + 776 := by
                    rw [← h776]; exact hc
                  omega
                clear hc
                let workBase := workPtr + BitVec.ofNat 64 padNat
                let avail := workLen.toNat - padNat
                let padR := region workPtr padNat ⋆ R
                have hm_sp1 : (region workPtr padNat ⋆ region workBase avail ⋆
                    bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ R) m := by
                  have hm0 := hm
                  rw [show workLen.toNat = padNat + avail by omega,
                    region_split (by omega : padNat + avail ≤ 2 ^ 64)] at hm0
                  exact sep_cast hm0 (by dsimp only [workBase]; ac_rfl)
                have hm_sp2 : (region workBase 776 ⋆ (region (workBase + 776#64) (avail - 776) ⋆
                    bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)) m := by
                  have hm0 := hm_sp1
                  rw [show avail = 776 + (avail - 776) by omega,
                    region_split (by omega : 776 + (avail - 776) ≤ 2 ^ 64)] at hm0
                  exact sep_cast hm0 (by
                    dsimp only [padR]; rw [show (776#64 : BitVec 64) = BitVec.ofNat 64 776 from rfl]
                    ac_rfl)
                obtain ⟨zs0, hzs0, hm_arr⟩ := region776_to_array_u8 (a := workBase)
                  (R := region (workBase + 776#64) (avail - 776) ⋆
                    bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)
                  (m := m) hm_sp2
                replace hm_arr : (array (t := i8) workBase zs0 ⋆
                    region (workBase + 776#64) (avail - 776) ⋆
                    bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR) m :=
                  sep_cast hm_arr (by ac_rfl)
                c0_hstraight
                rw [hpad_bv]
                have hav_bv : workLen - BitVec.ofNat 64 padNat = BitVec.ofNat 64 avail := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64)]
                    omega)), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : avail < 2 ^ 64)]
                rw [hav_bv]
                change wp Γ Q X (.group _ _) m
                refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i64]) (mL : Mem 64) =>
                    let ⟨zi, ⟨⟩⟩ := args
                    zi.toNat ≤ 776 ∧ rem = 776 - zi.toNat ∧
                    ∃ zs : List (BitVec 8), zs.length = 776 ∧
                      (∀ k < zi.toNat, zs.getD k 0#8 = 0#8) ∧
                      (array (t := i8) workBase zs ⋆
                        region (workBase + 776#64) (avail - 776) ⋆
                        bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR) mL) ?_ ?_
                · intro J rem ⟨zi, ⟨⟩⟩ mL hrec ⟨hzi_le, _, zs, hzs_len, hzs0_k, hmL⟩
                  c0_hstraight
                  refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                  · c0_hstraight
                    simp only [Arg.val, BitVec.ult, decide_eq_true_eq] at hc
                    rw [show ((776 : BitVec 64)).toNat = 776 from rfl] at hc
                    have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by
                      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    refine wp_store_sep (c0_store_array8 (a := workBase) (i := zi) (xs := zs)
                        (R := region (workBase + 776#64) (avail - 776) ⋆
                          bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)
                        (BitVec.truncate 8 0#32) (sep_cast hmL (by ac_rfl))
                        (by rw [hzs_len]; exact hc))
                      fun m_st hm_st => ?_
                    c0_hstraight
                    rw [show BitVec.truncate 8 0#32 = 0#8 from rfl] at hm_st
                    exact hrec (776 - (zi + 1#64).toNat) (zi + 1#64, ⟨⟩) m_st (by omega)
                      ⟨by omega, by rw [hzi1], zs.set zi.toNat 0#8, by simp [hzs_len],
                       fun k hk => by
                         rw [hzi1] at hk
                         rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
                         · rw [getD_eq_getElem (zs.set zi.toNat 0#8) 0#8
                             (by rw [List.length_set, hzs_len]; omega),
                             List.getElem_set_ne (by omega)]
                           have hk0 := hzs0_k k hlt
                           rwa [getD_eq_getElem zs 0#8 (by omega)] at hk0
                         · rw [getD_eq_getElem (zs.set zi.toNat 0#8) 0#8
                             (by rw [List.length_set, hzs_len]; omega),
                             List.getElem_set_self (by rw [List.length_set, hzs_len]; exact hc)],
                       sep_cast hm_st (by ac_rfl)⟩
                  · simp only [Arg.val, BitVec.ult, decide_eq_false_iff_not] at hc
                    rw [show ((776 : BitVec 64)).toNat = 776 from rfl] at hc
                    have hzi_eq : zi.toNat = 776 := by omega
                    have hzs_rep : zs = List.replicate 776 0#8 := by
                      refine List.ext_getElem (by rw [hzs_len, List.length_replicate])
                        (fun k hk1 hk2 => ?_)
                      simp only [List.getElem_replicate]
                      have hk' := hzs0_k k (by omega)
                      rwa [getD_eq_getElem zs 0#8 (by omega)] at hk'
                    rw [hzs_rep] at hmL
                    have hmL' : (array (t := i8) workBase (List.replicate 776 0#8) ⋆
                        (region (workBase + 776#64) (avail - 776) ⋆
                          bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)) mL :=
                      sep_cast hmL (by ac_rfl)
                    have hmL_ctx := array_zero776_to_arCtxMem (cx := workBase)
                      (R := region (workBase + 776#64) (avail - 776) ⋆
                        bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)
                      (m := mL) hmL'
                    c0_hsteps_nogrp
                    let s0 : ArCtxState :=
                      { zeroArCtxState with
                        w := workBase, wlen := BitVec.ofNat 64 avail, top := 776#64 }
                    have hwb_pos : 0 < workBase.toNat := by
                      dsimp only [workBase]
                      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : workPtr.toNat + padNat < 2 ^ 64)]
                      omega
                    have hwb_toNat : workBase.toNat = workPtr.toNat + padNat := by
                      dsimp only [workBase]
                      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega : padNat < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : workPtr.toNat + padNat < 2 ^ 64)]
                    have hav64 : (BitVec.ofNat 64 avail).toNat = avail := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : avail < 2 ^ 64)]
                    dsimp only [Arg.val]
                    apply wp_call_of_spec
                    refine hMain _ _ _ _ ⟨s0, aigBytes, artBytes, padR,
                      hwb_pos, rfl, by rw [hav64]; omega,
                      by dsimp only [s0]; rw [hav64, hwb_toNat]; omega,
                      haigLen, hartLen, hartFit,
                      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                      by dsimp only [s0]; rw [hav64]; exact sep_cast ‹_› (by ac_rfl),
                      fun ok m' hok ⟨s', hm'⟩ => ?_⟩
                    have hm'_reg : (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆
                        region workPtr workLen.toNat ⋆ R) m' := by
                      have h1 : (arCtxMem workBase s' ⋆
                          (region (workBase + 776#64) (avail - 776) ⋆
                            bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)) m' :=
                        sep_cast hm' (by dsimp only [s0]; rw [hav64]; ac_rfl)
                      have h2 := sep_mono (P' := region workBase 776)
                        (fun _ h => arCtxMem_to_region h) h1
                      have h3 : ((region workBase 776 ⋆
                          region (workBase + BitVec.ofNat 64 776) (avail - 776)) ⋆
                          (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ padR)) m' :=
                        sep_cast h2
                          (by rw [show (776#64 : BitVec 64) = BitVec.ofNat 64 776 from rfl]; ac_rfl)
                      rw [region_merge_eq (by omega) (by omega : avail ≤ 2 ^ 64)] at h3
                      have h4 : ((region workPtr padNat ⋆
                          region (workPtr + BitVec.ofNat 64 padNat) avail) ⋆
                          (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆ R)) m' :=
                        sep_cast h3 (by dsimp only [padR, workBase]; ac_rfl)
                      rw [region_merge_eq (by omega) (by omega : workLen.toNat ≤ 2 ^ 64)] at h4
                      exact sep_cast h4 (by ac_rfl)
                    cases ok
                    · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
                      c0_hstraight
                      exact hQ 0#64 m' (fun h => absurd h (by decide)) hm'_reg
                    · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
                      c0_hstraight
                      exact hQ 20#64 m' (fun _ => hok rfl) hm'_reg
                · intro J hJ; c0_hsteps_nogrp
                  exact hJ 776 (0#64, ⟨⟩) m ⟨Nat.zero_le _, Nat.sub_zero _, zs0, hzs0,
                    fun k hk => absurd hk (Nat.not_lt_zero k), hm_arr⟩

end

end LeanQbe.T.Examples.Arisca.Proof

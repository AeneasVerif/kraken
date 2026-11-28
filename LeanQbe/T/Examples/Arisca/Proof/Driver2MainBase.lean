/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver2Loop
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Top-Level `n_main` Loop Helpers (`Arisca.Proof.Driver2MainBase`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) arena unpack/repack lemmas, `ar_apply` bridge
(`main_apply_step`), failure collapse (`main_fail_collapse`), and flip invariant (`flip_curRRep`)
for `Driver2Main`.
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

@[expose] public section

/-- Alignment padding tail for an `i8` array of length `n`. -/
def u8PadTail (ptr : BitVec 64) (n : Nat) : Mem 64 → Prop :=
  region (ptr + BitVec.ofNat 64 n) (align8 n - n)

end

public section

theorem arrayPad_u8_unfold (ptr : BitVec 64) (xs : List (BitVec 8)) :
    arrayPad i8 ptr xs = (array (t := i8) ptr xs ⋆ u8PadTail ptr xs.length) := by
  unfold arrayPad u8PadTail SlabSeg.ofArrayAlign8 SlabSeg.ofArray
  simp [Ty.bytes, Ty.size]

theorem arena_unpack_apply {s0 s : ArCtxState} {top0 : Nat}
    {t : CmTabArrs} {d : CmDynArrs} :
    cmArenaMem s s0 top0 t d =
      (array (t := i32) s.partner t.partnerArr ⋆
       tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
       qMem s d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
       (aigArraysMem s t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 s.bind t.bindArr ⋆
        arrayPad i32 s.rule_off t.ruleOff ⋆ arrayPad i32 s.rule_n t.ruleN ⋆
        u32PadTail s.partner t.partnerArr.length ⋆ arrayPad i8 s.flipped t.flippedArr ⋆
        arrayPad i32 s.in_net t.inNetArr ⋆ arrayPad i32 s.out_ref t.outRefArr ⋆
        gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        rsMem s d.rsM d.rsL d.rsH d.rsPool ⋆
        rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
        region (s.w + s.top) (s.wlen.toNat - s.top.toNat))) := by
  dsimp only [cmArenaMem]
  rw [netTablesMem_unpack]
  conv =>
    rhs
    rw [arrayPad_u32_unfold s.bind t.bindArr, arrayPad_u32_unfold s.rule_off t.ruleOff,
      arrayPad_u32_unfold s.rule_n t.ruleN]
  ac_rfl

theorem arena_unpack_buildR {s0 s : ArCtxState} {top0 : Nat}
    {t : CmTabArrs} {d : CmDynArrs} :
    cmArenaMem s s0 top0 t d =
      (array (t := i32) s.rule_off t.ruleOff ⋆ array (t := i32) s.rule_n t.ruleN ⋆
       array (t := i8) s.flipped t.flippedArr ⋆ rsMem s d.rsM d.rsL d.rsH d.rsPool ⋆
       rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
       array (t := i32) s.ix d.ix ⋆ array (t := i32) s.ix2 d.ix2 ⋆
       (aigArraysMem s t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 s.bind t.bindArr ⋆
        u32PadTail s.rule_off t.ruleOff.length ⋆ u32PadTail s.rule_n t.ruleN.length ⋆
        arrayPad i32 s.partner t.partnerArr ⋆ u8PadTail s.flipped t.flippedArr.length ⋆
        arrayPad i32 s.in_net t.inNetArr ⋆ arrayPad i32 s.out_ref t.outRefArr ⋆
        gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
        arrayPad i32 s.qm d.qm ⋆ array64 s.qs d.qs ⋆ array64 s.ql d.ql ⋆ array64 s.qh d.qh ⋆
        u32PadTail s.ix d.ix.length ⋆ u32PadTail s.ix2 d.ix2.length ⋆
        arrayPad i32 s.bx d.bx ⋆ arrayPad i32 s.vq_off d.vqOff ⋆
        arrayPad i32 s.vq d.vq ⋆ arrayPad i8 s.vq_skip d.vqSkip ⋆
        region (s.w + s.top) (s.wlen.toNat - s.top.toNat))) := by
  dsimp only [cmArenaMem, qMem]
  rw [netTablesMem_unpack, arrayPad_u8_unfold s.flipped t.flippedArr,
    arrayPad_u32_unfold s.ix d.ix, arrayPad_u32_unfold s.ix2 d.ix2]
  conv =>
    rhs
    rw [arrayPad_u32_unfold s.bind t.bindArr, arrayPad_u32_unfold s.partner t.partnerArr]
  ac_rfl

theorem coeff128_one_and_mask {nOut : Nat} {mlo mhi : BitVec 64}
    (hm : MasksOk nOut mlo mhi) : coeff128 nOut (1#64 &&& mlo) 0#64 = 1#nOut := by
  have hmlo : mlo = maskVal64 nOut := hm.2.2.1
  have h1 : 1 ≤ min nOut 64 := by have := hm.1; omega
  have hle : 2 ^ min nOut 64 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
  have hpos : 0 < 2 ^ min nOut 64 := Nat.pow_pos (by decide)
  have hlt : 2 ^ min nOut 64 - 1 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.sub_lt hpos (by decide)) hle
  have hodd : (maskVal64 nOut).toNat % 2 = 1 := by
    rw [maskVal64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hpow : 2 ^ min nOut 64 = 2 * 2 ^ (min nOut 64 - 1) := by
      conv => lhs; rw [show min nOut 64 = 1 + (min nOut 64 - 1) by omega, Nat.pow_add, Nat.pow_one]
    have hp2 : 0 < 2 ^ (min nOut 64 - 1) := Nat.pow_pos (by decide)
    omega
  have hand : (1#64 &&& mlo).toNat = 1 := by
    rw [hmlo, BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.and_comm 1 _, Nat.and_one_is_mod, hodd]
  simp only [coeff128, hand, show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

theorem flip_curRRep {nOut : Nat} {σ : Nat → Bool} {v : Nat}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)} {rpool : List (BitVec 32)}
    {nl nh : BitVec 64} {mlo mhi : BitVec 64}
    (hm : MasksOk nOut mlo mhi) (hσ : σ (2 * v + 1) = !(σ (2 * v)))
    (hrm_len : 16 ≤ rm.length) (hrl_len : 16 ≤ rl.length) (hrh_len : 16 ≤ rh.length)
    (hrp_len : 192 ≤ rpool.length)
    (hrp0 : rpool.getD 0 0#32 = 0#32) (hrp1 : rpool.getD 1 0#32 = 1#32)
    (hrp2 : rpool.getD 2 0#32 = BitVec.ofNat 32 (2 * v + 1)) (h2v : 2 * v + 1 < 2 ^ 32)
    (hrm0 : rm.getD 0 0#32 = 0#32) (hrm1 : rm.getD 1 0#32 = 1#32)
    (hrl0 : rl.getD 0 0#64 = 1#64 &&& mlo) (hrh0 : rh.getD 0 0#64 = 0#64)
    (hrl1 : rl.getD 1 0#64 = nl) (hrh1 : rh.getD 1 0#64 = nh)
    (hcneg : coeff128 nOut nl nh = -coeff128 nOut 1#64 0#64) :
    CurRRep nOut σ 2 (2 * v) rm rl rh rpool := by
  refine ⟨by omega, by omega, by omega, fun i hi => ?_, ?_⟩
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [hrm0, show (0#32 : BitVec 32).toNat = 0 from rfl]
      exact ⟨by omega, by rw [hrp0]; simp only [BitVec.toNat_ofNat]; omega⟩
    · rw [hrm1, show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact ⟨by omega, by rw [hrp1]; simp only [BitVec.toNat_ofNat]; omega⟩
  · have hpoly : polyEval nOut σ rpool rm rl rh 2 =
        termEval nOut σ rpool rm rl rh 0 + termEval nOut σ rpool rm rl rh 1 := by
      rw [polyEval, polyEvalRange, show List.range 2 = [0, 1] from rfl]
      simp [BitVec.zero_add]
    have hsy0 : symListAt rpool 0 = [] := by
      unfold symListAt; rw [hrp0]; rfl
    have ht0 : termEval nOut σ rpool rm rl rh 0 = 1#nOut := by
      simp only [termEval, hrm0, show (0#32 : BitVec 32).toNat = 0 from rfl, hsy0, monoValL,
        ↓reduceIte, hrl0, hrh0, coeff128_one_and_mask hm]
    have hsy1 : symListAt rpool 1 = [2 * v + 1] := by
      unfold symListAt
      rw [hrp1, show (1#32 : BitVec 32).toNat = 1 from rfl]
      dsimp only
      rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, Nat.add_zero, hrp2,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2v]
    have h10 : coeff128 nOut 1#64 0#64 = 1#nOut := by
      simp [coeff128, show (1#64 : BitVec 64).toNat = 1 from rfl,
        show (0#64 : BitVec 64).toNat = 0 from rfl]
    have ht1 : termEval nOut σ rpool rm rl rh 1 =
        if σ (2 * v + 1) then -1#nOut else 0#nOut := by
      simp only [termEval, hrm1, show (1#32 : BitVec 32).toNat = 1 from rfl, hsy1, monoValL,
        Bool.and_true, hrl1, hrh1, hcneg, h10]
    rw [hpoly, ht0, ht1, hσ]
    cases σ (2 * v)
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, bv]
      cases nOut with
      | zero => exact Subsingleton.elim _ _
      | succ k =>
        apply BitVec.eq_of_toNat_eq
        have h1 : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
        simp [BitVec.toNat_add, BitVec.toNat_neg, Nat.add_sub_cancel' (Nat.le_of_lt h1)]
    · simp [bv]

theorem main_apply_step (Γ : LeanQbe.T.Env)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X → Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    {cx aig : Val i64} {sym : BitVec 32} {s0 sA : ArCtxState} {g : Aig} {top0 : Nat}
    {aigBytes artBytes : List UInt8} {t : CmTabArrs} {d : CmDynArrs}
    {curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)} {curRp : List (BitVec 32)}
    {Rcur : Mem 64 → Prop} {R : Mem 64 → Prop} {mA : Mem 64}
    {Q : Post [.bool]} {X : XPost} {kTrue : Expr Val Cont [.bool]}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (_htLen : t.LenOk g s0) (hdLen : d.LenOk s0.qcap.toNat)
    (_hs_w : sA.w = s0.w) (_hs_wl : sA.wlen = s0.wlen) (_hs_top : sA.top = s0.top)
    (hs_tcap : sA.tcap = s0.tcap) (hs_qcap : sA.qcap = s0.qcap) (hs_pcap : sA.pcap = s0.pcap)
    (hs_nn : sA.n_nets = s0.n_nets) (hs_no : sA.n_out = s0.n_out)
    (hs_mlo : sA.mlo = s0.mlo) (hs_mhi : sA.mhi = s0.mhi)
    (_hs_pa : sA.partner = s0.partner)
    (_hs_tm : sA.tm = s0.tm) (_hs_ts : sA.ts = s0.ts) (_hs_tl : sA.tl = s0.tl)
    (_hs_th : sA.th = s0.th) (_hs_po : sA.pool = s0.pool)
    (_hs_qm : sA.qm = s0.qm) (_hs_qs : sA.qs = s0.qs) (_hs_ql : sA.ql = s0.ql)
    (_hs_qh : sA.qh = s0.qh) (_hs_bx : sA.bx = s0.bx) (_hs_vqo : sA.vq_off = s0.vq_off)
    (_hs_vq : sA.vq = s0.vq) (_hs_vqs : sA.vq_skip = s0.vq_skip)
    (hpc : sA.pc.toNat < 2) (htc : sA.tc.toNat < 2)
    (htn : sA.tn.toNat ≤ s0.tcap.toNat) (hpt : sA.ptop.toNat ≤ s0.pcap.toNat)
    (hixSw : (sA.ix = s0.ix ∧ sA.ix2 = s0.ix2) ∨ (sA.ix = s0.ix2 ∧ sA.ix2 = s0.ix))
    (hPart : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ t.bindArr) s0.n_nets.toNat t.partnerArr)
    (hCurR : ∀ ρ : Nat → Bool, CurRRep s0.n_out.toNat (cSig g ρ t.bindArr)
      sA.cur_nr.toNat sym.toNat curRm curRl curRh curRp)
    (hCurSort : ∀ r < sA.cur_nr.toNat, MonoSorted curRp (curRm.getD r 0#32).toNat)
    (hCurOk : ∀ r < sA.cur_nr.toNat,
      (curRp.getD (curRm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hCurTot : monoTotalWords curRp curRm sA.cur_nr.toNat ≤ 4000000000)
    (hSlT : ∀ j < sA.tn.toNat,
      MonoSliceOk (if sA.pc.toNat = 0 then d.pool0 else d.pool1)
        ((if sA.tc.toNat = 0 then d.tm0 else d.tm1).getD j 0#32).toNat sA.ptop.toNat ∧
      ((if sA.pc.toNat = 0 then d.pool0 else d.pool1).getD
        ((if sA.tc.toNat = 0 then d.tm0 else d.tm1).getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortT : ∀ j < sA.tn.toNat,
      MonoSorted (if sA.pc.toNat = 0 then d.pool0 else d.pool1)
        ((if sA.tc.toNat = 0 then d.tm0 else d.tm1).getD j 0#32).toNat)
    (hSigT : SigOk (if sA.pc.toNat = 0 then d.pool0 else d.pool1)
      (if sA.tc.toNat = 0 then d.tm0 else d.tm1)
      (if sA.tc.toNat = 0 then d.ts0 else d.ts1) sA.tn.toNat)
    (hTotT : monoTotalWords (if sA.pc.toNat = 0 then d.pool0 else d.pool1)
      (if sA.tc.toNat = 0 then d.tm0 else d.tm1) sA.tn.toNat ≤ sA.ptop.toNat)
    (hEv : ∀ ρ : Nat → Bool,
      polyEval s0.n_out.toNat (cSig g ρ t.bindArr)
          (if sA.pc.toNat = 0 then d.pool0 else d.pool1)
          (if sA.tc.toNat = 0 then d.tm0 else d.tm1)
          (if sA.tc.toNat = 0 then d.tl0 else d.tl1)
          (if sA.tc.toNat = 0 then d.th0 else d.th1) sA.tn.toNat =
        BitVec.ofNat s0.n_out.toNat (outWord g ρ) -
          BitVec.ofInt s0.n_out.toNat (inWord (decide (s0.spec = 1#32)) (g.I / 2) ρ 0) *
            BitVec.ofInt s0.n_out.toNat (inWord (decide (s0.spec = 1#32)) (g.I / 2) ρ (g.I / 2)))
    (hmA : (arCtxMem cx sA ⋆ array (t := i32) sA.partner t.partnerArr ⋆
      array (t := i32) sA.cur_rm curRm ⋆ array64 sA.cur_rl curRl ⋆ array64 sA.cur_rh curRh ⋆
      array (t := i32) sA.cur_rp curRp ⋆
      tMem sA d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
      qMem sA d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
      Rcur ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mA)
    (hFail : ∀ (sB : ArCtxState) (dB : CmDynArrs) (mB : Mem 64),
      dB.LenOk s0.qcap.toNat →
      sB = { sA with
        tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop,
        qn := sB.qn, ix := sB.ix, ix2 := sB.ix2 } →
      ((sB.ix = s0.ix ∧ sB.ix2 = s0.ix2) ∨ (sB.ix = s0.ix2 ∧ sB.ix2 = s0.ix)) →
      dB.rsM = d.rsM → dB.rsL = d.rsL → dB.rsH = d.rsH → dB.rsPool = d.rsPool →
      dB.rm = d.rm → dB.rl = d.rl → dB.rh = d.rh →
      dB.rm2 = d.rm2 → dB.rl2 = d.rl2 → dB.rh2 = d.rh2 → dB.rpool = d.rpool →
      (arCtxMem cx sB ⋆ array (t := i32) sB.partner t.partnerArr ⋆
        array (t := i32) sB.cur_rm curRm ⋆ array64 sB.cur_rl curRl ⋆ array64 sB.cur_rh curRh ⋆
        array (t := i32) sB.cur_rp curRp ⋆
        tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1 dB.pool0 dB.pool1 ⋆
        qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq dB.vqSkip ⋆
        Rcur ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mB →
      Q (false, ⟨⟩) mB)
    (hkTrue : ∀ (sB : ArCtxState) (dB : CmDynArrs) (mB : Mem 64),
      dB.LenOk s0.qcap.toNat →
      sB = { sA with
        tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop,
        qn := sB.qn, ix := sB.ix, ix2 := sB.ix2 } →
      ((sB.ix = s0.ix ∧ sB.ix2 = s0.ix2) ∨ (sB.ix = s0.ix2 ∧ sB.ix2 = s0.ix)) →
      dB.rsM = d.rsM → dB.rsL = d.rsL → dB.rsH = d.rsH → dB.rsPool = d.rsPool →
      dB.rm = d.rm → dB.rl = d.rl → dB.rh = d.rh →
      dB.rm2 = d.rm2 → dB.rl2 = d.rl2 → dB.rh2 = d.rh2 → dB.rpool = d.rpool →
      sB.pc.toNat < 2 → sB.tc.toNat < 2 →
      sB.tn.toNat ≤ s0.tcap.toNat → sB.ptop.toNat ≤ s0.pcap.toNat →
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
        polyEval s0.n_out.toNat (cSig g ρ t.bindArr)
            (if sB.pc.toNat = 0 then dB.pool0 else dB.pool1)
            (if sB.tc.toNat = 0 then dB.tm0 else dB.tm1)
            (if sB.tc.toNat = 0 then dB.tl0 else dB.tl1)
            (if sB.tc.toNat = 0 then dB.th0 else dB.th1) sB.tn.toNat =
          BitVec.ofNat s0.n_out.toNat (outWord g ρ) -
            BitVec.ofInt s0.n_out.toNat (inWord (decide (s0.spec = 1#32)) (g.I / 2) ρ 0) *
              BitVec.ofInt s0.n_out.toNat
                (inWord (decide (s0.spec = 1#32)) (g.I / 2) ρ (g.I / 2))) →
      (arCtxMem cx sB ⋆ array (t := i32) sB.partner t.partnerArr ⋆
        array (t := i32) sB.cur_rm curRm ⋆ array64 sB.cur_rl curRl ⋆ array64 sB.cur_rh curRh ⋆
        array (t := i32) sB.cur_rp curRp ⋆
        tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1 dB.pool0 dB.pool1 ⋆
        qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq dB.vqSkip ⋆
        Rcur ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mB →
      wp Γ Q X kTrue mB) :
    wp Γ Q X (@Expr.call Val Cont [.bool] "ar_apply" [i64, i32] [.bool]
      (Arg.var cx, Arg.var sym, ()) fun p =>
      Expr.jnz (Arg.var p.fst) kTrue (Expr.ret (Arg.imm false, ())) ) mA := by
  have htcap30 : s0.tcap.toNat < 2 ^ 30 := by rw [hb.tcap_eq]; have := hb.cap_hi; omega
  have hqcap32 : s0.qcap.toNat + 16 < 2 ^ 32 := by have := hb.cap_hi; omega
  have hpcap32 : s0.pcap.toNat < 2 ^ 32 := by rw [hb.pcap_eq]; have := hb.cap_hi; omega
  have h2nn32 : 2 * s0.n_nets.toNat < 2 ^ 32 := by have := hb.nnets_bd; omega
  let Rrest : Mem 64 → Prop := Rcur ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R
  apply wp_call_of_spec
  refine hApply _ _ _ _ ⟨sA, d.tm0, d.tm1, d.ts0, d.tl0, d.th0, d.ts1, d.tl1, d.th1,
    d.pool0, d.pool1, d.qm, d.qs, d.ql, d.qh, d.ix, d.ix2, d.bx, d.vqOff, d.vq, d.vqSkip,
    t.partnerArr, curRm, curRl, curRh, curRp,
    fun σ => ∃ ρ : Nat → Bool, σ = cSig g ρ t.bindArr, Rrest,
    hpc, htc, by rw [hs_tcap]; exact htn, by rw [hs_tcap]; exact htcap30,
    by rw [hs_qcap]; exact hb.cap_lo, by rw [hs_qcap]; exact hqcap32,
    by rw [hs_pcap]; exact hpt, by rw [hs_pcap]; exact hpcap32,
    by rw [hs_nn]; exact hb.nnets_bd, by rw [hs_nn]; exact h2nn32,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_pcap, hb.pcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_pcap, hb.pcap_eq]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_tcap, hb.tcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_pcap, hb.pcap_eq]
       exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_qcap]; exact Nat.le_of_eq hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    by rw [hs_no, hs_mlo, hs_mhi]; exact hb.masks,
    ⟨cSig g (fun _ => false) t.bindArr, fun _ => false, rfl⟩,
    fun σ ⟨ρ, hρ⟩ => by subst hρ; rw [hs_nn]; exact hPart ρ,
    fun σ ⟨ρ, hρ⟩ => by subst hρ; rw [hs_no]; exact hCurR ρ,
    hCurSort, hCurOk, hCurTot, hSlT, hSortT, hSigT, hTotT,
    sep_cast hmA (by dsimp only [Rrest]; ac_rfl),
    fun okB sB tm0B tm1B ts0B tl0B th0B ts1B tl1B th1B pool0B pool1B
      qmB qsB qlB qhB ixB ix2B bxB vqOffB vqB vqSkipB mB
      hpcB htcB hptB htnB hsB ltm0 ltm1 lts0 ltl0 lth0 lts1 ltl1 lth1 lp0 lp1
      lqm lqs lql lqh hixSwB lbx lvqo lvq lvqs hokB hmB => ?_⟩
  let dB : CmDynArrs := { d with
    tm0 := tm0B, tm1 := tm1B, ts0 := ts0B, tl0 := tl0B, th0 := th0B,
    ts1 := ts1B, tl1 := tl1B, th1 := th1B, pool0 := pool0B, pool1 := pool1B,
    qm := qmB, qs := qsB, ql := qlB, qh := qhB, ix := ixB, ix2 := ix2B,
    bx := bxB, vqOff := vqOffB, vq := vqB, vqSkip := vqSkipB }
  have lixB : ixB.length = d.ix.length := by
    rcases hixSwB with ⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩ <;> rw [h1] <;>
      simp [hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have lix2B : ix2B.length = d.ix2.length := by
    rcases hixSwB with ⟨_, _, _, h2⟩ | ⟨_, _, _, h2⟩ <;> rw [h2] <;>
      simp [hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hdLenB : dB.LenOk s0.qcap.toNat :=
    ⟨hdLen.1, hdLen.2.1, hdLen.2.2.1, hdLen.2.2.2.1,
     ltm0.trans hdLen.2.2.2.2.1, ltm1.trans hdLen.2.2.2.2.2.1, lts0.trans hdLen.2.2.2.2.2.2.1,
     ltl0.trans hdLen.2.2.2.2.2.2.2.1, lth0.trans hdLen.2.2.2.2.2.2.2.2.1,
     lts1.trans hdLen.2.2.2.2.2.2.2.2.2.1, ltl1.trans hdLen.2.2.2.2.2.2.2.2.2.2.1,
     lth1.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.1, lp0.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lp1.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1, lqm.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lqs.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lql.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lqh.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lixB.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lix2B.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lbx.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lvqo.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lvq.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lvqs.trans hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hix_sw0 : (sB.ix = s0.ix ∧ sB.ix2 = s0.ix2) ∨
      (sB.ix = s0.ix2 ∧ sB.ix2 = s0.ix) := by
    rcases hixSw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hixSwB with ⟨h3, h4, _⟩ | ⟨h3, h4, _⟩
    · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inr ⟨h3.trans h2, h4.trans h1⟩
    · exact Or.inr ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inl ⟨h3.trans h2, h4.trans h1⟩
  have hmB' : (arCtxMem cx sB ⋆ array (t := i32) sB.partner t.partnerArr ⋆
      array (t := i32) sB.cur_rm curRm ⋆ array64 sB.cur_rl curRl ⋆ array64 sB.cur_rh curRh ⋆
      array (t := i32) sB.cur_rp curRp ⋆
      tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1 dB.pool0 dB.pool1 ⋆
      qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq dB.vqSkip ⋆
      Rcur ⋆ bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mB := by
    dsimp only [Rrest] at hmB; exact sep_cast hmB (by ac_rfl)
  cases okB
  · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    exact hFail sB dB mB hdLenB hsB hix_sw0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hmB'
  · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    obtain ⟨hSlB, hSortB, hSigB, hTotB, _, hEvB⟩ := hokB rfl
    exact hkTrue sB dB mB hdLenB hsB hix_sw0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hpcB htcB (by rw [← hs_tcap]; exact htnB) (by rw [← hs_pcap]; exact hptB)
      hSlB hSortB hSigB hTotB (fun ρ => by
        have h1 := hEvB (cSig g ρ t.bindArr) ⟨ρ, rfl⟩
        rw [hs_no] at h1
        exact h1.trans (hEv ρ))
      hmB'

theorem s1'_ar_eq {s1' sL s0 : ArCtxState} {top0 : Nat}
    {tL : CmTabArrs} {dL : CmDynArrs} (hs : s1' = { sL with pos := s1'.pos }) :
    cmArenaMem s1' s0 top0 tL dL = cmArenaMem sL s0 top0 tL dL := by
  dsimp only [cmArenaMem, aigArraysMem, netTablesMem, gateScratchMem, rsMem, tMem, qMem, rMem]
  rw [show s1'.rhs0 = sL.rhs0 by rw [hs], show s1'.rhs1 = sL.rhs1 by rw [hs],
    show s1'.olit = sL.olit by rw [hs], show s1'.bind = sL.bind by rw [hs],
    show s1'.rule_off = sL.rule_off by rw [hs], show s1'.rule_n = sL.rule_n by rw [hs],
    show s1'.partner = sL.partner by rw [hs], show s1'.flipped = sL.flipped by rw [hs],
    show s1'.in_net = sL.in_net by rw [hs], show s1'.out_ref = sL.out_ref by rw [hs],
    show s1'.stk_n = sL.stk_n by rw [hs], show s1'.stk_p = sL.stk_p by rw [hs],
    show s1'.memo_n = sL.memo_n by rw [hs], show s1'.memo_v = sL.memo_v by rw [hs],
    show s1'.dense = sL.dense by rw [hs], show s1'.gsy = sL.gsy by rw [hs],
    show s1'.gcl = sL.gcl by rw [hs], show s1'.gch = sL.gch by rw [hs],
    show s1'.rs_m = sL.rs_m by rw [hs], show s1'.rs_l = sL.rs_l by rw [hs],
    show s1'.rs_h = sL.rs_h by rw [hs], show s1'.rs_pool = sL.rs_pool by rw [hs],
    show s1'.tm = sL.tm by rw [hs], show s1'.ts = sL.ts by rw [hs],
    show s1'.tl = sL.tl by rw [hs], show s1'.th = sL.th by rw [hs],
    show s1'.pool = sL.pool by rw [hs], show s1'.qm = sL.qm by rw [hs],
    show s1'.qs = sL.qs by rw [hs], show s1'.ql = sL.ql by rw [hs],
    show s1'.qh = sL.qh by rw [hs], show s1'.ix = sL.ix by rw [hs],
    show s1'.ix2 = sL.ix2 by rw [hs], show s1'.bx = sL.bx by rw [hs],
    show s1'.vq_off = sL.vq_off by rw [hs], show s1'.vq = sL.vq by rw [hs],
    show s1'.vq_skip = sL.vq_skip by rw [hs], show s1'.rm = sL.rm by rw [hs],
    show s1'.rl = sL.rl by rw [hs], show s1'.rh = sL.rh by rw [hs],
    show s1'.rm2 = sL.rm2 by rw [hs], show s1'.rl2 = sL.rl2 by rw [hs],
    show s1'.rh2 = sL.rh2 by rw [hs], show s1'.rpool = sL.rpool by rw [hs],
    show s1'.w = sL.w by rw [hs], show s1'.top = sL.top by rw [hs],
    show s1'.wlen = sL.wlen by rw [hs]]

theorem d_LenOk_buildR {dL : CmDynArrs} {cap : Nat} (hdL : dL.LenOk cap)
    {rmR rm2R : List (BitVec 32)} {rlR rhR rl2R rh2R : List (BitVec 64)}
    {rpoolR ixR ix2R : List (BitVec 32)}
    (lrmR : rmR.length = dL.rm.length) (lrlR : rlR.length = dL.rl.length)
    (lrhR : rhR.length = dL.rh.length) (lrm2R : rm2R.length = dL.rm2.length)
    (lrl2R : rl2R.length = dL.rl2.length) (lrh2R : rh2R.length = dL.rh2.length)
    (lrpR : rpoolR.length = dL.rpool.length) (lixR : ixR.length = dL.ix.length)
    (lix2R : ix2R.length = dL.ix2.length) :
    ({ dL with
       rm := rmR, rl := rlR, rh := rhR, rm2 := rm2R, rl2 := rl2R, rh2 := rh2R,
       rpool := rpoolR, ix := ixR, ix2 := ix2R } : CmDynArrs).LenOk cap :=
  ⟨hdL.1, hdL.2.1, hdL.2.2.1, hdL.2.2.2.1, hdL.2.2.2.2.1, hdL.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lixR.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lix2R.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrmR.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrlR.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrhR.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrm2R.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrl2R.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrh2R.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrpR.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem cmArena_apply_rs_repack {cx aig : Val i64} {s0 s1' sR sB : ArCtxState}
    {top0 off : Nat} {aigBytes artBytes : List UInt8}
    {tL : CmTabArrs} {dR dB : CmDynArrs} {R : Mem 64 → Prop} {mB : Mem 64}
    (hsR : sR = { s1' with
      cur_rm := sR.cur_rm, cur_rl := sR.cur_rl,
      cur_rh := sR.cur_rh, cur_rp := sR.cur_rp, cur_nr := sR.cur_nr })
    (hsB : sB = { sR with
      tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop,
      qn := sB.qn, ix := sB.ix, ix2 := sB.ix2 })
    (hcm : sR.cur_rm = s1'.rs_m + BitVec.ofNat 64 (4 * off))
    (hcl : sR.cur_rl = s1'.rs_l + BitVec.ofNat 64 (8 * off))
    (hch : sR.cur_rh = s1'.rs_h + BitVec.ofNat 64 (8 * off))
    (hcp : sR.cur_rp = s1'.rs_pool)
    (hoff_m : off ≤ dR.rsM.length) (hoff_l : off ≤ dR.rsL.length)
    (hoff_h : off ≤ dR.rsH.length)
    (hrsM : dB.rsM = dR.rsM) (hrsL : dB.rsL = dR.rsL)
    (hrsH : dB.rsH = dR.rsH) (hrsP : dB.rsPool = dR.rsPool)
    (hrm : dB.rm = dR.rm) (hrl : dB.rl = dR.rl) (hrh : dB.rh = dR.rh)
    (hrm2 : dB.rm2 = dR.rm2) (hrl2 : dB.rl2 = dR.rl2) (hrh2 : dB.rh2 = dR.rh2)
    (hrp : dB.rpool = dR.rpool)
    (hmB : (arCtxMem cx sB ⋆ array (t := i32) sB.partner tL.partnerArr ⋆
      array (t := i32) sB.cur_rm (dR.rsM.drop off) ⋆
      array64 sB.cur_rl (dR.rsL.drop off) ⋆ array64 sB.cur_rh (dR.rsH.drop off) ⋆
      array (t := i32) sB.cur_rp dR.rsPool ⋆
      tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1 dB.pool0 dB.pool1 ⋆
      qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq dB.vqSkip ⋆
      (aigArraysMem sR tL.rhs0 tL.rhs1 tL.olit ⋆ arrayPad i32 sR.bind tL.bindArr ⋆
        arrayPad i32 sR.rule_off tL.ruleOff ⋆ arrayPad i32 sR.rule_n tL.ruleN ⋆
        u32PadTail sR.partner tL.partnerArr.length ⋆ arrayPad i8 sR.flipped tL.flippedArr ⋆
        arrayPad i32 sR.in_net tL.inNetArr ⋆ arrayPad i32 sR.out_ref tL.outRefArr ⋆
        gateScratchMem sR tL.stkN tL.stkP tL.memoN tL.memoV tL.dense tL.gsy tL.gcl tL.gch ⋆
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        array (t := i32) sR.rs_m (dR.rsM.take off) ⋆
        array64 sR.rs_l (dR.rsL.take off) ⋆ array64 sR.rs_h (dR.rsH.take off) ⋆
        u32PadTail sR.rs_m dR.rsM.length ⋆ u32PadTail sR.rs_pool dR.rsPool.length ⋆
        rMem sR dR.rm dR.rl dR.rh dR.rm2 dR.rl2 dR.rh2 dR.rpool ⋆
        region (sR.w + sR.top) (sR.wlen.toNat - sR.top.toNat)) ⋆
      bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mB) :
    (arCtxMem cx sB ⋆ bytes s0.art artBytes ⋆ cmArenaMem sB s0 top0 tL dB ⋆
      bytes aig aigBytes ⋆ R) mB := by
  rw [arena_unpack_apply, rsMem_unpack, hrsM, hrsL, hrsH, hrsP, hrm, hrl, hrh,
    hrm2, hrl2, hrh2, hrp, rs_split_at hoff_m hoff_l hoff_h]
  dsimp only [aigArraysMem, gateScratchMem, rMem]
  dsimp only [aigArraysMem, gateScratchMem, rMem] at hmB
  rw [show sB.cur_rm = sR.cur_rm by rw [hsB], show sB.cur_rl = sR.cur_rl by rw [hsB],
    show sB.cur_rh = sR.cur_rh by rw [hsB], show sB.cur_rp = sR.cur_rp by rw [hsB],
    hcm, hcl, hch, hcp, Nat.mul_comm 4 off, Nat.mul_comm 8 off,
    show s1'.rs_m = sB.rs_m by rw [hsB, hsR], show s1'.rs_l = sB.rs_l by rw [hsB, hsR],
    show s1'.rs_h = sB.rs_h by rw [hsB, hsR], show s1'.rs_pool = sB.rs_pool by rw [hsB, hsR],
    show sR.rs_m = sB.rs_m by rw [hsB], show sR.rs_l = sB.rs_l by rw [hsB],
    show sR.rs_h = sB.rs_h by rw [hsB], show sR.rs_pool = sB.rs_pool by rw [hsB],
    show sR.rhs0 = sB.rhs0 by rw [hsB], show sR.rhs1 = sB.rhs1 by rw [hsB],
    show sR.olit = sB.olit by rw [hsB], show sR.bind = sB.bind by rw [hsB],
    show sR.rule_off = sB.rule_off by rw [hsB], show sR.rule_n = sB.rule_n by rw [hsB],
    show sR.flipped = sB.flipped by rw [hsB], show sR.in_net = sB.in_net by rw [hsB],
    show sR.out_ref = sB.out_ref by rw [hsB], show sR.stk_n = sB.stk_n by rw [hsB],
    show sR.stk_p = sB.stk_p by rw [hsB], show sR.memo_n = sB.memo_n by rw [hsB],
    show sR.memo_v = sB.memo_v by rw [hsB], show sR.dense = sB.dense by rw [hsB],
    show sR.gsy = sB.gsy by rw [hsB], show sR.gcl = sB.gcl by rw [hsB],
    show sR.gch = sB.gch by rw [hsB], show sR.rm = sB.rm by rw [hsB],
    show sR.rl = sB.rl by rw [hsB], show sR.rh = sB.rh by rw [hsB],
    show sR.rm2 = sB.rm2 by rw [hsB], show sR.rl2 = sB.rl2 by rw [hsB],
    show sR.rh2 = sB.rh2 by rw [hsB], show sR.rpool = sB.rpool by rw [hsB],
    show sR.w = sB.w by rw [hsB], show sR.top = sB.top by rw [hsB],
    show sR.wlen = sB.wlen by rw [hsB], show sR.partner = sB.partner by rw [hsB]] at hmB
  exact sep_cast hmB (by ac_rfl)

theorem cmArena_apply_r2_repack {cx aig : Val i64} {s0 s1' sR sB : ArCtxState}
    {top0 : Nat} {aigBytes artBytes : List UInt8}
    {tL : CmTabArrs} {dR dB : CmDynArrs} {R : Mem 64 → Prop} {mB : Mem 64}
    (hsR : sR = { s1' with
      cur_rm := sR.cur_rm, cur_rl := sR.cur_rl,
      cur_rh := sR.cur_rh, cur_rp := sR.cur_rp, cur_nr := sR.cur_nr })
    (hsB : sB = { sR with
      tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop,
      qn := sB.qn, ix := sB.ix, ix2 := sB.ix2 })
    (hcm : sR.cur_rm = s1'.rm2) (hcl : sR.cur_rl = s1'.rl2)
    (hch : sR.cur_rh = s1'.rh2) (hcp : sR.cur_rp = s1'.rpool)
    (hrsM : dB.rsM = dR.rsM) (hrsL : dB.rsL = dR.rsL)
    (hrsH : dB.rsH = dR.rsH) (hrsP : dB.rsPool = dR.rsPool)
    (hrm : dB.rm = dR.rm) (hrl : dB.rl = dR.rl) (hrh : dB.rh = dR.rh)
    (hrm2 : dB.rm2 = dR.rm2) (hrl2 : dB.rl2 = dR.rl2)
    (hrh2 : dB.rh2 = dR.rh2) (hrp : dB.rpool = dR.rpool)
    (hmB : (arCtxMem cx sB ⋆ array (t := i32) sB.partner tL.partnerArr ⋆
      array (t := i32) sB.cur_rm dR.rm2 ⋆ array64 sB.cur_rl dR.rl2 ⋆
      array64 sB.cur_rh dR.rh2 ⋆ array (t := i32) sB.cur_rp dR.rpool ⋆
      tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1 dB.pool0 dB.pool1 ⋆
      qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq dB.vqSkip ⋆
      (aigArraysMem sR tL.rhs0 tL.rhs1 tL.olit ⋆ arrayPad i32 sR.bind tL.bindArr ⋆
        arrayPad i32 sR.rule_off tL.ruleOff ⋆ arrayPad i32 sR.rule_n tL.ruleN ⋆
        u32PadTail sR.partner tL.partnerArr.length ⋆ arrayPad i8 sR.flipped tL.flippedArr ⋆
        arrayPad i32 sR.in_net tL.inNetArr ⋆ arrayPad i32 sR.out_ref tL.outRefArr ⋆
        gateScratchMem sR tL.stkN tL.stkP tL.memoN tL.memoV tL.dense tL.gsy tL.gcl tL.gch ⋆
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        rsMem sR dR.rsM dR.rsL dR.rsH dR.rsPool ⋆
        arrayPad i32 sR.rm dR.rm ⋆ array64 sR.rl dR.rl ⋆ array64 sR.rh dR.rh ⋆
        u32PadTail sR.rm2 dR.rm2.length ⋆ u32PadTail sR.rpool dR.rpool.length ⋆
        region (sR.w + sR.top) (sR.wlen.toNat - sR.top.toNat)) ⋆
      bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mB) :
    (arCtxMem cx sB ⋆ bytes s0.art artBytes ⋆ cmArenaMem sB s0 top0 tL dB ⋆
      bytes aig aigBytes ⋆ R) mB := by
  rw [arena_unpack_apply]
  dsimp only [aigArraysMem, gateScratchMem, rsMem, rMem]
  rw [arrayPad_u32_unfold sB.rm2 dB.rm2, arrayPad_u32_unfold sB.rpool dB.rpool,
    hrm, hrl, hrh, hrm2, hrl2, hrh2, hrp, hrsM, hrsL, hrsH, hrsP]
  dsimp only [aigArraysMem, gateScratchMem, rsMem] at hmB
  rw [show sB.cur_rm = sR.cur_rm by rw [hsB], show sB.cur_rl = sR.cur_rl by rw [hsB],
    show sB.cur_rh = sR.cur_rh by rw [hsB], show sB.cur_rp = sR.cur_rp by rw [hsB],
    hcm, hcl, hch, hcp,
    show s1'.rm2 = sB.rm2 by rw [hsB, hsR], show s1'.rl2 = sB.rl2 by rw [hsB, hsR],
    show s1'.rh2 = sB.rh2 by rw [hsB, hsR], show s1'.rpool = sB.rpool by rw [hsB, hsR],
    show sR.rm2 = sB.rm2 by rw [hsB], show sR.rpool = sB.rpool by rw [hsB],
    show sR.rhs0 = sB.rhs0 by rw [hsB], show sR.rhs1 = sB.rhs1 by rw [hsB],
    show sR.olit = sB.olit by rw [hsB], show sR.bind = sB.bind by rw [hsB],
    show sR.rule_off = sB.rule_off by rw [hsB], show sR.rule_n = sB.rule_n by rw [hsB],
    show sR.flipped = sB.flipped by rw [hsB], show sR.in_net = sB.in_net by rw [hsB],
    show sR.out_ref = sB.out_ref by rw [hsB], show sR.stk_n = sB.stk_n by rw [hsB],
    show sR.stk_p = sB.stk_p by rw [hsB], show sR.memo_n = sB.memo_n by rw [hsB],
    show sR.memo_v = sB.memo_v by rw [hsB], show sR.dense = sB.dense by rw [hsB],
    show sR.gsy = sB.gsy by rw [hsB], show sR.gcl = sB.gcl by rw [hsB],
    show sR.gch = sB.gch by rw [hsB], show sR.rs_m = sB.rs_m by rw [hsB],
    show sR.rs_l = sB.rs_l by rw [hsB], show sR.rs_h = sB.rs_h by rw [hsB],
    show sR.rs_pool = sB.rs_pool by rw [hsB], show sR.rm = sB.rm by rw [hsB],
    show sR.rl = sB.rl by rw [hsB], show sR.rh = sB.rh by rw [hsB],
    show sR.w = sB.w by rw [hsB], show sR.top = sB.top by rw [hsB],
    show sR.wlen = sB.wlen by rw [hsB], show sR.partner = sB.partner by rw [hsB]] at hmB
  exact sep_cast hmB (by ac_rfl)

theorem cmArena_apply_r1_repack {cx aig : Val i64} {s0 s1' sF sB : ArCtxState}
    {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t : CmTabArrs} {flL flB : List (BitVec 8)} {dF dB : CmDynArrs}
    {R : Mem 64 → Prop} {mB : Mem 64}
    (hsF : sF = { s1' with
      cur_rm := s1'.rm, cur_rl := s1'.rl, cur_rh := s1'.rh,
      cur_rp := s1'.rpool, cur_nr := 2#32 })
    (hsB : sB = { sF with
      tc := sB.tc, tn := sB.tn, pc := sB.pc, ptop := sB.ptop,
      qn := sB.qn, ix := sB.ix, ix2 := sB.ix2 })
    (lfl : flB.length = flL.length)
    (hrsM : dB.rsM = dF.rsM) (hrsL : dB.rsL = dF.rsL)
    (hrsH : dB.rsH = dF.rsH) (hrsP : dB.rsPool = dF.rsPool)
    (hrmB : dB.rm = dF.rm) (hrlB : dB.rl = dF.rl) (hrhB : dB.rh = dF.rh)
    (hrm2B : dB.rm2 = dF.rm2) (hrl2B : dB.rl2 = dF.rl2) (hrh2B : dB.rh2 = dF.rh2)
    (hrpB : dB.rpool = dF.rpool)
    (hmB : (arCtxMem cx sB ⋆ array (t := i32) sB.partner t.partnerArr ⋆
      array (t := i32) sB.cur_rm dF.rm ⋆ array64 sB.cur_rl dF.rl ⋆
      array64 sB.cur_rh dF.rh ⋆ array (t := i32) sB.cur_rp dF.rpool ⋆
      tMem sB dB.tm0 dB.tm1 dB.ts0 dB.tl0 dB.th0 dB.ts1 dB.tl1 dB.th1 dB.pool0 dB.pool1 ⋆
      qMem sB dB.qm dB.qs dB.ql dB.qh dB.ix dB.ix2 dB.bx dB.vqOff dB.vq dB.vqSkip ⋆
      (array (t := i8) sF.flipped flB ⋆
        aigArraysMem s1' t.rhs0 t.rhs1 t.olit ⋆ arrayPad i32 s1'.bind t.bindArr ⋆
        arrayPad i32 s1'.rule_off t.ruleOff ⋆ arrayPad i32 s1'.rule_n t.ruleN ⋆
        u32PadTail s1'.partner t.partnerArr.length ⋆ u8PadTail s1'.flipped flL.length ⋆
        arrayPad i32 s1'.in_net t.inNetArr ⋆ arrayPad i32 s1'.out_ref t.outRefArr ⋆
        gateScratchMem s1' t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        rsMem s1' dF.rsM dF.rsL dF.rsH dF.rsPool ⋆
        u32PadTail s1'.rm dF.rm.length ⋆
        arrayPad i32 s1'.rm2 dF.rm2 ⋆ array64 s1'.rl2 dF.rl2 ⋆ array64 s1'.rh2 dF.rh2 ⋆
        u32PadTail s1'.rpool dF.rpool.length ⋆
        region (s1'.w + s1'.top) (s1'.wlen.toNat - s1'.top.toNat)) ⋆
      bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R) mB) :
    (arCtxMem cx sB ⋆ bytes s0.art artBytes ⋆
      cmArenaMem sB s0 top0 { t with flippedArr := flB } dB ⋆
      bytes aig aigBytes ⋆ R) mB := by
  rw [arena_unpack_apply]
  dsimp only [aigArraysMem, gateScratchMem, rsMem, rMem]
  rw [arrayPad_u8_unfold sB.flipped flB, arrayPad_u32_unfold sB.rm dB.rm,
    arrayPad_u32_unfold sB.rpool dB.rpool,
    lfl, hrmB, hrlB, hrhB, hrpB, hrsM, hrsL, hrsH, hrsP, hrm2B, hrl2B, hrh2B]
  dsimp only [aigArraysMem, gateScratchMem, rsMem] at hmB
  rw [show sB.cur_rm = sF.cur_rm by rw [hsB], show sB.cur_rl = sF.cur_rl by rw [hsB],
    show sB.cur_rh = sF.cur_rh by rw [hsB], show sB.cur_rp = sF.cur_rp by rw [hsB],
    show sF.cur_rm = sB.rm by rw [hsB, hsF], show sF.cur_rl = sB.rl by rw [hsB, hsF],
    show sF.cur_rh = sB.rh by rw [hsB, hsF], show sF.cur_rp = sB.rpool by rw [hsB, hsF],
    show sF.flipped = sB.flipped by rw [hsB],
    show s1'.rhs0 = sB.rhs0 by rw [hsB, hsF], show s1'.rhs1 = sB.rhs1 by rw [hsB, hsF],
    show s1'.olit = sB.olit by rw [hsB, hsF], show s1'.bind = sB.bind by rw [hsB, hsF],
    show s1'.rule_off = sB.rule_off by rw [hsB, hsF],
    show s1'.rule_n = sB.rule_n by rw [hsB, hsF],
    show s1'.flipped = sB.flipped by rw [hsB, hsF],
    show s1'.in_net = sB.in_net by rw [hsB, hsF],
    show s1'.out_ref = sB.out_ref by rw [hsB, hsF],
    show s1'.stk_n = sB.stk_n by rw [hsB, hsF], show s1'.stk_p = sB.stk_p by rw [hsB, hsF],
    show s1'.memo_n = sB.memo_n by rw [hsB, hsF], show s1'.memo_v = sB.memo_v by rw [hsB, hsF],
    show s1'.dense = sB.dense by rw [hsB, hsF], show s1'.gsy = sB.gsy by rw [hsB, hsF],
    show s1'.gcl = sB.gcl by rw [hsB, hsF], show s1'.gch = sB.gch by rw [hsB, hsF],
    show s1'.rs_m = sB.rs_m by rw [hsB, hsF], show s1'.rs_l = sB.rs_l by rw [hsB, hsF],
    show s1'.rs_h = sB.rs_h by rw [hsB, hsF], show s1'.rs_pool = sB.rs_pool by rw [hsB, hsF],
    show s1'.rm = sB.rm by rw [hsB, hsF], show s1'.rpool = sB.rpool by rw [hsB, hsF],
    show s1'.rm2 = sB.rm2 by rw [hsB, hsF], show s1'.rl2 = sB.rl2 by rw [hsB, hsF],
    show s1'.rh2 = sB.rh2 by rw [hsB, hsF], show s1'.w = sB.w by rw [hsB, hsF],
    show s1'.top = sB.top by rw [hsB, hsF], show s1'.wlen = sB.wlen by rw [hsB, hsF],
    show s1'.partner = sB.partner by rw [hsB, hsF]] at hmB
  exact sep_cast hmB (by ac_rfl)

theorem cmArena_buildR_repack {cx aig : Val i64} {s0 s1' sR : ArCtxState}
    {top0 : Nat} {aigBytes artBytes : List UInt8}
    {tL : CmTabArrs} {dL dR : CmDynArrs} {R : Mem 64 → Prop} {mR : Mem 64}
    (hsR : sR = { s1' with
      cur_rm := sR.cur_rm, cur_rl := sR.cur_rl,
      cur_rh := sR.cur_rh, cur_rp := sR.cur_rp, cur_nr := sR.cur_nr })
    (hdR : dR = { dL with
      rm := dR.rm, rl := dR.rl, rh := dR.rh, rm2 := dR.rm2, rl2 := dR.rl2, rh2 := dR.rh2,
      rpool := dR.rpool, ix := dR.ix, ix2 := dR.ix2 })
    (lixR : dR.ix.length = dL.ix.length) (lix2R : dR.ix2.length = dL.ix2.length)
    (hmR : (arCtxMem cx sR ⋆ array (t := i32) sR.rule_off tL.ruleOff ⋆
      array (t := i32) sR.rule_n tL.ruleN ⋆
      rsMem sR dR.rsM dR.rsL dR.rsH dR.rsPool ⋆
      array (t := i8) sR.flipped tL.flippedArr ⋆
      rMem sR dR.rm dR.rl dR.rh dR.rm2 dR.rl2 dR.rh2 dR.rpool ⋆
      array (t := i32) sR.ix dR.ix ⋆ array (t := i32) sR.ix2 dR.ix2 ⋆
      (aigArraysMem s1' tL.rhs0 tL.rhs1 tL.olit ⋆ arrayPad i32 s1'.bind tL.bindArr ⋆
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
        bytes s0.art artBytes ⋆ bytes aig aigBytes ⋆ R)) mR) :
    (arCtxMem cx sR ⋆ bytes s0.art artBytes ⋆ cmArenaMem sR s0 top0 tL dR ⋆
      bytes aig aigBytes ⋆ R) mR := by
  rw [arena_unpack_buildR]
  dsimp only [aigArraysMem, gateScratchMem, tMem]
  dsimp only [aigArraysMem, gateScratchMem, tMem] at hmR
  rw [show sR.rule_off = s1'.rule_off by rw [hsR], show sR.rule_n = s1'.rule_n by rw [hsR],
    show sR.flipped = s1'.flipped by rw [hsR], show sR.ix = s1'.ix by rw [hsR],
    show sR.ix2 = s1'.ix2 by rw [hsR]] at hmR ⊢
  rw [show sR.rhs0 = s1'.rhs0 by rw [hsR], show sR.rhs1 = s1'.rhs1 by rw [hsR],
    show sR.olit = s1'.olit by rw [hsR], show sR.bind = s1'.bind by rw [hsR],
    show sR.partner = s1'.partner by rw [hsR],
    show sR.in_net = s1'.in_net by rw [hsR], show sR.out_ref = s1'.out_ref by rw [hsR],
    show sR.stk_n = s1'.stk_n by rw [hsR], show sR.stk_p = s1'.stk_p by rw [hsR],
    show sR.memo_n = s1'.memo_n by rw [hsR], show sR.memo_v = s1'.memo_v by rw [hsR],
    show sR.dense = s1'.dense by rw [hsR], show sR.gsy = s1'.gsy by rw [hsR],
    show sR.gcl = s1'.gcl by rw [hsR], show sR.gch = s1'.gch by rw [hsR],
    show sR.tm = s1'.tm by rw [hsR], show sR.ts = s1'.ts by rw [hsR],
    show sR.tl = s1'.tl by rw [hsR], show sR.th = s1'.th by rw [hsR],
    show sR.pool = s1'.pool by rw [hsR], show sR.qm = s1'.qm by rw [hsR],
    show sR.qs = s1'.qs by rw [hsR], show sR.ql = s1'.ql by rw [hsR],
    show sR.qh = s1'.qh by rw [hsR],
    show sR.bx = s1'.bx by rw [hsR],
    show sR.vq_off = s1'.vq_off by rw [hsR], show sR.vq = s1'.vq by rw [hsR],
    show sR.vq_skip = s1'.vq_skip by rw [hsR], show sR.w = s1'.w by rw [hsR],
    show sR.top = s1'.top by rw [hsR], show sR.wlen = s1'.wlen by rw [hsR],
    show dR.tm0 = dL.tm0 by rw [hdR], show dR.tm1 = dL.tm1 by rw [hdR],
    show dR.ts0 = dL.ts0 by rw [hdR], show dR.tl0 = dL.tl0 by rw [hdR],
    show dR.th0 = dL.th0 by rw [hdR], show dR.ts1 = dL.ts1 by rw [hdR],
    show dR.tl1 = dL.tl1 by rw [hdR], show dR.th1 = dL.th1 by rw [hdR],
    show dR.pool0 = dL.pool0 by rw [hdR], show dR.pool1 = dL.pool1 by rw [hdR],
    show dR.qm = dL.qm by rw [hdR], show dR.qs = dL.qs by rw [hdR],
    show dR.ql = dL.ql by rw [hdR], show dR.qh = dL.qh by rw [hdR],
    show dR.bx = dL.bx by rw [hdR], show dR.vqOff = dL.vqOff by rw [hdR],
    show dR.vq = dL.vq by rw [hdR], show dR.vqSkip = dL.vqSkip by rw [hdR],
    lixR, lix2R]
  exact sep_cast hmR (by ac_rfl)

theorem main_fail_collapse {cx aig : Val i64} {s0 s1 s2 sF : ArCtxState}
    {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t : CmTabArrs} {flF : List (BitVec 8)} {dF : CmDynArrs}
    {R : Mem 64 → Prop} {mF : Mem 64} {Q : Post [.bool]}
    (hb : CmBase s0 g top0 aigBytes artBytes) (htLen : t.LenOk g s0)
    (hs1_eq : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (lflF : flF.length = t.flippedArr.length) (hdF : dF.LenOk s0.qcap.toNat)
    (hsF : sF = { s1 with
      pos := sF.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := sF.tc, tn := sF.tn, pc := sF.pc, ptop := sF.ptop, qn := sF.qn,
      ix := sF.ix, ix2 := sF.ix2, cur_rm := sF.cur_rm, cur_rl := sF.cur_rl,
      cur_rh := sF.cur_rh, cur_rp := sF.cur_rp, cur_nr := sF.cur_nr })
    (hixF : (sF.ix = s0.ix ∧ sF.ix2 = s0.ix2) ∨ (sF.ix = s0.ix2 ∧ sF.ix2 = s0.ix))
    (hmF : (arCtxMem cx sF ⋆ bytes s0.art artBytes ⋆
      cmArenaMem sF s0 top0 { t with flippedArr := flF } dF ⋆ bytes aig aigBytes ⋆ R) mF)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m') :
    Q (false, ⟨⟩) mF :=
  hFail sF mF (collapse_dyn_and_tables (t := { t with flippedArr := flF }) hb
    ⟨htLen.1, htLen.2.1, htLen.2.2.1, htLen.2.2.2.1, htLen.2.2.2.2.1, htLen.2.2.2.2.2.1,
     htLen.2.2.2.2.2.2.1, lflF ▸ htLen.2.2.2.2.2.2.2.1, htLen.2.2.2.2.2.2.2.2⟩
    hdF
    (DynGeom.preserve hb.dgeom (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) hixF (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]))
    (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
    (by rw [show sF.top = s0.top by rw [hsF, hs1_eq],
            show sF.wlen = s0.wlen by rw [hsF, hs1_eq]]; exact hb.top_le_wlen)
    (tgeom_rw (s := sF) hb.tgeom (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq]) (by rw [hsF, hs1_eq])
      (by rw [hsF, hs1_eq]))
    hmF)

theorem CmDynArrs.len_ix {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) : d.ix.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_ix2 {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) :
    d.ix2.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rm {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) : d.rm.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rl {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) : d.rl.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rh {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) : d.rh.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rm2 {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) :
    d.rm2.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rl2 {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) :
    d.rl2.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rh2 {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) :
    d.rh2.length = cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem CmDynArrs.len_rpool {d : CmDynArrs} {cap : Nat} (h : d.LenOk cap) :
    d.rpool.length = 12 * cap :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem d_LenOk_flip {d : CmDynArrs} {cap : Nat}
    {rm' : List (BitVec 32)} {rl' rh' : List (BitVec 64)} {rp' : List (BitVec 32)}
    (hd : d.LenOk cap) (lrm : rm'.length = d.rm.length) (lrl : rl'.length = d.rl.length)
    (lrh : rh'.length = d.rh.length) (lrp : rp'.length = d.rpool.length) :
    ({ d with rm := rm', rl := rl', rh := rh', rpool := rp' } : CmDynArrs).LenOk cap :=
  ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   lrm.trans (CmDynArrs.len_rm hd), lrl.trans (CmDynArrs.len_rl hd),
   lrh.trans (CmDynArrs.len_rh hd),
   CmDynArrs.len_rm2 (d := d) hd, CmDynArrs.len_rl2 (d := d) hd, CmDynArrs.len_rh2 (d := d) hd,
   lrp.trans (CmDynArrs.len_rpool hd)⟩

theorem main_rulesRep_step {s0 s1 s2 s1' : ArCtxState} {g : Aig} {t : CmTabArrs}
    {d0 dL : CmDynArrs}
    (hs2_eq : s2 = { s1 with
      pos := s2.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s2.tc, tn := s2.tn, pc := s2.pc, ptop := s2.ptop, qn := s2.qn,
      ix := s2.ix, ix2 := s2.ix2, cur_rm := s2.cur_rm, cur_rl := s2.cur_rl,
      cur_rh := s2.cur_rh, cur_rp := s2.cur_rp, cur_nr := s2.cur_nr })
    (hs1'_s1 : s1' = { s1 with
      pos := s1'.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
      tc := s1'.tc, tn := s1'.tn, pc := s1'.pc, ptop := s1'.ptop, qn := s1'.qn,
      ix := s1'.ix, ix2 := s1'.ix2, cur_rm := s1'.cur_rm, cur_rl := s1'.cur_rl,
      cur_rh := s1'.cur_rh, cur_rp := s1'.cur_rp, cur_nr := s1'.cur_nr })
    (hrsm : dL.rsM = d0.rsM) (hrsl : dL.rsL = d0.rsL)
    (hrsh : dL.rsH = d0.rsH) (hrsp : dL.rsPool = d0.rsPool)
    (hRep : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ t.bindArr) s0.n_nets.toNat t.partnerArr ∧
      RulesRep s0.n_out.toNat (cSig g ρ t.bindArr) s2 t.ruleOff t.ruleN
        d0.rsM d0.rsL d0.rsH d0.rsPool) :
    ∀ ρ : Nat → Bool,
      RulesRep s0.n_out.toNat (cSig g ρ t.bindArr) s1' t.ruleOff t.ruleN
        dL.rsM dL.rsL dL.rsH dL.rsPool := fun ρ => by
  have hR0 := (hRep ρ).2
  rw [hrsm, hrsl, hrsh, hrsp]
  refine ⟨by rw [show s1'.n_nets = s2.n_nets by rw [hs1'_s1, hs2_eq]]; exact hR0.1,
    by rw [show s1'.n_nets = s2.n_nets by rw [hs1'_s1, hs2_eq]]; exact hR0.2.1,
    by rw [show s1'.rs_n = s2.rs_n by rw [hs1'_s1],
           show s1'.rs_cap = s2.rs_cap by rw [hs1'_s1, hs2_eq]]; exact hR0.2.2.1,
    by rw [show s1'.rs_ptop = s2.rs_ptop by rw [hs1'_s1],
           show s1'.rs_pcap = s2.rs_pcap by rw [hs1'_s1, hs2_eq]]; exact hR0.2.2.2.1,
    by rw [show s1'.rs_cap = s2.rs_cap by rw [hs1'_s1, hs2_eq]]; exact hR0.2.2.2.2.1,
    by rw [show s1'.rs_cap = s2.rs_cap by rw [hs1'_s1, hs2_eq]]; exact hR0.2.2.2.2.2.1,
    by rw [show s1'.rs_cap = s2.rs_cap by rw [hs1'_s1, hs2_eq]]; exact hR0.2.2.2.2.2.2.1,
    by rw [show s1'.rs_pcap = s2.rs_pcap by rw [hs1'_s1, hs2_eq]]; exact hR0.2.2.2.2.2.2.2.1,
    by rw [show s1'.rs_n = s2.rs_n by rw [hs1'_s1],
           show s1'.rs_ptop = s2.rs_ptop by rw [hs1'_s1]]; exact hR0.2.2.2.2.2.2.2.2.1,
    fun w hw hne => by
      rw [show s1'.n_nets = s2.n_nets by rw [hs1'_s1, hs2_eq]] at hw
      rw [show s1'.rs_n = s2.rs_n by rw [hs1'_s1]]
      exact hR0.2.2.2.2.2.2.2.2.2 w hw hne⟩

end

end LeanQbe.T.Examples.Arisca.Proof

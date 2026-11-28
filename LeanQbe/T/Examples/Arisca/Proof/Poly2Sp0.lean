/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Sp0Base
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Initial Polynomial `ar_build_sp0` WP (`Arisca.Proof.Poly2Sp0`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for `ar_build_sp0` (`ar_build_sp0_wp`),
covering both `SPEC_UMUL`/`SPEC_SMUL` (`spec ∈ {0, 1}`) and `SPEC_MITER` (`spec = 2`).
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

/-! ## 1. Pure & AST Extraction Helpers for `ar_build_sp0` -/

private theorem miter_add_A {w j : Nat} {g : Aig} {ρ : Nat → Bool} {prev next : BitVec w}
    (hPrev : prev = BitVec.ofNat w (outSlice g ρ 0 j) - BitVec.ofNat w (outSlice g ρ w j))
    (hStep : next = prev + BitVec.ofNat w (2 ^ j) * bv w (g.litVal ρ (g.outs.getD j 0))) :
    next = BitVec.ofNat w (outSlice g ρ 0 (j + 1)) - BitVec.ofNat w (outSlice g ρ w j) := by
  rw [hStep, hPrev, show g.outs.getD j 0 = g.outs.getD (0 + j) 0 by rw [Nat.zero_add],
    sp0_outSlice_succ w g ρ 0 j]
  simp only [BitVec.sub_eq_add_neg]; ac_rfl

private theorem miter_add_B {w j : Nat} {g : Aig} {ρ : Nat → Bool} {prev next : BitVec w}
    (hPrev : prev = BitVec.ofNat w (outSlice g ρ 0 (j + 1)) - BitVec.ofNat w (outSlice g ρ w j))
    (hStep : next =
      prev + (-BitVec.ofNat w (2 ^ j)) * bv w (g.litVal ρ (g.outs.getD (w + j) 0))) :
    next = BitVec.ofNat w (outSlice g ρ 0 (j + 1)) - BitVec.ofNat w (outSlice g ρ w (j + 1)) := by
  rw [hStep, hPrev, sp0_outSlice_succ w g ρ w j, BitVec.neg_mul]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

private def sp0FindTrue : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, .jnz _ eTrue _ => eTrue
  | n + 1, e => sp0FindTrue n (sp0StepStraight e)

private def sp0MiterBExpr (cx : Val i64) (J1 : Cont [.bits 32]) (wV jV : Val i32)
    (l0 h0 nl nh : Val i64) : Expr Val Cont [.bool] :=
  match sp0FindTrue 20 (ar_build_sp0_body Val Cont (cx, ())) with
  | @Expr.let_ _ _ _ [.bits 64] _ ka => match ka (0#64, ()) with
    | @Expr.load _ _ _ (.bits 32) _ kb => match kb 0#32 with
      | @Expr.let_ _ _ _ [.bits 32] _ kc => match kc (wV, ()) with
        | @Expr.group _ _ _ [[.bits 32]] bs1 _ =>
          match bs1 (J1, ()) with
          | .cons b1 _ => match sp0StepStraight (b1 (jV, ())) with
            | .jnz _ (@Expr.call _ _ _ (as := [.bits 64, .bits 32])
                (bs := [.bits 64, .bits 64]) "ar_cpow2" _ k1) _ =>
              match k1 (l0, h0, ()) with
              | @Expr.call _ _ _ (as := [.bits 64, .bits 64, .bits 64])
                  (bs := [.bits 64, .bits 64]) "ar_cneg" _ k2 =>
                match k2 (nl, nh, ()) with
                | @Expr.let_ _ _ _ [.bits 64] _ k3 => match k3 (0#64, ()) with
                  | @Expr.load _ _ _ (.bits 64) _ k4 => match k4 0#64 with
                    | @Expr.let_ _ _ _ [.bits 64] _ k5 => match k5 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ k6 => match k6 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ k7 => match k7 (0#64, ()) with
                          | @Expr.load _ _ _ (.bits 32) _ k8 => match k8 0#32 with
                            | @Expr.group _ _ _ [[]] bsA _ =>
                              match bsA (fun _ _ => False, ()) with
                              | .cons bA _ => bA ()
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

/-! ## 2. `SPEC_MITER` Loop (`sp0_miter_B_wp` & `sp0_miter_loop_wp`) -/

private theorem sp0_miter_B_wp (Γ : T.Env)
    (hAddQ : ∀ xs m Q X, arAddQSpec xs m Q X →
      Γ "ar_add_q" [i64, i32, i32, i32, i64, i64] [.bool] xs m Q X)
    {cx : Val i64} {J1 : Cont [.bits 32]} {wV jV : Val i32} {l0 h0 nl nh : Val i64}
    {Q : Post [.bool]} {X : XPost} {w : Nat}
    {s : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr partnerArr olit ruleN : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {restQ R : Mem 64 → Prop} {ptA qnA : Nat}
    {pool0A pool1A qmA : List (BitVec 32)} {qsA qlA qhA : List (BitVec 64)} {mA : Mem 64}
    (hw : w = s.modW) (_hspec2 : s.spec = 2#32)
    (hw_eq : wV.toNat = w) (hw_2 : 2 * w = g.outs.length) (hj_lt : jV.toNat < w)
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (hptA : ptA ≤ s.pcap.toNat) (hqnA : qnA ≤ s.qcap.toNat)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnnets : s.n_nets.toNat ≤ 0x3FFFFFFF) (hnn2 : 2 * s.n_nets.toNat < 2 ^ 32)
    (holit_len : olit.length = g.outs.length)
    (holit_eq : ∀ j < g.outs.length, (olit.getD j 0#32).toNat = g.outs.getD j 0)
    (hruleN_len : s.n_nets.toNat ≤ ruleN.length)
    (hp0A : pool0A.length = pool0.length) (hp1A : pool1A.length = pool1.length)
    (hp0_len : s.pcap.toNat ≤ pool0.length) (hp1_len : s.pcap.toNat ≤ pool1.length)
    (hqmA : qmA.length = qm.length) (hqsA : qsA.length = qs.length)
    (hqlA : qlA.length = ql.length) (hqhA : qhA.length = qh.length)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hqs_len : s.qcap.toNat ≤ qs.length)
    (hql_len : s.qcap.toNat ≤ ql.length) (hqh_len : s.qcap.toNat ≤ qh.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi) (hBind : BindRep s g bindArr inNetArr outRefArr)
    (hPart : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr)
    (hlh0' : coeff128 w l0 h0 = BitVec.ofNat w (2 ^ jV.toNat))
    (hnlnh' : coeff128 w nl nh = -BitVec.ofNat w (2 ^ jV.toNat))
    (hSlA : ∀ idx < qnA,
      MonoSliceOk (if s.pc.toNat = 0 then pool0A else pool1A) (qmA.getD idx 0#32).toNat ptA ∧
      ((if s.pc.toNat = 0 then pool0A else pool1A).getD
        (qmA.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortedA : ∀ idx < qnA,
      MonoSorted (if s.pc.toNat = 0 then pool0A else pool1A) (qmA.getD idx 0#32).toNat)
    (hSigA : SigOk (if s.pc.toNat = 0 then pool0A else pool1A) qmA qsA qnA)
    (hWA : monoTotalWords (if s.pc.toNat = 0 then pool0A else pool1A) qmA qnA ≤ ptA)
    (hEvA : ∀ ρ : Nat → Bool,
      polyEval w (cSig g ρ bindArr) (if s.pc.toNat = 0 then pool0A else pool1A)
          qmA qlA qhA qnA =
        BitVec.ofNat w (outSlice g ρ 0 (jV.toNat + 1)) -
          BitVec.ofNat w (outSlice g ρ w jV.toNat))
    (hmA : (arCtxMem cx (Sp0LoopState s ptA qnA) ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s ptA qnA) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
      array (t := i32) s.qm qmA ⋆ array64 s.qs qsA ⋆ array64 s.ql qlA ⋆
      array64 s.qh qhA ⋆ restQ ⋆
      (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) mA)
    (hFail : ∀ {ptF qnF : Nat} {pool0F pool1F qmF : List (BitVec 32)}
        {qsF qlF qhF : List (BitVec 64)} {mF : Mem 64},
      ptF ≤ s.pcap.toNat → qnF ≤ s.qcap.toNat →
      pool0F.length = pool0.length → pool1F.length = pool1.length →
      qmF.length = qm.length → qsF.length = qs.length →
      qlF.length = ql.length → qhF.length = qh.length →
      (arCtxMem cx (Sp0LoopState s ptF qnF) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0F pool1F ⋆
        array (t := i32) s.qm qmF ⋆ array64 s.qs qsF ⋆ array64 s.ql qlF ⋆
        array64 s.qh qhF ⋆ restQ ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) mF →
      Q (false, ⟨⟩) mF)
    (hRecStep : ∀ (j' : BitVec 32) (ptB qnB : Nat) (pool0B pool1B qmB : List (BitVec 32))
        (qsB qlB qhB : List (BitVec 64)) (mB : Mem 64),
      j'.toNat = jV.toNat + 1 →
      ptB ≤ s.pcap.toNat → qnB ≤ s.qcap.toNat →
      pool0B.length = pool0.length → pool1B.length = pool1.length →
      qmB.length = qm.length → qsB.length = qs.length →
      qlB.length = ql.length → qhB.length = qh.length →
      (∀ idx < qnB,
        MonoSliceOk (if s.pc.toNat = 0 then pool0B else pool1B) (qmB.getD idx 0#32).toNat ptB ∧
        ((if s.pc.toNat = 0 then pool0B else pool1B).getD
          (qmB.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ idx < qnB,
        MonoSorted (if s.pc.toNat = 0 then pool0B else pool1B) (qmB.getD idx 0#32).toNat) →
      SigOk (if s.pc.toNat = 0 then pool0B else pool1B) qmB qsB qnB →
      monoTotalWords (if s.pc.toNat = 0 then pool0B else pool1B) qmB qnB ≤ ptB →
      (∀ ρ : Nat → Bool,
        polyEval w (cSig g ρ bindArr) (if s.pc.toNat = 0 then pool0B else pool1B)
            qmB qlB qhB qnB =
          BitVec.ofNat w (outSlice g ρ 0 (jV.toNat + 1)) -
            BitVec.ofNat w (outSlice g ρ w (jV.toNat + 1))) →
      (arCtxMem cx (Sp0LoopState s ptB qnB) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptB qnB) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0B pool1B ⋆
        array (t := i32) s.qm qmB ⋆ array64 s.qs qsB ⋆ array64 s.ql qlB ⋆
        array64 s.qh qhB ⋆ restQ ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) mB →
      J1 (j', ⟨⟩) mB) :
    wp Γ Q X (sp0MiterBExpr cx J1 wV jV l0 h0 nl nh) mA := by
  have hnout_eq : s.n_out.toNat = g.outs.length := hBind.out_eq
  have hbj_32 : wV.toNat + jV.toNat < 2 ^ 32 := by have := s.n_out.isLt; omega
  have hbj_toNat : (wV + jV).toNat = w + jV.toNat := by
    rw [BitVec.toNat_add, hw_eq, Nat.mod_eq_of_lt (by omega)]
  have hbj_out : (wV + jV).toNat < s.n_out.toNat := by omega
  have hbj_arr : (wV + jV).toNat < outRefArr.length := by have := hBind.out_len; omega
  have hbj_ol : (wV + jV).toNat < olit.length := by omega
  dsimp only [sp0MiterBExpr]
  c0_hsteps_nogrp
  have hmA_out : (array (t := i32) s.out_ref outRefArr ⋆
      (arCtxMem cx (Sp0LoopState s ptA qnA) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptA qnA) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
        array (t := i32) s.qm qmA ⋆ array64 s.qs qsA ⋆ array64 s.ql qlA ⋆
        array64 s.qh qhA ⋆ restQ ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R))) mA :=
    sep_cast hmA (by ac_rfl)
  refine wp_load_arr32_idx (off := 0) (i := wV + jV) (hm := hmA_out) ?_ ?_ ?_
  · dsimp only [Sp0LoopState]; simp
  · simpa using hbj_arr
  c0_hsteps_nogrp
  let rfB := outRefArr[0 + (wV + jV).toNat]'(by simpa using hbj_arr)
  have hrfB_eq : rfB = outRefArr.getD (w + jV.toNat) 0#32 := by
    dsimp only [rfB]
    rw [← getD_eq_getElem outRefArr 0#32 (by simpa using hbj_arr), Nat.zero_add, hbj_toNat]
  have hjp1 : (jV + 1#32).toNat = jV.toNat + 1 := by
    have : jV.toNat + 1 < 2 ^ 32 := by have := wV.isLt; omega
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt this]
  refine wp_unroll_group fun J_endB hJ_endB => ?_
  refine wp_unroll_group fun J_thenB hJ_thenB => ?_
  have hToThenB :
      outRefArr.getD (w + jV.toNat) 0#32 = cNone32 ∨ g.outs.getD (w + jV.toNat) 0 ≤ 1 →
      J_thenB () mA := by
    intro hconstB
    refine hJ_thenB () mA ?_
    refine wp_unroll_group fun _ hEndB => ?_
    c0_hsteps_nogrp
    have hmA_ol : (array (t := i32) s.olit olit ⋆
        (arCtxMem cx (Sp0LoopState s ptA qnA) ⋆ array (t := i32) s.bind bindArr ⋆
          array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
          array (t := i32) s.partner partnerArr ⋆
          tMem (Sp0LoopState s ptA qnA) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
          array (t := i32) s.qm qmA ⋆ array64 s.qs qsA ⋆ array64 s.ql qlA ⋆
          array64 s.qh qhA ⋆ restQ ⋆
          (array (t := i32) s.rule_n ruleN ⋆ R))) mA :=
      sep_cast hmA (by ac_rfl)
    refine wp_load_arr32_idx (off := 0) (i := wV + jV) (hm := hmA_ol) ?_ ?_ ?_
    · dsimp only [Sp0LoopState]; simp
    · simpa using hbj_ol
    c0_hsteps_nogrp
    · have hlit1 : g.litVal (fun _ => false) (g.outs.getD (w + jV.toNat) 0) = true := by
        rw [hBind.miterOut_bit (fun _ => false) (hbj_toNat ▸ hbj_out) hconstB]
        have hol := holit_eq (w + jV.toNat) (by omega)
        have helem : olit[0 + (wV + jV).toNat]'(by simpa using hbj_ol) =
            olit.getD (w + jV.toNat) 0#32 := by
          rw [← getD_eq_getElem olit 0#32 (by simpa using hbj_ol), Nat.zero_add, hbj_toNat]
        have hc1 : (olit.getD (w + jV.toNat) 0#32).toNat = 1 := by
          rw [← helem]; exact congrArg BitVec.toNat hc
        rw [← hol, hc1]; decide
      refine sp0_call_addQ_wp Γ hAddQ 0 0 0 rfl rfl rfl rfl hptA hqnA hpc htc hqcap32 hpcap32
        hnnets hnn2 hp0A hp1A hp0_len hp1_len hqmA hqsA hqlA hqhA
        hqm_len hqs_len hql_len hqh_len hMasks hPart hSlA hSortedA hSigA
        (fun h => by cases h) hWA hmA hFail
        (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
          hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
          c0_hsteps
          refine hRecStep (jV + 1#32) pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1 hjp1
            hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 ?_ hm1
          intro ρ; refine miter_add_B (hEvA ρ) ?_
          have hEv1' := hw ▸ hEv1 ρ
          rw [hEv1', ← hnlnh']
          have hlitρ : g.litVal ρ (g.outs.getD (w + jV.toNat) 0) = true := by
            rw [hBind.miterOut_bit ρ (hbj_toNat ▸ hbj_out) hconstB]
            rw [← hBind.miterOut_bit (fun _ => false) (hbj_toNat ▸ hbj_out) hconstB]; exact hlit1
          rw [hlitρ]; simp [addQSyms, monoValL, bv])
    · refine hRecStep (jV + 1#32) ptA qnA pool0A pool1A qmA qsA qlA qhA mA hjp1
        hptA hqnA hp0A hp1A hqmA hqsA hqlA hqhA hSlA hSortedA hSigA hWA ?_ hmA
      intro ρ; refine miter_add_B (hEvA ρ) ?_
      have hlit0 : g.litVal ρ (g.outs.getD (w + jV.toNat) 0) = false := by
        rw [hBind.miterOut_bit ρ (hbj_toNat ▸ hbj_out) hconstB]
        have hol := holit_eq (w + jV.toNat) (by omega)
        have helem : olit[0 + (wV + jV).toNat]'(by simpa using hbj_ol) =
            olit.getD (w + jV.toNat) 0#32 := by
          rw [← getD_eq_getElem olit 0#32 (by simpa using hbj_ol), Nat.zero_add, hbj_toNat]
        have hne1 : (olit.getD (w + jV.toNat) 0#32).toNat ≠ 1 := by
          intro h1; apply hc
          have h0 : olit[0 + (wV.toNat + jV.toNat) % 2 ^ 32]'(by omega) =
              olit.getD (w + jV.toNat) 0#32 := by
            rw [← getD_eq_getElem olit 0#32 (by omega), Nat.zero_add,
              Nat.mod_eq_of_lt hbj_32, hw_eq]
          rw [h0]; exact BitVec.eq_of_toNat_eq (by simpa using h1)
        have h01 : g.outs.getD (w + jV.toNat) 0 ≤ 1 := by
          rcases hconstB with hnone | hle
          · rcases hBind.out_ok (w + jV.toNat) (hbj_toNat ▸ hbj_out) with ⟨_, _, ha⟩ | hok
            · exact ha
            · have hlt := hok.1; rw [hnone] at hlt
              have hcc : (cNone32 >>> 1).toNat = 0x7FFFFFFF := by decide
              omega
          · exact hle
        have h0 : g.outs.getD (w + jV.toNat) 0 = 0 := by omega
        rw [h0]; decide
      rw [hlit0]; simp [bv, BitVec.add_zero]
  c0_hsplit
  · exact hToThenB (Or.inl (hrfB_eq ▸ hc))
  · have hrfB_ne : outRefArr.getD (w + jV.toNat) 0#32 ≠ cNone32 := hrfB_eq ▸ hc
    have hrfB_lt := ((hBind.out_ok (w + jV.toNat) (hbj_toNat ▸ hbj_out)).resolve_left
      (fun h => hrfB_ne h.2.1)).1
    refine wp_unroll_group fun J_elseB hJ_elseB => ?_
    have hToElseB : J_elseB () mA := by
      refine hJ_elseB () mA ?_
      refine wp_unroll_group fun _ hEndB => ?_
      have hshB : (rfB >>> (1 : Nat)).toNat = rfB.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      c0_hsteps_nogrp
      · have hodd : (rfB &&& 1#32) ≠ 0#32 := hc
        refine sp0_call_addQ_wp Γ hAddQ 0 0 0 rfl rfl rfl rfl hptA hqnA hpc htc hqcap32 hpcap32
          hnnets hnn2 hp0A hp1A hp0_len hp1_len hqmA hqsA hqlA hqhA
          hqm_len hqs_len hql_len hqh_len hMasks hPart hSlA hSortedA hSigA
          (fun h => by cases h) hWA hmA hFail
          (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
            hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
            c0_hsteps_nogrp
            refine sp0_call_addQ_wp Γ hAddQ 1 (2 * (rfB >>> (1 : Nat)).toNat) 0 rfl
              (by change (2#32 * (rfB >>> 1#32)).toNat = 2 * (rfB >>> (1 : Nat)).toNat
                  rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
                    show (rfB >>> 1#32).toNat = (rfB >>> (1 : Nat)).toNat from rfl,
                    Nat.mod_eq_of_lt (by rw [hshB]; omega)])
              rfl rfl hpt1 hqn1 hpc htc hqcap32 hpcap32
              hnnets hnn2 hp0_1 hp1_1 hp0_len hp1_len hqm1 hqs1 hql1 hqh1
              hqm_len hqs_len hql_len hqh_len hMasks hPart hSl1 hSorted1 hSig1
              (fun h => by cases h) hW1 hm1 hFail
              (fun pt2 qn2 pool0_2 pool1_2 qm2 qs2 ql2 qh2 m2
                hpt2 hqn2 hp0_2 hp1_2 hqm2 hqs2 hql2 hqh2 hSl2 hSorted2 hSig2
                hW2 hEv2 hm2 => by
                c0_hsteps
                refine hRecStep (jV + 1#32) pt2 qn2 pool0_2 pool1_2 qm2 qs2 ql2 qh2 m2 hjp1
                  hpt2 hqn2 hp0_2 hp1_2 hqm2 hqs2 hql2 hqh2 hSl2 hSorted2 hSig2 hW2 ?_ hm2
                intro ρ; refine miter_add_B (hEvA ρ) ?_
                have hEv2' := hw ▸ hEv2 ρ
                have hEv1' := hw ▸ hEv1 ρ
                dsimp only at hEv2' hEv1'
                rw [hEv2', hEv1', BitVec.add_assoc]
                congr 1
                rw [sp0_out_step_odd_gen (-BitVec.ofNat w (2 ^ jV.toNat))
                  (cSig g ρ bindArr) rfB hodd hnlnh' (by rw [hlh0', BitVec.neg_neg]),
                  hrfB_eq, hBind.out_sig ρ (hbj_toNat ▸ hbj_out) hrfB_ne]))
      · have heven : (rfB &&& 1#32) = 0#32 := hc
        refine sp0_call_addQ_wp Γ hAddQ 1 (2 * (rfB >>> (1 : Nat)).toNat) 0 rfl
          (by change (2#32 * (rfB >>> 1#32)).toNat = 2 * (rfB >>> (1 : Nat)).toNat
              rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
                show (rfB >>> 1#32).toNat = (rfB >>> (1 : Nat)).toNat from rfl,
                Nat.mod_eq_of_lt (by rw [hshB]; omega)])
          rfl rfl hptA hqnA hpc htc hqcap32 hpcap32
          hnnets hnn2 hp0A hp1A hp0_len hp1_len hqmA hqsA hqlA hqhA
          hqm_len hqs_len hql_len hqh_len hMasks hPart hSlA hSortedA hSigA
          (fun h => by cases h) hWA hmA hFail
          (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
            hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
            c0_hsteps
            refine hRecStep (jV + 1#32) pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1 hjp1
              hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 ?_ hm1
            intro ρ; refine miter_add_B (hEvA ρ) ?_
            have hEv1' := hw ▸ hEv1 ρ
            dsimp only at hEv1'
            rw [hEv1', sp0_out_step_even_gen (-BitVec.ofNat w (2 ^ jV.toNat))
              (cSig g ρ bindArr) rfB heven hnlnh', hrfB_eq,
              hBind.out_sig ρ (hbj_toNat ▸ hbj_out) hrfB_ne])
    c0_hsteps_nogrp
    have hmA_ol : (array (t := i32) s.olit olit ⋆
        (arCtxMem cx (Sp0LoopState s ptA qnA) ⋆ array (t := i32) s.bind bindArr ⋆
          array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
          array (t := i32) s.partner partnerArr ⋆
          tMem (Sp0LoopState s ptA qnA) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
          array (t := i32) s.qm qmA ⋆ array64 s.qs qsA ⋆ array64 s.ql qlA ⋆
          array64 s.qh qhA ⋆ restQ ⋆
          (array (t := i32) s.rule_n ruleN ⋆ R))) mA :=
      sep_cast hmA (by ac_rfl)
    refine wp_load_arr32_idx (off := 0) (i := wV + jV) (hm := hmA_ol) ?_ ?_ ?_
    · dsimp only [Sp0LoopState]; simp
    · simpa using hbj_ol
    c0_hsplit
    · have hncB : (olit.getD (w + jV.toNat) 0#32).toNat ≤ 1 := by
        rw [getD_eq_getElem olit 0#32 (by omega)]
        simpa [hw_eq, Nat.zero_add, Nat.mod_eq_of_lt hbj_32] using hc
      have hmA_rn : (array (t := i32) s.rule_n ruleN ⋆
          (arCtxMem cx (Sp0LoopState s ptA qnA) ⋆ array (t := i32) s.bind bindArr ⋆
            array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
            array (t := i32) s.partner partnerArr ⋆
            tMem (Sp0LoopState s ptA qnA) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
            array (t := i32) s.qm qmA ⋆ array64 s.qs qsA ⋆ array64 s.ql qlA ⋆
            array64 s.qh qhA ⋆ restQ ⋆
            (array (t := i32) s.olit olit ⋆ R))) mA :=
        sep_cast hmA (by ac_rfl)
      c0_hsteps_nogrp
      refine wp_load_arr32_idx (off := 0) (i := rfB >>> 1#32) (hm := hmA_rn)
        (by dsimp only [Sp0LoopState, rfB]; simp [Nat.zero_add, hbj_toNat])
        (by rw [← hrfB_eq] at hrfB_lt; simpa using Nat.lt_of_lt_of_le hrfB_lt hruleN_len)
        ?_
      c0_hsplit
      · refine hToThenB (Or.inr ?_)
        have hol := holit_eq (w + jV.toNat) (by omega)
        omega
      · exact hToElseB
    · exact hToElseB

private theorem sp0_miter_loop_wp (Γ : T.Env)
    (hAddQ : ∀ xs m Q X, arAddQSpec xs m Q X →
      Γ "ar_add_q" [i64, i32, i32, i32, i64, i64] [.bool] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCpow2 : ∀ xs m Q X, arCpow2Spec xs m Q X →
      Γ "ar_cpow2" [i64, i32] [i64, i64] xs m Q X)
    {cx : Val i64} {Q : Post [.bool]} {X : XPost} {w : Nat}
    {s : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr partnerArr olit ruleN : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {restQ R : Mem 64 → Prop} {m : Mem 64}
    (hw : w = s.modW) (hspec2 : s.spec = 2#32)
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnnets : s.n_nets.toNat ≤ 0x3FFFFFFF) (hnn2 : 2 * s.n_nets.toNat < 2 ^ 32)
    (holit_len : olit.length = g.outs.length)
    (holit_eq : ∀ j < g.outs.length, (olit.getD j 0#32).toNat = g.outs.getD j 0)
    (hruleN_len : s.n_nets.toNat ≤ ruleN.length)
    (htm0_len : s.tcap.toNat ≤ tm0.length) (htm1_len : s.tcap.toNat ≤ tm1.length)
    (hts0_len : s.tcap.toNat ≤ ts0.length) (htl0_len : s.tcap.toNat ≤ tl0.length)
    (hth0_len : s.tcap.toNat ≤ th0.length) (hts1_len : s.tcap.toNat ≤ ts1.length)
    (htl1_len : s.tcap.toNat ≤ tl1.length) (hth1_len : s.tcap.toNat ≤ th1.length)
    (hp0_len : s.pcap.toNat ≤ pool0.length) (hp1_len : s.pcap.toNat ≤ pool1.length)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hqs_len : s.qcap.toNat ≤ qs.length)
    (hql_len : s.qcap.toNat ≤ ql.length) (hqh_len : s.qcap.toNat ≤ qh.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hix2_len : s.qcap.toNat ≤ ix2.length)
    (hix_eq : ix.length = ix2.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi) (hBind : BindRep s g bindArr inNetArr outRefArr)
    (hPart : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr)
    (hqBack : ∀ s' qm' qs' ql' qh',
      s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
      s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx →
      s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip → qm'.length = qm.length →
      qMem s' qm' qs' ql' qh' ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) s'.qm qm' ⋆ array64 s'.qs qs' ⋆ array64 s'.ql ql' ⋆
          array64 s'.qh qh' ⋆ restQ))
    (hm : (arCtxMem cx (Sp0LoopState s 0 0) ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s 0 0) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
      array64 s.qh qh ⋆ restQ ⋆
      (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) m)
    (hFail : ∀ {ptF qnF : Nat} {pool0F pool1F qmF : List (BitVec 32)}
        {qsF qlF qhF : List (BitVec 64)} {mF : Mem 64},
      ptF ≤ s.pcap.toNat → qnF ≤ s.qcap.toNat →
      pool0F.length = pool0.length → pool1F.length = pool1.length →
      qmF.length = qm.length → qsF.length = qs.length →
      qlF.length = ql.length → qhF.length = qh.length →
      (arCtxMem cx (Sp0LoopState s ptF qnF) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0F pool1F ⋆
        array (t := i32) s.qm qmF ⋆ array64 s.qs qsF ⋆ array64 s.ql qlF ⋆
        array64 s.qh qhF ⋆ restQ ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) mF →
      Q (false, ⟨⟩) mF)
    (hExitQ : ∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s'.pc.toNat < 2 → s'.tc.toNat < 2 → s'.tn.toNat ≤ s.tcap.toNat →
      s'.ptop.toNat ≤ s.pcap.toNat → s'.qn.toNat ≤ s.qcap.toNat →
      s' = { s with
        tc := s'.tc, tn := s'.tn, ptop := s'.ptop, qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      (ok = true →
        (∀ i < s'.tn.toNat,
          MonoSliceOk (if s'.pc.toNat = 0 then pool0' else pool1')
              ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat s'.ptop.toNat ∧
          ((if s'.pc.toNat = 0 then pool0' else pool1').getD
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ i < s'.tn.toNat,
          MonoSorted (if s'.pc.toNat = 0 then pool0' else pool1')
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat) ∧
        SigOk (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then ts0' else ts1')
          s'.tn.toNat ∧
        monoTotalWords (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') s'.tn.toNat ≤ s'.ptop.toNat ∧
        ∀ ρ : Nat → Bool,
          polyEval s.modW (cSig g ρ bindArr) (if s'.pc.toNat = 0 then pool0' else pool1')
              (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then tl0' else tl1')
              (if s'.tc.toNat = 0 then th0' else th1') s'.tn.toNat =
            sp0TargetEval s.spec s.modW g ρ) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.bind bindArr ⋆
        array (t := i32) s'.in_net inNetArr ⋆ array (t := i32) s'.out_ref outRefArr ⋆
        array (t := i32) s'.partner partnerArr ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) m' →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (sp0FindTrue 20 (ar_build_sp0_body Val Cont (cx, ()))) m := by
  let R0 := array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R
  let wV : BitVec 32 := s.n_out >>> 1#32
  have hev_out : g.outs.length % 2 = 0 := hBind.out_even hspec2
  have hs_modW : w = g.outs.length / 2 := by
    rw [hw]; simp [ArCtxState.modW, hspec2, hBind.out_eq]
  have hw_eq : wV.toNat = w := by
    change (s.n_out >>> (1 : Nat)).toNat = w
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hBind.out_eq, hs_modW]
  have hw_2 : 2 * w = g.outs.length := by omega
  have hw_bd : 1 ≤ w ∧ w ≤ 128 := by rw [hw]; exact hBind.out_bounds
  have hnout_eq : s.n_out.toNat = g.outs.length := hBind.out_eq
  dsimp only [ar_build_sp0_body]
  simp only [sp0FindTrue, sp0StepStraight]
  c0_hsteps_nogrp
  refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i32]) (mL : Mem 64) =>
      let ⟨jV, ⟨⟩⟩ := args
      jV.toNat ≤ w ∧ rem = w - jV.toNat ∧
      ∃ (pt qn : Nat) (pool0C pool1C qmC : List (BitVec 32)) (qsC qlC qhC : List (BitVec 64)),
        pt ≤ s.pcap.toNat ∧ qn ≤ s.qcap.toNat ∧
        pool0C.length = pool0.length ∧ pool1C.length = pool1.length ∧
        qmC.length = qm.length ∧ qsC.length = qs.length ∧
        qlC.length = ql.length ∧ qhC.length = qh.length ∧
        (∀ idx < qn,
          MonoSliceOk (if s.pc.toNat = 0 then pool0C else pool1C) (qmC.getD idx 0#32).toNat pt ∧
          ((if s.pc.toNat = 0 then pool0C else pool1C).getD
            (qmC.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ idx < qn,
          MonoSorted (if s.pc.toNat = 0 then pool0C else pool1C) (qmC.getD idx 0#32).toNat) ∧
        SigOk (if s.pc.toNat = 0 then pool0C else pool1C) qmC qsC qn ∧
        monoTotalWords (if s.pc.toNat = 0 then pool0C else pool1C) qmC qn ≤ pt ∧
        (∀ ρ : Nat → Bool,
          polyEval w (cSig g ρ bindArr) (if s.pc.toNat = 0 then pool0C else pool1C)
              qmC qlC qhC qn =
            BitVec.ofNat w (outSlice g ρ 0 jV.toNat) -
              BitVec.ofNat w (outSlice g ρ w jV.toNat)) ∧
        (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
          array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
          array (t := i32) s.partner partnerArr ⋆
          tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
          array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
          array64 s.qh qhC ⋆ restQ ⋆ R0) mL) ?_ ?_
  · intro J1 rem ⟨jV, ⟨⟩⟩ mL hrec1
      ⟨hj_le, _, pt, qn, pool0C, pool1C, qmC, qsC, qlC, qhC,
        hpt, hqn, hp0C, hp1C, hqmC, hqsC, hqlC, hqhC, hSl, hSorted, hSig, hW, hEv, hmL⟩
    c0_hsteps_nogrp
    · have hj_lt : jV.toNat < w := by rw [hs_modW, ← hBind.out_eq]; simpa [Sp0LoopState] using hc
      have hj_out : jV.toNat < s.n_out.toNat := by omega
      have hj_arr : jV.toNat < outRefArr.length := by have := hBind.out_len; omega
      have hj_ol : jV.toNat < olit.length := by omega
      let Rcp := array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
        array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
        array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
        array64 s.qh qhC ⋆ restQ ⋆ R0
      apply wp_call_of_spec
      refine hCpow2 _ _ _ _
        ⟨Sp0LoopState s pt qn, Rcp, hMasks, sep_cast hmL (by dsimp only [Rcp]; ac_rfl),
          fun l0 h0 hlh0 => ?_⟩
      have hlh0' : coeff128 w l0 h0 = BitVec.ofNat w (2 ^ jV.toNat) := by
        change coeff128 s.modW l0 h0 =
          if jV.toNat < 128 then BitVec.ofNat s.modW (2 ^ jV.toNat) else 0#(s.modW) at hlh0
        simp only [show jV.toNat < 128 by omega, ite_true] at hlh0
        rw [hw]; exact hlh0
      apply wp_call_of_spec
      refine hCneg _ _ _ _
        ⟨Sp0LoopState s pt qn, Rcp, hMasks, sep_cast hmL (by dsimp only [Rcp]; ac_rfl),
          fun nl nh hnlnh => ?_⟩
      have hnlnh' : coeff128 w nl nh = -BitVec.ofNat w (2 ^ jV.toNat) := by
        change coeff128 s.modW nl nh = -coeff128 s.modW l0 h0 at hnlnh
        rw [hw, hnlnh, ← hw, hlh0']
      c0_hsteps_nogrp
      have hmL_out : (array (t := i32) s.out_ref outRefArr ⋆
          (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
            array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.partner partnerArr ⋆
            tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
            array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
            array64 s.qh qhC ⋆ restQ ⋆ R0)) mL :=
        sep_cast hmL (by ac_rfl)
      refine wp_load_arr32_idx (off := 0) (i := jV) (hm := hmL_out) ?_ ?_ ?_
      · dsimp only [Sp0LoopState]; simp
      · simpa using hj_arr
      c0_hsteps_nogrp
      let rfA := outRefArr[0 + jV.toNat]'(by simpa using hj_arr)
      have hrfA_eq : rfA = outRefArr.getD jV.toNat 0#32 := by
        dsimp only [rfA]
        rw [← getD_eq_getElem outRefArr 0#32 (by simpa using hj_arr), Nat.zero_add]
      refine wp_join_group (fun (_ : Tup Val []) mA =>
          ∃ (ptA qnA : Nat) (pool0A pool1A qmA : List (BitVec 32)) (qsA qlA qhA : List (BitVec 64)),
            ptA ≤ s.pcap.toNat ∧ qnA ≤ s.qcap.toNat ∧
            pool0A.length = pool0.length ∧ pool1A.length = pool1.length ∧
            qmA.length = qm.length ∧ qsA.length = qs.length ∧
            qlA.length = ql.length ∧ qhA.length = qh.length ∧
            (∀ idx < qnA,
              MonoSliceOk (if s.pc.toNat = 0 then pool0A else pool1A)
                  (qmA.getD idx 0#32).toNat ptA ∧
              ((if s.pc.toNat = 0 then pool0A else pool1A).getD
                (qmA.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
            (∀ idx < qnA,
              MonoSorted (if s.pc.toNat = 0 then pool0A else pool1A) (qmA.getD idx 0#32).toNat) ∧
            SigOk (if s.pc.toNat = 0 then pool0A else pool1A) qmA qsA qnA ∧
            monoTotalWords (if s.pc.toNat = 0 then pool0A else pool1A) qmA qnA ≤ ptA ∧
            (∀ ρ : Nat → Bool,
              polyEval w (cSig g ρ bindArr) (if s.pc.toNat = 0 then pool0A else pool1A)
                  qmA qlA qhA qnA =
                BitVec.ofNat w (outSlice g ρ 0 (jV.toNat + 1)) -
                  BitVec.ofNat w (outSlice g ρ w jV.toNat)) ∧
            (arCtxMem cx (Sp0LoopState s ptA qnA) ⋆ array (t := i32) s.bind bindArr ⋆
              array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
              array (t := i32) s.partner partnerArr ⋆
              tMem (Sp0LoopState s ptA qnA) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
              array (t := i32) s.qm qmA ⋆ array64 s.qs qsA ⋆ array64 s.ql qlA ⋆
              array64 s.qh qhA ⋆ restQ ⋆ R0) mA) ?_ ?_
      · rintro JA ⟨⟩ mA ⟨ptA, qnA, pool0A, pool1A, qmA, qsA, qlA, qhA,
          hptA, hqnA, hp0A, hp1A, hqmA, hqsA, hqlA, hqhA, hSlA, hSortedA, hSigA, hWA, hEvA, hmA⟩
        change wp Γ Q X (sp0MiterBExpr cx J1 wV jV l0 h0 nl nh) mA
        exact sp0_miter_B_wp Γ hAddQ hw hspec2 hw_eq hw_2 hj_lt hpc htc hptA hqnA hqcap32 hpcap32
          hnnets hnn2 holit_len holit_eq hruleN_len hp0A hp1A hp0_len hp1_len hqmA hqsA hqlA hqhA
          hqm_len hqs_len hql_len hqh_len hMasks hBind hPart hlh0' hnlnh'
          hSlA hSortedA hSigA hWA hEvA hmA hFail
          (fun j' ptB qnB pool0B pool1B qmB qsB qlB qhB mB hj'
            hptB hqnB hp0B hp1B hqmB hqsB hqlB hqhB hSlB hSortedB hSigB hWB hEvB hmB =>
            hrec1 (w - j'.toNat) (j', ⟨⟩) mB (by omega)
              ⟨by omega, rfl, ptB, qnB, pool0B, pool1B, qmB, qsB, qlB, qhB,
                hptB, hqnB, hp0B, hp1B, hqmB, hqsB, hqlB, hqhB, hSlB, hSortedB, hSigB, hWB,
                fun ρ => by rw [hj']; exact hEvB ρ, hmB⟩)
      · intro JA hJA
        refine wp_unroll_group fun J_thenA hJ_thenA => ?_
        have hToThenA : outRefArr.getD jV.toNat 0#32 = cNone32 ∨ g.outs.getD jV.toNat 0 ≤ 1 →
            J_thenA () mL := by
          intro hconstA
          refine hJ_thenA () mL ?_
          refine wp_unroll_group fun _ hEndA => ?_
          c0_hsteps_nogrp
          have hmL_ol : (array (t := i32) s.olit olit ⋆
              (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
                array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
                array (t := i32) s.partner partnerArr ⋆
                tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
                array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
                array64 s.qh qhC ⋆ restQ ⋆
                (array (t := i32) s.rule_n ruleN ⋆ R))) mL := by
            dsimp only [R0] at hmL
            exact sep_cast hmL (by ac_rfl)
          refine wp_load_arr32_idx (off := 0) (i := jV) (hm := hmL_ol) ?_ ?_ ?_
          · dsimp only [Sp0LoopState]; simp
          · simpa using hj_ol
          c0_hsteps_nogrp
          · have hlit1 : g.litVal (fun _ => false) (g.outs.getD jV.toNat 0) = true := by
              rw [hBind.miterOut_bit (fun _ => false) hj_out hconstA]
              have hol := holit_eq jV.toNat (by omega)
              have helem : olit[0 + jV.toNat]'(by simpa using hj_ol) = olit.getD jV.toNat 0#32 := by
                rw [← getD_eq_getElem olit 0#32 (by simpa using hj_ol), Nat.zero_add]
              have hc1 : (olit.getD jV.toNat 0#32).toNat = 1 := by
                rw [← helem]; exact congrArg BitVec.toNat hc
              rw [← hol, hc1]; decide
            refine sp0_call_addQ_wp Γ hAddQ 0 0 0 rfl rfl rfl rfl hpt hqn hpc htc hqcap32 hpcap32
              hnnets hnn2 hp0C hp1C hp0_len hp1_len hqmC hqsC hqlC hqhC
              hqm_len hqs_len hql_len hqh_len hMasks hPart hSl hSorted hSig
              (fun h => by cases h) hW hmL hFail
              (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
                hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
                c0_hsteps
                refine hJA () m1 ⟨pt1, qn1, pool0_1, pool1_1, qm1, qs1, ql1, qh1,
                  hpt1, hqn1, hp0_1, hp1_1, hqm1, hqs1, hql1, hqh1, hSl1, hSorted1, hSig1,
                  hW1, ?_, hm1⟩
                intro ρ; refine miter_add_A (hEv ρ) ?_
                have hEv1' := hw ▸ hEv1 ρ
                rw [hEv1', ← hlh0']
                have hlitρ : g.litVal ρ (g.outs.getD jV.toNat 0) = true := by
                  rw [hBind.miterOut_bit ρ hj_out hconstA]
                  rw [← hBind.miterOut_bit (fun _ => false) hj_out hconstA]; exact hlit1
                rw [hlitρ]; simp [addQSyms, monoValL, bv])
          · refine hJA () mL ⟨pt, qn, pool0C, pool1C, qmC, qsC, qlC, qhC,
              hpt, hqn, hp0C, hp1C, hqmC, hqsC, hqlC, hqhC, hSl, hSorted, hSig, hW, ?_, hmL⟩
            intro ρ; refine miter_add_A (hEv ρ) ?_
            have hlit0 : g.litVal ρ (g.outs.getD jV.toNat 0) = false := by
              rw [hBind.miterOut_bit ρ hj_out hconstA]
              have hol := holit_eq jV.toNat (by omega)
              have helem : olit[0 + jV.toNat]'(by simpa using hj_ol) = olit.getD jV.toNat 0#32 := by
                rw [← getD_eq_getElem olit 0#32 (by simpa using hj_ol), Nat.zero_add]
              have hne1 : (olit.getD jV.toNat 0#32).toNat ≠ 1 := by
                intro h1; apply hc; rw [helem]; apply BitVec.eq_of_toNat_eq; simpa using h1
              have h01 : g.outs.getD jV.toNat 0 ≤ 1 := by
                rcases hconstA with hnone | hle
                · rcases hBind.out_ok jV.toNat hj_out with ⟨_, _, ha⟩ | hok
                  · exact ha
                  · have hlt := hok.1; rw [hnone] at hlt
                    have hcc : (cNone32 >>> 1).toNat = 0x7FFFFFFF := by decide
                    omega
                · exact hle
              have h0 : g.outs.getD jV.toNat 0 = 0 := by omega
              rw [h0]; decide
            rw [hlit0]; simp [bv, BitVec.add_zero]
        c0_hsplit
        · exact hToThenA (Or.inl (hrfA_eq ▸ hc))
        · have hrfA_ne : outRefArr.getD jV.toNat 0#32 ≠ cNone32 := hrfA_eq ▸ hc
          have hrfA_lt := ((hBind.out_ok jV.toNat hj_out).resolve_left
            (fun h => hrfA_ne h.2.1)).1
          refine wp_unroll_group fun J_elseA hJ_elseA => ?_
          have hToElseA : J_elseA () mL := by
            refine hJ_elseA () mL ?_
            refine wp_unroll_group fun _ hEndA => ?_
            c0_hsteps_nogrp
            · have hodd : (rfA &&& 1#32) ≠ 0#32 := hc
              have hshA : (rfA >>> 1#32).toNat = rfA.toNat / 2 := by
                change (rfA >>> (1 : Nat)).toNat = rfA.toNat / 2
                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
              refine sp0_call_addQ_wp Γ hAddQ 0 0 0 rfl rfl rfl rfl hpt hqn hpc htc hqcap32 hpcap32
                hnnets hnn2 hp0C hp1C hp0_len hp1_len hqmC hqsC hqlC hqhC
                hqm_len hqs_len hql_len hqh_len hMasks hPart hSl hSorted hSig
                (fun h => by cases h) hW hmL hFail
                (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
                  hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
                  c0_hsteps_nogrp
                  refine sp0_call_addQ_wp Γ hAddQ 1 (2 * (rfA >>> (1 : Nat)).toNat) 0 rfl
                    (by change (2#32 * (rfA >>> 1#32)).toNat = 2 * (rfA >>> (1 : Nat)).toNat
                        rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
                          hshA, Nat.mod_eq_of_lt (by omega)]; rfl)
                    rfl rfl hpt1 hqn1 hpc htc hqcap32 hpcap32
                    hnnets hnn2 hp0_1 hp1_1 hp0_len hp1_len hqm1 hqs1 hql1 hqh1
                    hqm_len hqs_len hql_len hqh_len hMasks hPart hSl1 hSorted1 hSig1
                    (fun h => by cases h) hW1 hm1 hFail
                    (fun pt2 qn2 pool0_2 pool1_2 qm2 qs2 ql2 qh2 m2
                      hpt2 hqn2 hp0_2 hp1_2 hqm2 hqs2 hql2 hqh2 hSl2 hSorted2 hSig2
                      hW2 hEv2 hm2 => by
                      c0_hsteps
                      refine hJA () m2 ⟨pt2, qn2, pool0_2, pool1_2, qm2, qs2, ql2, qh2,
                        hpt2, hqn2, hp0_2, hp1_2, hqm2, hqs2, hql2, hqh2, hSl2, hSorted2, hSig2,
                        hW2, ?_, hm2⟩
                      intro ρ; refine miter_add_A (hEv ρ) ?_
                      have hEv2' := hw ▸ hEv2 ρ
                      have hEv1' := hw ▸ hEv1 ρ
                      dsimp only at hEv2' hEv1'
                      rw [hEv2', hEv1', BitVec.add_assoc]
                      congr 1
                      rw [sp0_out_step_odd_gen (BitVec.ofNat w (2 ^ jV.toNat))
                        (cSig g ρ bindArr) rfA hodd hlh0' hnlnh', hrfA_eq,
                        hBind.out_sig ρ hj_out hrfA_ne]))
            · have heven : (rfA &&& 1#32) = 0#32 := hc
              have hshA : (rfA >>> 1#32).toNat = rfA.toNat / 2 := by
                change (rfA >>> (1 : Nat)).toNat = rfA.toNat / 2
                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
              refine sp0_call_addQ_wp Γ hAddQ 1 (2 * (rfA >>> (1 : Nat)).toNat) 0 rfl
                (by change (2#32 * (rfA >>> 1#32)).toNat = 2 * (rfA >>> (1 : Nat)).toNat
                    rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
                      hshA, Nat.mod_eq_of_lt (by omega)]; rfl)
                rfl rfl hpt hqn hpc htc hqcap32 hpcap32
                hnnets hnn2 hp0C hp1C hp0_len hp1_len hqmC hqsC hqlC hqhC
                hqm_len hqs_len hql_len hqh_len hMasks hPart hSl hSorted hSig
                (fun h => by cases h) hW hmL hFail
                (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
                  hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
                  c0_hsteps
                  refine hJA () m1 ⟨pt1, qn1, pool0_1, pool1_1, qm1, qs1, ql1, qh1,
                    hpt1, hqn1, hp0_1, hp1_1, hqm1, hqs1, hql1, hqh1, hSl1, hSorted1, hSig1,
                    hW1, ?_, hm1⟩
                  intro ρ; refine miter_add_A (hEv ρ) ?_
                  have hEv1' := hw ▸ hEv1 ρ
                  dsimp only at hEv1'
                  rw [hEv1', sp0_out_step_even_gen (BitVec.ofNat w (2 ^ jV.toNat))
                    (cSig g ρ bindArr) rfA heven hlh0', hrfA_eq,
                    hBind.out_sig ρ hj_out hrfA_ne])
          c0_hsteps_nogrp
          have hmL_ol : (array (t := i32) s.olit olit ⋆
              (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
                array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
                array (t := i32) s.partner partnerArr ⋆
                tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
                array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
                array64 s.qh qhC ⋆ restQ ⋆
                (array (t := i32) s.rule_n ruleN ⋆ R))) mL := by
            dsimp only [R0] at hmL
            exact sep_cast hmL (by ac_rfl)
          refine wp_load_arr32_idx (off := 0) (i := jV) (hm := hmL_ol) ?_ ?_ ?_
          · dsimp only [Sp0LoopState]; simp
          · simpa using hj_ol
          c0_hsplit
          · have hncA : (olit[0 + jV.toNat]'(by simpa using hj_ol)).toNat ≤ 1 := by
              simpa using hc
            have hmL_rn : (array (t := i32) s.rule_n ruleN ⋆
                (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
                  array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
                  array (t := i32) s.partner partnerArr ⋆
                  tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
                  array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
                  array64 s.qh qhC ⋆ restQ ⋆
                  (array (t := i32) s.olit olit ⋆ R))) mL := by
              dsimp only [R0] at hmL
              exact sep_cast hmL (by ac_rfl)
            c0_hsteps_nogrp
            refine wp_load_arr32_idx (off := 0) (i := rfA >>> 1#32) (hm := hmL_rn)
              (by dsimp only [Sp0LoopState, rfA]; simp)
              (by rw [← hrfA_eq] at hrfA_lt; simpa using Nat.lt_of_lt_of_le hrfA_lt hruleN_len)
              ?_
            c0_hsplit
            · refine hToThenA (Or.inr ?_)
              have hol := holit_eq jV.toNat (by omega)
              have helem : olit[0 + jV.toNat]'(by simpa using hj_ol) = olit.getD jV.toNat 0#32 := by
                rw [← getD_eq_getElem olit 0#32 (by simpa using hj_ol), Nat.zero_add]
              have hle1 : (olit.getD jV.toNat 0#32).toNat ≤ 1 := by
                rw [← helem]; exact hncA
              omega
            · exact hToElseA
          · exact hToElseA
    · exact hFail hpt hqn hp0C hp1C hqmC hqsC hqlC hqhC hmL
    · have hj_done : jV.toNat = w := by
        have hc0 : ¬ jV.toNat < (Sp0LoopState s 0 0).n_out.toNat / 2 ^ OfNat.ofNat 1 := by
          assumption
        have hc' : ¬ jV.toNat < s.n_out.toNat / 2 := by simpa [Sp0LoopState] using hc0
        rw [hs_modW, ← hBind.out_eq] at hj_le
        omega
      rw [hj_done] at hEv
      have hqn_tcap : qn ≤ s.tcap.toNat := by
        have hqn32 : (BitVec.ofNat 32 qn).toNat = qn := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qn < 2 ^ 32)]
        have hc' : ¬ s.tcap.toNat < (BitVec.ofNat 32 qn).toNat := by
          simpa [Sp0LoopState] using hc
        omega
      refine sp0_merge_exit_ok Γ hMerge hpc htc htcap30 hqcap32 hpt hqn hqn_tcap
          htm0_len htm1_len hts0_len htl0_len hth0_len hts1_len htl1_len hth1_len
          hp0C hp1C hqmC hqsC hqlC hqhC hp0_len hp1_len hqm_len hqs_len hql_len hqh_len
          hix_len hix2_len hix_eq (sp0TargetEval s.spec s.modW g) hMasks hBind hSl hSorted hSig hW
          (fun ρ => by
            rw [← hw, hEv ρ]
            simp only [sp0TargetEval, hspec2, ↓reduceIte])
          hqBack hmL hExitQ
  · intro J1 hJ1
    c0_hsteps
    refine hJ1 w (0#32, ⟨⟩) m
      ⟨Nat.zero_le _, rfl, 0, 0, pool0, pool1, qm, qs, ql, qh,
        Nat.zero_le _, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ h0 => absurd h0 (Nat.not_lt_zero _),
        fun _ h0 => absurd h0 (Nat.not_lt_zero _), sigOk_empty _ _ _, by simp [monoTotalWords],
        fun _ => by rw [polyEval_zero]; simp [outSlice, outSliceL], hm⟩

/-! ## 3. `SPEC_UMUL` / `SPEC_SMUL` Loop (`sp0_mul_loop_wp`) -/

private abbrev Sp0MulOk (s : ArCtxState) (pool0 pool1 qm : List (BitVec 32))
    (qs ql qh : List (BitVec 64)) (pt qn : Nat)
    (pool0C pool1C qmC : List (BitVec 32)) (qsC qlC qhC : List (BitVec 64)) : Prop :=
  pt ≤ s.pcap.toNat ∧ qn ≤ s.qcap.toNat ∧
  pool0C.length = pool0.length ∧ pool1C.length = pool1.length ∧
  qmC.length = qm.length ∧ qsC.length = qs.length ∧
  qlC.length = ql.length ∧ qhC.length = qh.length ∧
  (∀ idx < qn,
    MonoSliceOk (if s.pc.toNat = 0 then pool0C else pool1C) (qmC.getD idx 0#32).toNat pt ∧
    ((if s.pc.toNat = 0 then pool0C else pool1C).getD
      (qmC.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
  (∀ idx < qn,
    MonoSorted (if s.pc.toNat = 0 then pool0C else pool1C) (qmC.getD idx 0#32).toNat) ∧
  SigOk (if s.pc.toNat = 0 then pool0C else pool1C) qmC qsC qn ∧
  monoTotalWords (if s.pc.toNat = 0 then pool0C else pool1C) qmC qn ≤ pt

private abbrev Sp0MulHeap (cx : Val i64) (s : ArCtxState)
    (bindArr inNetArr outRefArr partnerArr tm0 tm1 : List (BitVec 32))
    (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pt qn : Nat)
    (pool0C pool1C qmC : List (BitVec 32)) (qsC qlC qhC : List (BitVec 64))
    (restQ R0 : Mem 64 → Prop) : Mem 64 → Prop :=
  arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
    array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
    array (t := i32) s.partner partnerArr ⋆
    tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
    array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
    array64 s.qh qhC ⋆ restQ ⋆ R0

private theorem sp0_mul_loop_wp (Γ : T.Env)
    (hAddQ : ∀ xs m Q X, arAddQSpec xs m Q X →
      Γ "ar_add_q" [i64, i32, i32, i32, i64, i64] [.bool] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCpow2 : ∀ xs m Q X, arCpow2Spec xs m Q X →
      Γ "ar_cpow2" [i64, i32] [i64, i64] xs m Q X)
    {cx : Val i64} {Q : Post [.bool]} {X : XPost} {w : Nat}
    {s : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr partnerArr olit ruleN : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {restQ R : Mem 64 → Prop} {m : Mem 64}
    (hw : w = s.modW) (hns : s.spec ≠ 2#32)
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnnets : s.n_nets.toNat ≤ 0x3FFFFFFF) (hnn2 : 2 * s.n_nets.toNat < 2 ^ 32)
    (htm0_len : s.tcap.toNat ≤ tm0.length) (htm1_len : s.tcap.toNat ≤ tm1.length)
    (hts0_len : s.tcap.toNat ≤ ts0.length) (htl0_len : s.tcap.toNat ≤ tl0.length)
    (hth0_len : s.tcap.toNat ≤ th0.length) (hts1_len : s.tcap.toNat ≤ ts1.length)
    (htl1_len : s.tcap.toNat ≤ tl1.length) (hth1_len : s.tcap.toNat ≤ th1.length)
    (hp0_len : s.pcap.toNat ≤ pool0.length) (hp1_len : s.pcap.toNat ≤ pool1.length)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hqs_len : s.qcap.toNat ≤ qs.length)
    (hql_len : s.qcap.toNat ≤ ql.length) (hqh_len : s.qcap.toNat ≤ qh.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hix2_len : s.qcap.toNat ≤ ix2.length)
    (hix_eq : ix.length = ix2.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi) (hBind : BindRep s g bindArr inNetArr outRefArr)
    (hPart : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr)
    (hqBack : ∀ s' qm' qs' ql' qh',
      s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
      s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx →
      s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip → qm'.length = qm.length →
      qMem s' qm' qs' ql' qh' ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) s'.qm qm' ⋆ array64 s'.qs qs' ⋆ array64 s'.ql ql' ⋆
          array64 s'.qh qh' ⋆ restQ))
    (hm : (arCtxMem cx (Sp0LoopState s 0 0) ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s 0 0) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
      array64 s.qh qh ⋆ restQ ⋆
      (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) m)
    (hFail : ∀ {ptF qnF : Nat} {pool0F pool1F qmF : List (BitVec 32)}
        {qsF qlF qhF : List (BitVec 64)} {mF : Mem 64},
      ptF ≤ s.pcap.toNat → qnF ≤ s.qcap.toNat →
      pool0F.length = pool0.length → pool1F.length = pool1.length →
      qmF.length = qm.length → qsF.length = qs.length →
      qlF.length = ql.length → qhF.length = qh.length →
      (arCtxMem cx (Sp0LoopState s ptF qnF) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0F pool1F ⋆
        array (t := i32) s.qm qmF ⋆ array64 s.qs qsF ⋆ array64 s.ql qlF ⋆
        array64 s.qh qhF ⋆ restQ ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) mF →
      Q (false, ⟨⟩) mF)
    (hExitQ : ∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s'.pc.toNat < 2 → s'.tc.toNat < 2 → s'.tn.toNat ≤ s.tcap.toNat →
      s'.ptop.toNat ≤ s.pcap.toNat → s'.qn.toNat ≤ s.qcap.toNat →
      s' = { s with
        tc := s'.tc, tn := s'.tn, ptop := s'.ptop, qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      (ok = true →
        (∀ i < s'.tn.toNat,
          MonoSliceOk (if s'.pc.toNat = 0 then pool0' else pool1')
              ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat s'.ptop.toNat ∧
          ((if s'.pc.toNat = 0 then pool0' else pool1').getD
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ i < s'.tn.toNat,
          MonoSorted (if s'.pc.toNat = 0 then pool0' else pool1')
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat) ∧
        SigOk (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then ts0' else ts1')
          s'.tn.toNat ∧
        monoTotalWords (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') s'.tn.toNat ≤ s'.ptop.toNat ∧
        ∀ ρ : Nat → Bool,
          polyEval s.modW (cSig g ρ bindArr) (if s'.pc.toNat = 0 then pool0' else pool1')
              (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then tl0' else tl1')
              (if s'.tc.toNat = 0 then th0' else th1') s'.tn.toNat =
            sp0TargetEval s.spec s.modW g ρ) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.bind bindArr ⋆
        array (t := i32) s'.in_net inNetArr ⋆ array (t := i32) s'.out_ref outRefArr ⋆
        array (t := i32) s'.partner partnerArr ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆
        (array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R)) m' →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (sp0FindElse 20 (ar_build_sp0_body Val Cont (cx, ()))) m := by
  let R0 := array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R
  have hs_modW : w = s.n_out.toNat := by
    rw [hw]; simp [ArCtxState.modW, hns]
  have hout_bd : 1 ≤ w ∧ w ≤ 128 := by rw [hw]; exact hBind.out_bounds
  have hnin_lt : s.n_in.toNat = g.I := hBind.in_eq
  have heven_I : g.I % 2 = 0 ∧ 2 ≤ g.I := hBind.i_even hns
  have hn_eq : (s.n_in >>> 1#32).toNat = g.I / 2 := by
    change (s.n_in >>> (1 : Nat)).toNat = g.I / 2
    rw [BitVec.toNat_ushiftRight, hnin_lt, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  let nV : BitVec 32 := s.n_in >>> 1#32
  let n : Nat := g.I / 2
  have hn_ge1 : 1 ≤ n := by omega
  have h2n_eq : 2 * n = g.I := by omega
  dsimp only [ar_build_sp0_body]
  simp only [sp0FindElse, sp0StepStraight]
  c0_hsteps_nogrp
  refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i32]) (mL : Mem 64) =>
      let ⟨jV, ⟨⟩⟩ := args
      jV.toNat ≤ w ∧ rem = w - jV.toNat ∧
      ∃ (pt qn : Nat) (pool0C pool1C qmC : List (BitVec 32)) (qsC qlC qhC : List (BitVec 64)),
        Sp0MulOk s pool0 pool1 qm qs ql qh pt qn pool0C pool1C qmC qsC qlC qhC ∧
        (∀ ρ : Nat → Bool,
          polyEval w (cSig g ρ bindArr)
              (if s.pc.toNat = 0 then pool0C else pool1C) qmC qlC qhC qn =
            outSum w (cSig g ρ bindArr)
              ((outRefArr.take jV.toNat).map BitVec.toNat) 0) ∧
        Sp0MulHeap cx s bindArr inNetArr outRefArr partnerArr tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
          pt qn pool0C pool1C qmC qsC qlC qhC restQ R0 mL) ?_ ?_
  · intro J1 rem ⟨jV, ⟨⟩⟩ mL hrec1
      ⟨hj_le, _, pt, qn, pool0C, pool1C, qmC, qsC, qlC, qhC,
        ⟨hpt, hqn, hp0C, hp1C, hqmC, hqsC, hqlC, hqhC, hSl, hSorted, hSig, hW⟩, hEv, hmL⟩
    dsimp only [Sp0MulHeap] at hmL
    c0_hsteps_nogrp
    · have hj_lt : jV.toNat < w := by rw [hs_modW]; exact hc
      have hj_arr : jV.toNat < outRefArr.length := by have := hBind.out_len; omega
      have hmL_out : (array (t := i32) s.out_ref outRefArr ⋆
          (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
            array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.partner partnerArr ⋆
            tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
            array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
            array64 s.qh qhC ⋆ restQ ⋆ R0)) mL :=
        sep_cast hmL (by ac_rfl)
      refine wp_load_arr32_idx (off := 0) (i := jV) (hm := hmL_out) ?_ ?_ ?_
      · dsimp only [Sp0LoopState]; simp
      · simpa using hj_arr
      c0_hsteps_nogrp
      let rf := outRefArr[0 + jV.toNat]'(by simpa using hj_arr)
      have hrf_eq : rf = outRefArr.getD jV.toNat 0#32 := by
        dsimp only [rf]
        rw [← getD_eq_getElem outRefArr 0#32 (by simpa using hj_arr), Nat.zero_add]
      let Rcp1 := array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
        array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
        array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
        array64 s.qh qhC ⋆ restQ ⋆ R0
      apply wp_call_of_spec
      refine hCpow2 _ _ _ _
        ⟨Sp0LoopState s pt qn, Rcp1, hMasks, sep_cast hmL (by dsimp only [Rcp1]; ac_rfl),
          fun l0 h0 hlh0 => ?_⟩
      have hlh0' : coeff128 w l0 h0 = BitVec.ofNat w (2 ^ jV.toNat) := by
        change coeff128 s.modW l0 h0 =
          if jV.toNat < 128 then BitVec.ofNat s.modW (2 ^ jV.toNat) else 0#(s.modW) at hlh0
        simp only [show jV.toNat < 128 by omega, ite_true] at hlh0
        rw [hw]; exact hlh0
      refine wp_join_group (fun (_ : Tup Val [i64, i64]) mJ1 =>
          ∃ (pt' qn' : Nat) (pool0' pool1' qm' : List (BitVec 32))
            (qs' ql' qh' : List (BitVec 64)),
            Sp0MulOk s pool0 pool1 qm qs ql qh pt' qn' pool0' pool1' qm' qs' ql' qh' ∧
            (∀ ρ : Nat → Bool,
              polyEval w (cSig g ρ bindArr)
                  (if s.pc.toNat = 0 then pool0' else pool1') qm' ql' qh' qn' =
                outSum w (cSig g ρ bindArr)
                  ((outRefArr.take (jV.toNat + 1)).map BitVec.toNat) 0) ∧
            Sp0MulHeap cx s bindArr inNetArr outRefArr partnerArr tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
              pt' qn' pool0' pool1' qm' qs' ql' qh' restQ R0 mJ1) ?_ ?_
      · rintro JJ1 ⟨_, _, ⟨⟩⟩ mJ1 ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
          ⟨hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW'⟩, hEv', hmJ1⟩
        c0_hsteps
        have hjp1 : (jV + 1#32).toNat = jV.toNat + 1 := by c0_bv_omega
        refine hrec1 (w - (jV + 1#32).toNat) (jV + 1#32, ⟨⟩) mJ1 (by omega)
          ⟨by omega, rfl, pt', qn', pool0', pool1', qm', qs', ql', qh',
            ⟨hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW'⟩,
            ?_, hmJ1⟩
        intro ρ; rw [hjp1]; exact hEv' ρ
      · intro JJ1 hJJ1
        c0_hsteps_nogrp
        · have hodd : (rf &&& 1#32) ≠ 0#32 := hc
          refine sp0_call_addQ_wp Γ hAddQ 0 0 0 rfl rfl rfl rfl hpt hqn hpc htc hqcap32 hpcap32
            hnnets hnn2 hp0C hp1C hp0_len hp1_len hqmC hqsC hqlC hqhC
            hqm_len hqs_len hql_len hqh_len hMasks hPart hSl hSorted hSig
            (fun h => by cases h) hW hmL hFail
            (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
              hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
              c0_hsteps_nogrp
              let Rcn1 := array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
                array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
                tMem (Sp0LoopState s pt1 qn1) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
                array (t := i32) s.qm qm1 ⋆ array64 s.qs qs1 ⋆ array64 s.ql ql1 ⋆
                array64 s.qh qh1 ⋆ restQ ⋆ R0
              apply wp_call_of_spec
              refine hCneg _ _ _ _
                ⟨Sp0LoopState s pt1 qn1, Rcn1, hMasks,
                  sep_cast hm1 (by dsimp only [Rcn1]; ac_rfl), fun l1 h1 hlh1 => ?_⟩
              have hlh1' : coeff128 w l1 h1 = -coeff128 w l0 h0 := by
                change coeff128 s.modW l1 h1 = -coeff128 s.modW l0 h0 at hlh1
                rw [hw]; exact hlh1
              refine sp0_call_addQ_wp Γ hAddQ 1 (2 * (rf >>> 1#32).toNat) 0 rfl
                (by dsimp only [Arg.val, rf]
                    rw [BitVec.toNat_mul, show (2 : BitVec 32).toNat = 2 from rfl,
                      Nat.mod_eq_of_lt (by
                        have hlt32 := (outRefArr[0 + jV.toNat]'(by simpa using hj_arr)).isLt
                        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                        omega)]; rfl)
                rfl rfl hpt1 hqn1 hpc htc hqcap32 hpcap32
                hnnets hnn2 hp0_1 hp1_1 hp0_len hp1_len hqm1 hqs1 hql1 hqh1
                hqm_len hqs_len hql_len hqh_len hMasks hPart hSl1 hSorted1 hSig1
                (fun h => by cases h) hW1 hm1 hFail
                (fun pt2 qn2 pool0_2 pool1_2 qm2 qs2 ql2 qh2 m2
                  hpt2 hqn2 hp0_2 hp1_2 hqm2 hqs2 hql2 hqh2 hSl2 hSorted2 hSig2
                  hW2 hEv2 hm2 => by
                  c0_hsteps
                  refine hJJ1 (l1, h1, ⟨⟩) m2 ⟨pt2, qn2, pool0_2, pool1_2, qm2, qs2, ql2, qh2,
                    ⟨hpt2, hqn2, hp0_2, hp1_2, hqm2, hqs2, hql2, hqh2, hSl2, hSorted2, hSig2,
                      hW2⟩, ?_, hm2⟩
                  intro ρ
                  have hEv2' := hw ▸ hEv2 ρ
                  have hEv1' := hw ▸ hEv1 ρ
                  rw [hEv2', hEv1', hEv ρ, BitVec.add_assoc,
                    sp0_outSum_take_succ w (cSig g ρ bindArr) outRefArr hj_arr, ← hrf_eq]
                  congr 1
                  exact sp0_out_step_odd w (cSig g ρ bindArr) rf hodd hlh0' hlh1'))
        · have heven : (rf &&& 1#32) = 0#32 := hc
          refine sp0_call_addQ_wp Γ hAddQ 1 (2 * (rf >>> 1#32).toNat) 0 rfl
            (by dsimp only [Arg.val, rf]
                rw [BitVec.toNat_mul, show (2 : BitVec 32).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt (by
                    have hlt32 := (outRefArr[0 + jV.toNat]'(by simpa using hj_arr)).isLt
                    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                    omega)]; rfl)
            rfl rfl hpt hqn hpc htc hqcap32 hpcap32
            hnnets hnn2 hp0C hp1C hp0_len hp1_len hqmC hqsC hqlC hqhC
            hqm_len hqs_len hql_len hqh_len hMasks hPart hSl hSorted hSig
            (fun h => by cases h) hW hmL hFail
            (fun pt1 qn1 pool0_1 pool1_1 qm1 qs1 ql1 qh1 m1
              hpt1 hqn1 hp0_1 hp1_1 hqm1 hqs1 hql1 hqh1 hSl1 hSorted1 hSig1 hW1 hEv1 hm1 => by
              c0_hsteps
              refine hJJ1 (l0, h0, ⟨⟩) m1 ⟨pt1, qn1, pool0_1, pool1_1, qm1, qs1, ql1, qh1,
                ⟨hpt1, hqn1, hp0_1, hp1_1, hqm1, hqs1, hql1, hqh1, hSl1, hSorted1, hSig1,
                  hW1⟩, ?_, hm1⟩
              intro ρ
              have hEv1' := hw ▸ hEv1 ρ
              rw [hEv1', hEv ρ,
                sp0_outSum_take_succ w (cSig g ρ bindArr) outRefArr hj_arr, ← hrf_eq]
              congr 1
              exact sp0_out_step_even w (cSig g ρ bindArr) rf heven hlh0')
    · have hj_done : jV.toNat = w := by
        have hc' : ¬ jV.toNat < s.n_out.toNat := by simpa [Sp0LoopState] using hc
        omega
      rw [hj_done] at hEv
      c0_hsteps_nogrp
      refine wp_loop_group (fun (remi : Nat) (args : Tup Val [i32]) (mO : Mem 64) =>
          let ⟨iV, ⟨⟩⟩ := args
          iV.toNat ≤ n ∧ remi = n - iV.toNat ∧
          ∃ (ptO qnO : Nat) (pool0O pool1O qmO : List (BitVec 32))
            (qsO qlO qhO : List (BitVec 64)),
            Sp0MulOk s pool0 pool1 qm qs ql qh ptO qnO pool0O pool1O qmO qsO qlO qhO ∧
            (∀ ρ : Nat → Bool,
              polyEval w (cSig g ρ bindArr)
                  (if s.pc.toNat = 0 then pool0O else pool1O) qmO qlO qhO qnO =
                outSum w (cSig g ρ bindArr)
                    ((outRefArr.take w).map BitVec.toNat) 0 -
                  inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                    ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
                  inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                    (((inNetArr.drop n).take n).map BitVec.toNat) 0) ∧
            Sp0MulHeap cx s bindArr inNetArr outRefArr partnerArr tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
              ptO qnO pool0O pool1O qmO qsO qlO qhO restQ R0 mO) ?_ ?_
      · intro Ji remi ⟨iV, ⟨⟩⟩ mO hreci
          ⟨hi_le, _, ptO, qnO, pool0O, pool1O, qmO, qsO, qlO, qhO,
            ⟨hptO, hqnO, hp0O, hp1O, hqmO, hqsO, hqlO, hqhO, hSlO, hSortedO, hSigO, hWO⟩,
            hEvO, hmO⟩
        dsimp only [Sp0MulHeap] at hmO
        c0_hsteps_nogrp
        · have hi_lt : iV.toNat < n := by
            have hc' : iV.toNat < s.n_in.toNat / 2 := by simpa [Sp0LoopState] using hc
            dsimp only [n]; rw [← hBind.in_eq]; exact hc'
          have hi_in : iV.toNat < inNetArr.length := by have := hBind.in_len; omega
          refine wp_loop_group (fun (remk : Nat) (args : Tup Val [i32]) (mK : Mem 64) =>
              let ⟨kV, ⟨⟩⟩ := args
              kV.toNat ≤ n ∧ remk = n - kV.toNat ∧
              ∃ (pt qn : Nat) (pool0C pool1C qmC : List (BitVec 32))
                (qsC qlC qhC : List (BitVec 64)),
                Sp0MulOk s pool0 pool1 qm qs ql qh pt qn pool0C pool1C qmC qsC qlC qhC ∧
                (∀ ρ : Nat → Bool,
                  polyEval w (cSig g ρ bindArr)
                      (if s.pc.toNat = 0 then pool0C else pool1C) qmC qlC qhC qn =
                    outSum w (cSig g ρ bindArr)
                        ((outRefArr.take w).map BitVec.toNat) 0 -
                      inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                        ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
                      inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                        (((inNetArr.drop n).take n).map BitVec.toNat) 0 -
                      inTerm w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                        (inNetArr.getD iV.toNat 0#32).toNat iV.toNat *
                      inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                        (((inNetArr.drop n).take kV.toNat).map BitVec.toNat) 0) ∧
                Sp0MulHeap cx s bindArr inNetArr outRefArr partnerArr tm0 tm1 ts0 tl0 th0
                  ts1 tl1 th1 pt qn pool0C pool1C qmC qsC qlC qhC restQ R0 mK) ?_ ?_
          · intro Jk remk ⟨kV, ⟨⟩⟩ mK hreck
              ⟨hk_le, _, ptK, qnK, pool0K, pool1K, qmK, qsK, qlK, qhK,
                ⟨hptK, hqnK, hp0K, hp1K, hqmK, hqsK, hqlK, hqhK, hSlK, hSortedK, hSigK, hWK⟩,
                hEvK, hmK⟩
            dsimp only [Sp0MulHeap] at hmK
            c0_hsteps_nogrp
            · have hk_lt : kV.toNat < n := by
                have hc' : kV.toNat < s.n_in.toNat / 2 := by simpa [Sp0LoopState] using hc
                dsimp only [n]; rw [← hBind.in_eq]; exact hc'
              have hnk_in : n + kV.toNat < inNetArr.length := by have := hBind.in_len; omega
              have hkp1 : (kV + 1#32).toNat = kV.toNat + 1 := by
                have : kV.toNat + 1 < 2 ^ 32 := by have := s.n_in.isLt; omega
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt this]
              refine wp_join_group (fun (_ : Tup Val []) mJ =>
                  ∃ (pt' qn' : Nat) (pool0' pool1' qm' : List (BitVec 32))
                    (qs' ql' qh' : List (BitVec 64)),
                    Sp0MulOk s pool0 pool1 qm qs ql qh pt' qn' pool0' pool1' qm' qs' ql' qh' ∧
                    (∀ ρ : Nat → Bool,
                      polyEval w (cSig g ρ bindArr)
                          (if s.pc.toNat = 0 then pool0' else pool1') qm' ql' qh' qn' =
                        outSum w (cSig g ρ bindArr)
                            ((outRefArr.take w).map BitVec.toNat) 0 -
                          inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                            ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
                          inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                            (((inNetArr.drop n).take n).map BitVec.toNat) 0 -
                          inTerm w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                            (inNetArr.getD iV.toNat 0#32).toNat iV.toNat *
                          inSum w (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                            (((inNetArr.drop n).take (kV.toNat + 1)).map BitVec.toNat) 0) ∧
                    Sp0MulHeap cx s bindArr inNetArr outRefArr partnerArr tm0 tm1 ts0 tl0 th0
                      ts1 tl1 th1 pt' qn' pool0' pool1' qm' qs' ql' qh' restQ R0 mJ) ?_ ?_
              · rintro JJ ⟨⟩ mJ ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
                  ⟨hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW'⟩,
                  hEv', hmJ⟩
                c0_hsteps
                refine hreck (n - (kV + 1#32).toNat) (kV + 1#32, ⟨⟩) mJ (by omega)
                  ⟨by omega, rfl, pt', qn', pool0', pool1', qm', qs', ql', qh',
                    ⟨hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW'⟩,
                    ?_, hmJ⟩
                intro ρ; rw [hkp1]; exact hEv' ρ
              · intro JJ hJJ
                change wp Γ Q X (sp0KBodyExpr cx nV iV kV JJ) mK
                exact sp0_k_body_wp Γ hAddQ hCneg hCpow2 rfl hn_eq hn_ge1 hi_lt hk_lt hpc htc
                  hptK hqnK hqcap32 hpcap32 hnnets hnn2 hp0K hp1K hp0_len hp1_len
                  hqmK hqsK hqlK hqhK hqm_len hqs_len hql_len hqh_len hns hMasks hBind hPart
                  h2n_eq hi_in hnk_in hSlK hSortedK hSigK hWK (fun ρ => hw ▸ hEvK ρ) hmK hFail
                  (fun ys m' ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
                    hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh',
                    hSl', hSorted', hSig', hW', hEv', hm'⟩ =>
                    hJJ ys m' ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
                      ⟨hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh',
                        hSl', hSorted', hSig', hW'⟩, fun ρ => hw ▸ hEv' ρ, hm'⟩)
            · have hk_done : kV.toNat = n := by
                have hc' : ¬ kV.toNat < s.n_in.toNat / 2 := by simpa [Sp0LoopState] using hc
                have hn_eq' : s.n_in.toNat / 2 = n := by dsimp only [n]; rw [hBind.in_eq]
                omega
              rw [hk_done] at hEvK
              c0_hsteps
              have hip1 : (iV + 1#32).toNat = iV.toNat + 1 := by
                have : iV.toNat + 1 < 2 ^ 32 := by have := s.n_in.isLt; omega
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt this]
              refine hreci (n - (iV + 1#32).toNat) (iV + 1#32, ⟨⟩) mK (by omega)
                ⟨by omega, rfl, ptK, qnK, pool0K, pool1K, qmK, qsK, qlK, qhK,
                  ⟨hptK, hqnK, hp0K, hp1K, hqmK, hqsK, hqlK, hqhK, hSlK, hSortedK, hSigK, hWK⟩,
                  ?_, hmK⟩
              intro ρ; rw [hip1]
              exact sp0_loop2_row_done (cSig g ρ bindArr) (decide (s.spec = 1#32)) n inNetArr
                hi_in _ _ _ (hEvK ρ)
          · intro Jk hJk
            c0_hsteps
            refine hJk n (0#32, ⟨⟩) mO
              ⟨Nat.zero_le _, rfl, ptO, qnO, pool0O, pool1O, qmO, qsO, qlO, qhO,
                ⟨hptO, hqnO, hp0O, hp1O, hqmO, hqsO, hqlO, hqhO, hSlO, hSortedO, hSigO, hWO⟩,
                ?_, hmO⟩
            intro ρ
            rw [BitVec.toNat_zero, List.take_zero, List.map_nil, inSum,
              show (0 : BitVec w) = 0#w from rfl, BitVec.mul_zero, BitVec.sub_zero]
            exact hEvO ρ
        · exact hFail hptO hqnO hp0O hp1O hqmO hqsO hqlO hqhO hmO
        · have hi_done : iV.toNat = n := by
            have hc0 : ¬ iV.toNat < (Sp0LoopState s 0 0).n_in.toNat / 2 ^ OfNat.ofNat 1 := by
              assumption
            have hc' : ¬ iV.toNat < s.n_in.toNat / 2 := by simpa [Sp0LoopState] using hc0
            have hn_eq' : s.n_in.toNat / 2 = n := by dsimp only [n]; rw [hBind.in_eq]
            omega
          rw [hi_done] at hEvO
          have hqn_tcap : qnO ≤ s.tcap.toNat := by
            have hqn32 : (BitVec.ofNat 32 qnO).toNat = qnO := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qnO < 2 ^ 32)]
            have hc' : ¬ s.tcap.toNat < (BitVec.ofNat 32 qnO).toNat := by
              simpa [Sp0LoopState] using hc
            omega
          exact sp0_merge_exit_ok Γ hMerge hpc htc htcap30 hqcap32 hptO hqnO hqn_tcap
            htm0_len htm1_len hts0_len htl0_len hth0_len hts1_len htl1_len hth1_len
            hp0O hp1O hqmO hqsO hqlO hqhO hp0_len hp1_len hqm_len hqs_len hql_len hqh_len
            hix_len hix2_len hix_eq (sp0TargetEval s.spec s.modW g) hMasks hBind
            hSlO hSortedO hSigO hWO
            (fun ρ => (hw ▸ hEvO ρ).trans (sp0_done_eval_eq hBind hns ρ))
            hqBack hmO hExitQ
      · intro Ji hJi
        c0_hsteps
        refine hJi n (0#32, ⟨⟩) mL
          ⟨Nat.zero_le _, rfl, pt, qn, pool0C, pool1C, qmC, qsC, qlC, qhC,
            ⟨hpt, hqn, hp0C, hp1C, hqmC, hqsC, hqlC, hqhC, hSl, hSorted, hSig, hW⟩, ?_, hmL⟩
        intro ρ
        rw [BitVec.toNat_zero, List.take_zero, List.map_nil, inSum,
          show (0 : BitVec w) = 0#w from rfl, BitVec.zero_mul, BitVec.sub_zero]
        exact hEv ρ
  · intro J1 hJ1
    c0_hsteps
    refine hJ1 w (0#32, ⟨⟩) m
      ⟨Nat.zero_le _, rfl, 0, 0, pool0, pool1, qm, qs, ql, qh,
        ⟨Nat.zero_le _, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ h0 => absurd h0 (Nat.not_lt_zero _),
          fun _ h0 => absurd h0 (Nat.not_lt_zero _), sigOk_empty _ _ _, by simp [monoTotalWords]⟩,
        fun _ => by rw [polyEval_zero]; simp [outSum], hm⟩

/-! ## 4. `ar_build_sp0_wp` -/

public theorem ar_build_sp0_wp (Γ : T.Env)
    (hAddQ : ∀ xs m Q X, arAddQSpec xs m Q X →
      Γ "ar_add_q" [i64, i32, i32, i32, i64, i64] [.bool] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCpow2 : ∀ xs m Q X, arCpow2Spec xs m Q X →
      Γ "ar_cpow2" [i64, i32] [i64, i64] xs m Q X) :
    ∀ xs m Q X, arBuildSp0Spec xs m Q X → Func.wp Γ ar_build_sp0_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X
    ⟨s, g, bindArr, inNetArr, outRefArr, partnerArr, olit, ruleN,
      tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1, qm, qs, ql, qh,
      ix, ix2, bx, vqOff, vq, vqSkip, R,
      hpc, htc, htcap30, hqcap16, hqcap32, hpcap32, hnnets, hnn2, hspec,
      holit_len, holit_eq, hruleN_len,
      htm0_len, htm1_len, hts0_len, htl0_len, hth0_len, hts1_len, htl1_len, hth1_len,
      hp0_len, hp1_len, hqm_len, hqs_len, hql_len, hqh_len, hix_len, hix2_len, hix_eq,
      hMasks, hBind, hPart, hm, hQ⟩
  let R0 : Mem 64 → Prop := array (t := i32) s.olit olit ⋆ array (t := i32) s.rule_n ruleN ⋆ R
  obtain ⟨restQ, hqEq, hqBack⟩ := qMem_focus_q s qm qs ql qh ix ix2 bx vqOff vq vqSkip
  have hFail : ∀ {ptF qnF : Nat} {pool0F pool1F qmF : List (BitVec 32)}
      {qsF qlF qhF : List (BitVec 64)} {mF : Mem 64},
      ptF ≤ s.pcap.toNat → qnF ≤ s.qcap.toNat →
      pool0F.length = pool0.length → pool1F.length = pool1.length →
      qmF.length = qm.length → qsF.length = qs.length →
      qlF.length = ql.length → qhF.length = qh.length →
      (arCtxMem cx (Sp0LoopState s ptF qnF) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0F pool1F ⋆
        array (t := i32) s.qm qmF ⋆ array64 s.qs qsF ⋆ array64 s.ql qlF ⋆
        array64 s.qh qhF ⋆ restQ ⋆ R0) mF →
      Q (false, ⟨⟩) mF := by
    intro ptF qnF pool0F pool1F qmF qsF qlF qhF mF hptF hqnF hp0F hp1F hqmF hqsF hqlF hqhF hmF
    have hptF_nat : (Sp0LoopState s ptF qnF).ptop.toNat = ptF := by
      dsimp only [Sp0LoopState]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ptF < 2 ^ 64)]
    have hqnF_nat : (Sp0LoopState s ptF qnF).qn.toNat = qnF := by
      dsimp only [Sp0LoopState]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qnF < 2 ^ 32)]
    refine hQ false (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
      pool0F pool1F qmF qsF qlF qhF ix ix2 mF hpc htc (by simp [Sp0LoopState])
      (by rw [hptF_nat]; exact hptF) (by rw [hqnF_nat]; exact hqnF) rfl
      rfl rfl rfl rfl rfl rfl rfl rfl hp0F hp1F hqmF hqsF hqlF hqhF
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (fun h => by cases h) ?_
    have hm_pk := buildSp0_pack_mem (cx := cx) (s := s) (s' := Sp0LoopState s ptF qnF)
      (bindArr := bindArr) (inNetArr := inNetArr) (outRefArr := outRefArr)
      (partnerArr := partnerArr) (tm0 := tm0) (tm1 := tm1) (ts0 := ts0) (tl0 := tl0)
      (th0 := th0) (ts1 := ts1) (tl1 := tl1) (th1 := th1) (pool0 := pool0F) (pool1 := pool1F)
      (qm := qmF) (qs := qsF) (ql := qlF) (qh := qhF) (ix := ix) (ix2 := ix2) (bx := bx)
      (vqOff := vqOff) (vq := vq) (vqSkip := vqSkip) (R := R0) rfl (by
        rw [hqBack (Sp0LoopState s ptF qnF) qmF qsF qlF qhF rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl hqmF]
        exact sep_cast hmF (by ac_rfl))
    have hol_pt : (Sp0LoopState s ptF qnF).olit = s.olit := rfl
    have hrn_pt : (Sp0LoopState s ptF qnF).rule_n = s.rule_n := rfl
    rw [hol_pt, hrn_pt]
    exact sep_cast hm_pk (by dsimp only [R0]; ac_rfl)
  have hExitQ : ∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
      (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
      (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
      (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s'.pc.toNat < 2 → s'.tc.toNat < 2 → s'.tn.toNat ≤ s.tcap.toNat →
      s'.ptop.toNat ≤ s.pcap.toNat → s'.qn.toNat ≤ s.qcap.toNat →
      s' = { s with
        tc := s'.tc, tn := s'.tn, ptop := s'.ptop, qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      (ok = true →
        (∀ i < s'.tn.toNat,
          MonoSliceOk (if s'.pc.toNat = 0 then pool0' else pool1')
              ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat s'.ptop.toNat ∧
          ((if s'.pc.toNat = 0 then pool0' else pool1').getD
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ i < s'.tn.toNat,
          MonoSorted (if s'.pc.toNat = 0 then pool0' else pool1')
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat) ∧
        SigOk (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then ts0' else ts1')
          s'.tn.toNat ∧
        monoTotalWords (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') s'.tn.toNat ≤ s'.ptop.toNat ∧
        ∀ ρ : Nat → Bool,
          polyEval s.modW (cSig g ρ bindArr) (if s'.pc.toNat = 0 then pool0' else pool1')
              (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then tl0' else tl1')
              (if s'.tc.toNat = 0 then th0' else th1') s'.tn.toNat =
            sp0TargetEval s.spec s.modW g ρ) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.bind bindArr ⋆
        array (t := i32) s'.in_net inNetArr ⋆ array (t := i32) s'.out_ref outRefArr ⋆
        array (t := i32) s'.partner partnerArr ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R0) m' →
      Q (ok, ⟨⟩) m' := by
    intro ok s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh' ix' ix2' m'
      hpc' htc' htn' hpt' hqn' hs' htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1'
      hp0' hp1' hqm' hqs' hql' hqh' hix' hok' hm'
    refine hQ ok s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' qm' qs' ql' qh'
      ix' ix2' m' hpc' htc' htn' hpt' hqn' hs' htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1'
      hp0' hp1' hqm' hqs' hql' hqh' hix' hok' ?_
    have hol' : s'.olit = s.olit := by rw [hs']
    have hrn' : s'.rule_n = s.rule_n := by rw [hs']
    rw [hol', hrn']
    exact sep_cast hm' (by dsimp only [R0]; ac_rfl)
  rw [hqEq] at hm
  c0_hstraight
  c0_hsplit
  · have hspec2 : s.spec = 2#32 := by simpa using hc
    change wp Γ Q X (sp0FindTrue 20 (ar_build_sp0_body Val Cont (cx, ()))) _
    exact sp0_miter_loop_wp Γ hAddQ hMerge hCneg hCpow2 rfl hspec2 hpc htc htcap30 hqcap32 hpcap32
      hnnets hnn2 holit_len holit_eq hruleN_len htm0_len htm1_len hts0_len htl0_len hth0_len
      hts1_len htl1_len hth1_len hp0_len hp1_len hqm_len hqs_len hql_len hqh_len
      hix_len hix2_len hix_eq hMasks hBind hPart hqBack
      (sep_cast ‹_› (by dsimp only [Sp0LoopState, R0]; ac_rfl))
      hFail hExitQ
  · have hns : s.spec ≠ 2#32 := by simpa using hc
    change wp Γ Q X (sp0FindElse 20 (ar_build_sp0_body Val Cont (cx, ()))) _
    exact sp0_mul_loop_wp Γ hAddQ hMerge hCneg hCpow2 rfl hns hpc htc htcap30 hqcap32 hpcap32
      hnnets hnn2 htm0_len htm1_len hts0_len htl0_len hth0_len hts1_len htl1_len hth1_len
      hp0_len hp1_len hqm_len hqs_len hql_len hqh_len hix_len hix2_len hix_eq
      hMasks hBind hPart hqBack (sep_cast ‹_› (by dsimp only [Sp0LoopState, R0]; ac_rfl))
      hFail hExitQ

end LeanQbe.T.Examples.Arisca.Proof

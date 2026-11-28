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

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for `ar_build_sp0` (`ar_build_sp0_wp`).
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

/-! ## 1. Pure Helpers for `ar_build_sp0` -/
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
    ⟨s, g, bindArr, inNetArr, outRefArr, partnerArr, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1,
      pool0, pool1, qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, R,
      hpc, htc, htcap30, hqcap16, hqcap32, hpcap32, hnnets, hnn2, hspec,
      htm0_len, htm1_len, hts0_len, htl0_len, hth0_len, hts1_len, htl1_len, hth1_len,
      hp0_len, hp1_len, hqm_len, hqs_len, hql_len, hqh_len, hix_len, hix2_len, hix_eq,
      hMasks, hBind, hPart, hm, hQ⟩
  obtain ⟨restQ, hqEq, hqBack⟩ := qMem_focus_q s qm qs ql qh ix ix2 bx vqOff vq vqSkip
  have hnin_lt : s.n_in.toNat = g.I := hBind.in_eq
  have heven_I : g.I % 2 = 0 ∧ 2 ≤ g.I := hBind.i_even
  have hout_bd : 1 ≤ s.n_out.toNat ∧ s.n_out.toNat ≤ 128 := hBind.out_bounds
  have hn_eq : (s.n_in >>> 1#32).toNat = g.I / 2 := by
    change (s.n_in >>> (1 : Nat)).toNat = g.I / 2
    rw [BitVec.toNat_ushiftRight, hnin_lt, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  let nV : BitVec 32 := s.n_in >>> 1#32
  let n : Nat := g.I / 2
  have hn_ge1 : 1 ≤ n := by omega
  have h2n_eq : 2 * n = g.I := by omega
  have hn_div : s.n_in.toNat / 2 ^ OfNat.ofNat 1 = n := by
    dsimp only [n]; rw [← hnin_lt]
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
        array64 s.qh qhF ⋆ restQ ⋆ R) mF →
      Q (false, ⟨⟩) mF := by
    intro ptF qnF pool0F pool1F qmF qsF qlF qhF mF hptF hqnF hp0F hp1F hqmF hqsF hqlF hqhF hmF
    have hptF_nat : (Sp0LoopState s ptF qnF).ptop.toNat = ptF := by
      dsimp only [Sp0LoopState]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ptF < 2 ^ 64)]
    have hqnF_nat : (Sp0LoopState s ptF qnF).qn.toNat = qnF := by
      dsimp only [Sp0LoopState]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qnF < 2 ^ 32)]
    refine hQ false (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
      pool0F pool1F qmF qsF qlF qhF ix ix2 mF hpc htc (by simp [Sp0LoopState])
      (by rw [hptF_nat]; exact hptF) (by rw [hqnF_nat]; exact hqnF) rfl
      rfl rfl rfl rfl rfl rfl rfl rfl hp0F hp1F hqmF hqsF hqlF hqhF
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      (fun h => by cases h) ?_
    exact buildSp0_pack_mem (cx := cx) (s := s) (s' := Sp0LoopState s ptF qnF)
      (bindArr := bindArr) (inNetArr := inNetArr) (outRefArr := outRefArr)
      (partnerArr := partnerArr) (tm0 := tm0) (tm1 := tm1) (ts0 := ts0) (tl0 := tl0)
      (th0 := th0) (ts1 := ts1) (tl1 := tl1) (th1 := th1) (pool0 := pool0F) (pool1 := pool1F)
      (qm := qmF) (qs := qsF) (ql := qlF) (qh := qhF) (ix := ix) (ix2 := ix2) (bx := bx)
      (vqOff := vqOff) (vq := vq) (vqSkip := vqSkip) (R := R) rfl (by
        rw [hqBack (Sp0LoopState s ptF qnF) qmF qsF qlF qhF rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl hqmF]
        exact sep_cast hmF (by ac_rfl))
  c0_hsteps_nogrp
  refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i32]) (mL : Mem 64) =>
      let ⟨jV, ⟨⟩⟩ := args
      jV.toNat ≤ s.n_out.toNat ∧ rem = s.n_out.toNat - jV.toNat ∧
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
          polyEval s.n_out.toNat (cSig g ρ bindArr)
              (if s.pc.toNat = 0 then pool0C else pool1C) qmC qlC qhC qn =
            outSum s.n_out.toNat (cSig g ρ bindArr)
              ((outRefArr.take jV.toNat).map BitVec.toNat) 0) ∧
        (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
          array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
          array (t := i32) s.partner partnerArr ⋆
          tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
          array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
          array64 s.qh qhC ⋆ restQ ⋆ R) mL) ?_ ?_
  ·
      intro J1 rem ⟨jV, ⟨⟩⟩ mL hrec1
        ⟨hj_le, _, pt, qn, pool0C, pool1C, qmC, qsC, qlC, qhC,
          hpt, hqn, hp0C, hp1C, hqmC, hqsC, hqlC, hqhC, hSl, hSorted, hSig, hW, hEv, hmL⟩
      have hj_out_len : jV.toNat < outRefArr.length ∨ jV.toNat = s.n_out.toNat := by
        have := hBind.out_len; omega
      c0_hsteps_nogrp
      · have hj_lt : jV.toNat < s.n_out.toNat := hc
        have hj_arr : jV.toNat < outRefArr.length := by have := hBind.out_len; omega
        have hmL_out : (array (t := i32) s.out_ref outRefArr ⋆
            (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
              array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.partner partnerArr ⋆
              tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
              array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
              array64 s.qh qhC ⋆ restQ ⋆ R)) mL :=
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
          array64 s.qh qhC ⋆ restQ ⋆ R
        apply wp_call_of_spec
        refine hCpow2 _ _ _ _
          ⟨Sp0LoopState s pt qn, Rcp1, by simpa [Sp0LoopState] using hMasks,
            sep_cast hmL (by dsimp only [Rcp1]; ac_rfl), fun l0 h0 hlh0 => ?_⟩
        have hlh0' : coeff128 s.n_out.toNat l0 h0 = BitVec.ofNat s.n_out.toNat (2 ^ jV.toNat) := by
          simpa [Sp0LoopState, show jV.toNat < 128 by omega] using hlh0
        refine wp_join_group (fun (_ : Tup Val [i64, i64]) mJ1 =>
            ∃ (pt' qn' : Nat) (pool0' pool1' qm' : List (BitVec 32))
              (qs' ql' qh' : List (BitVec 64)),
              pt' ≤ s.pcap.toNat ∧ qn' ≤ s.qcap.toNat ∧
              pool0'.length = pool0.length ∧ pool1'.length = pool1.length ∧
              qm'.length = qm.length ∧ qs'.length = qs.length ∧
              ql'.length = ql.length ∧ qh'.length = qh.length ∧
              (∀ idx < qn',
                MonoSliceOk (if s.pc.toNat = 0 then pool0' else pool1')
                    (qm'.getD idx 0#32).toNat pt' ∧
                ((if s.pc.toNat = 0 then pool0' else pool1').getD
                  (qm'.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
              (∀ idx < qn',
                MonoSorted (if s.pc.toNat = 0 then pool0' else pool1')
                  (qm'.getD idx 0#32).toNat) ∧
              SigOk (if s.pc.toNat = 0 then pool0' else pool1') qm' qs' qn' ∧
              monoTotalWords (if s.pc.toNat = 0 then pool0' else pool1') qm' qn' ≤ pt' ∧
              (∀ ρ : Nat → Bool,
                polyEval s.n_out.toNat (cSig g ρ bindArr)
                    (if s.pc.toNat = 0 then pool0' else pool1') qm' ql' qh' qn' =
                  outSum s.n_out.toNat (cSig g ρ bindArr)
                    ((outRefArr.take (jV.toNat + 1)).map BitVec.toNat) 0) ∧
              (arCtxMem cx (Sp0LoopState s pt' qn') ⋆ array (t := i32) s.bind bindArr ⋆
                array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
                array (t := i32) s.partner partnerArr ⋆
                tMem (Sp0LoopState s pt' qn') tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆
                array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆ array64 s.ql ql' ⋆
                array64 s.qh qh' ⋆ restQ ⋆ R) mJ1) ?_ ?_
        · rintro JJ1 ⟨_, _, ⟨⟩⟩ mJ1 ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
            hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW', hEv', hmJ1⟩
          c0_hsteps
          have hjp1 : (jV + 1#32).toNat = jV.toNat + 1 := by c0_bv_omega
          refine hrec1 (s.n_out.toNat - (jV + 1#32).toNat) (jV + 1#32, ⟨⟩) mJ1 (by omega)
            ⟨by omega, rfl, pt', qn', pool0', pool1', qm', qs', ql', qh',
              hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW',
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
                  array64 s.qh qh1 ⋆ restQ ⋆ R
                apply wp_call_of_spec
                refine hCneg _ _ _ _
                  ⟨Sp0LoopState s pt1 qn1, Rcn1, by simpa [Sp0LoopState] using hMasks,
                    sep_cast hm1 (by dsimp only [Rcn1]; ac_rfl), fun l1 h1 hlh1 => ?_⟩
                have hlh1' : coeff128 s.n_out.toNat l1 h1 = -coeff128 s.n_out.toNat l0 h0 := hlh1
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
                      hpt2, hqn2, hp0_2, hp1_2, hqm2, hqs2, hql2, hqh2, hSl2, hSorted2, hSig2,
                      hW2, ?_, hm2⟩
                    intro ρ
                    rw [hEv2 ρ, hEv1 ρ, hEv ρ, BitVec.add_assoc,
                      sp0_outSum_take_succ s.n_out.toNat (cSig g ρ bindArr) outRefArr hj_arr,
                      ← hrf_eq]
                    congr 1
                    exact sp0_out_step_odd s.n_out.toNat (cSig g ρ bindArr) rf hodd hlh0' hlh1'))
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
                  hpt1, hqn1, hp0_1, hp1_1, hqm1, hqs1, hql1, hqh1, hSl1, hSorted1, hSig1,
                  hW1, ?_, hm1⟩
                intro ρ
                rw [hEv1 ρ, hEv ρ,
                  sp0_outSum_take_succ s.n_out.toNat (cSig g ρ bindArr) outRefArr hj_arr,
                  ← hrf_eq]
                congr 1
                exact sp0_out_step_even s.n_out.toNat (cSig g ρ bindArr) rf heven hlh0')
      · have hj_done : jV.toNat = s.n_out.toNat := by
          have hc' : ¬ jV.toNat < s.n_out.toNat := by simpa [Sp0LoopState] using hc
          omega
        rw [hj_done] at hEv
        c0_hsteps_nogrp
        refine wp_loop_group (fun (remi : Nat) (args : Tup Val [i32]) (mO : Mem 64) =>
            let ⟨iV, ⟨⟩⟩ := args
            iV.toNat ≤ n ∧ remi = n - iV.toNat ∧
            ∃ (ptO qnO : Nat) (pool0O pool1O qmO : List (BitVec 32))
              (qsO qlO qhO : List (BitVec 64)),
              ptO ≤ s.pcap.toNat ∧ qnO ≤ s.qcap.toNat ∧
              pool0O.length = pool0.length ∧ pool1O.length = pool1.length ∧
              qmO.length = qm.length ∧ qsO.length = qs.length ∧
              qlO.length = ql.length ∧ qhO.length = qh.length ∧
              (∀ idx < qnO,
                MonoSliceOk (if s.pc.toNat = 0 then pool0O else pool1O)
                    (qmO.getD idx 0#32).toNat ptO ∧
                ((if s.pc.toNat = 0 then pool0O else pool1O).getD
                  (qmO.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
              (∀ idx < qnO,
                MonoSorted (if s.pc.toNat = 0 then pool0O else pool1O)
                  (qmO.getD idx 0#32).toNat) ∧
              SigOk (if s.pc.toNat = 0 then pool0O else pool1O) qmO qsO qnO ∧
              monoTotalWords (if s.pc.toNat = 0 then pool0O else pool1O) qmO qnO ≤ ptO ∧
              (∀ ρ : Nat → Bool,
                polyEval s.n_out.toNat (cSig g ρ bindArr)
                    (if s.pc.toNat = 0 then pool0O else pool1O) qmO qlO qhO qnO =
                  outSum s.n_out.toNat (cSig g ρ bindArr)
                      ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
                    inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                      ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
                    inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                      (((inNetArr.drop n).take n).map BitVec.toNat) 0) ∧
              (arCtxMem cx (Sp0LoopState s ptO qnO) ⋆ array (t := i32) s.bind bindArr ⋆
                array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
                array (t := i32) s.partner partnerArr ⋆
                tMem (Sp0LoopState s ptO qnO) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0O pool1O ⋆
                array (t := i32) s.qm qmO ⋆ array64 s.qs qsO ⋆ array64 s.ql qlO ⋆
                array64 s.qh qhO ⋆ restQ ⋆ R) mO) ?_ ?_
        · intro Ji remi ⟨iV, ⟨⟩⟩ mO hreci
            ⟨hi_le, _, ptO, qnO, pool0O, pool1O, qmO, qsO, qlO, qhO,
              hptO, hqnO, hp0O, hp1O, hqmO, hqsO, hqlO, hqhO, hSlO, hSortedO, hSigO,
              hWO, hEvO, hmO⟩
          c0_hsteps_nogrp
          · have hi_lt : iV.toNat < n := by omega
            have hi_in : iV.toNat < inNetArr.length := by have := hBind.in_len; omega
            refine wp_loop_group (fun (remk : Nat) (args : Tup Val [i32]) (mK : Mem 64) =>
                let ⟨kV, ⟨⟩⟩ := args
                kV.toNat ≤ n ∧ remk = n - kV.toNat ∧
                ∃ (pt qn : Nat) (pool0C pool1C qmC : List (BitVec 32))
                  (qsC qlC qhC : List (BitVec 64)),
                  pt ≤ s.pcap.toNat ∧ qn ≤ s.qcap.toNat ∧
                  pool0C.length = pool0.length ∧ pool1C.length = pool1.length ∧
                  qmC.length = qm.length ∧ qsC.length = qs.length ∧
                  qlC.length = ql.length ∧ qhC.length = qh.length ∧
                  (∀ idx < qn,
                    MonoSliceOk (if s.pc.toNat = 0 then pool0C else pool1C)
                        (qmC.getD idx 0#32).toNat pt ∧
                    ((if s.pc.toNat = 0 then pool0C else pool1C).getD
                      (qmC.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
                  (∀ idx < qn,
                    MonoSorted (if s.pc.toNat = 0 then pool0C else pool1C)
                      (qmC.getD idx 0#32).toNat) ∧
                  SigOk (if s.pc.toNat = 0 then pool0C else pool1C) qmC qsC qn ∧
                  monoTotalWords (if s.pc.toNat = 0 then pool0C else pool1C) qmC qn ≤ pt ∧
                  (∀ ρ : Nat → Bool,
                    polyEval s.n_out.toNat (cSig g ρ bindArr)
                        (if s.pc.toNat = 0 then pool0C else pool1C) qmC qlC qhC qn =
                      outSum s.n_out.toNat (cSig g ρ bindArr)
                          ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
                        inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                          ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
                        inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                          (((inNetArr.drop n).take n).map BitVec.toNat) 0 -
                        inTerm s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                          (inNetArr.getD iV.toNat 0#32).toNat iV.toNat *
                        inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                          (((inNetArr.drop n).take kV.toNat).map BitVec.toNat) 0) ∧
                  (arCtxMem cx (Sp0LoopState s pt qn) ⋆ array (t := i32) s.bind bindArr ⋆
                    array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
                    array (t := i32) s.partner partnerArr ⋆
                    tMem (Sp0LoopState s pt qn) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
                    array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
                    array64 s.qh qhC ⋆ restQ ⋆ R) mK) ?_ ?_
            · intro Jk remk ⟨kV, ⟨⟩⟩ mK hreck
                ⟨hk_le, _, ptK, qnK, pool0K, pool1K, qmK, qsK, qlK, qhK,
                  hptK, hqnK, hp0K, hp1K, hqmK, hqsK, hqlK, hqhK, hSlK, hSortedK, hSigK,
                  hWK, hEvK, hmK⟩
              c0_hsteps_nogrp
              · have hk_lt : kV.toNat < n := by omega
                have hnk_in : n + kV.toNat < inNetArr.length := by have := hBind.in_len; omega
                have hkp1 : (kV + 1#32).toNat = kV.toNat + 1 := by
                  have : kV.toNat + 1 < 2 ^ 32 := by have := s.n_in.isLt; omega
                  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt this]
                refine wp_join_group (fun (_ : Tup Val []) mJ =>
                    ∃ (pt' qn' : Nat) (pool0' pool1' qm' : List (BitVec 32))
                      (qs' ql' qh' : List (BitVec 64)),
                      pt' ≤ s.pcap.toNat ∧ qn' ≤ s.qcap.toNat ∧
                      pool0'.length = pool0.length ∧ pool1'.length = pool1.length ∧
                      qm'.length = qm.length ∧ qs'.length = qs.length ∧
                      ql'.length = ql.length ∧ qh'.length = qh.length ∧
                      (∀ idx < qn',
                        MonoSliceOk (if s.pc.toNat = 0 then pool0' else pool1')
                            (qm'.getD idx 0#32).toNat pt' ∧
                        ((if s.pc.toNat = 0 then pool0' else pool1').getD
                          (qm'.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
                      (∀ idx < qn',
                        MonoSorted (if s.pc.toNat = 0 then pool0' else pool1')
                          (qm'.getD idx 0#32).toNat) ∧
                      SigOk (if s.pc.toNat = 0 then pool0' else pool1') qm' qs' qn' ∧
                      monoTotalWords (if s.pc.toNat = 0 then pool0' else pool1') qm' qn' ≤ pt' ∧
                      (∀ ρ : Nat → Bool,
                        polyEval s.n_out.toNat (cSig g ρ bindArr)
                            (if s.pc.toNat = 0 then pool0' else pool1') qm' ql' qh' qn' =
                          outSum s.n_out.toNat (cSig g ρ bindArr)
                              ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
                            inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                              ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
                            inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                              (((inNetArr.drop n).take n).map BitVec.toNat) 0 -
                            inTerm s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                              (inNetArr.getD iV.toNat 0#32).toNat iV.toNat *
                            inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                              (((inNetArr.drop n).take (kV.toNat + 1)).map BitVec.toNat) 0) ∧
                      (arCtxMem cx (Sp0LoopState s pt' qn') ⋆ array (t := i32) s.bind bindArr ⋆
                        array (t := i32) s.in_net inNetArr ⋆
                        array (t := i32) s.out_ref outRefArr ⋆
                        array (t := i32) s.partner partnerArr ⋆
                        tMem (Sp0LoopState s pt' qn') tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
                          pool0' pool1' ⋆
                        array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆ array64 s.ql ql' ⋆
                        array64 s.qh qh' ⋆ restQ ⋆ R) mJ) ?_ ?_
                · rintro JJ ⟨⟩ mJ ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
                    hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig',
                    hW', hEv', hmJ⟩
                  c0_hsteps
                  refine hreck (n - (kV + 1#32).toNat) (kV + 1#32, ⟨⟩) mJ (by omega)
                    ⟨by omega, rfl, pt', qn', pool0', pool1', qm', qs', ql', qh',
                      hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig',
                      hW', ?_, hmJ⟩
                  intro ρ; rw [hkp1]; exact hEv' ρ
                · intro JJ hJJ
                  change wp Γ Q X (sp0KBodyExpr cx nV iV kV JJ) mK
                  exact sp0_k_body_wp Γ hAddQ hCneg hCpow2 rfl hn_eq hn_ge1 hi_lt hk_lt hpc htc
                    hptK hqnK hqcap32 hpcap32 hnnets hnn2 hp0K hp1K hp0_len hp1_len
                    hqmK hqsK hqlK hqhK hqm_len hqs_len hql_len hqh_len hMasks hBind hPart
                    h2n_eq hi_in hnk_in hSlK hSortedK hSigK hWK hEvK hmK hFail hJJ
              · have hk_done : kV.toNat = n := by omega
                rw [hk_done] at hEvK
                c0_hsteps
                have hip1 : (iV + 1#32).toNat = iV.toNat + 1 := by
                  have : iV.toNat + 1 < 2 ^ 32 := by have := s.n_in.isLt; omega
                  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt this]
                refine hreci (n - (iV + 1#32).toNat) (iV + 1#32, ⟨⟩) mK (by omega)
                  ⟨by omega, rfl, ptK, qnK, pool0K, pool1K, qmK, qsK, qlK, qhK,
                    hptK, hqnK, hp0K, hp1K, hqmK, hqsK, hqlK, hqhK, hSlK, hSortedK, hSigK,
                    hWK, ?_, hmK⟩
                intro ρ
                rw [hip1]
                exact sp0_loop2_row_done (cSig g ρ bindArr) (decide (s.spec = 1#32)) n inNetArr
                  hi_in _ _ _ (hEvK ρ)
            · intro Jk hJk
              c0_hsteps
              refine hJk n (0#32, ⟨⟩) mO
                ⟨Nat.zero_le _, rfl, ptO, qnO, pool0O, pool1O, qmO, qsO, qlO, qhO,
                  hptO, hqnO, hp0O, hp1O, hqmO, hqsO, hqlO, hqhO, hSlO, hSortedO, hSigO,
                  hWO, ?_, hmO⟩
              intro ρ
              rw [BitVec.toNat_zero, List.take_zero, List.map_nil, inSum,
                show (0 : BitVec s.n_out.toNat) = 0#(s.n_out.toNat) from rfl,
                BitVec.mul_zero, BitVec.sub_zero]
              exact hEvO ρ
          · exact hFail hptO hqnO hp0O hp1O hqmO hqsO hqlO hqhO hmO
          · have hi_done : iV.toNat = n := by omega
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
              hix_len hix2_len hix_eq hMasks hBind hSlO hSortedO hSigO hWO hEvO hqBack hmO hQ
        · intro Ji hJi
          c0_hsteps
          refine hJi n (0#32, ⟨⟩) mL
            ⟨Nat.zero_le _, rfl, pt, qn, pool0C, pool1C, qmC, qsC, qlC, qhC,
              hpt, hqn, hp0C, hp1C, hqmC, hqsC, hqlC, hqhC, hSl, hSorted, hSig, hW, ?_, hmL⟩
          intro ρ
          rw [BitVec.toNat_zero, List.take_zero, List.map_nil, inSum,
            show (0 : BitVec s.n_out.toNat) = 0#(s.n_out.toNat) from rfl,
            BitVec.zero_mul, BitVec.sub_zero]
          exact hEv ρ
  · intro J1 hJ1
    c0_hsteps
    refine hJ1 s.n_out.toNat (0#32, ⟨⟩) m
      ⟨Nat.zero_le _, rfl, 0, 0, pool0, pool1, qm, qs, ql, qh,
        Nat.zero_le _, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ h0 => absurd h0 (Nat.not_lt_zero _),
        fun _ h0 => absurd h0 (Nat.not_lt_zero _), sigOk_empty _ _ _, by simp [monoTotalWords],
        fun _ => by rw [polyEval_zero]; simp [outSum], ?_⟩
    have hm0 := hm
    rw [hqEq] at hm0
    exact sep_cast hm0 (by ac_rfl)

end LeanQbe.T.Examples.Arisca.Proof

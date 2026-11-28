/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Spec
public import LeanQbe.T.Examples.Arisca.Proof.Poly1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Rule Load & `ar_add_q` WPs (`Arisca.Proof.Poly2Base`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proofs for `2` functions of
`LeanQbe.T.Examples.Arisca.Src.Poly`:
- `ar_add_q_wp`
- `ar_load_rule_wp`.
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

/-! ## 1. Pure Helpers (`tMem`, `rsMem`, `monoTotalWords`, `addQSyms`, `build_sp0`) -/

private theorem arrayPad_u8_unfold (a : BitVec 64) (xs : List (BitVec 8)) :
    arrayPad i8 a xs =
      (array (t := i8) a xs ⋆
        region (a + BitVec.ofNat 64 xs.length) (align8 xs.length - xs.length)) := by
  simp only [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size]
  rw [show (8 + 7) / 8 = 1 from rfl, Nat.one_mul]

private theorem tMem_focus_pool (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
    (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
    (hpc : s.pc.toNat < 2) :
    let srcPool := if s.pc.toNat = 0 then pool0 else pool1
    ∃ rest : Mem 64 → Prop,
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆ rest)) ∧
      (∀ (s' : ArCtxState) (pool' : List (BitVec 32)),
        s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
        pool'.length = srcPool.length →
        tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
            (if s.pc.toNat = 0 then pool' else pool0)
            (if s.pc.toNat = 0 then pool1 else pool') =
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pool' ⋆ rest)) := by
  have hpc' := bv32_lt2_cases hpc
  have hu := arrayPad_u32_unfold
  rcases hpc' with h0 | h1
  · refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆ arrayPad i32 (s.pool.getD 1 0#64) pool1,
      by simp only [tMem, h0, BitVec.toNat_zero, ↓reduceIte, hu]; ac_rfl,
      fun s' pool' htm hts htl hth hpool hlen => by
        simp only [tMem, h0, BitVec.toNat_zero, ↓reduceIte, hu, htm, hts, htl, hth, hpool, hlen]
        ac_rfl⟩
  · refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length,
      by simp only [tMem, h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' pool' htm hts htl hth hpool hlen => by
        simp only [tMem, h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts, htl, hth, hpool, hlen]
        ac_rfl⟩

theorem tMem_focus_cur (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
    (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) :
    let srcPool := if s.pc.toNat = 0 then pool0 else pool1
    let srcTm := if s.tc.toNat = 0 then tm0 else tm1
    let srcTs := if s.tc.toNat = 0 then ts0 else ts1
    let srcTl := if s.tc.toNat = 0 then tl0 else tl1
    let srcTh := if s.tc.toNat = 0 then th0 else th1
    ∃ rest : Mem 64 → Prop,
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
         array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
         array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
         array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
         array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ rest)) ∧
      (∀ (s' : ArCtxState) (tm' : List (BitVec 32)) (ts' tl' th' : List (BitVec 64))
          (pool' : List (BitVec 32)),
        s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
        tm'.length = srcTm.length → ts'.length = srcTs.length →
        tl'.length = srcTl.length → th'.length = srcTh.length → pool'.length = srcPool.length →
        tMem s' (if s.tc.toNat = 0 then tm' else tm0) (if s.tc.toNat = 0 then tm1 else tm')
            (if s.tc.toNat = 0 then ts' else ts0) (if s.tc.toNat = 0 then tl' else tl0)
            (if s.tc.toNat = 0 then th' else th0) (if s.tc.toNat = 0 then ts1 else ts')
            (if s.tc.toNat = 0 then tl1 else tl') (if s.tc.toNat = 0 then th1 else th')
            (if s.pc.toNat = 0 then pool' else pool0)
            (if s.pc.toNat = 0 then pool1 else pool') =
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pool' ⋆
           array (t := i32) (s.tm.getD s.tc.toNat 0#64) tm' ⋆
           array64 (s.ts.getD s.tc.toNat 0#64) ts' ⋆
           array64 (s.tl.getD s.tc.toNat 0#64) tl' ⋆
           array64 (s.th.getD s.tc.toNat 0#64) th' ⋆ rest)) := by
  have hpc' := bv32_lt2_cases hpc; have htc' := bv32_lt2_cases htc; have hu := arrayPad_u32_unfold
  rcases hpc' with h0 | h1 <;> rcases htc' with ht0 | ht1
  · have hpc0 : s.pc.toNat = 0 := by rw [h0]; rfl
    have htc0 : s.tc.toNat = 0 := by rw [ht0]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆ u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆
      arrayPad i32 (s.pool.getD 1 0#64) pool1,
      by simp only [tMem, hpc0, htc0, ↓reduceIte, hu]; ac_rfl,
      fun s' tm' ts' tl' th' pool' htm hts htl hth hpool h1 _ _ _ h5 => by
        simp only [tMem, hpc0, htc0, ↓reduceIte, hu, htm, hts, htl, hth, hpool, h1, h5]; ac_rfl⟩
  · have hpc0 : s.pc.toNat = 0 := by rw [h0]; rfl
    have htc1 : s.tc.toNat = 1 := by rw [ht1]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆ u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆
      arrayPad i32 (s.pool.getD 1 0#64) pool1,
      by simp only [tMem, hpc0, htc1, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' tm' ts' tl' th' pool' htm hts htl hth hpool h1 _ _ _ h5 => by
        simp only [tMem, hpc0, htc1, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts,
          htl, hth, hpool, h1, h5]; ac_rfl⟩
  · have hpc1 : s.pc.toNat = 1 := by rw [h1]; rfl
    have htc0 : s.tc.toNat = 0 := by rw [ht0]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆ u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆
      arrayPad i32 (s.pool.getD 0 0#64) pool0,
      by simp only [tMem, hpc1, htc0, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' tm' ts' tl' th' pool' htm hts htl hth hpool h1 _ _ _ h5 => by
        simp only [tMem, hpc1, htc0, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts,
          htl, hth, hpool, h1, h5]; ac_rfl⟩
  · have hpc1 : s.pc.toNat = 1 := by rw [h1]; rfl
    have htc1 : s.tc.toNat = 1 := by rw [ht1]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆ u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆
      arrayPad i32 (s.pool.getD 0 0#64) pool0,
      by simp only [tMem, hpc1, htc1, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' tm' ts' tl' th' pool' htm hts htl hth hpool h1 _ _ _ h5 => by
        simp only [tMem, hpc1, htc1, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts,
          htl, hth, hpool, h1, h5]; ac_rfl⟩

theorem rsMem_unfold (s : ArCtxState) (rsM : List (BitVec 32))
    (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32)) :
    rsMem s rsM rsL rsH rsPool =
      (array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
       array (t := i32) s.rs_pool rsPool ⋆
       u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length) := by
  simp only [rsMem, arrayPad_u32_unfold]; ac_rfl

theorem polyEval_congr_prefix (nOut : Nat) (σ : Nat → Bool)
    {pool1 pool2 mOff1 mOff2 : List (BitVec 32)} {cl1 ch1 cl2 ch2 : List (BitVec 64)}
    {bd n : Nat}
    (hSl : ∀ i < n, MonoSliceOk pool1 (mOff1.getD i 0#32).toNat bd)
    (hP : ∀ idx < bd, pool2.getD idx 0#32 = pool1.getD idx 0#32)
    (hM : ∀ i < n, mOff2.getD i 0#32 = mOff1.getD i 0#32 ∧
      cl2.getD i 0#64 = cl1.getD i 0#64 ∧ ch2.getD i 0#64 = ch1.getD i 0#64) :
    polyEval nOut σ pool2 mOff2 cl2 ch2 n = polyEval nOut σ pool1 mOff1 cl1 ch1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polyEval_succ, polyEval_succ,
      ih (fun i hi => hSl i (by omega)) (fun i hi => hM i (by omega))]
    congr 1
    have hmn := hM n (Nat.lt_succ_self n)
    have hsn := hSl n (Nat.lt_succ_self n)
    have hsy : symListAt pool2 (mOff2.getD n 0#32).toNat =
        symListAt pool1 (mOff1.getD n 0#32).toNat := by
      have hlen_p : (pool2.getD (mOff1.getD n 0#32).toNat 0#32).toNat =
          (pool1.getD (mOff1.getD n 0#32).toNat 0#32).toNat := by
        rw [hP _ hsn.1]
      rw [hmn.1]
      simp only [symListAt, hlen_p]
      apply List.map_congr_left
      intro i hi
      have hil := List.mem_range.mp hi
      have hbd := hsn.2
      rw [hP _ (by omega)]
    simp only [termEval, hsy, hmn.2.1, hmn.2.2]

theorem polyEvalRange_congr_prefix (nOut : Nat) (σ : Nat → Bool)
    {pool1 pool2 mOff1 mOff2 : List (BitVec 32)} {cl1 ch1 cl2 ch2 : List (BitVec 64)}
    {bd lo len : Nat}
    (hSl : ∀ t < len, MonoSliceOk pool1 (mOff1.getD (lo + t) 0#32).toNat bd)
    (hP : ∀ idx < bd, pool2.getD idx 0#32 = pool1.getD idx 0#32)
    (hM : ∀ t < len, mOff2.getD (lo + t) 0#32 = mOff1.getD (lo + t) 0#32 ∧
      cl2.getD (lo + t) 0#64 = cl1.getD (lo + t) 0#64 ∧
      ch2.getD (lo + t) 0#64 = ch1.getD (lo + t) 0#64) :
    polyEvalRange nOut σ pool2 mOff2 cl2 ch2 lo len =
      polyEvalRange nOut σ pool1 mOff1 cl1 ch1 lo len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [polyEvalRange_succ, polyEvalRange_succ,
      ih (fun t ht => hSl t (by omega)) (fun t ht => hM t (by omega))]
    congr 1
    have hmn := hM len (Nat.lt_succ_self len)
    have hsn := hSl len (Nat.lt_succ_self len)
    have hsy : symListAt pool2 (mOff2.getD (lo + len) 0#32).toNat =
        symListAt pool1 (mOff1.getD (lo + len) 0#32).toNat := by
      have hlen_p : (pool2.getD (mOff1.getD (lo + len) 0#32).toNat 0#32).toNat =
          (pool1.getD (mOff1.getD (lo + len) 0#32).toNat 0#32).toNat := by
        rw [hP _ hsn.1]
      rw [hmn.1]
      simp only [symListAt, hlen_p]
      apply List.map_congr_left; intro i hi
      have hil := List.mem_range.mp hi; have hbd := hsn.2; rw [hP _ (by omega)]
    simp only [termEval, hsy, hmn.2.1, hmn.2.2]

theorem monoTotalWords_congr_prefix
    {pool1 pool2 mOff1 mOff2 : List (BitVec 32)} {bd n : Nat}
    (hSl : ∀ i < n, MonoSliceOk pool1 (mOff1.getD i 0#32).toNat bd)
    (hP : ∀ idx < bd, pool2.getD idx 0#32 = pool1.getD idx 0#32)
    (hM : ∀ i < n, mOff2.getD i 0#32 = mOff1.getD i 0#32) :
    monoTotalWords pool2 mOff2 n = monoTotalWords pool1 mOff1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [monoTotalWords_succ, monoTotalWords_succ,
      ih (fun i hi => hSl i (by omega)) (fun i hi => hM i (by omega)),
      hM n (Nat.lt_succ_self n), hP _ (hSl n (Nat.lt_succ_self n)).1]

/-! ## 2. WP Proof: `ar_add_q` -/

private theorem addQSyms_symListAt (pool : List (BitVec 32)) (ptop : Nat) (len s0 s1 : BitVec 32)
    (hlen : len.toNat ≤ 2) (h0 : pool.getD ptop 0#32 = len)
    (h1 : 1 ≤ len.toNat → pool.getD (ptop + 1) 0#32 = s0)
    (h2 : 2 ≤ len.toNat → pool.getD (ptop + 2) 0#32 = s1) :
    symListAt pool ptop = addQSyms len.toNat s0.toNat s1.toNat := by
  simp only [symListAt, h0, addQSyms]
  rcases Nat.lt_trichotomy len.toNat 1 with hlt | heq1 | hgt1
  · have hz : len.toNat = 0 := by omega
    simp [hz]
  · have h1v := h1 (by omega)
    rw [heq1, ite_eq_right (by decide), ite_eq_left rfl]
    simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.cons.injEq,
      and_true]
    exact congrArg BitVec.toNat h1v
  · have h2v : len.toNat = 2 := by omega
    have h1' := h1 (by omega)
    have h2' := h2 (by omega)
    rw [h2v, ite_eq_right (by decide), ite_eq_right (by decide)]
    simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, Nat.add_zero,
      List.cons.injEq, and_true]
    exact ⟨congrArg BitVec.toNat h1', congrArg BitVec.toNat h2'⟩

theorem arCtx_lengths {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s := by
  unfold arCtxMem at hm
  exact (sep_pure_l (φ := ArCtxLengthsOk s) (P := fun m => (arCtxTree cx s).eval m)
    (R := R) |>.mp hm).1

theorem ar_add_q_wp (Γ : T.Env)
    (hMvan : ∀ xs m Q X, arMvanishSpec xs m Q X → Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X)
    (hMsig : ∀ xs m Q X, arMsigSpec xs m Q X → Γ "ar_msig" [i64] [i64] xs m Q X) :
    ∀ xs m Q X, arAddQSpec xs m Q X → Func.wp Γ ar_add_q_body xs m Q X := by
  rintro ⟨cx, len, s0, s1, l, h, ⟨⟩⟩ m Q X
    ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1, qm, qs, ql, qh, partnerArr,
      Valid, R, hpc, htc, hqn_le, hqcap32, hpt_le, hpcap32, hnn_le, hnn2, hp0_len, hp1_len,
      hqm_len, hqs_len, hql_len, hqh_len, hMasks, hNonEmpty, hPart,
      hQmOk, hQmSorted, hQmSig, hs01_lt, hQwords, hm, hQ⟩
  obtain ⟨restT, htEq, htBack⟩ :=
    tMem_focus_pool s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 hpc
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  have hpool_len : s.pcap.toNat ≤ srcPool.length := by
    dsimp only [srcPool]; split <;> assumption
  have hm_u : (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.qm qm ⋆
      array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆ (restT ⋆ R)) m := by
    have hm0 := hm; rw [htEq] at hm0; exact sep_cast hm0 (by ac_rfl)
  c0_hsteps_nogrp
  refine wp_join_group (fun (_ : Tup Val []) m0 => m0 = m ∧ ¬ (l = 0#64 ∧ h = 0#64)) ?_ ?_
  · intro Js _ m0 ⟨hm0, _hne⟩
    cases hm0
    c0_hsteps_nogrp
    · refine hQ false s pool0 pool1 qm qs ql qh m hqn_le hpt_le rfl rfl rfl rfl rfl rfl rfl
        (by split <;> rfl) (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩)
        (fun h => by cases h) hm
    · refine hQ false s pool0 pool1 qm qs ql qh m hqn_le hpt_le rfl rfl rfl rfl rfl rfl rfl
        (by split <;> rfl) (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩)
        (fun h => by cases h) hm
    · refine hQ false s pool0 pool1 qm qs ql qh m hqn_le hpt_le rfl rfl rfl rfl rfl rfl rfl
        (by split <;> rfl) (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩)
        (fun h => by cases h) hm
    · have hlen_le2 : len.toNat ≤ 2 := by c0_bv_omega
      have hqn_lt : s.qn.toNat < s.qcap.toNat := by c0_bv_omega
      have hpt_cap : s.ptop.toNat + len.toNat + 1 ≤ s.pcap.toNat := by c0_bv_omega
      have hpt_len : s.ptop.toNat < srcPool.length := by omega
      have hl_s : ArCtxLengthsOk s :=
        arCtx_lengths (R := array (t := i32) s.partner partnerArr ⋆
          tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ array (t := i32) s.qm qm ⋆
          array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆ R) (sep_cast hm (by ac_rfl))
      have hpool_pc : s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) =
          s.pool.getD s.pc.toNat 0#64 :=
        (getD_eq_getElem s.pool 0#64 (by rw [hl_s.pool]; exact hpc)).symm
      let Rq := arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
        array64 s.qh qh ⋆ restT ⋆ R
      refine wp_store_arr32_abs (base := s.pool.getD s.pc.toNat 0#64) (xs := srcPool)
        (idx := s.ptop) (R := Rq) rfl (by dsimp only [Arg.val]; rw [hpool_pc]; simp)
        hpt_len (sep_cast hm_u (by dsimp only [Rq]; ac_rfl)) ?_
      intro m1 hm1
      dsimp only [Rq] at hm1
      c0_hsteps_nogrp
      refine wp_join_group (fun (_ : Tup Val []) m2 =>
        ∃ pA : List (BitVec 32), pA.length = srcPool.length ∧
          (∀ idx < s.ptop.toNat, pA.getD idx 0#32 = srcPool.getD idx 0#32) ∧
          pA.getD s.ptop.toNat 0#32 = len ∧
          (1 ≤ len.toNat → pA.getD (s.ptop.toNat + 1) 0#32 = s0) ∧
          (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) pA ⋆
            array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.qm qm ⋆
            array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆ (restT ⋆ R)) m2) ?_ ?_
      · intro J2 _ m2 ⟨pA, hp1_len', hpref1, hp1_0, hp1_1, hm2⟩
        c0_hsteps_nogrp
        refine wp_join_group (fun (_ : Tup Val []) m3 =>
          ∃ pB : List (BitVec 32), pB.length = srcPool.length ∧
            (∀ idx < s.ptop.toNat, pB.getD idx 0#32 = srcPool.getD idx 0#32) ∧
            pB.getD s.ptop.toNat 0#32 = len ∧
            (1 ≤ len.toNat → pB.getD (s.ptop.toNat + 1) 0#32 = s0) ∧
            (2 ≤ len.toNat → pB.getD (s.ptop.toNat + 2) 0#32 = s1) ∧
            (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) pB ⋆
              array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.qm qm ⋆
              array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆ (restT ⋆ R)) m3) ?_ ?_
        · intro J3 _ m3 ⟨pB, hp2_len', hpref2, hp2_0, hp2_1, hp2_2, hm3⟩
          c0_hsteps_nogrp
          have houtPtr : (s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc)) + s.ptop * 4 =
              s.pool.getD s.pc.toNat 0#64 + BitVec.ofNat 64 (4 * s.ptop.toNat) := by
            rw [hpool_pc]; congr 1; c0_bv_omega
          have hmo2 : MonoSliceOk pB s.ptop.toNat pB.length := by
            refine ⟨by omega, ?_⟩; rw [hp2_0]; omega
          let Rvan := array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
            array64 s.qh qh ⋆ restT ⋆ R
          have hm3_van : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
              array (t := i32) (s.pool.getD s.pc.toNat 0#64) pB ⋆ Rvan) m3 :=
            sep_cast hm3 (by dsimp only [Rvan]; ac_rfl)
          have hdst_eq : (if s.pc.toNat = 0 then (if s.pc.toNat = 0 then pB else pool0)
              else (if s.pc.toNat = 0 then pool1 else pB)) = pB := by split <;> rfl
          have hQm2 : ∀ i < s.qn.toNat,
              MonoSliceOk pB (qm.getD i 0#32).toNat s.ptop.toNat ∧
              (pB.getD (qm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 := fun i hi => by
            have ho := hQmOk i hi
            refine ⟨⟨ho.1.1, by rw [hpref2 _ ho.1.1]; exact ho.1.2⟩, by
              rw [hpref2 _ ho.1.1]; exact ho.2⟩
          have hQmSorted2 : ∀ i < s.qn.toNat, MonoSorted pB (qm.getD i 0#32).toNat := by
            intro i hi
            have ho := (hQmOk i hi).1
            have hsy_eq : symListAt pB (qm.getD i 0#32).toNat =
                symListAt srcPool (qm.getD i 0#32).toNat := by
              simp only [symListAt, hpref2 _ ho.1]
              exact List.map_congr_left fun r hr =>
                congrArg BitVec.toNat (hpref2 _ (by
                  have h2 : (qm.getD i 0#32).toNat + 1 +
                      (srcPool.getD (qm.getD i 0#32).toNat 0#32).toNat ≤ s.ptop.toNat := ho.2
                  have := List.mem_range.mp hr; omega))
            exact monoSorted_congr hsy_eq.symm (hQmSorted i hi)
          have hQmSig2 : SigOk pB qm qs s.qn.toNat := by
            intro i hi x hx
            have ho := (hQmOk i hi).1
            have hsy_eq : symListAt pB (qm.getD i 0#32).toNat =
                symListAt srcPool (qm.getD i 0#32).toNat := by
              simp only [symListAt, hpref2 _ ho.1]
              exact List.map_congr_left fun r hr =>
                congrArg BitVec.toNat (hpref2 _ (by
                  have h2 : (qm.getD i 0#32).toNat + 1 +
                      (srcPool.getD (qm.getD i 0#32).toNat 0#32).toNat ≤ s.ptop.toNat := ho.2
                  have := List.mem_range.mp hr; omega))
            rw [hsy_eq] at hx
            exact hQmSig i hi x hx
          have hWords2 : monoTotalWords pB qm s.qn.toNat ≤ s.ptop.toNat := by
            rw [monoTotalWords_congr_prefix (fun i hi => (hQmOk i hi).1) hpref2 (fun _ _ => rfl)]
            exact hQwords
          have hEval2 : ∀ σ, Valid σ →
              polyEval s.modW σ pB qm ql qh s.qn.toNat =
                polyEval s.modW σ srcPool qm ql qh s.qn.toNat := fun σ _ =>
            polyEval_congr_prefix s.modW σ (fun i hi => (hQmOk i hi).1) hpref2
              (fun _ _ => ⟨rfl, rfl, rfl⟩)
          refine wp_call_of_spec _ _ ?_
          refine arMvanish_forall_of_spec Γ hMvan houtPtr hmo2 (by rw [hp2_0]; omega)
            (by omega) hNonEmpty hPart hm3_van fun ok hvan => ?_
          dsimp only [Rvan] at hm3_van
          c0_hsteps_nogrp
          · have hsy : symListAt pB s.ptop.toNat = addQSyms len.toNat s0.toNat s1.toNat :=
              addQSyms_symListAt pB s.ptop.toNat len s0 s1 hlen_le2 hp2_0 hp2_1 hp2_2
            have htP := htBack s pB rfl rfl rfl rfl rfl hp2_len'
            have hm3_back : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
                tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
                  (if s.pc.toNat = 0 then pB else pool0)
                  (if s.pc.toNat = 0 then pool1 else pB) ⋆
                array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
                array64 s.qh qh ⋆ R) m3 := by
              rw [htP]; exact sep_cast hm3 (by ac_rfl)
            refine hQ true s (if s.pc.toNat = 0 then pB else pool0)
              (if s.pc.toNat = 0 then pool1 else pB) qm qs ql qh m3 hqn_le hpt_le rfl
              (by by_cases h0 : s.pc.toNat = 0 <;> simp [srcPool, h0, hp2_len'])
              (by by_cases h0 : s.pc.toNat = 0 <;> simp [srcPool, h0, hp2_len'])
              rfl rfl rfl rfl (by split <;> rfl) (by rw [hdst_eq]; exact hpref2)
              (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ => ?_) hm3_back
            rw [hdst_eq]
            refine ⟨hQm2, hQmSorted2, hQmSig2, hWords2, fun σ hV => ?_⟩
            have hvan0 : monoValL σ (addQSyms len.toNat s0.toNat s1.toNat) = false := by
              rw [← hsy]; exact hvan hc σ hV
            have hev := hEval2 σ hV
            dsimp only [srcPool] at hev
            simp [hvan0, hev]
          · let qm1 := qm.set (BitVec.setWidth 64 s.qn).toNat (s.ptop.setWidth 32)
            let Rsig := arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
              array (t := i32) s.qm qm1 ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
              array64 s.qh qh ⋆ restT ⋆ R
            have hm_sig : (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pB ⋆ Rsig) m :=
              sep_cast hm (by dsimp only [Rsig]; ac_rfl)
            refine wp_call_of_spec _ _ (hMsig (s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) +
                s.ptop * 4, ⟨⟩)
              m _ _ ⟨s.pool.getD s.pc.toNat 0#64, pB, s.ptop.toNat, Rsig,
              houtPtr, hmo2, by rw [hp2_0]; omega, hm_sig, fun sig hsig => ?_⟩)
            dsimp only [Rsig] at hm_sig
            have hqm_len' : (BitVec.setWidth 64 s.qn).toNat < qm.length := by c0_bv_omega
            have hqs_len' : (BitVec.setWidth 64 s.qn).toNat < qs.length := by c0_bv_omega
            have hql_len' : (BitVec.setWidth 64 s.qn).toNat < ql.length := by c0_bv_omega
            have hqh_len' : (BitVec.setWidth 64 s.qn).toNat < qh.length := by c0_bv_omega
            have hpt_add : (s.ptop + (BitVec.setWidth 64 len + 1#64)).toNat =
                s.ptop.toNat + len.toNat + 1 := by c0_bv_omega
            have hqn_add : (s.qn + 1#32).toNat = s.qn.toNat + 1 := by c0_bv_omega
            c0_hsteps_nogrp
            let s' : ArCtxState :=
              { s with qn := s.qn + 1#32, ptop := s.ptop + (BitVec.setWidth 64 len + 1#64) }
            let qm' := qm.set s.qn.toNat (s.ptop.setWidth 32)
            let qs' := qs.set s.qn.toNat sig
            let ql' := ql.set s.qn.toNat l
            let qh' := qh.set s.qn.toNat h
            have hsw_qn : (BitVec.setWidth 64 s.qn).toNat = s.qn.toNat := by c0_bv_omega
            have hsw_pt : (s.ptop.setWidth 32).toNat = s.ptop.toNat := by c0_bv_omega
            have htP := htBack s' pB rfl rfl rfl rfl rfl hp2_len'
            have hm'_cast : (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
                tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
                  (if s.pc.toNat = 0 then pB else pool0)
                  (if s.pc.toNat = 0 then pool1 else pB) ⋆
                array (t := i32) s'.qm qm' ⋆ array64 s'.qs qs' ⋆ array64 s'.ql ql' ⋆
                array64 s'.qh qh' ⋆ R) m := by
              rw [htP]; dsimp only [qm1] at hm; rw [hsw_qn] at hm
              try rw [BitVec.add_assoc s.ptop (BitVec.setWidth 64 len) 1] at hm
              try rw [BitVec.add_comm 1#64 (BitVec.setWidth 64 len)] at hm
              exact sep_cast hm (by ac_rfl)
            refine hQ true s' (if s.pc.toNat = 0 then pB else pool0)
              (if s.pc.toNat = 0 then pool1 else pB) qm' qs' ql' qh' m
              (by dsimp only [s']; rw [hqn_add]; omega)
              (by dsimp only [s']; rw [hpt_add]; exact hpt_cap) rfl
              (by by_cases h0 : s.pc.toNat = 0 <;> simp [srcPool, h0, hp2_len'])
              (by by_cases h0 : s.pc.toNat = 0 <;> simp [srcPool, h0, hp2_len'])
              (by simp [qm']) (by simp [qs']) (by simp [ql']) (by simp [qh'])
              (by split <;> rfl) (by rw [hdst_eq]; exact hpref2)
              (fun i hi => ⟨by
                  dsimp only [qm']; rw [getD_set_eq qm 0#32 _ (by omega), ite_eq_right (by omega)],
                by dsimp only [ql']; rw [getD_set_eq ql 0#64 _ (by omega), ite_eq_right (by omega)],
                by
                  dsimp only [qh']; rw [getD_set_eq qh 0#64 _ (by omega), ite_eq_right (by omega)]⟩)
              (fun _ => ?_) hm'_cast
            rw [hdst_eq]
            refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi x hx => ?_, ?_, fun σ hV => ?_⟩
            · dsimp only [s', qm']; rw [hpt_add, getD_set_eq qm 0#32 _ (by omega)]
              by_cases hiq : i = s.qn.toNat
              · subst hiq; simp only [↓reduceIte, hsw_pt]
                refine ⟨⟨by omega, by rw [hp2_0]; omega⟩, by rw [hp2_0]; omega⟩
              · simp only [hiq, ↓reduceIte]
                have hi_lt : i < s.qn.toNat := by
                  dsimp only [s'] at hi; rw [hqn_add] at hi
                  exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hiq
                have hq := hQm2 i hi_lt
                exact ⟨⟨by have := hq.1.1; omega, by have := hq.1.2; omega⟩, hq.2⟩
            · dsimp only [s', qm']
              rw [getD_set_eq qm 0#32 _ (by omega)]
              by_cases hiq : i = s.qn.toNat
              · subst hiq; simp only [↓reduceIte, hsw_pt]
                by_cases h2 : len.toNat = 2
                · refine monoSorted_two (by rw [hp2_0, h2]) ?_
                  rw [hp2_1 (by omega), hp2_2 (by omega)]
                  exact hs01_lt h2
                · apply monoSorted_of_le1
                  rw [hp2_0]; omega
              · simp only [hiq, ↓reduceIte]
                have hi_lt : i < s.qn.toNat := by
                  dsimp only [s'] at hi; rw [hqn_add] at hi
                  exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hiq
                exact hQmSorted2 i hi_lt
            · dsimp only [s', qm', qs'] at hi hx ⊢
              rw [getD_set_eq qm 0#32 _ (by omega)] at hx
              rw [getD_set_eq qs 0#64 _ (by omega)]
              by_cases hiq : i = s.qn.toNat
              · subst hiq; simp only [↓reduceIte, hsw_pt] at hx ⊢
                exact hsig x hx
              · simp only [hiq, ↓reduceIte] at hx ⊢
                have hi_lt : i < s.qn.toNat := by rw [hqn_add] at hi; omega
                exact hQmSig2 i hi_lt x hx
            · dsimp only [s', qm']
              rw [hqn_add, hpt_add, monoTotalWords_succ]
              have hcongr : monoTotalWords pB (qm.set s.qn.toNat (s.ptop.setWidth 32)) s.qn.toNat =
                  monoTotalWords pB qm s.qn.toNat := by
                apply monoTotalWords_congr_prefix (fun i hi => (hQm2 i hi).1) (fun _ _ => rfl)
                intro i hi; rw [getD_set_eq qm 0#32 _ (by omega), ite_eq_right (by omega)]
              rw [hcongr, getD_set_eq qm 0#32 _ (by omega), ite_eq_left rfl, hsw_pt, hp2_0]
              omega
            · dsimp only [s']
              rw [hqn_add, polyEval_succ]
              have hprev : polyEval s.modW σ pB qm' ql' qh' s.qn.toNat =
                  polyEval s.modW σ srcPool qm ql qh s.qn.toNat := by
                rw [← hEval2 σ hV]
                refine polyEval_congr_prefix s.modW σ (fun i hi => (hQm2 i hi).1)
                  (fun _ _ => rfl) fun i hi => ?_
                exact ⟨by
                    dsimp only [qm']
                    rw [getD_set_eq qm 0#32 _ (by omega), ite_eq_right (by omega)],
                  by
                    dsimp only [ql']
                    rw [getD_set_eq ql 0#64 _ (by omega), ite_eq_right (by omega)],
                  by
                    dsimp only [qh']
                    rw [getD_set_eq qh 0#64 _ (by omega), ite_eq_right (by omega)]⟩
              have hsy : symListAt pB (qm'.getD s.qn.toNat 0#32).toNat =
                  addQSyms len.toNat s0.toNat s1.toNat := by
                dsimp only [qm']; rw [getD_set_eq qm 0#32 _ (by omega), ite_eq_left rfl, hsw_pt]
                exact addQSyms_symListAt pB s.ptop.toNat len s0 s1 hlen_le2 hp2_0 hp2_1 hp2_2
              have hql_n : ql'.getD s.qn.toNat 0#64 = l := by
                dsimp only [ql']; rw [getD_set_eq ql 0#64 _ (by omega), ite_eq_left rfl]
              have hqh_n : qh'.getD s.qn.toNat 0#64 = h := by
                dsimp only [qh']; rw [getD_set_eq qh 0#64 _ (by omega), ite_eq_left rfl]
              rw [hprev]; dsimp only [srcPool]
              exact congrArg (_ + ·) (by simp only [termEval, hsy, hql_n, hqh_n])
        · intro Jc hJc
          c0_hsteps_nogrp
          · have h2le : 2 ≤ len.toNat := by c0_bv_omega
            have hpt2 : (s.ptop + 2#64).toNat = s.ptop.toNat + 2 := by c0_bv_omega
            refine wp_store_arr32_abs (base := s.pool.getD s.pc.toNat 0#64) (xs := pA)
              (idx := s.ptop + 2#64) (R := Rq) rfl
              (by dsimp only [Arg.val]; rw [hpool_pc, BitVec.add_mul, BitVec.add_assoc])
              (by omega) (sep_cast hm2 (by dsimp only [Rq]; ac_rfl)) ?_
            intro m3 hm3
            dsimp only [Rq] at hm3
            c0_hsteps
            refine hJc ⟨⟩ m3 ⟨pA.set (s.ptop + 2#64).toNat s1, by simp [hp1_len'],
              fun idx hidx => by
                rw [getD_set_eq _ 0#32 s1 (by omega), ite_eq_right (by omega)]
                exact hpref1 idx hidx,
              by rw [getD_set_eq _ 0#32 s1 (by omega), ite_eq_right (by omega)]; exact hp1_0,
              fun h1 => by
                rw [getD_set_eq _ 0#32 s1 (by omega), ite_eq_right (by omega)]; exact hp1_1 h1,
              fun _ => by rw [hpt2, getD_set_eq _ 0#32 s1 (by omega), ite_eq_left rfl],
              sep_cast hm3 (by ac_rfl)⟩
          · have hn2 : ¬ 2 ≤ len.toNat := by c0_bv_omega
            c0_hsteps
            exact hJc ⟨⟩ m2 ⟨pA, hp1_len', hpref1, hp1_0, hp1_1, fun h2 => absurd h2 hn2, hm2⟩
      · intro J1 hJ1
        c0_hsteps_nogrp
        · have h1le : 1 ≤ len.toNat := by c0_bv_omega
          have hpt1 : (s.ptop + 1#64).toNat = s.ptop.toNat + 1 := by c0_bv_omega
          refine wp_store_arr32_abs (base := s.pool.getD s.pc.toNat 0#64)
            (xs := srcPool.set s.ptop.toNat len) (idx := s.ptop + 1#64) (R := Rq) rfl
            (by dsimp only [Arg.val]; rw [hpool_pc, BitVec.add_mul, BitVec.add_assoc])
            (by simp; omega) (sep_cast hm1 (by dsimp only [Rq]; ac_rfl)) ?_
          intro m2 hm2
          dsimp only [Rq] at hm2
          c0_hsteps
          refine hJ1 ⟨⟩ m2 ⟨(srcPool.set s.ptop.toNat len).set (s.ptop + 1#64).toNat s0,
            by simp,
            fun idx hidx => by
              rw [getD_set_eq _ 0#32 s0 (by simp; omega), ite_eq_right (by omega),
                getD_set_eq _ 0#32 len hpt_len, ite_eq_right (by omega)],
            by rw [getD_set_eq _ 0#32 s0 (by simp; omega), ite_eq_right (by omega),
                getD_set_eq _ 0#32 len hpt_len, ite_eq_left rfl],
            fun _ => by rw [hpt1, getD_set_eq _ 0#32 s0 (by simp; omega), ite_eq_left rfl],
            sep_cast hm2 (by ac_rfl)⟩
        · have hn1 : ¬ 1 ≤ len.toNat := by c0_bv_omega
          c0_hsteps
          refine hJ1 ⟨⟩ m1 ⟨srcPool.set s.ptop.toNat len, by simp,
            fun idx hidx => by rw [getD_set_eq _ 0#32 len hpt_len, ite_eq_right (by omega)],
            by rw [getD_set_eq _ 0#32 len hpt_len, ite_eq_left rfl],
            fun h1 => absurd h1 hn1, sep_cast hm1 (by ac_rfl)⟩
  · intro Js hJs
    c0_hsteps_nogrp
    · have hl0 : l = 0#64 := ‹l = 0#64›
      have hh0 : h = 0#64 := hc
      c0_hsteps
      refine hQ true s pool0 pool1 qm qs ql qh m hqn_le hpt_le rfl rfl rfl rfl rfl rfl rfl
        (by split <;> rfl) (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ => ?_) hm
      refine ⟨hQmOk, hQmSorted, hQmSig, hQwords, fun σ _ => ?_⟩
      simp [hl0, hh0, coeff128]
    · c0_hsteps; exact hJs ⟨⟩ m ⟨rfl, fun ⟨_, hh0⟩ => hc hh0⟩
    · c0_hsteps; exact hJs ⟨⟩ m ⟨rfl, fun ⟨hl0, _⟩ => hc hl0⟩

/-! ## 3. WP Proof: `ar_load_rule` -/

theorem polyEval_eq_polyEvalRange_of_prefix (nOut : Nat) (σ : Nat → Bool)
    {pool1 tm1 pool2 mOff2 : List (BitVec 32)} {tl1 th1 cl2 ch2 : List (BitVec 64)}
    {off n : Nat}
    (h : ∀ t < n,
      symListAt pool1 (tm1.getD t 0#32).toNat = symListAt pool2 (mOff2.getD (off + t) 0#32).toNat ∧
      tl1.getD t 0#64 = cl2.getD (off + t) 0#64 ∧
      th1.getD t 0#64 = ch2.getD (off + t) 0#64) :
    polyEval nOut σ pool1 tm1 tl1 th1 n = polyEvalRange nOut σ pool2 mOff2 cl2 ch2 off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polyEval_succ, polyEvalRange_succ, ih (fun t ht => h t (by omega))]
    congr 1
    have hn := h n (Nat.lt_succ_self n)
    simp only [termEval, hn.1, hn.2.1, hn.2.2]

theorem symListAt_congr_slice {p1 p2 : List (BitVec 32)} {o1 o2 : Nat}
    (hlen : (p1.getD o1 0#32).toNat = (p2.getD o2 0#32).toNat)
    (heq : ∀ r ≤ (p2.getD o2 0#32).toNat, p1.getD (o1 + r) 0#32 = p2.getD (o2 + r) 0#32) :
    symListAt p1 o1 = symListAt p2 o2 := by
  simp only [symListAt, hlen]
  apply List.map_congr_left
  intro r hr
  have hrl := List.mem_range.mp hr
  rw [Nat.add_assoc, Nat.add_assoc, heq (1 + r) (by omega)]

private theorem loadRule_step_inv {srcPool dstPool rsPool dstTm rsM : List (BitVec 32)}
    {dstTl dstTh rsL rsH : List (BitVec 64)}
    {i off mOff mlen pt : Nat}
    (hPrev : ∀ k < i,
      MonoSliceOk srcPool (dstTm.getD k 0#32).toNat pt ∧
      (srcPool.getD (dstTm.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 ∧
      symListAt srcPool (dstTm.getD k 0#32).toNat =
        symListAt rsPool (rsM.getD (off + k) 0#32).toNat ∧
      dstTl.getD k 0#64 = rsL.getD (off + k) 0#64 ∧
      dstTh.getD k 0#64 = rsH.getD (off + k) 0#64)
    (hWords : monoTotalWords srcPool dstTm i ≤ pt)
    (hi_tm : i < dstTm.length) (hi_tl : i < dstTl.length) (hi_th : i < dstTh.length)
    (hm_eq : (rsM.getD (off + i) 0#32).toNat = mOff)
    (hm_len : (rsPool.getD mOff 0#32).toNat = mlen)
    (hmlen32 : mlen + 1 < 2 ^ 32)
    (hpt32 : pt < 2 ^ 32)
    (hOld : ∀ q < pt, dstPool.getD q 0#32 = srcPool.getD q 0#32)
    (hCopied : ∀ r ≤ mlen, dstPool.getD (pt + r) 0#32 = rsPool.getD (mOff + r) 0#32)
    {lNew hNew : BitVec 64}
    (hlNew : lNew = rsL.getD (off + i) 0#64) (hhNew : hNew = rsH.getD (off + i) 0#64) :
    let tm' := dstTm.set i (BitVec.ofNat 32 pt)
    let tl' := dstTl.set i lNew
    let th' := dstTh.set i hNew
    let pt' := pt + mlen + 1
    (∀ k < i + 1,
      MonoSliceOk dstPool (tm'.getD k 0#32).toNat pt' ∧
      (dstPool.getD (tm'.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 ∧
      symListAt dstPool (tm'.getD k 0#32).toNat =
        symListAt rsPool (rsM.getD (off + k) 0#32).toNat ∧
      tl'.getD k 0#64 = rsL.getD (off + k) 0#64 ∧
      th'.getD k 0#64 = rsH.getD (off + k) 0#64) ∧
    monoTotalWords dstPool tm' (i + 1) ≤ pt' := by
  intro tm' tl' th' pt'
  have hpt_toNat : (BitVec.ofNat 32 pt).toNat = pt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpt32]
  have hpt0 : dstPool.getD pt 0#32 = rsPool.getD mOff 0#32 := by
    have := hCopied 0 (Nat.zero_le mlen); simpa only [Nat.add_zero] using this
  have hpt0_nat : (dstPool.getD pt 0#32).toNat = mlen := by rw [hpt0, hm_len]
  have hWords_eq : monoTotalWords dstPool dstTm i = monoTotalWords srcPool dstTm i :=
    monoTotalWords_congr_prefix (fun k hk => (hPrev k hk).1) hOld (fun _ _ => rfl)
  refine ⟨fun k hk => ?_, ?_⟩
  · by_cases hki : k = i
    · subst hki
      have htm_k : (tm'.getD k 0#32).toNat = pt := by
        dsimp only [tm']; rw [getD_set_eq dstTm 0#32 _ hi_tm, ite_eq_left rfl, hpt_toNat]
      rw [htm_k]
      refine ⟨⟨by omega, by rw [hpt0_nat]; dsimp only [pt']; omega⟩,
        by rw [hpt0_nat]; exact hmlen32, ?_, ?_, ?_⟩
      · rw [hm_eq]
        exact symListAt_congr_slice (by rw [hpt0_nat, hm_len]) (fun r hr => by
          rw [hm_len] at hr; exact hCopied r hr)
      · dsimp only [tl']; rw [getD_set_eq dstTl 0#64 _ hi_tl, ite_eq_left rfl, hlNew]
      · dsimp only [th']; rw [getD_set_eq dstTh 0#64 _ hi_th, ite_eq_left rfl, hhNew]
    · have hk_lt : k < i := by omega
      obtain ⟨hsl, h32, hsy, htl, hth⟩ := hPrev k hk_lt
      have htm_k : tm'.getD k 0#32 = dstTm.getD k 0#32 := by
        dsimp only [tm']; rw [getD_set_eq dstTm 0#32 _ hi_tm, ite_eq_right hki]
      rw [htm_k]
      have hlen_keep : dstPool.getD (dstTm.getD k 0#32).toNat 0#32 =
          srcPool.getD (dstTm.getD k 0#32).toNat 0#32 := hOld _ hsl.1
      have hsl1 := hsl.1
      have hsl2 := hsl.2
      dsimp only [pt']
      refine ⟨⟨by omega, by rw [hlen_keep]; omega⟩,
        by rw [hlen_keep]; exact h32, ?_, ?_, ?_⟩
      · rw [← hsy]
        exact symListAt_congr_slice (by rw [hlen_keep])
          (fun r hr => hOld _ (by omega))
      · dsimp only [tl']; rw [getD_set_eq dstTl 0#64 _ hi_tl, ite_eq_right hki]; exact htl
      · dsimp only [th']; rw [getD_set_eq dstTh 0#64 _ hi_th, ite_eq_right hki]; exact hth
  · rw [monoTotalWords_succ]
    have hpref : monoTotalWords dstPool tm' i = monoTotalWords dstPool dstTm i :=
      monoTotalWords_congr_prefix (fun k hk => ⟨(hPrev k hk).1.1,
        by rw [hOld _ (hPrev k hk).1.1]; exact (hPrev k hk).1.2⟩) (fun _ _ => rfl)
        (fun k hk => by
          dsimp only [tm']; rw [getD_set_eq dstTm 0#32 _ hi_tm, ite_eq_right (by omega)])
    rw [hpref, hWords_eq]
    dsimp only [tm']
    rw [getD_set_eq dstTm 0#32 _ hi_tm, ite_eq_left rfl, hpt_toNat, hpt0_nat]
    dsimp only [pt']; omega

private theorem loadRule_pack_mem {cx : BitVec 64} {s s' : ArCtxState}
    {ruleOff ruleN rsM rsPool tm0 tm1 pool0 pool1 tmC poolC : List (BitVec 32)}
    {rsL rsH ts0 tl0 th0 ts1 tl1 th1 tsC tlC thC : List (BitVec 64)}
    {restT R : Mem 64 → Prop} {m : Mem 64}
    (htms : s'.tm = s.tm) (htss : s'.ts = s.ts) (htls : s'.tl = s.tl) (hths : s'.th = s.th)
    (hpools : s'.pool = s.pool) (hro : s'.rule_off = s.rule_off) (hrn : s'.rule_n = s.rule_n)
    (hrsm : s'.rs_m = s.rs_m) (hrsl : s'.rs_l = s.rs_l) (hrsh : s'.rs_h = s.rs_h)
    (hrsp : s'.rs_pool = s.rs_pool)
    (htmC_len : tmC.length = (if s.tc.toNat = 0 then tm0 else tm1).length)
    (htsC_len : tsC.length = (if s.tc.toNat = 0 then ts0 else ts1).length)
    (htlC_len : tlC.length = (if s.tc.toNat = 0 then tl0 else tl1).length)
    (hthC_len : thC.length = (if s.tc.toNat = 0 then th0 else th1).length)
    (hpoolC_len : poolC.length = (if s.pc.toNat = 0 then pool0 else pool1).length)
    (htBack : ∀ (s1 : ArCtxState) (tm' : List (BitVec 32)) (ts' tl' th' : List (BitVec 64))
        (pool' : List (BitVec 32)),
      s1.tm = s.tm → s1.ts = s.ts → s1.tl = s.tl → s1.th = s.th → s1.pool = s.pool →
      tm'.length = (if s.tc.toNat = 0 then tm0 else tm1).length →
      ts'.length = (if s.tc.toNat = 0 then ts0 else ts1).length →
      tl'.length = (if s.tc.toNat = 0 then tl0 else tl1).length →
      th'.length = (if s.tc.toNat = 0 then th0 else th1).length →
      pool'.length = (if s.pc.toNat = 0 then pool0 else pool1).length →
      tMem s1 (if s.tc.toNat = 0 then tm' else tm0) (if s.tc.toNat = 0 then tm1 else tm')
          (if s.tc.toNat = 0 then ts' else ts0) (if s.tc.toNat = 0 then tl' else tl0)
          (if s.tc.toNat = 0 then th' else th0) (if s.tc.toNat = 0 then ts1 else ts')
          (if s.tc.toNat = 0 then tl1 else tl') (if s.tc.toNat = 0 then th1 else th')
          (if s.pc.toNat = 0 then pool' else pool0)
          (if s.pc.toNat = 0 then pool1 else pool') =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pool' ⋆
         array (t := i32) (s.tm.getD s.tc.toNat 0#64) tm' ⋆
         array64 (s.ts.getD s.tc.toNat 0#64) ts' ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tl' ⋆
         array64 (s.th.getD s.tc.toNat 0#64) th' ⋆ restT))
    (hmF : (arCtxMem cx s' ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolC ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
      array64 (s.th.getD s.tc.toNat 0#64) thC ⋆
      (array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
        array (t := i32) s.rs_pool rsPool ⋆
        u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R)) m) :
    (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
      rsMem s' rsM rsL rsH rsPool ⋆
      tMem s' (if s.tc.toNat = 0 then tmC else tm0) (if s.tc.toNat = 0 then tm1 else tmC)
        (if s.tc.toNat = 0 then tsC else ts0) (if s.tc.toNat = 0 then tlC else tl0)
        (if s.tc.toNat = 0 then thC else th0) (if s.tc.toNat = 0 then ts1 else tsC)
        (if s.tc.toNat = 0 then tl1 else tlC) (if s.tc.toNat = 0 then th1 else thC)
        (if s.pc.toNat = 0 then poolC else pool0) (if s.pc.toNat = 0 then pool1 else poolC) ⋆
      R) m := by
  have htC := htBack s' tmC tsC tlC thC poolC htms htss htls hths hpools
    htmC_len htsC_len htlC_len hthC_len hpoolC_len
  rw [htC, rsMem_unfold, hro, hrn, hrsm, hrsl, hrsh, hrsp]
  exact sep_cast hmF (by ac_rfl)

private theorem loadRule_false_exit {cx : BitVec 64} {s s0 : ArCtxState}
    {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 srcTm srcPool : List (BitVec 32)} {srcTs srcTl srcTh : List (BitVec 64)}
    {restT R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    (hm : (arCtxMem cx s0 ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
      array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      array (t := i32) s.rs_pool rsPool ⋆
      (u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R)) m)
    (hs0 : s0 = { s with tn := 0#32, ptop := 0#64, qn := 0#32 })
    (hsrc : srcTm = (if s.tc.toNat = 0 then tm0 else tm1) ∧
      srcTs = (if s.tc.toNat = 0 then ts0 else ts1) ∧
      srcTl = (if s.tc.toNat = 0 then tl0 else tl1) ∧
      srcTh = (if s.tc.toNat = 0 then th0 else th1) ∧
      srcPool = (if s.pc.toNat = 0 then pool0 else pool1))
    (ht0 : tMem s0 (if s.tc.toNat = 0 then srcTm else tm0) (if s.tc.toNat = 0 then tm1 else srcTm)
        (if s.tc.toNat = 0 then srcTs else ts0) (if s.tc.toNat = 0 then srcTl else tl0)
        (if s.tc.toNat = 0 then srcTh else th0) (if s.tc.toNat = 0 then ts1 else srcTs)
        (if s.tc.toNat = 0 then tl1 else srcTl) (if s.tc.toNat = 0 then th1 else srcTh)
        (if s.pc.toNat = 0 then srcPool else pool0) (if s.pc.toNat = 0 then pool1 else srcPool) =
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
        array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ restT)
    (hQ : ∀ (ok : Bool) (s' : ArCtxState)
        (tm0' tm1' : List (BitVec 32)) (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' : List (BitVec 32)) (m' : Mem 64),
      s'.tn.toNat ≤ s.tcap.toNat → s'.ptop.toNat ≤ s.pcap.toNat →
      s' = { s with tn := s'.tn, ptop := s'.ptop, qn := 0#32 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      (ok = true → False) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆
        array (t := i32) s'.rule_n ruleN ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆ R) m' →
      Q (ok, ⟨⟩) m') :
    Q (false, ⟨⟩) m := by
  have hm_back : (arCtxMem cx s0 ⋆ array (t := i32) s0.rule_off ruleOff ⋆
      array (t := i32) s0.rule_n ruleN ⋆ rsMem s0 rsM rsL rsH rsPool ⋆
      tMem s0 tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m := by
    rw [rsMem_unfold]
    have hm_eq : (if s.tc.toNat = 0 then srcTm else tm0) = tm0 ∧
        (if s.tc.toNat = 0 then tm1 else srcTm) = tm1 ∧
        (if s.tc.toNat = 0 then srcTs else ts0) = ts0 ∧
        (if s.tc.toNat = 0 then srcTl else tl0) = tl0 ∧
        (if s.tc.toNat = 0 then srcTh else th0) = th0 ∧
        (if s.tc.toNat = 0 then ts1 else srcTs) = ts1 ∧
        (if s.tc.toNat = 0 then tl1 else srcTl) = tl1 ∧
        (if s.tc.toNat = 0 then th1 else srcTh) = th1 ∧
        (if s.pc.toNat = 0 then srcPool else pool0) = pool0 ∧
        (if s.pc.toNat = 0 then pool1 else srcPool) = pool1 := by
      rcases hsrc with ⟨h1, h2, h3, h4, h5⟩
      rw [h1, h2, h3, h4, h5]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl
    rw [← hm_eq.1, ← hm_eq.2.1, ← hm_eq.2.2.1, ← hm_eq.2.2.2.1, ← hm_eq.2.2.2.2.1,
      ← hm_eq.2.2.2.2.2.1, ← hm_eq.2.2.2.2.2.2.1, ← hm_eq.2.2.2.2.2.2.2.1,
      ← hm_eq.2.2.2.2.2.2.2.2.1, ← hm_eq.2.2.2.2.2.2.2.2.2, ht0]
    have hfields : s0.rule_off = s.rule_off ∧ s0.rule_n = s.rule_n ∧ s0.rs_m = s.rs_m ∧
        s0.rs_l = s.rs_l ∧ s0.rs_h = s.rs_h ∧ s0.rs_pool = s.rs_pool := by
      rw [hs0]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
      hfields.2.2.2.2.1, hfields.2.2.2.2.2]
    exact sep_cast hm (by ac_rfl)
  exact hQ false s0 tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 m
    (by simp [hs0]) (by simp [hs0]) (by rw [hs0]) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun h => by cases h) hm_back

private theorem loadRule_pt_add {pt : Nat} {s : ArCtxState} {rsPool : List (BitVec 32)}
    {mOff32 mlen : BitVec 32} (hm_lt : mOff32.toNat < rsPool.length)
    (hml_eq : (rsPool[mOff32.toNat]'hm_lt).toNat = mlen.toNat)
    (hpt_le : pt ≤ s.pcap.toNat) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hmlen32 : mlen.toNat + 1 < 2 ^ 32)
    (hc' : ¬ (2 ^ 64 - pt % 2 ^ 64 + s.pcap.toNat) % 2 ^ 64 <
      ((rsPool[mOff32.toNat]'hm_lt).toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64) :
    pt + mlen.toNat + 1 ≤ s.pcap.toNat := by
  rw [hml_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : pt < 2 ^ 64),
    show 2 ^ 64 - pt + s.pcap.toNat = 2 ^ 64 + (s.pcap.toNat - pt) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : s.pcap.toNat - pt < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : mlen.toNat + 1 < 2 ^ 64)] at hc'
  exact Nat.le_of_not_lt fun hlt => hc' (by omega)

private theorem loadRule_step_pack
    {s : ArCtxState} {rsM rsPool tmC poolC poolJ : List (BitVec 32)}
    {rsL rsH tsC tlC thC : List (BitVec 64)}
    {off iV mlen : BitVec 32} {pt mOff : Nat} {sig : BitVec 64}
    (hPrev : ∀ k < iV.toNat,
      MonoSliceOk poolC (tmC.getD k 0#32).toNat pt ∧
      (poolC.getD (tmC.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 ∧
      symListAt poolC (tmC.getD k 0#32).toNat =
        symListAt rsPool (rsM.getD (off.toNat + k) 0#32).toNat ∧
      tlC.getD k 0#64 = rsL.getD (off.toNat + k) 0#64 ∧
      thC.getD k 0#64 = rsH.getD (off.toNat + k) 0#64)
    (hSigC : SigOk poolC tmC tsC iV.toNat) (hWords : monoTotalWords poolC tmC iV.toNat ≤ pt)
    (hi_tm : iV.toNat < tmC.length) (hi_ts : iV.toNat < tsC.length)
    (hi_tl : iV.toNat < tlC.length) (hi_th : iV.toNat < thC.length)
    (hmOff_eq : mOff = (rsM.getD (off.toNat + iV.toNat) 0#32).toNat)
    (hmlen_eq : mlen.toNat = (rsPool.getD mOff 0#32).toNat)
    (hmlen32 : mlen.toNat + 1 < 2 ^ 32) (hpt_add : pt + mlen.toNat + 1 ≤ s.pcap.toNat)
    (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hOld : ∀ q < pt, poolJ.getD q 0#32 = poolC.getD q 0#32)
    (hCopied' : ∀ r ≤ mlen.toNat, poolJ.getD (pt + r) 0#32 = rsPool.getD (mOff + r) 0#32)
    (hofi_rsl : (off + iV).toNat < rsL.length) (hofi_rsh : (off + iV).toNat < rsH.length)
    (hofi_eq : (off + iV).toNat = off.toNat + iV.toNat)
    (hsig : ∀ x ∈ symListAt rsPool mOff, (sig &&& sigBit (BitVec.ofNat 32 x)) ≠ 0#64) :
    let tmN := tmC.set iV.toNat (BitVec.ofNat 32 pt)
    let tsN := tsC.set iV.toNat sig
    let tlN := tlC.set iV.toNat (rsL[(off + iV).toNat]'hofi_rsl)
    let thN := thC.set iV.toNat (rsH[(off + iV).toNat]'hofi_rsh)
    (∀ k < iV.toNat + 1,
      MonoSliceOk poolJ (tmN.getD k 0#32).toNat (pt + mlen.toNat + 1) ∧
      (poolJ.getD (tmN.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 ∧
      symListAt poolJ (tmN.getD k 0#32).toNat =
        symListAt rsPool (rsM.getD (off.toNat + k) 0#32).toNat ∧
      tlN.getD k 0#64 = rsL.getD (off.toNat + k) 0#64 ∧
      thN.getD k 0#64 = rsH.getD (off.toNat + k) 0#64) ∧
    SigOk poolJ tmN tsN (iV.toNat + 1) ∧
    monoTotalWords poolJ tmN (iV.toNat + 1) ≤ pt + mlen.toNat + 1 := by
  have hstep := loadRule_step_inv hPrev hWords hi_tm hi_tl hi_th hmOff_eq.symm
    hmlen_eq.symm hmlen32 (by omega) hOld hCopied'
    (show rsL[(off + iV).toNat]'hofi_rsl = rsL.getD (off.toNat + iV.toNat) 0#64 by
      rw [← getD_eq_getElem rsL 0#64 hofi_rsl, hofi_eq])
    (show rsH[(off + iV).toNat]'hofi_rsh = rsH.getD (off.toNat + iV.toNat) 0#64 by
      rw [← getD_eq_getElem rsH 0#64 hofi_rsh, hofi_eq])
  refine ⟨hstep.1, fun k hk x hx => ?_, hstep.2⟩
  rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hklt
  · rw [getD_set_eq tsC 0#64 sig hi_ts, ite_eq_left rfl]
    have hsy_new := (hstep.1 iV.toNat (Nat.lt_succ_self _)).2.2.1
    rw [hsy_new, ← hmOff_eq] at hx
    exact hsig x hx
  · rw [getD_set_eq tsC 0#64 sig (by omega), ite_eq_right (by omega)]
    have hsy_old := (hstep.1 k (by omega)).2.2.1.trans (hPrev k hklt).2.2.1.symm
    rw [getD_set_eq tmC 0#32 _ (by omega), ite_eq_right (by omega)] at hx hsy_old
    rw [hsy_old] at hx
    exact hSigC k hklt x hx

private theorem loadRule_done_inv {s : ArCtxState} {v cnt : BitVec 32}
    {ruleOff ruleN rsM rsPool tm0 tm1 pool0 pool1 tmC poolC : List (BitVec 32)}
    {rsL rsH ts0 tl0 th0 ts1 tl1 th1 tsC tlC thC : List (BitVec 64)}
    {Valid : (Nat → Bool) → Prop} {pt : Nat} {iV : BitVec 32}
    (hv_lt : v.toNat < s.n_nets.toNat) (hvn_ne : ruleN.getD v.toNat 0#32 ≠ cNone32)
    (_hpc : s.pc.toNat < 2) (_htc : s.tc.toNat < 2)
    (hcnt_def : cnt = ruleN.getD v.toNat 0#32)
    (hoff_cnt : (ruleOff.getD v.toNat 0#32).toNat + cnt.toNat ≤ s.rs_n.toNat)
    (hi_done : iV.toNat = cnt.toNat)
    (hpt_toNat : (BitVec.ofNat 64 pt).toNat = pt)
    (hPrev : ∀ k < iV.toNat,
      MonoSliceOk poolC (tmC.getD k 0#32).toNat pt ∧
      (poolC.getD (tmC.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 ∧
      symListAt poolC (tmC.getD k 0#32).toNat =
        symListAt rsPool (rsM.getD ((ruleOff.getD v.toNat 0#32).toNat + k) 0#32).toNat ∧
      tlC.getD k 0#64 = rsL.getD ((ruleOff.getD v.toNat 0#32).toNat + k) 0#64 ∧
      thC.getD k 0#64 = rsH.getD ((ruleOff.getD v.toNat 0#32).toNat + k) 0#64)
    (hSigC : SigOk poolC tmC tsC iV.toNat) (hWords : monoTotalWords poolC tmC iV.toNat ≤ pt)
    (hRules : ∀ σ : Nat → Bool, Valid σ →
      RulesRep s.modW σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hRulesSorted : RulesSorted rsPool rsM s.rs_n.toNat) :
    let s' : ArCtxState := { s with tn := cnt, ptop := BitVec.ofNat 64 pt, qn := 0#32 }
    let dstPool := if s'.pc.toNat = 0 then (if s.pc.toNat = 0 then poolC else pool0)
      else (if s.pc.toNat = 0 then pool1 else poolC)
    let dstTm := if s'.tc.toNat = 0 then (if s.tc.toNat = 0 then tmC else tm0)
      else (if s.tc.toNat = 0 then tm1 else tmC)
    let dstTs := if s'.tc.toNat = 0 then (if s.tc.toNat = 0 then tsC else ts0)
      else (if s.tc.toNat = 0 then ts1 else tsC)
    let dstTl := if s'.tc.toNat = 0 then (if s.tc.toNat = 0 then tlC else tl0)
      else (if s.tc.toNat = 0 then tl1 else tlC)
    let dstTh := if s'.tc.toNat = 0 then (if s.tc.toNat = 0 then thC else th0)
      else (if s.tc.toNat = 0 then th1 else thC)
    (∀ k < s'.tn.toNat,
      MonoSliceOk dstPool (dstTm.getD k 0#32).toNat s'.ptop.toNat ∧
      (dstPool.getD (dstTm.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    (∀ k < s'.tn.toNat, MonoSorted dstPool (dstTm.getD k 0#32).toNat) ∧
    SigOk dstPool dstTm dstTs s'.tn.toNat ∧
    monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat ∧
    (∀ (bd : Nat), SymsBound rsPool rsM s.rs_n.toNat bd →
      SymsBound dstPool dstTm s'.tn.toNat bd) ∧
    (∀ σ : Nat → Bool, Valid σ →
      polyEval s'.modW σ dstPool dstTm dstTl dstTh s'.tn.toNat =
        bv s'.modW (σ (2 * v.toNat))) := by
  intro s' dstPool dstTm dstTs dstTl dstTh
  have hdst_p : dstPool = poolC := by dsimp only [dstPool, s']; split <;> rfl
  have hdst_m : dstTm = tmC := by dsimp only [dstTm, s']; split <;> rfl
  have hdst_s : dstTs = tsC := by dsimp only [dstTs, s']; split <;> rfl
  have hdst_l : dstTl = tlC := by dsimp only [dstTl, s']; split <;> rfl
  have hdst_h : dstTh = thC := by dsimp only [dstTh, s']; split <;> rfl
  rw [hdst_p, hdst_m, hdst_s, hdst_l, hdst_h]; dsimp only [s']; rw [hpt_toNat]
  refine ⟨fun k hk => ⟨(hPrev k (by omega)).1, (hPrev k (by omega)).2.1⟩,
    fun k hk => monoSorted_congr (hPrev k (by omega)).2.2.1.symm
      (hRulesSorted ((ruleOff.getD v.toNat 0#32).toNat + k)
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hoff_cnt)),
    by rw [← hi_done]; exact hSigC, by rw [← hi_done]; exact hWords,
    fun bd hSb k hk x hx => by
      have hk_lt : k < cnt.toNat := by omega
      have hsym := (hPrev k (by omega)).2.2.1
      rw [hsym] at hx
      exact hSb ((ruleOff.getD v.toNat 0#32).toNat + k)
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk_lt _) hoff_cnt) x hx,
    fun σ hV => ?_⟩
  have hs'_modW : s'.modW = s.modW := rfl
  rw [hs'_modW, polyEval_eq_polyEvalRange_of_prefix s.modW σ (fun k hk =>
    ⟨(hPrev k (by omega)).2.2.1, (hPrev k (by omega)).2.2.2.1, (hPrev k (by omega)).2.2.2.2⟩),
    hcnt_def]
  exact ((hRules σ hV).2.2.2.2.2.2.2.2.2 v.toNat hv_lt hvn_ne).2.symm

theorem ar_load_rule_wp (Γ : T.Env)
    (hMsig : ∀ xs m Q X, arMsigSpec xs m Q X → Γ "ar_msig" [i64] [i64] xs m Q X) :
    ∀ xs m Q X, arLoadRuleSpec xs m Q X → Func.wp Γ ar_load_rule_body xs m Q X := by
  rintro ⟨cx, v, ⟨⟩⟩ m Q X
    ⟨s, ruleOff, ruleN, rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1,
      pool0, pool1, Valid, R, hpc, htc, hv_lt, hvn_ne, htcap30, hpcap32, hrspcap32,
      htm0_len, htm1_len, hts0_len, htl0_len, hth0_len, hts1_len, htl1_len, hth1_len,
      hp0_len, hp1_len, hNonEmpty, hRules, hRulesSorted, hrsOk32, hm, hQ⟩
  obtain ⟨σ₀, hV₀⟩ := hNonEmpty
  obtain ⟨hroff_len, hrn_len, hrsn_le, hrspt_le, hrsm_len, hrsl_len, hrsh_len, hrsp_len,
    hrsSlices, hRuleMap₀⟩ := hRules σ₀ hV₀
  obtain ⟨hoff_cnt, _⟩ := hRuleMap₀ v.toNat hv_lt hvn_ne
  let off := ruleOff.getD v.toNat 0#32
  let cnt := ruleN.getD v.toNat 0#32
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  let srcTm := if s.tc.toNat = 0 then tm0 else tm1
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  have hpool_len : s.pcap.toNat ≤ srcPool.length := by dsimp only [srcPool]; split <;> assumption
  have htm_len : s.tcap.toNat ≤ srcTm.length := by dsimp only [srcTm]; split <;> assumption
  have hts_len : s.tcap.toNat ≤ srcTs.length := by dsimp only [srcTs]; split <;> assumption
  have htl_len : s.tcap.toNat ≤ srcTl.length := by dsimp only [srcTl]; split <;> assumption
  have hth_len : s.tcap.toNat ≤ srcTh.length := by dsimp only [srcTh]; split <;> assumption
  obtain ⟨restT, htEq, htBack⟩ :=
    tMem_focus_cur s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 hpc htc
  have hm_u : (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
      array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      array (t := i32) s.rs_pool rsPool ⋆
      (u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R)) m := by
    have hm0 := hm; rw [rsMem_unfold, htEq] at hm0; exact sep_cast hm0 (by ac_rfl)
  have hl_s : ArCtxLengthsOk s :=
    arCtx_lengths (R := array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R)
      (sep_cast hm (by ac_rfl))
  have hv_sw : (BitVec.setWidth 64 v).toNat = v.toNat := by c0_bv_omega
  have hro_eq : ruleOff[v.toNat]'(by omega) = off := (getD_eq_getElem ruleOff 0#32 (by omega)).symm
  have hrn_eq : ruleN[v.toNat]'(by omega) = cnt := (getD_eq_getElem ruleN 0#32 (by omega)).symm
  c0_hsteps_nogrp
  · have hm_u0 : (arCtxMem cx { s with tn := 0#32, ptop := 0#64, qn := 0#32 } ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
        array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
        array (t := i32) s.rs_pool rsPool ⋆
        (u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R)) m :=
      sep_cast hm (by ac_rfl)
    exact loadRule_false_exit (s := s) (R := R) hm_u0 rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
      (htBack _ srcTm srcTs srcTl srcTh srcPool rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
      (fun ok s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' m'
          h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hok hm' =>
        hQ ok s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' m'
          h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (fun h => absurd h hok) hm')
  · dsimp only
    have hcnt_le : cnt.toNat ≤ s.tcap.toNat := by c0_bv_omega
    have hpool_pc : s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) =
        s.pool.getD s.pc.toNat 0#64 :=
      (getD_eq_getElem s.pool 0#64 (by rw [hl_s.pool]; exact hpc)).symm
    have htm_tc : s.tm[s.tc.toNat]'(by rw [hl_s.tm]; exact htc) =
        s.tm.getD s.tc.toNat 0#64 :=
      (getD_eq_getElem s.tm 0#64 (by rw [hl_s.tm]; exact htc)).symm
    have hts_tc : s.ts[s.tc.toNat]'(by rw [hl_s.ts]; exact htc) =
        s.ts.getD s.tc.toNat 0#64 :=
      (getD_eq_getElem s.ts 0#64 (by rw [hl_s.ts]; exact htc)).symm
    have htl_tc : s.tl[s.tc.toNat]'(by rw [hl_s.tl]; exact htc) =
        s.tl.getD s.tc.toNat 0#64 :=
      (getD_eq_getElem s.tl 0#64 (by rw [hl_s.tl]; exact htc)).symm
    have hth_tc : s.th[s.tc.toNat]'(by rw [hl_s.th]; exact htc) =
        s.th.getD s.tc.toNat 0#64 :=
      (getD_eq_getElem s.th 0#64 (by rw [hl_s.th]; exact htc)).symm
    let Rloop := array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      array (t := i32) s.rs_pool rsPool ⋆
      u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
    refine wp_loop_group (fun rem ⟨iV, ⟨⟩⟩ mL =>
        iV.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - iV.toNat ∧
        ∃ (pt : Nat) (tmC poolC : List (BitVec 32)) (tsC tlC thC : List (BitVec 64)),
          pt ≤ s.pcap.toNat ∧
          tmC.length = srcTm.length ∧ tsC.length = srcTs.length ∧
          tlC.length = srcTl.length ∧ thC.length = srcTh.length ∧ poolC.length = srcPool.length ∧
          (∀ k < iV.toNat,
            MonoSliceOk poolC (tmC.getD k 0#32).toNat pt ∧
            (poolC.getD (tmC.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 ∧
            symListAt poolC (tmC.getD k 0#32).toNat =
              symListAt rsPool (rsM.getD (off.toNat + k) 0#32).toNat ∧
            tlC.getD k 0#64 = rsL.getD (off.toNat + k) 0#64 ∧
            thC.getD k 0#64 = rsH.getD (off.toNat + k) 0#64) ∧
          SigOk poolC tmC tsC iV.toNat ∧
          monoTotalWords poolC tmC iV.toNat ≤ pt ∧
          (arCtxMem cx { s with tn := 0#32, ptop := BitVec.ofNat 64 pt, qn := 0#32 } ⋆
            array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolC ⋆
            array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
            array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆
            array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
            array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop) mL) ?_ ?_
    · intro J rem ⟨iV, ⟨⟩⟩ mL hrec
        ⟨hi_le, _, pt, tmC, poolC, tsC, tlC, thC, hpt_le, htmC_len, htsC_len, htlC_len, hthC_len,
          hpoolC_len, hPrev, hSigC, hWords, hmL⟩
      let sC : ArCtxState := { s with tn := 0#32, ptop := BitVec.ofNat 64 pt, qn := 0#32 }
      have hpt_toNat : (BitVec.ofNat 64 pt).toNat = pt := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      · have hi_lt : iV.toNat < cnt.toNat := by rw [← hrn_eq]; exact hc
        have hofi_le : off.toNat + cnt.toNat ≤ s.rs_n.toNat := hoff_cnt
        have hrs_i : off.toNat + iV.toNat < s.rs_n.toNat := by omega
        have hofi_32 : off.toNat + iV.toNat < 2 ^ 32 := by
          have := s.rs_cap.isLt; omega
        have hofi_eq : (off + iV).toNat = off.toNat + iV.toNat := by c0_bv_omega
        let Rrsm := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolC ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
          array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ array (t := i32) s.rule_off ruleOff ⋆
          array (t := i32) s.rule_n ruleN ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
          array (t := i32) s.rs_pool rsPool ⋆
          u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
        refine wp_load_arr32_idx (base := s.rs_m) (off := 0) (i := off + iV) (xs := rsM)
          (R := Rrsm) (by simp only [Arg.val, hv_sw, hro_eq]; simp) (by simp; omega)
          (sep_cast hmL (by dsimp only [sC, Rrsm, Rloop]; ac_rfl)) ?_
        let mOff32 := rsM[0 + (off + iV).toNat]'(by simp; omega)
        let mOff := mOff32.toNat
        have hmOff_eq : mOff = (rsM.getD (off.toNat + iV.toNat) 0#32).toNat := by
          dsimp only [mOff, mOff32]
          rw [← getD_eq_getElem rsM 0#32 (by simp; omega), Nat.zero_add, hofi_eq]
        have hmSlice := hrsSlices (off.toNat + iV.toNat) hrs_i
        have hmOk32 := hrsOk32 (off.toNat + iV.toNat) hrs_i
        rw [← hmOff_eq] at hmSlice hmOk32
        have hm_len_pool : mOff < rsPool.length := by have := hmSlice.1; omega
        have hm_sw : (BitVec.setWidth 64 mOff32).toNat = mOff := by c0_bv_omega
        c0_hsteps_nogrp
        let Rrsp := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolC ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
          array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ array (t := i32) s.rule_off ruleOff ⋆
          array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.rs_m rsM ⋆
          array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
          u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
        refine wp_load_arr32_abs (base := s.rs_pool) (xs := rsPool) (R := Rrsp)
          (i := BitVec.setWidth 64 mOff32) (by dsimp only [Arg.val, sC, mOff32]; simp)
          (by rw [hm_sw]; exact hm_len_pool)
          (sep_cast hmL (by dsimp only [sC, Rrsp, Rloop]; ac_rfl)) ?_
        let mlen := rsPool[(BitVec.setWidth 64 mOff32).toNat]'(by rw [hm_sw]; exact hm_len_pool)
        have hmlen_eq : mlen.toNat = (rsPool.getD mOff 0#32).toNat := by
          dsimp only [mlen]
          rw [← getD_eq_getElem rsPool 0#32 (by rw [hm_sw]; exact hm_len_pool), hm_sw]
        have hmlen32 : mlen.toNat + 1 < 2 ^ 32 := by rw [hmlen_eq]; exact hmOk32
        have hfail_pack : ∀ {mF : Mem 64} (sF : ArCtxState),
            sF = { s with tn := 0#32, ptop := BitVec.ofNat 64 pt, qn := 0#32 } →
            (arCtxMem cx sF ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolC ⋆
              array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
              array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆
              array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
              array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop) mF →
            Q (false, ⟨⟩) mF := fun {mF} sF hsF hmF =>
          hQ false sF _ _ _ _ _ _ _ _ _ _ mF
            (by subst sF; simp) (by subst sF; simp [hpt_toNat, hpt_le])
            (by subst sF; rfl)
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTm, htmC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTm, htmC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTs, htsC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTl, htlC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTh, hthC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTs, htsC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTl, htlC_len])
            (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTh, hthC_len])
            (by by_cases h0 : s.pc.toNat = 0 <;> simp [h0, srcPool, hpoolC_len])
            (by by_cases h0 : s.pc.toNat = 0 <;> simp [h0, srcPool, hpoolC_len])
            (fun h => by cases h)
            (loadRule_pack_mem (by subst sF; rfl) (by subst sF; rfl) (by subst sF; rfl)
              (by subst sF; rfl) (by subst sF; rfl) (by subst sF; rfl) (by subst sF; rfl)
              (by subst sF; rfl) (by subst sF; rfl) (by subst sF; rfl) (by subst sF; rfl)
              htmC_len htsC_len htlC_len hthC_len hpoolC_len htBack
              (by dsimp only [Rloop] at hmF; exact hmF))
        c0_hsteps_nogrp
        · exact hfail_pack sC rfl hmL
        · have hpt_add : pt + mlen.toNat + 1 ≤ s.pcap.toNat := by
            have hi_eq : (BitVec.setWidth 64 mOff32).toNat = mOff32.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := mOff32.isLt; omega)]
            exact loadRule_pt_add (hm_lt := by dsimp only [mOff] at hm_len_pool; exact hm_len_pool)
              (mlen := mlen) (by simp only [mlen, hi_eq]) hpt_le hpcap32 (by omega)
              (by simp only [← hi_eq]; exact hc)
          refine wp_loop_group (fun remj ⟨jV, ⟨⟩⟩ mJ =>
              jV.toNat ≤ mlen.toNat + 1 ∧ remj = mlen.toNat + 1 - jV.toNat ∧
              ∃ poolJ : List (BitVec 32), poolJ.length = poolC.length ∧
                (∀ q < pt, poolJ.getD q 0#32 = poolC.getD q 0#32) ∧
                (∀ r < jV.toNat, poolJ.getD (pt + r) 0#32 = rsPool.getD (mOff + r) 0#32) ∧
                (arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                  array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
                  array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆
                  array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                  array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop) mJ) ?_ ?_
          · intro Jj remj ⟨jV, ⟨⟩⟩ mJ hrecj ⟨hj_le, _, poolJ, hpoolJ_len, hOld, hCopied, hmJ⟩
            c0_hsteps_nogrp
            · have hj_ml : jV.toNat ≤ mlen.toNat := hc
              have hj_rs : mOff + jV.toNat < rsPool.length := by
                have := hmSlice.2; rw [← hmlen_eq] at this; omega
              have hj_dst : pt + jV.toNat < poolJ.length := by omega
              have hj_ptr : s.rs_pool + BitVec.setWidth 64 mOff32 * 4 +
                  BitVec.setWidth 64 jV * 4 =
                  s.rs_pool + BitVec.ofNat 64 (4 * mOff) + BitVec.setWidth 64 jV * 4 := by
                apply congrArg (· + BitVec.setWidth 64 jV * 4)
                apply congrArg (s.rs_pool + ·)
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_mul, BitVec.toNat_ofNat, hm_sw, Nat.mul_comm _ 4]
              let RrsJ := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ array (t := i32) s.rule_off ruleOff ⋆
                array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.rs_m rsM ⋆
                array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
                u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
              refine wp_load_arr32_idx (base := s.rs_pool) (off := mOff) (i := jV) (xs := rsPool)
                (R := RrsJ) hj_ptr hj_rs (sep_cast hmJ (by dsimp only [RrsJ, Rloop]; ac_rfl)) ?_
              have hptj_toNat : (BitVec.ofNat 64 pt + BitVec.setWidth 64 jV).toNat =
                  pt + jV.toNat := by
                rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by have := jV.isLt; omega),
                  Nat.mod_eq_of_lt (by omega)]
              let RpJ := arCtxMem cx sC ⋆ array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmC ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop
              refine wp_store_arr32_abs (base := s.pool.getD s.pc.toNat 0#64) (xs := poolJ)
                (idx := BitVec.ofNat 64 pt + BitVec.setWidth 64 jV) (R := RpJ) rfl
                (by dsimp only [Arg.val]; rw [hpool_pc, BitVec.add_mul])
                (by rw [hptj_toNat]; exact hj_dst) (sep_cast hmJ (by dsimp only [RpJ]; ac_rfl)) ?_
              intro mJ' hmJ'
              dsimp only [RpJ] at hmJ'
              have hjp1 : (jV + 1#32).toNat = jV.toNat + 1 := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32),
                  Nat.mod_eq_of_lt (by omega)]
              c0_hsteps
              refine hrecj (mlen.toNat + 1 - (jV + 1#32).toNat) (jV + 1#32, ⟨⟩) mJ' (by omega)
                ⟨by rw [hjp1]; omega, rfl,
                  poolJ.set (pt + jV.toNat) (rsPool[mOff + jV.toNat]'hj_rs),
                  by simp [hpoolJ_len], fun q hq => ?_, fun r hr => ?_, ?_⟩
              · rw [getD_set_eq poolJ 0#32 _ hj_dst, ite_eq_right (by omega)]
                exact hOld q hq
              · rw [getD_set_eq poolJ 0#32 _ hj_dst]
                by_cases hrj : r = jV.toNat
                · subst hrj; rw [ite_eq_left rfl, getD_eq_getElem rsPool 0#32 hj_rs]
                · rw [ite_eq_right (by omega)]; exact hCopied r (by rw [hjp1] at hr; omega)
              · rw [hptj_toNat] at hmJ'; exact sep_cast hmJ' (by ac_rfl)
            · have hj_done : jV.toNat = mlen.toNat + 1 := by
                have hc' : ¬ jV.toNat ≤ mlen.toNat := hc
                omega
              have hCopied' : ∀ r ≤ mlen.toNat,
                  poolJ.getD (pt + r) 0#32 = rsPool.getD (mOff + r) 0#32 :=
                fun r hr => hCopied r (by omega)
              have hmPtr : s.rs_pool + BitVec.setWidth 64 mOff32 * 4 =
                  s.rs_pool + BitVec.ofNat 64 (4 * mOff) := by
                apply congrArg (s.rs_pool + ·); apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_mul, BitVec.toNat_ofNat, hm_sw, Nat.mul_comm _ 4]
              have hi_tm : iV.toNat < tmC.length := by omega
              have hi_ts : iV.toNat < tsC.length := by omega
              have hi_tl : iV.toNat < tlC.length := by omega
              have hi_th : iV.toNat < thC.length := by omega
              have hofi_rsl : (off + iV).toNat < rsL.length := by rw [hofi_eq]; omega
              have hofi_rsh : (off + iV).toNat < rsH.length := by rw [hofi_eq]; omega
              let RtmJ := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop
              refine wp_store_arr32_idx (base := s.tm.getD s.tc.toNat 0#64) (idx := iV)
                (xs := tmC) (val := BitVec.ofNat 32 pt) (R := RtmJ)
                (by dsimp only [Arg.val, sC]; apply BitVec.eq_of_toNat_eq
                    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : pt < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : pt < 2 ^ 32)])
                (by dsimp only [Arg.val]; rw [htm_tc]) hi_tm
                (sep_cast hmJ (by dsimp only [RtmJ]; ac_rfl)) ?_
              intro m1 hm1
              dsimp only [RtmJ] at hm1
              c0_hsteps_nogrp
              let RsigJ := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64)
                  (tmC.set iV.toNat (BitVec.ofNat 32 pt)) ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) tsC ⋆ array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ array (t := i32) s.rule_off ruleOff ⋆
                array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.rs_m rsM ⋆
                array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
                u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
              refine wp_call_of_spec _ _ (hMsig (s.rs_pool + BitVec.setWidth 64 mOff32 * 4, ⟨⟩)
                m1 _ _ ⟨s.rs_pool, rsPool, mOff, RsigJ, hmPtr,
                  ⟨hm_len_pool, by have := hmSlice.2; omega⟩, hmOk32,
                  sep_cast hm1 (by dsimp only [RsigJ, Rloop]; ac_rfl), fun sig hsig => ?_⟩)
              let RtsJ := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64)
                  (tmC.set iV.toNat (BitVec.ofNat 32 pt)) ⋆
                array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop
              refine wp_store_arr64_idx (base := s.ts.getD s.tc.toNat 0#64) (idx := iV)
                (xs := tsC) (val := sig) (R := RtsJ) rfl
                (by dsimp only [Arg.val]; rw [hts_tc]) hi_ts
                (sep_cast hm1 (by dsimp only [RtsJ]; ac_rfl)) ?_
              intro m2 hm2
              dsimp only [RtsJ] at hm2
              c0_hsteps_nogrp
              let Rrsl := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64)
                  (tmC.set iV.toNat (BitVec.ofNat 32 pt)) ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) (tsC.set iV.toNat sig) ⋆
                array64 (s.tl.getD s.tc.toNat 0#64) tlC ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ array (t := i32) s.rule_off ruleOff ⋆
                array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.rs_m rsM ⋆
                array64 s.rs_h rsH ⋆ array (t := i32) s.rs_pool rsPool ⋆
                u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
              refine wp_load_arr64_idx (base := s.rs_l) (i := off + iV) (xs := rsL) (R := Rrsl)
                (by dsimp only [Arg.val, sC]; simp only [hv_sw, hro_eq]) hofi_rsl
                (sep_cast hm2 (by dsimp only [Rrsl, Rloop]; ac_rfl)) ?_
              let RtlJ := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64)
                  (tmC.set iV.toNat (BitVec.ofNat 32 pt)) ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) (tsC.set iV.toNat sig) ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ Rloop
              refine wp_store_arr64_idx (base := s.tl.getD s.tc.toNat 0#64) (idx := iV)
                (xs := tlC) (val := rsL[(off + iV).toNat]'hofi_rsl) (R := RtlJ) rfl
                (by dsimp only [Arg.val]; rw [htl_tc]) hi_tl
                (sep_cast hm2 (by dsimp only [RtlJ]; ac_rfl)) ?_
              intro m3 hm3
              dsimp only [RtlJ] at hm3
              c0_hsteps_nogrp
              let Rrsh := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64)
                  (tmC.set iV.toNat (BitVec.ofNat 32 pt)) ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) (tsC.set iV.toNat sig) ⋆
                array64 (s.tl.getD s.tc.toNat 0#64)
                  (tlC.set iV.toNat (rsL[(off + iV).toNat]'hofi_rsl)) ⋆
                array64 (s.th.getD s.tc.toNat 0#64) thC ⋆ array (t := i32) s.rule_off ruleOff ⋆
                array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.rs_m rsM ⋆
                array64 s.rs_l rsL ⋆ array (t := i32) s.rs_pool rsPool ⋆
                u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
              refine wp_load_arr64_idx (base := s.rs_h) (i := off + iV) (xs := rsH) (R := Rrsh)
                (by dsimp only [Arg.val, sC]; simp only [hv_sw, hro_eq]) hofi_rsh
                (sep_cast hm3 (by dsimp only [Rrsh, Rloop]; ac_rfl)) ?_
              let RthJ := arCtxMem cx sC ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolJ ⋆
                array (t := i32) (s.tm.getD s.tc.toNat 0#64)
                  (tmC.set iV.toNat (BitVec.ofNat 32 pt)) ⋆
                array64 (s.ts.getD s.tc.toNat 0#64) (tsC.set iV.toNat sig) ⋆
                array64 (s.tl.getD s.tc.toNat 0#64)
                  (tlC.set iV.toNat (rsL[(off + iV).toNat]'hofi_rsl)) ⋆ Rloop
              refine wp_store_arr64_idx (base := s.th.getD s.tc.toNat 0#64) (idx := iV)
                (xs := thC) (val := rsH[(off + iV).toNat]'hofi_rsh) (R := RthJ) rfl
                (by dsimp only [Arg.val]; rw [hth_tc]) hi_th
                (sep_cast hm3 (by dsimp only [RthJ]; ac_rfl)) ?_
              intro m4 hm4
              dsimp only [RthJ] at hm4
              have hpt'_eq : BitVec.ofNat 64 pt + BitVec.setWidth 64 mlen + (1 : BitVec 64) =
                  BitVec.ofNat 64 (pt + mlen.toNat + 1) := by
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                  show ((1 : BitVec 64)).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : pt < 2 ^ 64),
                  Nat.mod_eq_of_lt (by have := mlen.isLt; omega : mlen.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : pt + mlen.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : pt + mlen.toNat + 1 < 2 ^ 64)]
              have hip1 : (iV + 1#32).toNat = iV.toNat + 1 := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32),
                  Nat.mod_eq_of_lt (by omega : iV.toNat + 1 < 2 ^ 32)]
              c0_hsteps
              have hstep := loadRule_step_pack hPrev hSigC hWords hi_tm hi_ts hi_tl hi_th
                hmOff_eq hmlen_eq hmlen32 hpt_add hpcap32 hOld hCopied' hofi_rsl hofi_rsh
                hofi_eq hsig
              refine hrec (cnt.toNat - (iV + 1#32).toNat) (iV + 1#32, ⟨⟩) _ (by omega)
                ⟨by omega, rfl, pt + mlen.toNat + 1, tmC.set iV.toNat (BitVec.ofNat 32 pt),
                  poolJ, tsC.set iV.toNat sig,
                  tlC.set iV.toNat (rsL[(off + iV).toNat]'hofi_rsl),
                  thC.set iV.toNat (rsH[(off + iV).toNat]'hofi_rsh),
                  by omega, by simp [htmC_len], by simp [htsC_len], by simp [htlC_len],
                  by simp [hthC_len], hpoolJ_len.trans hpoolC_len,
                  by rw [hip1]; exact hstep.1, by rw [hip1]; exact hstep.2.1,
                  by rw [hip1]; exact hstep.2.2, ?_⟩
              · dsimp only [sC] at hm
                dsimp only [mlen] at hpt'_eq
                rw [hpt'_eq] at hm
                exact sep_cast hm (by ac_rfl)
          · intro Jj hJj
            c0_hsteps
            exact hJj (mlen.toNat + 1) (0#32, ⟨⟩) mL
              ⟨Nat.zero_le _, rfl, poolC, rfl, fun _ _ => rfl,
                fun _ hr => absurd hr (Nat.not_lt_zero _), hmL⟩
      · have hi_done : iV.toNat = cnt.toNat := by simp only [hrn_eq] at hc; c0_bv_omega
        c0_hsteps
        simp only [hv_sw, hrn_eq] at hm
        let s' : ArCtxState := { s with tn := cnt, ptop := BitVec.ofNat 64 pt, qn := 0#32 }
        have hm'_cast := loadRule_pack_mem (cx := cx) (s := s) (s' := s') (ruleOff := ruleOff)
          (ruleN := ruleN) (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool)
          (tm0 := tm0) (tm1 := tm1) (ts0 := ts0) (tl0 := tl0) (th0 := th0)
          (ts1 := ts1) (tl1 := tl1) (th1 := th1) (pool0 := pool0) (pool1 := pool1)
          (tmC := tmC) (tsC := tsC) (tlC := tlC) (thC := thC) (poolC := poolC)
          (restT := restT) (R := R)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          htmC_len htsC_len htlC_len hthC_len hpoolC_len htBack
          (sep_cast hm (by dsimp only [Rloop]; ac_rfl))
        refine hQ true s'
          (if s.tc.toNat = 0 then tmC else tm0) (if s.tc.toNat = 0 then tm1 else tmC)
          (if s.tc.toNat = 0 then tsC else ts0) (if s.tc.toNat = 0 then tlC else tl0)
          (if s.tc.toNat = 0 then thC else th0) (if s.tc.toNat = 0 then ts1 else tsC)
          (if s.tc.toNat = 0 then tl1 else tlC) (if s.tc.toNat = 0 then th1 else thC)
          (if s.pc.toNat = 0 then poolC else pool0) (if s.pc.toNat = 0 then pool1 else poolC)
          m hcnt_le (by simp [s', hpt_toNat, hpt_le]) rfl
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTm, htmC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTm, htmC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTs, htsC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTl, htlC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTh, hthC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTs, htsC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTl, htlC_len])
          (by by_cases h0 : s.tc.toNat = 0 <;> simp [h0, srcTh, hthC_len])
          (by by_cases h0 : s.pc.toNat = 0 <;> simp [h0, srcPool, hpoolC_len])
          (by by_cases h0 : s.pc.toNat = 0 <;> simp [h0, srcPool, hpoolC_len])
          (fun _ => loadRule_done_inv hv_lt hvn_ne hpc htc rfl hoff_cnt hi_done hpt_toNat
            hPrev hSigC hWords hRules hRulesSorted)
          hm'_cast
    · intro J hJ
      c0_hsteps
      have hm_init : (arCtxMem cx { s with tn := 0#32, ptop := BitVec.ofNat 64 0, qn := 0#32 } ⋆
          array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ Rloop) m := by
        try rw [rsMem_unfold] at hm
        try rw [htEq] at hm
        exact sep_cast hm (by dsimp only [Rloop]; ac_rfl)
      exact hJ cnt.toNat (0#32, ⟨⟩) m
        ⟨Nat.zero_le _, rfl, 0, srcTm, srcPool, srcTs, srcTl, srcTh,
          Nat.zero_le _, rfl, rfl, rfl, rfl, rfl,
          fun _ hk => absurd hk (Nat.not_lt_zero _), sigOk_empty _ _ _,
          by simp [monoTotalWords], hm_init⟩

end

end LeanQbe.T.Examples.Arisca.Proof
